freeze;

import "plocal.m": pLocalSubgroups, pLocalElements;
import "pdash.m": pDashSubgroup, pDashLocalElements, pDashLocals;
import "direct.m": ObtainDirectSumSpaces;
import "find-point.m": FindPoint;
import "../Smash/misc.m": BubbleSort;

SetVerbose ("Lattice", 1);

/* we believe that the best local subgroup is that 
   whose G-Module has shortest composition length */

BestCompLength := function (Subs)
   
   M := [GModule (Subs[i]) : i in [1..#Subs]];
   Len := [#CompositionSeries (M[i]) : i in [1..#Subs]];
   vprintf Tensor: "Composition lengths are %o\n", Len;
   m, index := Minimum (Len);

   // vprint Tensor: "Shortest composition length is ", m;

   return m, index; 

end function;

/* g is a power of parent; find a p-local subgroup of G which
   contains the normaliser of g */ 

LocalSubgroup := function (G, parent, g, Nmr, NmrTries)
   
   p := Characteristic (BaseRing (G));

   H := ProjectiveOrder (g) eq p select 
             pLocalSubgroups (G, parent, g, Nmr, NmrTries) else
             pDashSubgroup (G, parent, g, Nmr, NmrTries);

   return H;

end function;

/* does the submodule of H have a short lattice? */

HasShortLattice := function (H)

   /* maximum composition length */
   MaxLen := 4;

   M := GModule (H);

   cl := #CompositionSeries (M);
   if cl gt MaxLen then 
      vprintf Tensor: "Lattice has composition length %o\n", cl;
      return false; 
   end if;

   /* maximum number of submodules to compute */
   MaxNmrSubmodules := 1000;

   AllFound, L := SubmoduleLatticeAbort (M, MaxNmrSubmodules);

   return AllFound;

end function; 

/* compute lattice of H-submodules; if ComputePartial is true, 
   then return partial lattice */

ComputeLattice := function (H, MaxNmrSubmodules, ComputePartial)

   M := GModule (H);

   if ComputePartial then 
      L, AllFound := SubmoduleLattice (M: Limit := MaxNmrSubmodules);
   else 
      AllFound, L := SubmoduleLatticeAbort (M, MaxNmrSubmodules);
      if not AllFound then L := []; end if;
   end if; 

   if AllFound then 
      vprintf Tensor: "Length of submodule lattice is %o\n", #L;
   else 
      vprintf Tensor: "Lattice construction incomplete; it has length at least %o\n", 
            MaxNmrSubmodules;
   end if;
  
   return L, AllFound;

end function;

/* construct local subgroups for G which may act reducibly on 
   some of the factors whose dimensions are recorded in List */

procedure LocalSubgroups (G, ~Subs, Nmr, NmrTries, List, ~Result)

   /* parameters */
   ShortCompLength := 4;
   NmrpLocal := 5;
   TotalLocal := 10;
   NmrSearches := 25;

   RF := recformat <H : GrpMat, pLocal: BoolElt, 
                    pLocalElement : GrpMatElt, ReducibleDims : SetEnum>;

   Subs := [];

   p := Characteristic (BaseRing (G));

   vprintf Tensor: "\nFirst look for %o-local subgroups\n", p;

   pLocalElements (G, p, NmrSearches, ~Orders, ~Elts);

   /* distinct orders of parents */
   vprintf Tensor: "Orders of parents of %o-local elements are %o\n", p, Orders;

   for i in [1..#Orders] do 
      o := Orders[i];
      parent := Elts[i];
      g := parent^(o div p);
      pLocalSubgroups (G, parent, g, Nmr, NmrTries, ~NewSubs, ~Settled);

      /* have we found a p-local with a small submodule lattice? */
      if Settled then 
         r := rec <RF | H := NewSubs[1], pLocal := true, 
                        pLocalElement := g, ReducibleDims := List>;
         Subs := [r];
         return; 
      end if;

      for j in [1..#NewSubs] do 
         r := rec <RF | H := NewSubs[j], pLocal := true, 
                        pLocalElement := g, ReducibleDims := List>;
         Append (~Subs, r);
      end for;

      if (#Subs ge NmrpLocal) then break; end if;

   end for;

   pDashLocalElements (G, NmrSearches, ~Orders, ~Elts);

   vprintf Tensor: "Orders of parents of %o-dash elements are %o\n", p, Orders;

   /* distinct primes obtainable from Orders */
   D := &join{Set (PrimeBasis (o)) : o in Orders};
   vprintf Tensor: "Distinct primes are %o\n", D;

   pDashSubs := []; 
   /* now compute local subgroups for different primes */
   for i in [1..#Orders] do 
      o := Orders[i];
      parent := Elts[i];
      pDashLocals (G, RF, ~Subs, parent, o, Nmr, NmrTries, List, ~Settled);
      if (Settled) then return; end if;
      if (#Subs ge TotalLocal) then break; end if;
   end for;

end procedure;

/* investigate each submodule in the lattice and decide if it 
   is a flat in a u-projective geometry for some u in DimU */

procedure InvestigateLattice (G, L, DimU, ~Status, ~CB : Exact := false)

   d, F := BasicParameters (G);

   V := VectorSpace (F, d);

   for j in [1..#L] do 
      B := Morphism (L!j);
      Base := [V!B[i]: i in [1..Dimension(Domain(B))]];
      S := sub <V | Base>;
      if Dimension (S) mod d eq 0 then continue; end if;
      TestDim := {u : u in DimU | Dimension (S) mod u eq 0};
      if #TestDim ne 0 then 
         Spaces := [S];
         vprintf Tensor: "Processing space %o of dimension %o\n", j, Dimension (S);
         ObtainDirectSumSpaces (G, ~Spaces, ~flag);
         if flag eq true then 
            for u in TestDim do 
//            vprint Tensor: "Investigating geometry for u = ", u;
               FindPoint (G, ~Spaces, u, ~FPStatus, ~CB);
               if FPStatus cmpeq true then 
                  if Type (CB) eq Tup then 
                     if (CB[2] in DimU) or (Exact eq false) then 
                        vprint Tensor: "Found geometry for u = ", CB[2]; 
                        Status := true;
                        return; 
                     end if;
                  else 
                     vprint Tensor: "Found tensor decomposition over larger field";
                  end if;
               elif FPStatus cmpeq "unknown" then 
                  Status := "unknown"; 
               end if;
            end for;
         else 
            vprintf Tensor: "Failed to find points in general position\n";
            Status := "unknown"; 
         end if;
      end if;
   end for;

   if assigned Status eq false then 
      Status := false; 
   end if;
   CB := "undefined";

end procedure;

intrinsic IL (G:: GrpMat, L:: SubModLat, DimU:: SetEnum) -> BoolElt
{return intrinsic}
   InvestigateLattice (G, L, DimU, ~Status, ~CB : Exact := false);
  return true;
end intrinsic; 

/* run local subgroup test; List is possible dimensions of factorisations */

procedure LocalTest (G, ~List, ~Result, Nmr, NmrTries: Exact := false) 

   exact := Exact;

   Result := false;
   LocalSubgroups (G, ~Subs, Nmr, NmrTries, List, ~Result);
   if Type (Result) ne BoolElt then return; end if;

   //o := [Order (Subs[i]`H) : i in [1..#Subs]];
   //vprint Tensor: "Orders for these subgroups is ", o, "\n";

   /* we use composition lengths to sort local subgroups */

   M := [GModule (Subs[i]`H) : i in [1..#Subs]];
   Len := [#CompositionSeries (M[i]) : i in [1..#Subs]];
   vprintf Tensor: "Composition lengths are %o\n", Len;

   d := Degree (G);
   MaxNmrSubmodules := [1000, 10000];
   NmrTrials := 2; 

   BubbleSort (~Len, ~Subs);

   Trial := 0;
   repeat 
      Trial +:= 1;
      for i in [1..#Subs] do
         vprintf Tensor: "\nPossible dimensions of U are now %o\n", List;
         H := Subs[i]`H;
         m := Len[i];
         vprintf Tensor: "Shortest composition length for local subgroup H is %o\n", m;
    
         p := ProjectiveOrder (Subs[i]`pLocalElement);
         vprintf Tensor: "The subgroup is %o-local\n", p;

         if Subs[i]`pLocal then 
            /* here, H acts reducibly in all dimensions but there may be a 
               more general version later */
            RedH := Subs[i]`ReducibleDims;
            vprintf Tensor: "H is guaranteed to act reducibly in dimension %o\n", RedH;
         end if;

         L, AllFound := ComputeLattice (H, MaxNmrSubmodules[Trial], 
                                        Trial eq NmrTrials);

         /* we may change this later */
         if (AllFound eq false and Trial lt NmrTrials) then continue; end if;

         /* consider projective geometries for relevant dimensions */

         Search := List;

         vprintf Tensor: "Search for geometry in following dimensions %o\n", Search;
         InvestigateLattice (G, L, Search, ~Status, ~Result: Exact := exact);
         if Status cmpeq true then return; end if;

         /* there may be a more general version where pLocal is not true */
         if Status cmpeq false and AllFound and Subs[i]`pLocal then 
            DimU := {d div w : w in RedH};
            List diff:= DimU;
         end if;

         if #List eq 0 then Result := false; return; end if;

      end for;
   until Trial eq NmrTrials; 

   Result := (#List eq 0) select false else "unknown";

end procedure;
