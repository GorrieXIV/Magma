freeze;

// import "../Smash/random.m": RandomElement;
import "../Smash/random.m": ElementOfOrder;
import "../Smash/misc.m": ReverseBubbleSort, ElementCommutes;
import "../Smash/misc.m": EliminateRepetitions, CentralisedSpaceSetMod;
import "action.m": FindAction, SubQuotAction;
import "stabiliser.m": SpaceStabiliser;
import "local.m": HasShortLattice;

/* generate some elements having powers which have order RequiredOrder;
   in practice, we use this where RequiredOrder is the characteristic;
   we sort in decreasing order and seek to remove powers of elements
   from the list */

procedure pLocalElements (G, RequiredOrder, NmrTries, ~Orders, ~Elts)

   local o, i, rem, x;

   p := Characteristic (BaseRing (G));

   Orders := [];
   Elts := [];

   P := RandomProcess (G);
   M := Floor (Sqrt (NmrTries));
   for i in [1..M] do
      N := 1;
      repeat
         x := Random (P);
         o := RequiredOrder eq p select Order (x) else ProjectiveOrder (x);
         rem := (o mod RequiredOrder eq 0);
         N +:= 1;
      until rem or (N eq M);
      if rem and not (o in Orders) then
         Append (~Orders, o);
         Append (~Elts, x);
      end if;
   end for;

   ReverseBubbleSort (~Orders, ~Elts);
   EliminateRepetitions (~Elts, ~Orders);

end procedure;

/* given G is a matrix group of characteristic p
   X is a collection of elements of order dividing p;

   Is <X>^G a p-group or trivial?

   We need to find a chain of G-submodules 
  
   0 = V_0 <= V_1 <= ... <= V_k = V
   
   of the natural module such that x centralises 
   V_i / V_(i - 1) for all x in X and all i */

IspNormal := function (G, X)

   if Set (X) eq {Identity (G)} then return true; end if;

   M := GModule (G);
   W := Meataxe (M);

   if IsIrreducible (M) then return false; end if;

   F := BaseRing (G);
   d := Degree (G);
   V := VectorSpace (F, d);

   m := Morphism (W, M);
   BasisW := Basis (W);
   b := [Eltseq (m (BasisW[i])) : i in [1..#BasisW]];
   W := sub <V | b>;

   Sub, Quo, C := FindAction (G, V, W); 
   s, q := SubQuotAction (X, W, C);

   resultS := $$ (Sub, s);
   resultQ := $$ (Quo, q);

   return (resultS and resultQ);

end function;

/* compute chain of subspaces  
      0 = V_0 <= V_1 <= ... <= V_k = V
   of the natural module such that x centralises 
   V_i / V_(i - 1) for all x in X and all i */

ComputeSpaces := function (G, X)

   d := Degree (G);
   F := BaseRing (G);
   W := [];
   V := VectorSpace (F, d);
   Spaces := [V];

   i := 0;
   repeat 
      W := CentralisedSpaceSetMod (G, X, W);
      i +:= 1;
      Spaces[i] := W;
   until Dimension (W) eq d;

   // Spaces := [Spaces[j] : j in [1..i]];
   D := [Dimension (Spaces[i]) : i in [1..#Spaces]];

   return Spaces, D;

end function;

/* X is a collection of non-scalar elements of G and generates a 
   p-subgroup of G, W is an <X>-invariant space; return a p-local 
   subgroup H which normalises a p-subgroup containing X */

pLocal := function (G, X, W, Nmr, NmrTries)

   p := Characteristic (BaseRing (G));

   /* do all elements have order dividing p? */
   if #[Order (x) : x in X |  Order (x) ne p and Order (x) ne 1] ne 0 then 
     vprint Tensor: "Supplied set contains element of order different from ", p;
     return false;
   end if;

   U := CentralisedSpaceSetMod (G, X, W);
  
   H := SpaceStabiliser (G, U, Nmr, NmrTries);
   P := GL (Degree (G), BaseRing (G));
   H := sub <P | H, X>;

   if IspNormal (H, X) then return H; end if;

   return $$ (H, X, U, Nmr, NmrTries);

end function;

/* can we find element of order p in H which commutes with every 
   element of X? we also require that its chain of subspaces  
   differs from those stored in Spaces */

CommutingElement := function (G, H, X, g, Spaces, p, NmrTries)

   N := 10;

   P := GL (Degree (G), BaseRing (G));
   s := sub <P | g>;
   i := 0;
   repeat
      i +:= 1;
      h := ElementOfOrder (H, p, N);
      if Type (h) ne BoolElt then 
         if not (h in s) and ElementCommutes (h, X) then 
            S, D := ComputeSpaces (H, [h]);
            if not (S in Spaces) then 
               vprint Tensor: "New element found on attempt ", i;
               vprintf Tensor: "Dimensions of associated spaces is %o\n", D;
               return true, h, S, D; 
            end if;
         end if;
      end if;
   until i eq N;

   vprint Tensor: "No new element found";
   return false, Identity (H), false, false;

end function; 

/* construct a list of p-local subgroups where each p-group 
   contains g and may have rank at most Rank */

procedure pLocalSubgroups (G, parent, g, Nmr, NmrTries, ~Subs, ~Settled)

   P := GL (Degree (G), BaseRing (G));
   X := [P!g];
   W := [];

   /* compute p-local subgroup containing g */
   H := pLocal (G, X, W, Nmr, NmrTries);
   H := sub <P | H, parent>; 
   // vprint Tensor: "Order is ", Order (H);

   Subs := [H]; 
   Settled := HasShortLattice (H);

   /* if H is cyclic, we will not find a new element */
   if Ngens (H) eq 1 or Settled then return; end if;

   /* compute information about our element, g */
   MaxRank := 3;
   Bin := [X];

   Spaces := []; Dims := [];
   Spaces[1], Dims[1] := ComputeSpaces (G, Bin[1]);
   vprintf Tensor: "Dimensions of associated spaces is %o\n", Dims;

   p := Characteristic (BaseRing (G));

   /* now look for element h in p-local subgroup H which commutes with 
      all elements in the bin of H; if the dimensions of its associated 
      spaces are the same as those of elements in that bin, we expect that 
      the elements are conjugate; we add h to the bin for H and compute 
      p-local containing this larger bin; otherwise, we create new bin 
      with single element h */ 

   i := 0;
   repeat
      i +:= 1;
      H := Subs[i];
      X := Bin[i];

      if Ngens (H) eq 1 then continue; end if;

      found, h, S, D := CommutingElement (G, H, X, g, Spaces, p, NmrTries);

      /* if we find a new element, its construction ensures that the 
         new element h and the elements of X are not conjugate in H */

      /* did we find new element? */
      if found then 

         /* if the new element has the same dimensions as the elements 
            of the bin, then they are probably conjugate in G (we know
            by construction that these are not conjugate in H); if so,
            compute local subgroup containing existing bin + this new element; 
            otherwise compute local subgroup for new element */

         X := D eq Dims[i] select (Bin[i] cat [h]) else [h];
         vprintf Tensor: "i = %o #X is now %o\n", i, #X;

         Append (~Bin, X);
         Append (~Spaces, S);
         Append (~Dims, D);

         H := pLocal (G, X, W, Nmr, NmrTries);

         /* can this subgroup settle the computation? */
         if HasShortLattice (H) then 
            Subs := [H]; Settled := true; 
            return;
         end if;

         Append (~Subs, H);
      end if;

   until (i eq Minimum (MaxRank, #Subs)); 

   Settled := false;
   
end procedure;
