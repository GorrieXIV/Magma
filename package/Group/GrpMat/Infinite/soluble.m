freeze;

import "attributes.m": RF;
import "general.m": IsDiagonalisable, IsKnownFinite, IsKnownSF, IsKnownSoluble, 
   SetVirtualValues, SetValues, IsKnownCR, IsUpperTriangularGroup; 
import "virtual.m": BasisEnvelopingAlgebraClosure;
import "virtual.m": ExploreBasis, IsMonomialGroup; 
import "finite.m": ConstructCT, MatrixHasFiniteOrder;
import "jordan.m": JordanIndexTest;
import "congruence.m": IsValidInput, MyCongruenceImage;
import "present.m": ConstructPresentation;

/* are matrices diagonalisable? */

procedure DiagonalCheck (G)
   if Type (G) in {GrpMatElt, AlgMatElt} then 
      gens := {G}; 
   else
      gens := {G.i: i in [1..Ngens (G)]}; 
   end if;
   if exists{g : g in gens | not IsDiagonalisable (g)} then 
      error "Not all generators diagonalisable: cannot decide soluble-by-finite";
   end if;
end procedure;

/* is G-normal closure of K unipotent-by-abelian? */

IsUnipotentByAbelian := function (G, K)
   S := [G.i: i in [1..Ngens (G)]];
   vprint Infinite: "Construct basis for enveloping algebra of closure of congruence subgroup";
   B := BasisEnvelopingAlgebraClosure (G, K, S);
   // vprint Infinite: "Last reported was for BasisEnvelopingAlgebraClosure"; 
   flag, CList, blocks := ExploreBasis (K, S, B, [* *], []);
   if flag then 
      return flag, CList, blocks;
   else
      return flag, _, _;
   end if;
end function;

/* is G-normal closure of E unipotent-by-abelian? */

TestKernelElements := function (G, E, tau)
   E := {E[i]^(Order (tau (E[i]))): i in [1..#E]};
   if forall{e : e in E | IsIdentity (e)} then return true; end if;
   F := BaseRing (G); d := Degree (G);
   MA := MatrixAlgebra (F, d);
   flag := IsUnipotentByAbelian (G, sub<MA | E>);
   return flag;
end function;

/* is index of soluble radical of congruence image for NmrTrials primes > p 
   always less than Jordan index? If so, return true, else false */
 
TestSolubleRadical := function (G, p: NmrTrials := 2)
   nmr := 1;
   repeat 
      H, tau, images := MyCongruenceImage (G: Selberg := true, 
                           Virtual := true, Prime := NextPrime (p));
      p := Characteristic (BaseRing (H));
      o := ConstructCT (H);
      if JordanIndexTest (H) eq false then
         vprint Infinite: "Index of soluble radical is too large";
         return false;
      end if;
      nmr +:= 1;
   until nmr gt NmrTrials;

   return true;
end function;

ConstructBasis := function (G, CBList)
   d := Degree (G);
   F := BaseRing (G);
   blocks := [CBList[i][2]: i in [1..#CBList]];
   return GL(d, F) ! &*[CBList[i][1]: i in [#CBList..1 by -1]], blocks;

   d := Degree (G);
   F := BaseRing (G);
   blocks := [CBList[i][2]: i in [1..#CBList]];
   r := d - &+blocks;
   if r gt 0 then blocks cat:= [r]; end if;
   MA := MatrixAlgebra (F, d);
   // L := [* CB[1][1] *];
   CB := CBList[1][1];
   for i in [2..#CBList] do
      offset := &+[blocks[j]: j in [1..i - 1]];
      A := Identity (MA);
      B := CBList[i][1];
      InsertBlock (~A, B, offset + 1, offset + 1); 
      CB := A * CB;
   end for;
   return GL(d, F) ! CB, blocks;
end function;

/* Exact: is G soluble? */

MyIsSolubleByFinite := function (G: OrderLimit := 10^15, Exact := false,
   NeedChangeOfBasis := false, UseCongruence := true, Small := 10^6, 
   Short := 30, Presentation := "CT") 

   if IsKnownFinite (G) and Exact eq false then return true; end if;
   
   flag := Exact select IsKnownSoluble (G) else IsKnownSF (G);

   // can we decide quickly? 
   if not NeedChangeOfBasis then 
      if flag cmpeq true or flag cmpeq false then return flag; end if;
      if IsAbelian (G) or IsUpperTriangularGroup (G) then 
         SetVirtualValues (G, "Soluble", true); return true; 
      end if;

      if IsMonomialGroup (G) and not Exact then 
         SetVirtualValues (G, "SF", true); 
         return true;
      end if;
   else 
      if (flag cmpeq true and assigned G`SFChangeOfBasis) or 
         (flag cmpeq false) then return flag; end if;
   end if;

   if not IsValidInput (G) then 
      error "IsSolubleByFinite: incorrect input";
   end if;

   F := BaseRing (G); d := Degree (G);
   
   if not UseCongruence and 
      ((ISA (Type (F), FldRat) or ISA (Type (F), RngInt) or 
        ISA (Type (F), FldNum))) and (InternalIsFinite (G) cmpeq true) then 
      return InternalIsSoluble (G);
   end if;

   p := Characteristic (F);
   Virtual := not (p in {2..d}); 

   // NumberRandom: test if normal closure of at most this number of random 
   // infinite order elements of congruence subgroup is unipotent-by-abelian; 
   NumberRandom := 0; 

   // TestRelations: construct normal generators of congruence subgroup 
   // one-by-one, and test if normal closure so far is unipotent-by-abelian 
   TestRelations := false;
     
   /* do we know map of the appropriate type? */
   if assigned G`Congruence and assigned G`Congruence`Subgroup then 
      known := (Virtual eq true  and G`Congruence`Virtual) or 
               (Virtual eq false and G`Congruence`Selberg);
   else 
      known := false; 
   end if;
   
   if known then 
      Data := G`Congruence;
      I := Data`Image; 
      if Exact and not LMGIsSoluble (I) then 
         SetVirtualValues (G, "Soluble", false);
         return false; 
      end if;
      K := Data`Subgroup;  
      if (not Virtual) then DiagonalCheck (K); end if;
   else
      H, tau, images := MyCongruenceImage (G: Selberg := true, Virtual := Virtual);
      if IsTrivial (H) then 
         K := G;
         G`Congruence`Subgroup := K;
         if not Virtual then DiagonalCheck (K); end if;
      else 
         o := ConstructCT (H);
         if Exact and not LMGIsSoluble (H) then 
            SetVirtualValues (G, "Soluble", false);
            return false; 
         end if;

         /* in characteristic 0 apply Jordan index test */
         if p eq 0 and JordanIndexTest (H) eq false then
            vprint Infinite: "Index of soluble radical is too large";
            SetVirtualValues (G, "SF", false); 
            return false;
         end if;

         /* try various congruence images for other primes */
         if p eq 0 then 
            keep := G`Congruence;
            flag := TestSolubleRadical (G, Characteristic (BaseRing (H)));
            G`Congruence := keep;
            if flag eq false then 
               SetVirtualValues (G, "SF", false); 
               return false;
            end if;
         end if;

         gens, Rels := ConstructPresentation (G, H, images: Short := Short, 
         Small := Small, OrderLimit := OrderLimit, Presentation := Presentation);

         MA := MatrixAlgebra (F, d);
         if not Virtual then
            E := [MA | ];
            for i in [1..#Rels] do
               vprint Infinite: "Non virtual case: process relator ", i;
               E[i] := Evaluate (Rels[i], gens);
               DiagonalCheck (E[i]); 
            end for;
         else 
            if p eq 0 and NumberRandom gt 0 then 
               vprint Infinite: "Test some random elements of kernel";
               P := RandomProcess (G: Scramble := 10);
               E := [Random (P): i in [1..NumberRandom]];
               E := [e : e in E | not MatrixHasFiniteOrder (e)];
               vprintf Infinite: "Constructed %o elements of infinite order\n", #E;
               if TestKernelElements (G, E, tau) eq false then 
                  SetVirtualValues (G, "SF", false); 
                  return false; 
               end if;
            end if;

            if p eq 0 and TestRelations then 
               E := [MA | ];
               for i in [1..#Rels] do
                  vprint Infinite: "Virtual case: process relator ", i;
                  E[i] := Evaluate (Rels[i], gens);
                  if TestKernelElements (G, E, tau) eq false then 
                     SetVirtualValues (G, "SF", false); return false; 
                  end if;
               end for;
            else
               vprint Infinite: "Now evaluating all relators ...";
               E := Evaluate (Rels, gens);
            end if;
         end if;
         K := sub<MA | E>;
         K`UserGenerators := E;
         K`UserWords := <gens, Rels>;
         SetValues (G, H, K, Rels);
      end if;

      if IsKnownFinite (G) and Exact eq false then 
         SetVirtualValues (G, "SF", true); 
         return true; 
      end if;
   end if;

   flag, CList, blocks := IsUnipotentByAbelian (G, K);

   /* completely reducible? all 3 of SF, NF, AF are equivalent */
   if Exact then 
      SetVirtualValues (G, "Soluble", flag);
   elif IsKnownCR (G) cmpeq true then 
      G`Congruence`SolubleByFinite := flag;
      G`Congruence`NilpotentByFinite := flag;
      G`Congruence`AbelianByFinite := flag;
   else
      SetVirtualValues (G, "SF", flag);
   end if;

   if flag then 
      CB := ConstructBasis (G, CList); 
      if #blocks eq 0 then blocks := [Degree (G)]; end if;
      G`SFChangeOfBasis := <CB, blocks>;
      // return true, CB, blocks;
      return true;
   else 
      // return false, _, _; 
      return false;
   end if;
end function;

intrinsic IsSolubleByFinite (G:: GrpMat: OrderLimit := 10^15, 
   NeedChangeOfBasis := false, Small := 10^6, Short := 30, 
   Presentation := "CT") -> BoolElt 
{ is G soluble-by-finite? if so, return true, else false;  
   Presentation: one of "CT", "FP", "PC" to dictate method of construction;
   Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
   Short: defining length for short presentation;
   NeedChangeOfBasis: is change-of-basis to exhibit this needed?   
}
   return MyIsSolubleByFinite (G: Exact := false, OrderLimit := OrderLimit,
      NeedChangeOfBasis := NeedChangeOfBasis, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic; 

intrinsic IsPolycyclicByFinite (G:: GrpMat[RngInt]: OrderLimit := 10^15, 
   Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt 
{ is matrix group G defined over the integers polycyclic-by-finite? 
  if so, return true, else false;  
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   return MyIsSolubleByFinite (G: OrderLimit := OrderLimit, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsPolycyclic (G:: GrpMat[RngInt]: OrderLimit := 10^15, 
   Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt 
{ is finite matrix group G defined over the integers polycyclic? 
  if so, return true, else false;  
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   return MyIsSolubleByFinite (G: Exact := true, OrderLimit := OrderLimit, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsSoluble (G:: GrpMat[RngInt]: OrderLimit := 10^15,
   UseCongruence := false, Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt
{ is matrix group G defined over the integers soluble?
  if so, return true, else false;
  UseCongruence: use congruence machinery to decide;
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   flag := IsKnownSoluble (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;
   return MyIsSolubleByFinite (G: OrderLimit := OrderLimit, Exact := true, 
      UseCongruence := UseCongruence, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsSoluble (G:: GrpMat[FldRat]: OrderLimit := 10^15,
  UseCongruence := false, Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt
{ is matrix group G defined over the rationals soluble?
  if so, return true, else false;
  UseCongruence: use congruence machinery to decide;
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   flag := IsKnownSoluble (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;
   return MyIsSolubleByFinite (G: OrderLimit := OrderLimit, Exact := true, 
      UseCongruence := UseCongruence, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsSoluble (G:: GrpMat[FldNum]: OrderLimit := 10^15,
   UseCongruence := false, 
   Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt
{ is matrix group G defined over rational number field soluble?
  if so, return true, else false;
  UseCongruence: use congruence machinery to decide;
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   flag := IsKnownSoluble (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;
   return MyIsSolubleByFinite (G: OrderLimit := OrderLimit, Exact := true, 
      UseCongruence := UseCongruence, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsSoluble (G:: GrpMat[FldFunRat]: OrderLimit := 10^15,
   Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt
{ is matrix group G defined over rational function field soluble?
  if so, return true, else false;
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   flag := IsKnownSoluble (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;
   return MyIsSolubleByFinite (G: OrderLimit := OrderLimit, Exact := true, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;

intrinsic IsSoluble (G:: GrpMat[FldFun]: OrderLimit := 10^15,
   Small := 10^6, Short := 30, Presentation := "CT") -> BoolElt
{ is matrix group G defined over an algebraic function field soluble?  
  if so, return true, else false;
  Presentation: one of "CT", "FP", "PC" to dictate method of construction;
  Small, OrderLimit: bounds determining use of FPGroup and FPGroupStrong;
  Short: defining length for short presentation
}
   flag := IsKnownSoluble (G);
   if flag cmpeq true or flag cmpeq false then return flag; end if;
   return IsSolubleByFinite (G: OrderLimit := OrderLimit, Exact := true, 
      Small := Small, Short := Short, Presentation := Presentation);
end intrinsic;
