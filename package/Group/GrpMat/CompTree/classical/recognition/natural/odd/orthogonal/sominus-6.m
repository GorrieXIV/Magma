freeze;

//$Id:: sominus-6.m 3010 2015-01-31 07:07:57Z eobr007                        $:

import "../../../section.m": ExtractFactor, ExtractAction;
import "../../../basics.m": MyHom, RestrictForm, OrthogonalComplement, InitialiseGroup, ClassicalVerify;
import "../../../conjugate.m": OrthogonalForm;
import "../sl/gen.m": FactorToParent; 
import "../../../derived.m": MyDerivedSubgroupWithWords;
import "involution.m": SOSplitSpace;
import "soplus.m": SOFormBaseChange;
import "sominus.m": MinusCentraliser, MinusChosenElements;
import "dp.m": SOGoodCentraliser;

/* decide if form for 2-dimensional space is of plus type */

IsFormOfPlusType := function (form)
   return IsSquare (-Determinant (form));
end function;

MyChangeOfBasis := function (Y)
   F := BaseRing (Y);
   M := GModule (Y);
   V := VectorSpace (F, Degree (Y));
   I := IndecomposableSummands (M);
   flag := exists{x : x in I | Dimension (x) eq 4}; 
   if not flag then return flag, _; end if;
   dim := [Dimension (x): x in I];
   ParallelSort (~dim, ~I);
   Reverse (~I);
   CB := [];
   for i in [1..#I] do
      B := Basis (I[i]);
      B := [V!(M!B[j]): j in [1..#B]];
      Append (~CB, B);
   end for;
   return true, MatrixAlgebra (F, 6) ! &cat (CB);
end function;

MySection := function (Y)
   CY := Y`ChangeOfBasis; 
   U := UserGenerators (Y);
   A := [];
   F := BaseRing (Y);
   for i in [1..#U] do
      g := CY * U[i]* CY^-1;
      a := GL(4, F) ! ExtractAction (g, [1..4]);
      Append (~A, a);
   end for;
   S := sub <GL(4, F) | A>;
   S`UserGenerators := A;
   return S;

end function;

/* constructively recognise O^-(6, q) when q = 3 mod 4 */

SolveSixMinus := function (G: SpecialGroup := false)

   F := BaseRing (G);
   q := #F;
   d := Degree (G);
   assert d eq 6;
   assert q mod 4 eq 3;
   V := VectorSpace (F, d);

   repeat 
      g, w, H, b, CB, dim, dimW, U, W := SOSplitSpace (G: 
                      type := "orthogonalminus", Range := [2, 4]);
      flag, form := OrthogonalForm (G);
      assert flag;
      form := CB * form * Transpose (CB);
      cb := SOFormBaseChange (G, form, dim: type := "orthogonalminus");
      cb := cb^-1;
      H := H^(cb^-1);
      H`SLPGroup := G`SLPGroup;
      H`UserGenerators := 
          [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
      H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));
      C := MinusCentraliser (H, b, w, [1..dim]);

      C4 := MyDerivedSubgroupWithWords (C);
      C2 := SOGoodCentraliser (H, C, [2], {1..4}: type := "minus"); 

      flag, form := OrthogonalForm (H);
      assert flag;

      U := Eigenspace (b, -1);
      if Dimension (U) eq 2 then U := Eigenspace (b, 1); end if;

      repeat 
         x, wx := RandomWord (H);
         T := U meet U^x;
         f := RestrictForm (form, Basis (T), 1);
      until IsFormOfPlusType (f);

      gens := [C2`UserGenerators[i] : i in [1..#C2`UserGenerators]] 
           cat [C2`UserGenerators[i]^x : i in [2..#C2`UserGenerators]];
      words := [C2`UserWords[i] : i in [1..#C2`UserWords]] 
           cat [C2`UserWords[i]^wx : i in [2..#C2`UserWords]] ;

      Y := sub <GL(6, F) | gens >;
      Y`UserGenerators := gens;
      Y`UserWords := words;

      flag, CY := MyChangeOfBasis (Y);

      if flag then 
         Y`ChangeOfBasis := CY;
         K := MySection (Y);
         type := ClassicalType (K);
      else 
         vprint User5: "No 4-dimensional summand found"; 
         type := "false";
      end if;
   until type cmpeq "orthogonalminus"; 

   CBG := cb * CB;

   CY := Y`ChangeOfBasis;

   first := ExtractBlock (CY, 1, 1, 4, 6);
   first := [first[i]: i in [1..Nrows (first)]]; 
   second := OrthogonalComplement (Basis (V), first, form, 1);
   third := first cat second;
   third := GL(6, F)!&cat[Eltseq (x): x in third];

   EK, WK, CK := MinusChosenElements (K);
   // assert ClassicalVerify (K, EK, WK, CK);

   tau := hom <K`SLPGroup -> H`SLPGroup | Y`UserWords>;
   WH := [tau (WK[i]) : i in [1..#WK]];

   CK := MatrixAlgebra (F, 4)!CK;
 
   MA := MatrixAlgebra (F, 6);
   I := Identity (MA);
   InsertBlock (~I, CK, 1, 1);
   A := I * third;

   flag, form := OrthogonalForm (H);
   assert flag;

   lambda := InnerProduct (A[1] * form, A[2]);

   U := sub <V | [A[i]: i in [1..4]]>;

   /* SLP for involution u */
   n := (q^2 - 1) div 4;
   K`UserWords := Y`UserWords;
   wu := FactorToParent (H, K, WK[3]^n);

   /* construct hyperbolic basis for complement W of U in V */
   o := OrthogonalComplement (Basis (V), Basis (U), form, 1);
   W := sub <V | o>;
   rs := RestrictForm (form, o, 1);
   tr := TransformForm (rs, "orthogonalplus");
   tr := tr^-1;
   a := o[1]; w := o[2];
   aa := tr[1][1] * a + tr[1][2] * w;
   ww := tr[2][1] * a + tr[2][2] * w;
   ww := lambda * ww;
   a := aa; w := ww;
   BasisW := [a, w];

   rs := RestrictForm (form, [a, w], 1);
   // assert rs eq lambda * (MatrixAlgebra (F, 2)![0,1,1,0]);

   /* new hyperbolic basis for H */
   NB := Matrix ([a, w] cat [U.i: i in [1..4]]);

   /* rewrite H to this new basis */
   U := UserGenerators (H);
   U := [NB * h * NB^-1: h in U];
   Hb := sub <GL(d, q) | U >;
   Hb`UserGenerators := U;
   Hb`SLPGroup := H`SLPGroup;
   Hb`SLPGroupHom := hom <Hb`SLPGroup -> Hb | U>;

   /* rewrite involution u wrt this new basis */
   b := GL(d, q) ! (NB * H`SLPGroupHom (wu) * NB^-1);
   
   RP := RandomProcessWithWords (Hb: WordGroup := Hb`SLPGroup);
   Cb, words := CentraliserOfInvolution (Hb, b, wu: Randomiser := RP);
   InitialiseGroup (Cb);
   Cb`UserWords := words;

   Cb := SOGoodCentraliser (Hb, Cb, [4], {5..6}: Words := true, 
                           SpecialGroup := SpecialGroup);

   T := ExtractFactor (Cb, [1..4]);
   if SpecialGroup eq true then 
      ET, WT, CBT := Internal_SolveSOPlus (T);
   else 
      ET, WT, CBT := Internal_SolveOPlus (T);
   end if;
   assert IsIdentity (CBT);
   // assert ClassicalVerify (T, ET, WT, CBT);

   E := MinusChosenElements (OmegaMinus (6, q): Words := false); 

   tau := hom <T`SLPGroup -> Cb`SLPGroup | [Cb`SLPGroup.i: i in [1..Ngens (Cb`SLPGroup)]]>;
   WH cat:= [FactorToParent (H, Cb, (tau (WT[4])))];

   return E, WH, NB * CBG;
end function;
