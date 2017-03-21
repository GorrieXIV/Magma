freeze;

//$Id:: so-5.m 3010 2015-01-31 07:07:57Z eobr007                             $:

import "../../../conjugate.m": StandardOPlusForm, OrthogonalForm;

import "../../../basics.m": MyHom, RestrictForm, GroupPreservingForm,
    ClassicalVerify, OrthogonalComplement, InitialiseGroup, 
    WordToUser, RecognitionError;

import "../../../order.m": GenerateInvolution;

import "../../../section.m": ExtractFactor, ExtractAction;

import "../../../derived.m": MyDerivedSubgroupWithWords;

import "../sl/gen.m": FactorToParent;

import "sominus-6.m": IsFormOfPlusType;
import "so.m": SOChosenElements, SOChangeForm;
import "involution.m": BasisOfInvolution;

import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;

/* code to deal with Omega (5, q) where q = 3 mod 4 */

FiveFormBaseChange := function (G, form, dim)
   F := BaseRing (G);
   q := #F;
   d := Degree (G);
   a := ExtractBlock (form, 1, 1, dim, dim);
   op := StandardOPlusForm (dim, q);
   x := TransformForm (a, "orthogonalplus");
   y := TransformForm (op, "orthogonalplus");
   a := x * y^-1;

   MA := MatrixAlgebra (F, d);
   A := Zero (MA);
   InsertBlock (~A, a, 1, 1);
   A[5][5] := 1;

   return GL(d, F)!A;
end function;

BasisMatrix := function (S, L)
   d := Dimension (S);
   F := BaseRing (S);
   mat := GL(d, F) ! &cat[ Coordinates (S, l): l in L];
   return mat;
end function;

/* find element y of even order 2n such that y^n has
   -1-eigenspace of dimension 4 */
 
FiveSplitSpace := function (G : Limit := Maximum (1000, 10 * Degree (G)))
   found := false;
   nmr := 0;
   repeat 
      flag, g, w := GenerateInvolution (G);
      if flag then 
         U := Eigenspace (g, -1);
         if Dimension (U) eq 4 then 
            W := Eigenspace (g, 1);
            b, H, CB := BasisOfInvolution (G, g, U, W);
            found := true;
         end if;
      end if;
      nmr +:= 1;
   until found or nmr gt Limit;

   if nmr gt Limit then
      error ERROR_RECOGNITION; 
      //error Error (rec<RecognitionError |
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to split space in FiveSplitSpace">);
   end if;

   vprint User5: "Number of random elements processed to split space is ", nmr;

   return g, w, H, b, CB, U, W;

end function;

/* T a 3-dimensional space; form acts on this space; 
   construct a new basis for T which is standard with respect to form */

FiveChangeOfBasis := function (T, form)
   F := BaseRing (T);
   V := VectorSpace (F, 5);
   value := F!(-1/2);
   repeat
      x := Random (T);
      v := InnerProduct (x * form, x); 
   until v ne 0 and IsSquare (-2 * v);
   P := OrthogonalComplement (Basis (V), [x], form, 1);
   P := sub <V | P >;
   U := P meet T;
   fp := RestrictForm (form, Basis (U), 1);
   if not IsFormOfPlusType (fp) then return false, _; end if; 

   x := x / Sqrt (-2 * v);
   // assert InnerProduct (x * form, x) eq value;

   B := Basis (U);
   e := B[1]; f := B[2];

   ve := InnerProduct (e * form, e);
   vf := InnerProduct (f * form, f);

   if ve eq 0 and vf eq 0 then
      v := InnerProduct (e * form, f);
      assert v ne 0; 
      f := f / v;
   elif ve eq 0 and vf ne 0 then 
      v := InnerProduct (e * form, f);
      assert v ne 0; 
      a := -vf / (2 * InnerProduct (f * form, e)); 
      f := f + a * e;
   elif ve ne 0 and vf eq 0 then 
      v := InnerProduct (e * form, f);
      assert v ne 0; 
      a := -ve / (2 * InnerProduct (e * form, f)); 
      e := e + a * f;
   else 
      P<a> := PolynomialRing (F);
      m := a^2 * InnerProduct (e * form, e) + 
            2 * a * InnerProduct (e * form, f) 
            + InnerProduct (f * form, f);
      flag, l := HasRoot (m);
      assert flag;
      e := l * e + f;
      a := -vf / (2 * InnerProduct (f * form, e)); 
      f := f + a * e;
   end if;

   f := f / InnerProduct (e * form, f);
   return true, [e, f, x];
   
end function;
   
/* construct standard generators for Omega (5, q) where q = 3 mod 4 */

SolveO5 := function (G)

   d := Degree (G);
   assert d eq 5;
   F := BaseRing (G);
   q := #F;
   assert q mod 4 eq 3;

   if q eq 3 then return SOChosenElements (G); end if;

   V := VectorSpace (F, d);

   g, w, H, b, CB, U, W := FiveSplitSpace (G);

   dim := Dimension (U);

   vprint User5: "Now sort out new form";
   flag, form := OrthogonalForm (G);
   assert flag;
   form := CB * form * Transpose (CB);
   form := SOChangeForm (d, F, form);
   cb := FiveFormBaseChange (G, form, dim);
   cb := cb^-1;
   H := H^(cb^-1);
   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   RP := RandomProcessWithWords (H: WordGroup := H`SLPGroup);
   C, words := CentraliserOfInvolution (H, b, w: Randomiser := RP);
   InitialiseGroup (C);
   C`UserWords := words;

   C4 := MyDerivedSubgroupWithWords (C);
   W4 := [FactorToParent (H, C, C4`UserWords[i]): i in [1..#C4`UserWords]];
   C4`UserWords := W4;
   C4A := ExtractFactor (C4, [1..4]);
   T4 := CompositionTree (C4A);

   flag, form := OrthogonalForm (H);
   assert flag;

   cob := cb * CB;

   U := Eigenspace (b, -1);
   repeat 
      h, wh := RandomWord (H);
      T := U meet U^h;
      P := OrthogonalComplement (Basis (V), Basis (T), form, 1);
      f := RestrictForm (form, Basis (T), 1);
      fp := RestrictForm (form, (P), 1);
   until Rank (f) eq 3 and IsFormOfPlusType (fp);

   flag, B := FiveChangeOfBasis (T, form);
   assert flag;

   x := B[3];
   O := OrthogonalComplement (Basis (V), [x], form, 1);
   O := sub <V | O>;

   /* construct first O_3(q) */

   S := U meet O;
   rS := RestrictForm (form, Basis (S), 1);

   // assert T meet O eq sub < V | B[1], B[2]>;

   K := GroupPreservingForm (rS, 1: Simple := true);           
   gens := [K.i : i in [1..Ngens (K)]];
   MA := MatrixAlgebra (F, d);
   A := [];
   for i in [1..#gens] do
      I := Identity (MA);
      InsertBlock (~I, gens[i], 1, 1);
      Append (~A, I);
   end for;
   OS := OrthogonalComplement (Basis (V), S, form, 1);
   BS1 := [S.1, S.2, S.3] cat OS;
   CB1 := BasisMatrix (V, BS1);
   /* generating set inside C4 for O3 */
   A1 := [GL(5, F) ! (CB1^-1 * A[i] * CB1): i in [1..#A]];

   R3 := SOChosenElements (Omega (3, q): Words := false);
   ou := OrthogonalComplement (Basis (U), B, form, 1);
   b := BasisMatrix (U, B cat ou);
   gens := [];
   M4 := MatrixAlgebra (F, 4);
   for i in [1..3] do
      I := Identity (M4);
      InsertBlock (~I, R3[i], 1,1);
      J := Identity (MA);
      InsertBlock (~J, b^-1 * I * b, 1, 1);
      gens[i] := GL(5, F) ! J;
   end for;

   tau := CompositionTreeNiceToUser (C4A);

   /* words for generators of O_3(q) inside O_4+(q) */
   W1 := [];
   for i in [1..#A1] do
      a := ExtractAction (A1[i], [1..4]);
      flag, w := CompositionTreeElementToWord (C4A, a);
      w := tau (w);
      w := WordToUser (C4, w);
      W1[i] := FactorToParent (H, C4, w);
   end for;
   // assert ClassicalVerify (H, A1, W1, H.1^0);

   /* words for standard generators for O_3(q) inside O_4+(q) */
   W3 := [];
   for i in [1..#gens] do
      a := ExtractAction (gens[i], [1..4]);
      flag, w := CompositionTreeElementToWord (C4A, a);
      w := tau (w);
      w := WordToUser (C4, w);
      W3[i] := FactorToParent (H, C4, w);
   end for;
   // assert ClassicalVerify (H, gens, W3, H.1^0);

   /* construct second O_3(q) */

   S := U^h meet O;
   rS := RestrictForm (form, Basis (S), 1);

   // assert T meet O eq sub < V | B[1], B[2]>;

   K := GroupPreservingForm (rS, 1: Simple := true);           
   MA := MatrixAlgebra (F, d);
   A := [];
   for i in [1..Ngens (K)] do
      I := Identity (MA);
      InsertBlock (~I, K.i, 1, 1);
      Append (~A, I);
   end for;

   OS := OrthogonalComplement (Basis (V), S, form, 1);
   BS2 := [S.1, S.2, S.3, OS[1], OS[2]];

   CB2 := BasisMatrix (V, BS2);
   A2 := [GL(5, F) ! (CB2^-1 * A[i] * CB2): i in [1..#A]];

   /* words for generators of O_3(q) inside O_4+(q) */
   W2 := [];
   hm1 := h^-1;
   for i in [1..#A2] do
      a := ExtractAction (A2[i]^(hm1), [1..4]);
      flag, w := CompositionTreeElementToWord (C4A, a);
      w := tau (w);
      w := WordToUser (C4, w);
      W2[i] := FactorToParent (H, C4, w)^wh;
   end for;
   // assert ClassicalVerify (H, A2, W2, H.1^0);
   // wrt this basis A2 is in C4 

   /* K is O4+(q) */
   K := sub <GL (5, q) | A1, A2>; 

   /* extend standard basis B for T to standard basis for V */
   O := OrthogonalComplement (Basis (V), B, form, 1);
   r := RestrictForm (form, O, 1);
   tr := TransformForm (r, "orthogonalplus");
   tr := tr^-1;
   a := &+[tr[1][i] * O[i]: i in [1..#O]];
   b := &+[tr[2][i] * O[i]: i in [1..#O]];

   /* hyperbolic basis for H */
   CB := Matrix ([a, b] cat B);

   /* M is O4+(q) written wrt to standard basis */
   M := sub <GL(5, F) | [CB * K.i * CB^-1: i in [1..Ngens (K)]]>;
   S := Sections (M);
   if Degree (S[1]) eq 4 then S := S[1]; else S := S[2]; end if;

   E4, W4, CB4 := Internal_SolveOPlus (S);
   assert IsIdentity (CB4);
 
   gamma := hom <S`SLPGroup -> H`SLPGroup | W1 cat W2>;
   w := gamma (W4[#W4]);
   
   E := SOChosenElements (H: Words := false);

   // EOB addition of word for standard generator u Oct 2012 
   return E, W3 cat [w, w], GL(5, F) ! (CB * cob);
end function;
