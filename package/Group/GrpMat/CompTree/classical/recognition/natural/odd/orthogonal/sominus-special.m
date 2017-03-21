freeze;

//$Id:: sominus-special.m 2748 2014-10-08 01:31:02Z eobr007                  $:

import "sominus.m": MinusCentraliser, MinusChosenElements, MinusProcess;
import "sominus-6.m": SolveSixMinus;
import "soplus.m": SOCentraliser, SOPlusGlueElement, PlusChosenElements, 
SOSpecialSplitSpace, SOFormBaseChange, SOPlusProcess, SolveSOPlus;
import "involution.m": SOSplitSpace;
import "dp.m": SOGoodCentraliser;

import "../sl/gen.m": 
FactorToParent, ProjectiveGenerator, CombineMatrices, ApplyCOB, Verify;

import "../../../conjugate.m" : OrthogonalForm;

import "../../../section.m": ExtractFactor, ExtractAction, MatrixBlocks;

import "../../../basics.m": RecognitionError, MyHom, SolveWord, 
ImagesOfWords, InitialiseGroup, WordToUser, ClassicalVerify; 

import "../../../is-classical.m": MyIsSOPlusGroup; 

import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;

/* G group with basis which exhibits split as f, d - f;
   G1 is O+(f) as f x f matrices;
   E1, W1 are elements, words for O+(f);
   similarly G2, E2, W2 describe O-(d - f); */
   
MinusSpecialGlue := function (G, G1, E1, W1, G2, E2, W2)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct word for 
      Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */

   w := W2[#W2];
   pow := (f - 2) div 2;
   w := w^(W1[#W1 - 1]^pow);

   /* set up matrix I for w */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
 
   /* construct centraliser SO+(4) x SO+(d - 4) in G of I */
   C := MinusCentraliser (G, I, w, {f - 1, f, f + 1, f + 2});

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d});

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   if MyIsSOPlusGroup (Y) eq false then 
      Y:Magma; error "3 Group not SO+4"; 
   end if;

   vprint User5: "Composition Tree call for degree", Degree (Y);
   T := CompositionTree (Y);
   g := SOPlusGlueElement (F);
   flag, wg := CompositionTreeElementToWord (Y, g);
   tau := CompositionTreeNiceToUser (Y);
   wg := tau (wg);

   InitialiseGroup (Y);
   Y`UserWords := C`UserWords;

   wg := WordToUser (Y, wg);

   /* SO+4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [w]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := MinusChosenElements (G: Words := false);

   cycle := W2[4] * wg * W1[8];

   word := (wg * W1[8]);

   W := W2;
   if f in {2} then 
      W[4] := word;
   elif d - f eq 4 then 
      W[4] := W1[4];
      W[5] := word;
   else 
      W[4] := W1[4];
      W[5] := cycle;
   end if;

   return E, W, W1, W2, wg;

end function;

/* recognize O-(d, q) where q = 3 mod 4 in its natural representation */

MinusSpecialProcess := function (G : Limit := Maximum (1000, 10 * Degree (G)), 
   Special := false, SpecialGroup := true)

   d := Degree (G);
   F := BaseRing (G);

   if (Degree (G) le 4) or (Degree (G) eq 6 and #F eq 3) then 
      vprint User5: "Call CompositionTree for degree ", d;
      X, Y := MinusChosenElements (G: SpecialGroup := SpecialGroup);
      return X, Y, Identity (G), _, _, _;
   end if;

   InitialiseGroup (G);

   if Degree (G) eq 6 then 
      E, W, CB := SolveSixMinus (G);
      return E, W, CB;
   end if;

   if IsOdd (d div 2) then Range := [d - 6]; else Range := [d - 4]; end if;
   g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range,
                                           type := "orthogonalminus");

   vprint User5: "Now sort out new form";
   flag, form := SymmetricBilinearForm (G);
   assert flag;
   form := CB * form * Transpose (CB);

   cb := SOFormBaseChange (G, form, dim: type := "orthogonalminus");
   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := MinusCentraliser (H, b, w, [1..dim]:
           Partial := true, SpecialGroup := SpecialGroup);

   C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d});
   C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: type := "minus");

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   flag, form1 := OrthogonalForm (G1);
   assert flag;
   flag, form2 := OrthogonalForm (G2);
   assert flag;

   nmr := 0;
   found := false;
   repeat
      x, w := RandomWord (C);
      nmr +:= 1;
      o := Order (x);
      if IsOdd (o div 2) then 
         x := x^(o div 2);
         b1 := ExtractBlock (x, 1, 1, dim, dim);
         b2 := ExtractBlock (x, dim+1, dim+1, d - dim, d - dim);
         B := [* b1, b2 *];
         f1 := SpinorNorm (GL(Nrows (B[1]), F)!B[1], form1);
         f2 := SpinorNorm (GL(Nrows (B[2]), F)!B[2], form2);
         found := f1 eq 1 and f2 eq 1 and Determinant (B[1]) eq 1
               and Determinant (B[2]) eq 1;
      end if;
   until found or nmr gt Limit;

   if nmr gt Limit then
      error ERROR_RECOGNITION; 
      //error Error (rec<RecognitionError |
      //   Description := "Constructive recognition for classical group",
      //   Error := "Failed to find good element in MinusSpecialProcess">);
   end if;

   B := MatrixBlocks (C, x);
   w := w^(o div 2);
   w := FactorToParent (G, C, w);

   D1 := sub < GL(d, F) | C1, x>;
   D1`UserGenerators := C1`UserGenerators cat [x];
   D1`UserWords := C1`UserWords cat [w];
   D1`SLPGroup := SLPGroup (#D1`UserGenerators);
   D1`SLPGroupHom := MyHom (D1, D1`SLPGroup, UserGenerators (D1));
   C1 := D1;

   G1 := ExtractFactor (C1, {1..dim});

   vprint User5: "MinusSpecial call 1 dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := SOPlusProcess (G1, d: Special := Special, 
                                        SpecialGroup := true);
   // assert ClassicalVerify (G1, E1, W1, CB1); 
/* 
   if ClassicalVerify (G1, E1, W1, CB1) eq false then
      G1:Magma;
      error "FAILED FIRST";
   end if;
*/

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];

   rem := d - dim;
   h := H`SLPGroupHom (W1[#W1]);

   D2 := sub < GL(d, F) | C2, h>;
   D2`UserGenerators := C2`UserGenerators cat [h];
   D2`UserWords := C2`UserWords cat [W1[#W1]];
   D2`SLPGroup := SLPGroup (#D2`UserGenerators);
   D2`SLPGroupHom := MyHom (D2, D2`SLPGroup, UserGenerators (D2));
   C2 := D2;
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "MinusSpecial call 2";
   E2, W2, CB2 := MinusProcess (G2, d: SpecialGroup := true);
   if ClassicalVerify (G2, E2, W2, CB2) eq false then
      G2:Magma;
      error "FAILED SECOND";
   end if;
   // assert ClassicalVerify (G2, E2, W2, CB2); 
   W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   // w := W2[#W2];

   vprint User5: "Call MinusSpecialGlue", Degree (G1), Degree (G2);
   t1 := Cputime ();
   X, Y, a,b,c := MinusSpecialGlue (H, G1, E1, W1, G2, E2, W2); 
   // assert ClassicalVerify (G,X,Y,Total * CB);

   vprint User5: "Time to glue in MinusSpecial is ", Cputime (t1);
   return X, Y, Total * cb * CB, a, b,c;
end function;
