freeze;

//$Id:: so.m 3034 2015-02-05 05:06:11Z eobr007                               $:

import "soplus-special.m" : SOPlusSpecialProcess;
import "so-special.m": SOSpecialProcess;
import "soplus.m": SOCentraliser, SOPlusGlueElement, SOFormBaseChange, 
    SOPlusProcess, BrayGenerators;
import "so-product.m": IsDirectProductOs;
import "involution.m": SOSplitSpace, BasisOfInvolution;
import "dp.m": SOGoodCentraliser, SpinorNorm;

import "../../../conjugate.m": StandardOPlusForm, StandardOMinusForm, 
StandardOForm, ConjugateToStandardCopy;
import "../sl/gen.m": SpecialGeneratorsWords, FactorToParent, 
    CombineMatrices, ApplyCOB;
import "../../../conjugate.m": OrthogonalForm;
import "../../../basics.m": MyHom, WordToUser, InitialiseGroup, 
   ClassicalVerify, SolveWord, ImagesOfWords;
import "../../../section.m": ExtractFactor, ExtractAction;

/* we have a specific choice of form */

SOChangeForm := function (d, F, form)
   if not IsSquare (-2 * ((-1)^((d - 1) div 2) * Determinant (form))) then
      flag := exists (v) { x : x in F | IsSquare (x) eq false};
      form := v * form;
   end if;
   return form;
end function;

/* if SpecialGroup is true, then standard generators
   for SO^0, otherwise for Omega */

SOChosenElements := function (G: Words := true, SpecialGroup := false)

   n := Degree (G);
   assert IsOdd (n) and n gt 1;

   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);
      
   A := MatrixAlgebra (F, 2);
 
   M := MatrixAlgebra (F, 3);
   a := M![1,1,2,0,1,0,0,1,1];
   U := Identity (MA);
   InsertBlock (~U, a, n - 2, n - 2);

   b := M![0,1,0,1,0,0,0,0,-1];
   L := Identity (MA);
   InsertBlock (~L, b, n - 2, n - 2);

   delta := M!DiagonalMatrix (F, [w^2, w^-2, 1]);
   D := Identity (MA);
   InsertBlock (~D, delta, n - 2, n - 2);

   Gens := [L, U, D];

   if n gt 4 then 
      I := A![1,0,0, 1];
      h := Zero (MA);
      m := n - 1;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2 - 1) * I, m - 1, 1);
      h[n][n]:=1;
      Append (~Gens, h);
   end if;

   // EOB -- add additional generator u Oct 2012 
   if n gt 3 then 
      u := Zero (MA);
      for i in [5..n] do u[i][i] := 1; end for;
      u[1][3] := 1; u[2][4] := 1; u[3][1] := -1; u[4][2] := -1;
   else
      u := Identity (MA);
   end if;
   Append (~Gens, u);
   
   if SpecialGroup then
      m :=  Identity (MA);
      _, b := Valuation (q - 1, 2);
      m[n - 2][n-2] := w^b;
      m[n - 1][n-1] := w^-b;
      Append (~Gens, m);
   end if;


   P := GL (n, q);
   gens := [P | x: x in Gens];

   _, cb := ConjugateToStandardCopy (G, "orthogonal");
   cb := cb^-1;

   if Words then
      W := [];
      if n eq 3 then
         /* avoid tests related to classical group in natural representation */
         if SpecialGroup then 
            /* see AschbacherPrioritiesInfo for ordering */
            priorities := [i : i in [19 .. 1 by -1]];
            for i in [16..18] do priorities[i] := 0; end for;
	    T := CompositionTree (G :
		Priorities := priorities, LeafPriorities := [1, 4, 3, 2]);
            tau := CompositionTreeNiceToUser (G);
            InitialiseGroup (G);
            for i in [1..#gens] do
               flag, w := CompositionTreeElementToWord (G, gens[i]^(cb));
               w := tau (w);
               w := WordToUser (G, w);
               Append (~W, w);
            end for;
         else
            flag, a, b, tau, phi := RecogniseSL2 (G, q);
            W := [tau (gens[i]^cb): i in [1..#gens]];
         end if;
      else
         RandomSchreier (G);
         InitialiseGroup (G);
         WG, tau := WordGroup (G);
         for i in [1..#gens] do
            w := (gens[i]^(cb)) @@ tau;
            w := WordToUser (G, w);
            Append (~W, w);
         end for;
      end if;
      return gens, W, cb;
   else
      return gens, cb, _;
   end if;

end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is O+(f) as f x f matrices;
   E1, W1 are elements, words for SO+(f);
   similarly G2, E2, W2 describe O(d - f) */
   
SOGlue := function (G, G1, E1, W1, G2, E2, W2: SpecialGroup := false)
 
   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([1, 1, ..., -1, -1]) 
      and       v = Diagonal ([-1,-1, ..., 1, 1]) */
   pow := (q - 1) div 4;
   if q mod 4 eq 1 then
      if f eq 2 then
         u := E1[3];
         o := Order (u);
         wu := W1[3];
         wu := wu^(o div 2);
      else
         wa1 := W1[6];  wb1 := W1[3];  wp := W1[8];
         wu := (wa1 * wb1)^(pow);
         wu := wu^(wp^-1);
      end if;
      wv := W2[3]^(pow); 
   else
      assert SpecialGroup;
      wu := W1[#W1]; wp := W1[8];
      wu := wu^(wp^-1);
      wv := W2[#W2];
   end if;

   /* w is word for 
      uv = Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
   // assert G`SLPGroupHom (w) eq I;

   /* construct centraliser SO+(4) x SO+(d - 4) in G of I */
   C := SOCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}: 
                       SpecialGroup := SpecialGroup);

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}: 
                         SpecialGroup := SpecialGroup);

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);

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
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := SOChosenElements (G: Words := false, SpecialGroup := SpecialGroup);

   word := (wg * W1[8]);

   // EOB -- addition of word for standard generator u Oct 2012 
   if d gt 5 then 
      W := [W2[i] : i in [1..3]] cat [word] cat [W1[4]];
   else 
      W := [W2[i] : i in [1..3]] cat [word] cat [word];
   end if;
   if SpecialGroup then W[#W + 1] := W2[#W2]; end if;

   return E, W;
end function;

SOProcess := function (G, InputDimension: SpecialGroup := false, Special := false)

   d := Degree (G);
   F := BaseRing (G);
   q := #F;

   if (d eq 3) or (d le 7 and q eq 3) then 
      vprint User5: "Call CompositionTree for degree ", d;
      X, Y, CB := SOChosenElements (G : SpecialGroup := SpecialGroup);
      return X, Y, CB;
   end if;

   InitialiseGroup (G); 

   if Degree (G) eq 4 then Range := [2]; end if;
   if not SpecialGroup and q mod 4 eq 3 and d mod 4 eq 1 then 
      Range := [d - 5]; 
   else 
      Range := [d - 3];
   end if;
   g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range, 
                                           type := "orthogonalcircle");
   flag, form := OrthogonalForm (G);
   assert flag;
   form := CB * form * Transpose (CB);
   
   vprint User5: "Now sort out new form";
   form := SOChangeForm (d, F, form);

   cb := SOFormBaseChange (G, form, dim: type := "orthogonalcircle");

   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := SOCentraliser (H, b, w, [1..dim]: SpecialGroup := SpecialGroup);

   type := IsEven (dim) select "orthogonalplus" else "orthogonalcircle"; 
   C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d}: type := type,
                            SpecialGroup := SpecialGroup);

   type := IsEven (d - dim) select "orthogonalplus" else "orthogonalcircle"; 
   C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: type := type,
                             SpecialGroup := SpecialGroup);

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "Call 1 SOProcess Dimension of G1 is ", Degree (G1);

   E1, W1, CB1 := SOPlusProcess(G1, d: SpecialGroup := SpecialGroup);
   // assert ClassicalVerify (G1, E1, W1, CB1); 
   
   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   vprint User5: "Call 2 SOProcess Dimension of G2 is ", Degree (G2);
   E2, W2, CB2 := $$ (G2, InputDimension: 
                      SpecialGroup := SpecialGroup, Special := Special);
   // assert ClassicalVerify (G2, E2, W2, CB2); 
   W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   vprint User5: "Call SOGlue", Degree (G1), Degree (G2);

   t1 := Cputime ();

   X, Y := SOGlue (H, G1, E1, W1, G2, E2, W2: SpecialGroup := SpecialGroup);
   // assert ClassicalVerify (G,X,Y,Total * CB);

   vprint User5: "Time to glue in SOProcess is ", Cputime (t1);

   return X, Y, Total * cb * CB;
end function;

/* construct Steinberg generators of G */

intrinsic Internal_SolveO(G :: GrpMat : Special := false) -> [], [], GrpMatElt
{construct standard generators for G, a conjugate of the natural copy of
the classical group Omega(d, q); return the standard generators in G,
their SLPs in terms of defining generators of G, and the change-of-basis
matrix to conjugate them to standard copy}

   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   require d ge 3 and IsOdd(d) and IsOdd (q): "Group must be in odd dimension at least 3 and field must have odd characteristic";
   if (d gt 3 and q mod 4 eq 3 and q gt 3) or (d gt 7 and q eq 3) then 
      E, W, CB := SOSpecialProcess (G: Special := false, SpecialGroup := true);
   else
      E, W, CB := SOProcess (G, d: Special := false, SpecialGroup := false);
   end if;

   /* add in 2 x identity if d = 3 */
   if d eq 3 then
      E[4] := E[3]^0; W[4] := W[3]^0; 
      E[5] := E[3]^0; W[5] := W[3]^0; 
   end if;

   return E, W, CB;
end intrinsic;

intrinsic Internal_SolveSO(G :: GrpMat[FldFin]: Special := false) -> [], [], GrpMatElt
{construct standard generators for G, a conjugate of the natural copy of
the classical group SO(d, q); return the standard generators in G,
their SLPs in terms of defining generators of G, and the change-of-basis
matrix to conjugate them to standard copy}

   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   require d ge 3 and IsOdd(d) and IsOdd (q): "Group must be in odd dimension at least 3 and field must have odd characteristic";
   E, W, CB := SOProcess (G, d: Special := false, SpecialGroup := true);

   /* add in identity if d = 3 */
   if d eq 3 then  
      E[6] := E[5]; W[6] := W[5];
      E[5] := E[5]^0; W[5] := W[5]^0;
   end if;

   WG := WordGroup (G); W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);
   return E, W, CB;
end intrinsic;
