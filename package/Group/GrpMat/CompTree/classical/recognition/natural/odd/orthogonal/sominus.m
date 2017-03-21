freeze;

//$Id:: sominus.m 3198 2016-05-18 04:09:45Z eobr007                          $:

import "../../../section.m": ExtractFactor, ExtractAction;
import "../../../basics.m": MyHom, SolveWord, ImagesOfWords, 
 InitialiseGroup, WordToUser, ClassicalVerify; 
import "../../../is-classical.m": MyIsSOPlusGroup; 
import "../../../conjugate.m": StandardOPlusForm, StandardOMinusForm, 
StandardOForm, ConjugateToStandardCopy;
import "../sl/gen.m": SpecialGeneratorsWords, FactorToParent, 
  CombineMatrices, ApplyCOB;
import "../../even/StdGensEvenSX.m": SolveClassicalEven;
import "so-product.m": IsDirectProductOs;
import "dp.m": SOGoodCentraliser;
import "soplus.m": SOPlusGlueElement, SOFormBaseChange, SOPlusProcess, 
 BrayGenerators;
import "sominus-6.m": SolveSixMinus;
import "involution.m": SOSplitSpace, BasisOfInvolution;
import "sominus-special.m": MinusSpecialProcess;
// import "../../../../rewriting/orth_minus_char2.m" : find_quad_ext_prim;
import "../../../standard.m" : find_quad_ext_prim;
import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;



MyConjugateToStandardCopy := function (G, Gens, n, F)
   P := GL(n, F);
   _, _, fG := OrthogonalForm (G);
   S := sub<P | Gens>;
   _, _, fS := OrthogonalForm (S);
   cb1 := GL(n, F)!TransformForm (fS, "orthogonalminus");
   cb2 := GL(n, F)!TransformForm (fG, "orthogonalminus");
   cb := cb1 * cb2^-1;
   return cb;
end function; 

/* if SpecialGroup is true, then standard generators
   for SO-, otherwise for Omega- */

MinusChosenElements := function (G: Words := true, SpecialGroup := false)

   n := Degree (G);
   assert IsEven (n) and n gt 2; 

   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);
   A := MatrixAlgebra (F, 2);

   EE := GF (q^2);
   delta := PrimitiveElement(EE);
   mu := delta^((q + 1) div 2);
//EE:Magma;
//   EE := ext<F | 2>;
//  delta := PrimitiveElement(EE);
//   mu := delta^((q + 1) div 2);
// mu^2, w;
// mu^2 in F;
// F!(mu^2);
/* 
   if mu^2 ne w then
       x := find_quad_ext_prim(F, EE);
       E<delta> := sub<EE | x>;
       SetPrimitiveElement(E, delta);
       mu := delta^((q + 1) div 2);
   else
       E := EE;
   end if;
*/
    E := EE;
// "HERE IN SOMINUS CODE ?", mu^2 eq w;
 //  if mu^2 ne w then error "FAILRE E"; end if;
      assert mu^2 eq w;
/* 
   try 
   catch err
      error ERROR_RECOGNITION;
   end try;
*/

   MA := MatrixAlgebra (F, n);
   
   I := A![1,0,0,1];
 
   M := MatrixAlgebra (F, 4);

   a := A![1,1,0,1];
   b := A![2,0,0,0];
   c := A![0,1,0,0];
   d := A![1,0,0,1];

   U := Identity (MA);
   U[n-3][n-3] := 0; U[n-3][n-2] := 1;
   U[n-2][n-3] := 1; U[n-2][n-2] := 0;
   U[n-1][n-1] := -1;

   a := A![1,0,1,1];
   b := A![0,0,2,0];
   c := A![1,0,0,0];
   d := A![1,0,0,1];
   L := Zero (MA);
   for i in [1..n - 4] do L[i][i] := 1; end for;
   InsertBlock (~L, a, n - 3, n - 3);
   InsertBlock (~L, b, n - 3, n - 1);
   InsertBlock (~L, c, n - 1, n - 3);
   InsertBlock (~L, d, n - 1, n - 1);
   L := Transpose (L);

   a := A![delta^(q + 1), 0, 0, delta^(-q - 1)]; 
   d := A![1/2 * (delta^(q - 1) + delta^(-q + 1)),
           1/2 * mu * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * mu^(-1) * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * (delta^(q - 1) + delta^(-q + 1))];
   D := Zero (MA);
   for i in [1..n - 4] do D[i][i] := 1; end for;
   InsertBlock (~D, a, n - 3, n - 3);
   InsertBlock (~D, d, n - 1, n - 1);
   D := Transpose (D);

   Gens := [U, L, D];

   if n gt 4 then
      p := Zero (MA);
      InsertBlock (~p, I, 1, 3);
      InsertBlock (~p, -I, 3, 1);
      for i in [5..n] do p[i][i] := 1; end for;
      Append (~Gens, p);
   end if;

   if n gt 6 then 
      h := Zero (MA);
      m := n - 2;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2) * I, m - 1, 1);
      InsertBlock (~h, I, n - 1, n - 1);
      Append (~Gens, h);
   end if;

   if SpecialGroup then
      m := Identity (MA);
      if q mod 4 eq 3 then 
         m[1][1] := -1;
         m[2][2] := -1;
       else
         m[n-1][n-1] := -1;
         m[n][n] := -1;
       end if;
      Append (~Gens, m);
   end if;

   P := GL (n, F);


   cb := MyConjugateToStandardCopy (G, Gens, n, F);

   //_, cb := ConjugateToStandardCopy (G, "orthogonalminus");
   //cb := cb^-1;

   gens := [P | x: x in Gens];
   X := [e^(cb): e in gens];

   if Words then
      W := [];
      if n in {2, 4} then 
         /* avoid tests related to classical group in natural representation */
         if SpecialGroup or d eq 2 then 
            /* see AschbacherPrioritiesInfo for ordering */
            priorities := [i : i in [19 .. 1 by -1]];
            if n eq 4 then for i in [16..18] do priorities[i] := 0; end for; end if;
            T := CompositionTree (G :
		Priorities := priorities, LeafPriorities := [1, 5, 4, 3, 2]);
            tau := CompositionTreeNiceToUser (G);
            InitialiseGroup (G);
            for i in [1..#gens] do
               flag, w := CompositionTreeElementToWord (G, X[i]);
	       assert flag;
               w := tau (w);
               w := WordToUser (G, w);
               Append (~W, w);
            end for;
         else 
            flag, a, b, tau, phi := RecogniseSL2 (G, E);
	    assert flag;
            W := [tau (x): x in X]; 
         end if;
      else
         RandomSchreier (G);
         InitialiseGroup (G);
         WG, tau := WordGroup (G);
         for i in [1..#gens] do
            w := X[i] @@ tau;
            w := WordToUser (G, w);
            Append (~W, w);
         end for;
      end if;
      return gens, W, cb;
   else
      return gens, cb, _;
   end if;
end function;

/* g involution in G; wg is corresponding word; construct its centraliser 
   whose derived group is SO+(f, q) x SO-(d - f, q) */

MinusCentraliser := function (G, g, wg, action: Partial := false, 
   Words := true, fct := Order, SpecialGroup := false)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G); q := #F;

   if Type (action) eq SeqEnum then action := {x : x in action}; end if;
   rest := Sort (SetToSequence ({1..d} diff action));
   action := Sort ([x : x in action]);
   r := #action;

   E := [[g]]; W := [[wg]]; 

   flag := false;
   i := 2;  
   repeat 
      if Words then 
         e, w := SpecialGeneratorsWords (G, g, wg: fct := fct);
      else 
         e := BrayGenerators (G, g);
      end if;
      e1 := [];  w1 := [];
      for i in [1..#e] do 
         x := e[i];
         if IsIdentity (x) or x in &cat (E) cat e1 then continue; end if;
         a := ExtractAction (x, action);
         b :=  ExtractAction (x, rest);
         if Determinant (a) eq 1 and Determinant (b) eq 1 then
            Append (~e1, x);
            if Words then Append (~w1, w[i]); end if;
         end if;
      end for;
      if #e1 gt 0 then 
         E[i]:= e1; if Words then W[i] := w1; end if;
         vprint User5: "Lengths are ", [#e: e in E];
         C := sub <GL(d, F) | &cat(E)>;
         S := Sections (C);
         vprint User5: "# of sections in result is now ", #S;
         // if #S eq 1 then error "Problem in MinusCentraliser"; end if;
         flag := IsDirectProductOs (C, action: Partial := Partial, 
                 SpecialGroup := SpecialGroup, Plus := false);
         i +:= 1;
      end if;
   until flag;

   vprint User5: "Number of generators for centraliser is", Ngens (C);

   E := &cat(E);
   W := &cat(W);
   C`UserGenerators := E;
   assert Ngens (C) eq #E;

   if Words then C`UserWords := W; end if;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   return C;
end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is O+(f) as f x f matrices;
   E1, W1 are elements, words for O+(f);
   similarly G2, E2, W2 describe O-(d - f) */
   
SOMinusGlue := function (G, G1, E1, W1, G2, E2, W2: SpecialGroup := false)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([1, 1, ..., -1, -1]) */
   if q mod 4 eq 1 then 
      if f eq 2 then
         u := E1[3];
         o := Order (u);
         wu := W1[3];
         wu := wu^(o div 2);
      else
         pow := (q - 1) div 4;
         wa1 := W1[6];  wb1 := W1[3];  wp := W1[8];
         wu := (wa1 * wb1)^(pow); 
         wu := wu^(wp^-1);
      end if;
      /* construct v = Diagonal ([-1,-1, ..., 1, 1]) */
      wv := W2[3]^((q^2 - 1) div 4); 
   else 
      assert SpecialGroup; 
      wu := W1[#W1]; wp := W1[8];
      wu := wu^(wp^-1);
      wv := W2[#W2];
   end if;

   /* w is word for 
      uv = Diagonal ([1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
   // assert I eq G`SLPGroupHom (w);
 
   /* construct centraliser SO+(4) x SO-(d - 4) in G of I */
   C := MinusCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}: 
             SpecialGroup := SpecialGroup);

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}: 
                         SpecialGroup := SpecialGroup);

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   if MyIsSOPlusGroup (Y) eq false then
      error "3 Group not SO+4";
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
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := MinusChosenElements (G: Words := false, SpecialGroup := SpecialGroup);

   word := (wg * W1[8]);
   
   if SpecialGroup then o := Order (E1[#E1]); o := o div 2; end if;
   W := W2;
   if f eq 2 then 
      W[4] := word;
   elif d - f in [4] then 
      W[4] := W1[4];
      W[5] := word;
   end if;

   if SpecialGroup then 
      if q mod 4 eq 3 then W[#W + 1] := W1[#W1]^o; else W[#W + 1] := W2[#W2]; end if;
   end if;

   return E, W;
end function;

MinusProcess := function (G, InputDimension: SpecialGroup := false, Special := false)
   d := Degree (G);
   F := BaseRing (G);
   q := #F;

   if (d eq 4) or (d le 8 and q eq 3) then
      X, Y, CB := MinusChosenElements (G : SpecialGroup := SpecialGroup);
      return X, Y, CB;
   end if;

   InitialiseGroup (G);

   if (not SpecialGroup) and Degree (G) eq 6 and q mod 4 eq 3 then 
      X, Y, CB := SolveSixMinus (G);
      return X, Y, CB;
   end if;

   Range := [d - 4];
   g, w, H, b, CB, dim := SOSplitSpace (G: SpecialGroup := SpecialGroup, 
                                        type := "orthogonalminus", Range := Range);

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

   C := MinusCentraliser (H, b, w, [1..dim]: SpecialGroup := SpecialGroup);

   C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d}: SpecialGroup := SpecialGroup);
   C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: 
                     type := "minus", SpecialGroup := SpecialGroup);

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "SOMinus call 1 dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := SOPlusProcess(G1, d: SpecialGroup := SpecialGroup);
   // assert ClassicalVerify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   vprint User5: "SOMinus call 2 dimension of G2 is ", Degree (G2);
   E2, W2, CB2 := $$ (G2, InputDimension: 
                      SpecialGroup := SpecialGroup, Special := Special);
   // assert ClassicalVerify (G2, E2, W2, CB2); 
   W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   vprint User5: "Call SOMinusGlue", Degree (G1), Degree (G2);

   t1 := Cputime ();
   X, Y := SOMinusGlue (H, G1, E1, W1, G2, E2, W2: SpecialGroup := SpecialGroup);
   // assert ClassicalVerify (G,X,Y,Total * CB);
   vprint User5: "Time to glue in SOMinus is ", Cputime (t1);
   return X, Y, Total * cb * CB;
end function;

intrinsic Internal_SolveOMinus(G :: GrpMat : Special := false) -> [], [], GrpMatElt
{construct standard generators for G, a conjugate of the natural copy of
the classical group Omega^-(d, q); return the standard generators in G,
their SLPs in terms of defining generators of G, and the change-of-basis
matrix to conjugate them to standard copy}

   d := Degree (G);
   require d ge 4 and IsEven (d): "Group must be in even dimension at least 4";

   F := BaseRing (G);
   if IsEven (#F) then return SolveClassicalEven (G: type := "O-"); end if;

   q := #F;
   if (d gt 8 and q eq 3) or (d gt 4 and q gt 3 and q mod 4 eq 3) then
      E, W, CB := MinusSpecialProcess (G: Special := false, SpecialGroup := true);
   else
      E, W, CB := MinusProcess (G, d: Special := false, SpecialGroup := false);
   end if;

   /* add in identity if d = 4 */
   if d eq 4 then  
      E[4] := E[3]^0; E[5] := E[3]^0;W[4] := W[3]^0; W[5] := W[3]^0;
   end if;

   /* add in repetition if d = 6 */
   if d eq 6 then
      E[5] := E[4]; W[5] := W[4];
   end if;
   return E, W, CB;
end intrinsic;

intrinsic Internal_SolveSOMinus(G :: GrpMat[FldFin]) -> [], [], GrpMatElt
{construct standard generators for G, a conjugate of the natural copy of
the classical group SO^-(d, q); return the standard generators in G,
their SLPs in terms of defining generators of G, and the change-of-basis
matrix to conjugate them to standard copy}

   d := Degree (G);
   require d ge 4 and IsEven (d): "Group must be in even dimension at least 4";

   F := BaseRing (G);
   if IsEven (#F) then error "Available for odd characteristic only"; end if;

   E, W, CB := MinusProcess (G, d: Special := false, SpecialGroup := true);

  /* add in identity if d = 4 */
   if d eq 4 then  
      special := E[4]; special_word := W[4];
      E[4] := E[3]^0; E[5] := E[3]^0;W[4] := W[3]^0; W[5] := W[3]^0;
      E[6] := special; W[6] := special_word;
   end if;

   /* add in repetition if d = 6 */
   if d eq 6 then
      special := E[5]; special_word := W[5];
      E[5] := E[4]; W[5] := W[4];
      E[6] := special; W[6] := special_word;
   end if;
   WG := WordGroup (G); W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);
   return E, W, CB;
end intrinsic;
