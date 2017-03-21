freeze;

//$Id:: su.m 3034 2015-02-05 05:06:11Z eobr007                               $:

import "../../../../../reduce/reduce.m": Reduction;

import "../../../basics.m": MyHom, WordToUser, InitialiseGroup, ImagesOfWords,
       RecognitionError, ClassicalVerify;
import "../../../section.m": ExtractFactor, ExtractAction;
import "../../../order.m": GenerateInvolution;
import "../../../is-classical.m": MyIsUnitaryGroup;
import "../../even/StdGensEvenSX.m": SolveClassicalEven;

import "../../../conjugate.m": StandardSUForm, ConjugateToStandardCopy;
import "../sl/gen.m": SecondSpecialCentraliser, GoodCentraliser, 
    RedefineGroup, ThirdCentraliser, InBaseGroup, GlueElement,
    SpecialSplitSpace, SplitSpace, SpecialCentraliser, FactorToParent,
    ProjectiveGenerator, CombineMatrices, ApplyCOB; 

import "../../../../../recog/magma/node.m": ERROR_RECOGNITION;

StandardSU := function (n, q) 
   G := SU (n, q);
   form := StandardSUForm (n, q);
   CB := TransformForm (form, "unitary");
   return G^(CB^-1), form;
end function;

SUHalfChangeBasis := function (G, form, dim)
   F := BaseRing (G);
   q := Isqrt (#F);
   d := Degree (G);
   a := ExtractBlock (form, 1, 1, dim, dim);
   op := StandardSUForm (dim, q);
   x := TransformForm (a, "unitary");
   y := TransformForm (op, "unitary");
   a := x * y^-1;

   b := ExtractBlock (form, dim + 1, dim + 1, d - dim, d - dim);
   om := StandardSUForm (d - dim, q);
   x := TransformForm (b, "unitary"); 
   y := TransformForm (om, "unitary");
   b := x * y^-1;
   
   A := DiagonalJoin (a, b);
   
   return GL(d, F)!A;

end function;

/* construct SU2 x SU2 in GU2 wr C2 */

ConstructSU2xSU2 := function (G)

   d := Degree (G);
   F := BaseRing (G);
   repeat 
      g, wg := RandomWord (G);
   until not InBaseGroup (g); 

   /* find element t = [b 0; 0 b^-1] where b is the 
     determinant of 2 x 2 block and b is primitive */

   E := [ GL(d, F) | ]; W := []; found := false;
   q := Isqrt (#F);
   repeat 
      repeat 
         h, wh := RandomWord (G);
      until InBaseGroup (h) eq false;
      product := g * h;
      wp := wg * wh;
      Append (~E, product);
      Append (~W, wp);
      t := &*E;
      flag, A, B := InBaseGroup (t);
      // if flag then w := Determinant (A); flag := IsPrimitive (w); end if;
      if flag then w := Determinant (A); flag := Order (w) eq q + 1; end if;
   until flag;
   vprint User5: "Number of trials to find primitive element is ", #E;
   wt := &*W;

   /* find wreathing element [0, a^-1 : a 0] where
      a is determinant of 2 x 2 block and has value 1 */

   a := ExtractBlock (g, 1, 3, 2, 2);
   k := Log (w, Determinant (a));
   tt := t^k;
   wtt := wt^k;
   b1 := g * tt;
   wb1 := wg * wtt;
   a := ExtractBlock (b1, 1, 3, 2, 2);
   // assert Determinant (a) eq 1;

   /* get generators for SU(2, q) x SU(2, q) */
   E := [GL(d, F) | ]; W := [];
   repeat 
      repeat 
         h, wh := RandomWord (G);
      until InBaseGroup (h) eq false;
      product := g * h;
      wp := wg * wh;
      flag, A, B := InBaseGroup (product);
      det := Determinant (A); 
      k := Log (w, Determinant (a));
      tt := t^k;
      wtt := wt^k;
      b2 :=  product * tt;
      wb2 := wp * wtt;
      Append (~E, b2);
      Append (~W, wb2);
      H := sub <GL(4, F) | E>;
      S := Sections (H);
      if #S eq 2 and forall{s : s in S | MyIsUnitaryGroup (s)} then
         U1 := S[1]`UserGenerators;
         U2 := S[2]`UserGenerators;
         flag := [ProjectiveOrder (x): x in U1] ne
                 [ProjectiveOrder (x): x in U2];
      else flag := false;
      end if;
   until flag;
   
   // assert forall{i: i in [1..Ngens (H)] | Determinant (H.i) eq 1};
   return H, E, W, b1, wb1;
end function;

/* additional elements to generate SU */

SUAdditionalElements := function (F: EvenCase := true)
   if EvenCase then d := 4; else d := 3; end if;
   M := MatrixAlgebra (F, d);
   gamma := PrimitiveElement (F);
   q := Isqrt (#F);
   I := Identity (M);
   if EvenCase then
      I[1][3] := 1;
      I[4][2] := -1;
      J := DiagonalMatrix (F, [gamma, gamma^-q, gamma^-1, gamma^q]);
   else
      if IsEven (q) then
         // phi := Trace(gamma, GF(q))^(-1) * gamma;
         P := PolynomialRing(F);
         py := P.1^q + P.1 + 1;
         phi := Roots(py)[1, 1];
      else
         phi := -1/2;
      end if;
      I := M![1, phi, 1, 0, 1, 0, 0, -1, 1];
      J := DiagonalMatrix (F, [gamma, gamma^(-q), gamma^(q - 1)]);
   end if;
   I := GL(d, F)!I;
   J := GL(d, F)!J;
   return I, J;
end function;

/* canonical basis for SU(d, q): needs additional element */

SUChosenElements := function (G : Words := true)

   d := Degree (G);
   E := BaseRing (G); 

   f := Degree (E) div 2;
   p := Characteristic (E);
   q := p^f;
   F := GF(p, f);

   w := PrimitiveElement (E);
   if IsEven (#E) then
      alpha := w^((q + q^2) div 2);
   else
      alpha := w^((q + 1) div 2);
   end if;
 
   w0 := alpha^2; 

   M := MatrixAlgebra (E, d);
   a := Zero (M);
   a[1][2] := alpha;
   a[2][1] := alpha^-q;
   for i in [3..d] do a[i][i] := 1; end for;
 
   t := Identity (M);
   t[1][2] := alpha;

   delta := Identity (M);
   if (d eq 3 and p eq 2 and f eq 1) then
      delta[1,2] := w;
      delta[1,3] := w;
      delta[3,2] := w^2;
   else
      delta[1][1] := w0;
      delta[2][2] := w0^-1;
   end if;

   if d ge 4 then 
      p := Zero (M);
      p[1][3] := 1; p[2][4] := 1; p[3][1] := 1; p[4][2] := 1;
      for i in [5..d] do p[i][i] := 1; end for;
   else
      p := Identity (M);
   end if;

   if d ge 4 then 
      b := Zero (M);
      n := d div 2;
      for i in [1..2 * n - 2 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[2 * n - 1][1] := 1;
       for i in [2..2 * n - 2 by 2] do
          b[i][i + 2] := 1;
     end for; 
      b[2 * n][2] := 1;
      if IsOdd (d) then b[d][d] := 1; end if;
   else 
      b := Identity (M);
   end if;

   P := GL(d, E);

   if d eq 2 then 
      x := Identity (P);
      y := Identity (P);
   elif d in [3, 4] then 
      x, y := SUAdditionalElements (E: EvenCase := IsEven (d));
   else 
      x, y := SUAdditionalElements (E: EvenCase := IsEven (d));
      f := d - Nrows (x);
      x := GL(d, E) ! (DiagonalJoin (Identity (MatrixAlgebra (E, f)), x)); 
      y := GL(d, E) ! (DiagonalJoin (Identity (MatrixAlgebra (E, f)), y)); 
   end if;

   _, cb := ConjugateToStandardCopy (G, "unitary");

   E := [P | a, b, t, delta, p, x, y];
   X := [cb * e * cb^-1: e in E];

   if Words then 
      if Degree (G) eq 2 then 
         prior := [i : i in [19 .. 1 by -1]];
         for i in [16..18] do prior[i] := 0; end for;
         T := CompositionTree(G : Priorities := prior);
         W := [];
         for i in [1..#X] do 
            flg, w := CompositionTreeElementToWord(G,X[i]);
            map := CompositionTreeNiceToUser(G);
            w   := Image(map,w);
            Append (~W, w);
         end for;
         return E, W, cb^-1;
/* 
      if Degree (G) eq 2 then
         flag, phi, gamma, tau := RecogniseSL2 (G, #F);
         if flag then 
            W := [tau (e): e in X];
         end if;
*/
      elif Degree (G) in {3, 4} then
         W := [];
         for i in [1..#X] do 
            repeat 
		flag, w := Reduction (G, X[i]: CentraliserMethod := "CT",
		    LieRank := Degree(G) - 1);  
            until flag;
            w := WordToUser (G, w);
            Append (~W, w);
         end for;
         flag := true;
      end if;
      if d gt 4 or flag eq false then
        error Error (rec<RecognitionError |
            Description := "Constructive recognition for classical group",
            Error := "Input group must be unitary of degree at most 4">);
      end if;
      return E, W, cb^-1;
   else 
      return E, cb^-1, _;
   end if;
end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is SU(f) as f x f matrices;
   E1, W1 are elements, words for SU(f);
   E1[2] = (1,3,5,...,f - 1) (2,4,6,...,f);
   similarly G2, E2, W2 describe SU(d - f);
   if FinalCall is true, then this is the final glue 
   and we must obtain additional element to
   generate all of SU */
   
SUGlue := function (G, G1, E1, W1, G2, E2, W2: FinalCall := false)

   d := Degree (G);
   E := BaseRing (G); 
   p := Characteristic (E);
   F := GF (p, Degree (E) div 2);
   q := #F;
   
   a := E1[1]; b1 := E1[2]; t := E1[3]; 
   wb1 := W1[2];
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([1, 1, ..., -1, -1]) */
   o := q - 1;
   // delta := E1[4]; u := delta^(o div 2); u :=   u^( b1^((f - 2) div 2));
   wdelta := W1[4]; wu := wdelta^(o div 2); wu := wu^(wb1^((f - 2) div 2));

   /* construct v = Diagonal ([-1,-1, ..., 1, 1]) */

   // E2[2] = (f + 1,f + 3,5,...,d - 1) (f + 2,f + 4,...,f + d)
   b2 := E2[2]; wb2 := W2[2];
   // delta := E2[4]; v := delta^(o div 2); 
   wdelta := W2[4]; wv := wdelta^(o div 2); 

   /* w is word for 
      uv = Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (E, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, E) ! I;
 
   /* construct centraliser SU(4) x SU(d - 4) in G of I */
   C := SecondSpecialCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}:
                                  IsCorrectType := MyIsUnitaryGroup);

   /* construct C = SU(4) acting on {f - 1, f, f + 1, f + 2} */
   if d gt 4 then 
      C := GoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}:
           type := "unitary", IsCorrectType := MyIsUnitaryGroup);
   end if;

   /* modify C to include u as generator */
   MA := MatrixAlgebra (E, d);
   u := Identity (MA);
   for i in [f-1..f] do u[i][i] := -1; end for;
   C := RedefineGroup (G, C, u, wu);

   /* set up Y = SU(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   InitialiseGroup (Y);

   q := #E;

   if (not FinalCall) and (q ne 9) then
      vprint User5: "We are in CompositionTree call";

      /* construct projective centraliser of Diagonal ([-1, -1, 1, 1])
         in SU4; this is SL2 wr C2 */
      n := #Y`UserGenerators;
      m := Ngens (Y); 
      Cu := ThirdCentraliser (Y, Y.m, Y`SLPGroup.n:
            type := "unitary", IsCorrectType := MyIsUnitaryGroup);

      words := Cu`UserWords;
      T := CompositionTree (Cu);

      g := GlueElement (E);
      flag, wg := CompositionTreeElementToWord (Cu, g);
      assert flag;

      tau := CompositionTreeNiceToUser (Cu);
      wg := tau (wg);

      InitialiseGroup (Cu);
      Cu`UserWords := words;

      wg := WordToUser (Cu, wg);
      gamma := hom <Cu`SLPGroup -> Y`SLPGroup | Cu`UserWords>;
      wg := gamma (wg);
   else 
      vprint User5: "Final call for SU 4", Degree (Y);
      g := GlueElement (E);
      repeat
         // flag, wg := Reduction (Y, g: Central := true, CentraliserMethod ...
	 //:= "CT", LieRank := Degree(G) - 1); 
	 flag, wg := Reduction (Y, g: CentraliserMethod := "CT",
	     LieRank := Degree(Y) - 1); 
      until flag;
      wg := WordToUser (Y, wg);

      /* two additional elements to generate SU */
      x, y := SUAdditionalElements (E: EvenCase := IsEven (f));
      repeat
	  // flag, wx := Reduction (Y, x: Central := true,
	  //CentraliserMethod := "CT"); 
	  flag, wx := Reduction (Y, x : CentraliserMethod := "CT",
	      LieRank := Degree(Y) - 1); 
      until flag;
      wx := WordToUser (Y, wx);
      repeat
	  // flag, wy := Reduction (Y, y: Central := true,
	  //CentraliserMethod := "CT");
	  flag, wy := Reduction (Y, y: CentraliserMethod := "CT",
	      LieRank := Degree(Y) - 1);
      until flag;
      wy := WordToUser (Y, wy);

      /* SL4 to C */
      wadd := ImagesOfWords (Y, C, [wx, wy]);

      /* C to G */
      T := G`SLPGroup;
      gamma := hom <C`SLPGroup -> T | C`UserWords cat [wu]>;
      wadd := [gamma (w): w in wadd];
   end if; 

   /* SU4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   basis := SUChosenElements (G: Words := false);

   A := basis[1];
   wa := W1[1]; 

   B1 := Identity (M);
   b1 := E1[2]; 
   MB := MatrixAlgebra (E, Nrows (b1));
   InsertBlock (~B1, MB!b1, 1, 1);
   B1 := GL(d, E)!B1; 
   wb1 := W1[2]; 

   Bg := Zero (M);
   Bg[f-1][f + 1] := 1; 
   Bg[f][f + 2] := 1;
   Bg[f + 1][f - 1] := 1;
   Bg[f + 2][f] := 1;
   for i in [1..f - 2] cat [f + 3..d] do Bg[i][i] := 1; end for;
   Bg := GL(d, E)!Bg; 
    
   b2 := E2[2]; 
   B2 := Identity (M);
   MB := MatrixAlgebra (E, Nrows (b2));
   InsertBlock (~B2, MB!b2, f + 1, f + 1);
   B2 := GL(d, E)!B2; 
   wb2 := W2[2];

   /* produce (1,3,...,d - 1)(2,4,...,d) */
   B := B2 * Bg * B1;
   wb := wb2 * wg * wb1; 
   B := GL(d, E)!B; 

   T := basis[3];
   wt := W1[3]; 

   D := basis[4];
   wdelta := W1[4];

   if f ge 4 then 
      P := basis[5];
      wp := W1[5]; 
   else
      P := B;
      wp := wb;
   end if;

   gl := GL(d, E);
   E := [gl | A, B, T, D, P];
   W := [wa, wb, wt, wdelta, wp];

   /* additional element to generate unitary group */
   if FinalCall and IsEven (d) then 
      E cat:= [basis[i]: i in [#basis - 1..#basis]];
      o := (d - f - 2) div 2; 
      wadd := [w^(W[2]^o): w in wadd];
      W cat:= wadd;
   else 
      E cat:= [basis[i]: i in [#basis - 1..#basis]];
      W cat:= [W2[i]: i in [#W2 - 1..#W2]];
   end if;

   return E, W;
end function;

/* find element y of even order 2n such that y^n has
   eigenspaces of dimension f, d - f where each lies in range
   d/3... 2d/3; write matrices wrt resulting eigenbasis */
 
SUSplitSpace := function (G : Limit := Maximum (100, 5 * Degree (G)), 
   SortSpaces := true, Range := [Degree(G) div 3..2 * Degree(G) div 3])

   found := false;
   nmr := 0;
   repeat 
      flag, g, w := GenerateInvolution (G);
      if flag then 
         /* ensure that even is at top: we can't easily
            produce diag[1,-1,-1] in SU(3) */
         if SortSpaces then 
            U := Eigenspace (g, -1);
            W := Eigenspace (g, +1);
         else 
            /* SplitInvolutions assumes this ordering */
            U := Eigenspace (g, +1);
            W := Eigenspace (g, -1);
         end if;
         degs := [Dimension (U), Dimension (W)];
         vprint User5: "Characteristic polynomial factors have degree ", degs;
         found := exists (x) {x : x in degs | x in Range};
      end if;
      nmr +:= 1;
   until found or nmr gt Limit;

   if nmr gt Limit then
       error ERROR_RECOGNITION;
      //error Error (rec<RecognitionError |
        // Description := "Constructive recognition for classical group",
        // Error := "Failed to split unitary space">);
   end if;

   vprint User5: "Number of random elements processed to split unitary space is ", nmr;

   /* if even, ensure large space is at top */
   if SortSpaces and IsEven (Dimension (W)) and Dimension (W) gt Dimension (U) then 
      tmp := U; U := W; W := tmp;
   end if;

   d := Degree (G);
   B := [Eltseq (u): u in Basis (U)] cat [Eltseq (u): u in Basis (W)]; 
   B := &cat (B);
   F := BaseRing (G);
   CB := GL (d, F) ! B;
   H := sub <GL(d, F) | [CB * G.i * CB^-1 : i in [1..Ngens (G)]]>;
   b := CB * g * CB^-1;
   return g, w, H, b, CB, Dimension (U), Dimension (W);
end function;

/* recognize SU in its natural representation */

SUProcess := function (G, InputDimension: Special := false)

   InitialiseGroup (G); 
   d := Degree (G);
   E := BaseRing (G);
   e := Degree (E);

   if (Degree (G) lt 4) or (Degree (G) eq 4 and #E eq 9) then 
      vprint User1 : "Call CompositionTree for degree ", d;
      X, Y, CB := SUChosenElements (G);
      return X, Y, CB;
   end if;

   /* if special, then split space of degree d = 4k + r as 4k and r */
   if Special and Degree (G) ne 5 then
      r := d mod 4;
      if r eq 0 then
         Range := [Degree (G) div 2];
         g, w, H, b, CB, dim := SpecialSplitSpace (G:
                                IsCorrectType := MyIsUnitaryGroup);
      elif r eq 1 then
         Range := [Degree (G) - 5];
         g, w, H, b, CB, dim := SUSplitSpace (G: Range := Range);
      else
         Range := [Degree (G) - r];
         g, w, H, b, CB, dim := SUSplitSpace (G: Range := Range);
      end if;
   else
      Range := [Degree(G) div 3..2 * Degree(G) div 3];
      if Degree (G) eq 5 then Range := [2, 3]; end if;
      g, w, H, b, CB, dim := SUSplitSpace (G: Range := Range);
   end if;

   flag, form := UnitaryForm (G);
/* 
   if not flag then
       flag, form := UnitaryForm(G : Scalars := true);
   end if;
*/
   assert flag;
   
   form := CB * form * Transpose (FrobeniusImage (CB, e div 2));
   cb := SUHalfChangeBasis (G, form, dim);
   cb := cb^-1;
   H := H^(cb^-1);

   vprint User5: "Length of word for involution is now ", #w;

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

    C := SpecialCentraliser (H, b, w, dim:
         type := "unitary", IsCorrectType := MyIsUnitaryGroup);

   C1 := GoodCentraliser (G, C, dim, {dim + 1..d}:
         type := "unitary", IsCorrectType := MyIsUnitaryGroup);
   C2 := GoodCentraliser (G, C, d - dim, {1..dim}:
         type := "unitary", IsCorrectType := MyIsUnitaryGroup);

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User1 : "call 1";
   vprint User1 : "dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := $$ (G1, InputDimension: Special := Special);
   // assert ClassicalVerify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   vprint User5: "Length from G1 is ", [#x : x in W1];
   
   /* if special we can conjugate solution for G1 under element 
      of projective centraliser to obtain solution for G2 */

   if Special and (Degree (G) mod 4 eq 0) then 
      vprint User5: "Search for projective generator";
      theta, wtheta := ProjectiveGenerator (G, g, w);
      theta := cb * CB * theta * CB^-1 * cb^-1;
      /* now conjugate */
      W2 := [w^wtheta: w in W1]; 
      E2 := E1;
      LCB1 := CombineMatrices (CB1, CB1^0);
      B2 := [LCB1[i] : i in [1..dim]] cat [LCB1[i] * theta : i in [1..dim]];
      LCB2 := GL(d, E) ! &cat [Eltseq (b2): b2 in B2];
      CB2 := ExtractBlock (LCB2, dim + 1, dim + 1, dim, dim);
   else 
      vprint User1 : "call 2";
      E2, W2, CB2 := $$ (G2, InputDimension: Special := Special);
      // assert ClassicalVerify (G2, E2, W2, CB2); 
      W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];
   end if;

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   vprint User1 : "call Glue", Degree (G1), Degree (G2);
   X, Y := SUGlue (H, G1, E1, W1, G2, E2, W2: FinalCall := Degree (H) 
                        eq InputDimension);
   // assert ClassicalVerify (G,X,Y,Total * CB);

   return X, Y, Total * cb * CB;
end function;

intrinsic Internal_SolveSU(G :: GrpMat) -> [], [], GrpMatElt
{construct standard generators for G, a conjugate of the natural copy of
the special unitary group; return the standard generators in G, their SLPs in
terms of defining generators of G, and the change-of-basis matrix to
conjugate them to standard copy}

   d := Degree (G);
   require d ge 2: "Input group must have dimension at least 2";

   F := BaseRing (G);
   if IsEven (#F) then return SolveClassicalEven (G: type := "SU"); end if;

   /* if possible split the space precisely */
   Special := true;
   E, W, CB := SUProcess (G, d: Special := Special);
   WG := WordGroup (G); W := Evaluate (W, [WG.i: i in [1..Ngens (WG)]]);
   return E, W, CB;
end intrinsic;
