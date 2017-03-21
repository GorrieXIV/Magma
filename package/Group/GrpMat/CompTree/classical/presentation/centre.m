freeze;

//$Id:: centre.m 1882 2010-06-17 01:22:14Z eobr007                           $:

import "sl.m": SLStandardToPresentation;
import "../recognition/standard.m": SLChosenElements;

/* variation of code used to recognise SL(2, q) in its natural representation */

CompleteSL2Basis := function (G)

   E := BaseRing (G);
   e := Degree (E);
   Z := Integers ();

   SLB := G`SL2Basis;
   B := SLB[1];
   L := B[1]; D := B[2]; U := B[3]; 
   W := SLB[2]; wL := W[1]; wU := W[3]; wD := W[2];

   /* make leading entry in diagonal element the 
      standard primitive element for E */
   x := PrimitiveElement (E);
   t := D[1][1];
   // "Discrete log call 4:";
   u := Log (t);
   R := RingOfIntegers (#E - 1);
   v := Z ! (Solution (R!u, R!1));
   D := GL(2, E) ! [x, 0, 0, x^-1]; wD := wD^(v);

   K := sub < E| x^2>;

   a := U[1][2];
   coeffs := Eltseq (K ! a^-1);
   coeffs := [Z!c: c in coeffs];

   /* standard basis element [1, 1, 0, 1] */
   US := GL (2, E) ![1,1,0,1];
   wUS := &*[(wU^(wD^-i))^coeffs[i + 1]: i in [0..#coeffs - 1]];

   /* set up complete basis for upper triangular matrices */
   UB := [GL(2, E) ! [1, x^(2 * i), 0, 1]: i in [0..e - 1]];
   wUB := [wUS^(wD^-i): i in [0..e - 1]];

   a := L[2][1];
   coeffs := Eltseq (K ! a^-1);
   coeffs := [Z!c: c in coeffs];

   /* standard basis element [1, 0, 1, 1] */
   LS := GL (2, E) ![1,0,1,1];
   wLS := &*[(wL^(wD^i))^coeffs[i + 1]: i in [0..#coeffs - 1]];

   /* set up complete basis for lower triangular matrices */
   LB := [GL(2, E) ! [1, 0, x^(2 * i), 1]: i in [0..e - 1]];
   wLB := [wLS^(wD^i): i in [0..e - 1]];

   B := <[* LB, D, UB *], [* wLB, wD, wUB *], SLB[3], SLB[4]>; 
  
   G`SL2Basis:= B; 
   
   return true;
end function;

/* given a canonical generating set gens for (P)SL(2, q),
   write g as word in gens */

MySL2ElementToSLP := function (G, g)
   
   if Determinant (g) ne 1 then return false; end if;

   Z := Integers ();
   E := BaseRing (Parent (g));

   SLB := G`SL2Basis;
   dim2cb := SLB[3]; cb := SLB[4];
   g := dim2cb * g * dim2cb^-1;

   LB := SLB[1][1]; wLB := SLB[2][1];
   UB := SLB[1][3]; wUB := SLB[2][3];

//   cb := SLB[3];
//   h := g;

   /* primitive element for field */
   D := SLB[1][2]; 
   x := D[1][1];
   K := sub <E | x^2>;

   /* if necessary interchange columns by 
      premultiplying g by C = 0, 1, -1, 0 */
   if g[1][1] eq 0 or g[2][2] eq 0 then 
      B := UB[1]; wB := wUB[1];
      coeffs := Eltseq (K!(-1));
      coeffs := [Z!c: c in coeffs];
      // A1 := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
      wA1 := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
      // C := B * A1; 
      wC := wB * wA1;
      coeffs := Eltseq (K!(1));
      coeffs := [Z!c: c in coeffs];
      // A2 := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
      wA2 := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
      // C := C * A2; 
      wC := wC * wA2;
      C := GL(2, E) ! [0, 1, -1, 0];
      g := C * g; 
      word := wC^-1;
 //    LM := [C];
   else
//      LM := [LB[1]^0];
      word := wLB[1]^0; 
   end if;

   /* zero out 2, 1 entry of g */
   x := -(g[2][1] / g[1][1]);
   coeffs := Eltseq (K!x); coeffs := [Z!c: c in coeffs];
   A := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
   word *:= wA^-1;
//   Append (~LM, A);
   g := A * g; 

   /* zero out 1, 2 entry of g */
   x := -(g[1][2] / g[2][2]);
   coeffs := Eltseq (K!x); coeffs := [Z!c: c in coeffs];
   A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   word *:= wA^-1;
//   Append (~LM, A);

   g := A * g; 
   /* construct resulting diagonal matrix g as product of basis elements */
   a := g[1][1];
   c := a - 1;

 //  RM := [];
   /* construct 1, c, 0, 1 */
   coeffs := Eltseq (K!c); coeffs := [Z!c: c in coeffs];
   // A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   second := wA;
   // Append (~RM, A);

   /* construct 1 + c, c, 1, 1 via column operation */
   B := LB[1];
   wB := wLB[1];
   // C := A * B;
   second := second * wB;
   // Append (~RM, B);

   /* construct 1 + c, 0 , 1, (1 + c)^-1 by column operation */
   coeffs := Eltseq (K! (-c / (1 + c))); coeffs := [Z!c: c in coeffs];
   // A := &*[UB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wUB[i]^coeffs[i]: i in [1..#coeffs]];
   // Append (~RM, A);
   second := second * wA;
   // C := C * A; 

   /* finally construct 1 + c, 0, 0, (1 + c)^-1 by column operation */
   coeffs := Eltseq (K! (-1 / (1 + c))); coeffs := [Z!c: c in coeffs];
   // A := &*[LB[i]^coeffs[i]: i in [1..#coeffs]];
   wA := &*[wLB[i]^coeffs[i]: i in [1..#coeffs]];
   second := wA * second;
   // Append (~RM, A);
   // C := A * C; 
   // assert h eq LM[1]^-1 * LM[2]^-1 * LM[3]^-1 * RM[4] * RM[1] * RM[2] * RM[3];
   word := word * second;
   return word;
   
end function;

/* construct diagonal matrix (alpha^-1, alpha);
   F is SLP group, X is list of standard generators for SL(2, q),
   W is corresponding list of SLPs */

DiagonalMatrix := function (F, X, W, alpha)
   P := Parent (Rep (X));
   d := Degree (P);
   K := BaseRing (P);
   q := #K;
   Gens := [(X[1]^X[2])^-1, X[4]^-1, X[1]];
   G := SL(2, q);
   gens := [G!ExtractBlock (g, 1, 1, 2, 2): g in Gens];
   S := SLPGroup (3);
   WS := [S.1, S.2, S.3];
   CB := Identity (G);
   G`SL2Basis := <gens, WS, CB, CB>;
   flag := CompleteSL2Basis (G);
   g := G![alpha^-1,0,0,alpha];
   w := MySL2ElementToSLP (G, g);
   if Degree (K) eq 1 then
      gens := [gens[1], gens[1]^0, gens[3]];
      tau := hom <S -> F | [(W[1]^W[2])^-1, W[1]^0, W[1]^1]>;
   elif d eq 2 then 
      tau := hom <S -> F | [(W[1]^W[2])^-1, W[4], W[1]]>;
   else
      tau := hom <S -> F | [(W[1]^W[2])^-1, W[4]^-1, W[1]^1]>;
   end if;
   // assert Evaluate (w, gens) eq g;
   w := tau (w);
   return w;
end function;

/* G = <U, V> is group of signed permutations mapping to
   (1, 2) and (1,2, ..., d) respectively; set up array Z 
   where image of Z[i] in Sym (d) is product of 2^(i - 1) 2-cycles
   (1, 2^(i - 1) + 1) (2, 2^(i - 1) + 2) ... (2^(i - 1), 2^i) */

SetupZ := function (U, V, d)
   Z := [U];
   i := 1;
   W := V;
   while (2^(i + 1) le d) do 
      a := Z[i]^W;
      b := Z[i]^a;
      Z[i + 1] := b * b^W;
      if 2^(i + 2) le d then W := W^2; end if;
      i +:= 1;
    end while;

    return Z;
end function;

/* input: diagonal matrix D whose first two diagonal entries
   are (a^-1, a) for some a, remaining entries are 1;
   set up array s where s[i] evaluates to diagonal matrix
   whose first 2^i entries are a, last entry a^(-2^i), remainder 1 */
   
SetupS := function (D, V, Z, d)
   S := [D^(V^-1)];
   i := 1;
   while 2^i le d do 
      S[i + 1] := S[i]^(Z[i]) * S[i];
      i +:= 1;
   end while;
   return S;
end function;
   
/* construct array X where X[1] evaluates
   to (1,...,d - 1)(d) and X[i] = X[i- 1]^2 */

SetupX := function (U, V, d)
   X := [V^2 * U * V^-1];
   i := 1;
   while 2^i lt d do 
      X[i + 1] := X[i]^2;
      i +:= 1;
   end while;
   return X;
end function;

/* given three generators 
   U [short cycle] and V [long cycle] for SL (d, q),
   and D [(alpha^-1, alpha, 1, ..., 1)], 
   construct efficiently the element mapping to the 
   diagonal matrix (alpha, ..., alpha, alpha^(1 - d)) */
   
Scalar := function (D, V, U, d)
   Z := SetupZ (U, V, d);
   S := SetupS (D, V, Z, d);
   X := SetupX (U, V, d);

   B := IntegerToSequence (d - 1, 2);
   j := 0;
   s := U^0;
   c := s;
   while 2^j lt d do
      if B[j + 1] eq 1 then 
         s *:= S[j + 1]^c;
         c *:= X[j + 1];
      end if;
      j +:= 1;
   end while;
   return s;
end function;

/* set up presentation standard generators for SL(d, q), and 
   identify D, U, W and their corresponding SLPS */

BasicSetup := function (Q, d, q)
   G := SL(d, q);
   E := SLChosenElements (G);
   X := SLStandardToPresentation (d, q);

   /* presentation for prime field case is on 3 generators */
   if IsPrime (q) then 
      U := Universe (X);
      W := SLPGroup (4);
      X := Evaluate (X, [W.i: i in [1..3]]);
      X cat:= [W.4^-1];
   end if;

   E := Evaluate(X, E);
   W := [Q.i :i in [1..Ngens (Q)]];

   F := BaseRing (G);
   e := Degree (F);

   IE := E;
   if d eq 2 and e eq 1 then 
      D := E[3]; V := E[2]; U := E[2];
      Dw := W[1]^0; Vw := W[2]; Uw := W[2]; 
      E := [E[1], U, V, D];
      W := [W[1], Uw, Vw, Dw];
   elif d eq 2 then 
      D := E[1]; V := E[3]; U := E[3]; T := E[2];
      Dw := W[1]; Vw := W[3]; Uw := W[3]; Tw := W[2];
      E := [E[2], U, V, D];
      W := [W[2], Uw, Vw, Dw];
   elif e eq 1 then
      D := E[4]; V := E[3]; U := E[2]; 
      Dw := W[3]^0; Vw := W[3]; Uw := W[2]; 
      if d eq 3 then V := V^-1; Vw := Vw^-1; end if;
      E := [E[1], E[2], V, D];
      W := [W[1], W[2], Vw, Vw^0]; 
   else 
      D := E[4]; V := E[3]; U := E[2]; 
      Dw := W[4]; Vw := W[3]; Uw := W[2]; 
      if d eq 3 then V := V^-1; Vw := Vw^-1; end if;
      E := [E[1], E[2], V, E[4]];
      W := [W[1], W[2], Vw, W[4]]; 
   end if;

   return D, V, U, Dw, Vw, Uw, IE, E, W;
end function;

/* construct generator s for centre of G = SL(d, q) as SLP t in 
   (presentation) standard generators for G; 
   t is an element of Q, the corresponding SLP group */

GeneratorOfCentre := function (Q, d, q) 
   D, V, U, Dw, Vw, Uw, IE, E, W := BasicSetup (Q, d, q);
   F := GF (q);
   w := PrimitiveElement (F);
   q := #F;
   m := (q - 1) div Gcd (d, q - 1);
   alpha := w^m;
   Dw := DiagonalMatrix (Q, E, W, alpha);
   D := Evaluate (Dw, IE); 
   s := Scalar (D, V, U, d);
   t := Scalar (Dw, Vw, Uw, d);
   return t, s;
end function;

/* construct diagonal matrix (alpha, ..., alpha, alpha^(1 - d))
   from standard generators of G = SL (d, q) */

ConstructScalar := function (Q, G, alpha: DiscreteLog := false)
   d := Degree (G);
   q := #BaseRing (G);
   D, V, U, Dw, Vw, Uw, IE, E, W := BasicSetup (Q, d, q);
   if DiscreteLog then 
      k := Log (D[1][1], alpha);
   else
      zw, z := GeneratorOfCentre (Q, d, q);
      /* we can do this since k is at most d */
      k := 0; alpha := z[1][1]; power := alpha^k; 
      while power ne alpha and k le d do 
          power *:= alpha;
          k +:= 1;
      end while;
      if power ne alpha then error "problem with alpha"; end if;
   end if;
   Dw := DiagonalMatrix (Q, E, W, alpha);
   D := Evaluate (Dw, IE); 
   s := Scalar (D, V, U, d);
   t := Scalar (Dw, Vw, Uw, d);
   return t, s;
end function;
