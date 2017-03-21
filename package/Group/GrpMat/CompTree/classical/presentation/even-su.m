freeze;

import "sl2q.m": UpperTriangle, PresentationForSL2;
import "../recognition/standard.m": SUChosenElements;
import "odd-su.m": OddSUStandardToPresentation, OddSUPresentationToStandard;

forward ConvertToStandard, GeneratorOfCentre;

/////////////////////////////////////////////////////////////////////////
//   standard presentation for SU(n, q) even n                         //
//                                                                     //
//   Input two parameters to compute this presentation of SU(n, q)     //
//     n = dimension                                                   //
//     q = field order                                                 //
//                                                                     //
//   July 2010 -- latest revision                                       //
/////////////////////////////////////////////////////////////////////////

EvenSU := function (n, q: original := false, Projective := false) 
  
   d := n div 2; /* rank */

   // Set up field elements
   E := GF (q^2); 
   e := Degree (E);    
   p := Characteristic (E); 
   w := PrimitiveElement (E);

  if IsEven (p) then
      alpha := w^((q + q^2) div 2);
      w0 := w^(q + 1);
   else
      alpha := w^((q + 1) div 2);
      w0 := alpha^2;
   end if;

   f := e div 2;
   I := Integers ();

   // Define the group
   if n eq 4 then F := SLPGroup (5); else F := SLPGroup (6); end if;

   T := F.1;     // Transvection t_12(alpha)
   S := F.2;     // Sigma_2143(1)
   D := F.3;     // Diagonal matrix [w^q, w^-1, w, w^-q, 1 ... 1]
   Z := F.4;     // 0, alpha, -alpha^-1 0 : I 
   U := F.5;     // Permutation matrix for the short cycle (1, 3)(2, 4)

   // Permutation matrix for long cycle (1,3,5, ...,n - 1)(2,4,...,n) 
   V := n eq 4 select F.5 else F.6;     
   
   Rels := []; 

   // For this procedure we'll use the standard (Coxeter) presentation 
   // of the symmetric group Sym(d) in terms of the 
   // short cycle U = (1, 3)(2,4) and the 
   // long cycle V = (1, 3, ..., n - 1)(2, 4, ... n)

   Append (~Rels, 1=U^2);
   if d gt 2 then 
      Append (~Rels, 1=V^d);
      Append (~Rels, 1=(U*V)^(d-1));
      Append (~Rels, 1=(U, V)^3);
   end if;
   for i in [2..(d div 2)] do Append (~Rels, 1=(U, V^i)^2); end for;

   /* R2 wreath product <U, V, Z> = Z_4 wr S_d */
   if p eq 2 then 
      Append (~Rels, Z^2 = 1); 
   else 
      Append (~Rels, Z^4 = 1);
   end if;

   if d gt 2 then 
      Append (~Rels, (Z, U^V) = 1);
   end if;
   if d gt 3 then 
      Append (~Rels, (Z, V * U) = 1);
   end if;
   Append (~Rels, (Z, Z^U) = 1);
   
   delta := (D, Z);

   // R3 These relations set up C_4 wr Sym(d-1) as stabilizing T and D 
   Append (~Rels, 1=(T, Z^U));
   Append (~Rels, 1=(delta, Z^U)); 

   if d gt 2 then 
      Append (~Rels, 1=(T, U^V));
      Append (~Rels, 1=(delta, U^V));
   end if;

   if d gt 3 then 
      Append (~Rels, 1=(T, V * U));
   end if;

   // R4 
   Append (~Rels, S^(Z^2) = S^-1); 
   Append (~Rels, T^(Z^2) = T); 
   Append (~Rels, delta^(Z) = delta^-1); 

   // R5 These relations set up C_4 wr Sym(d-2) as stabilizing S 
   if d gt 2 then 
      Append (~Rels, 1=(S, Z^(V^2)));
      Append (~Rels, 1=(D, Z^(V^2)));
   end if;

   if d gt 3 then 
      Append (~Rels, 1=(S, U^(V^2)));
      Append (~Rels, 1=(D, U^(V^2)));
   end if;

   if d gt 4 then 
      Append (~Rels, 1=(S, V * U * U^V));
      Append (~Rels, 1=(D, V * U * U^V));
   end if;

   // R6 relations giving presentation for SL(2, q) in delta, T, Z 
   G, R := PresentationForSL2 (p, f);
   if f gt 1 then 
      tau := hom<G -> F | delta, T, Z>;
   else 
      tau := hom<G -> F | T, Z>;
   end if;
   R6 := [tau (r): r in R];

   // R7 relations giving presentation for GF(p^e): GF(p^e)^* in D and S 
   G, R := UpperTriangle (p, e: Projective := false, Linear := true);
   tau := hom<G -> F | D, S>;
   R7 := [tau (r): r in R];

   // R8 Linking relations for <T, delta, D, U> and <S, D, U> 
   Append (~Rels, 1=(delta, D));
   Append (~Rels, D^U = D^q);
    
   Append (~Rels, (T, T^U) = 1);
   Append (~Rels, (delta, delta^U) = 1);
   Append (~Rels, (T, delta^U) = 1);
   Append (~Rels, S^U = S^-1);

   R := sub < E | w0^2>;
   k := Eltseq (R!(w0^-1));
   k := [I!x: x in k];
   Append (~Rels, T^D = &*[(T^(delta^(i-1)))^k[i]: i in [1..#k]]);

   // R9 Steinberg relations 

   // R := sub < E | w^2>;
   if p eq 2 then 
     S1 := S^Z;
   else 
      R := sub < E | w^2>;
      k := Eltseq (R!(-alpha^-1));
      k := [I!x: x in k];
      S1 := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]]; S1 := S1^Z;
   end if;
   Append (~Rels, (S, S1) = 1); // type S3 

   if p eq 2 then
      R := sub <E | w0>;
      val := w^(2 * q) - w^(2);
      T1 := T^(Z * U);
      k := Eltseq (R!val);
      k := [I!x: x in k];
      rhs := &*[(T1^(D^(i-1)))^k[i]: i in [1..#k]]; 
   else 
      R := sub <E | w0^2>;
      val := w^((7 * q + 3) div 2) - w^((3 * q + 7) div 2);
      k := Eltseq (R!val);
      k := [I!x: x in k];
      rhs := &*[(T^(delta^(i-1)))^k[i]: i in [1..#k]]; rhs := rhs^(D * Z * U);
   end if;
   Append (~Rels, (S^D, S1) = rhs); // type S3 
   
   Append (~Rels, (S, T^Z) = 1); // type S4 
   if p eq 2 then 
      Append (~Rels, (S, T) = S^Z * T^(Z * U)); // type S5 
   else 
      c := D^-1 * Z * U; 
      Append (~Rels, (S, T) = S^Z * T^c); // type S5 
   end if;
   Append (~Rels, (T, T^U) = 1); // type S6 

   if d gt 2 then 
      Append (~Rels, (S, S^V) = 1); // type S8 
      Append (~Rels, (S^D, S^V) = 1); // type S8 
      Append (~Rels, (S, T^(V^2)) = 1); // type S11
   end if;
   if d gt 3 then 
      Append (~Rels, (S, S^(V^2)) = 1); // type S10
   end if;

   if d gt 2 then 
      if p eq 2 then 
         rhs := (S^(V * U));
      else 
         R := sub <E | w^2>;
         k := Eltseq (R!(-alpha));
         k := [I!x: x in k];
         rhs := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]]; rhs := rhs^(U^V);
      end if;
      Append (~Rels, (S, S^(Z * V)) = rhs); // type S9
   end if;

   if d gt 2 then
      if p eq 2 then 
         Append (~Rels, (S^D, S^(Z * V)) = ((S^D)^(V * U)));
      else
         R := sub <E | w^2>;
         k := Eltseq (R!(-alpha));
         k := [I!x: x in k];
         rhs := &*[(S^(D^(i)))^k[i]: i in [1..#k]]; rhs := rhs^(U^V);
         Append (~Rels, (S^D, S^(Z * V)) = rhs); // type S9
      end if;
   end if;

   // R10
   // express D as words in conjugates of S and T
   R := sub<E | w^2>;
   if p eq 2 then 
      beta := 1 + w^(-q);
      k := Eltseq (R!beta);
   else 
      k := Eltseq (R!(w^(-2 * q - 1) - w^(-q - 1)));
   end if;
   k := [I!x: x in k];
   s1 := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]]; s1 := s1^(Z * Z^U);
    
   if p eq 2 then alpha := w; else alpha := -w; end if;
   k := Eltseq (R!(alpha));
   k := [I!x: x in k];
   s2 := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]];

   if p eq 2 then 
      gamma := w^-q + w^-(2 * q);
      k := Eltseq (R!gamma);
   else 
      k := Eltseq (R!(w^(-2 * q - 1) - w^(-3 * q - 1)));
   end if;
   k := [I!x: x in k];
   s3 := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]]; s3 := s3^(Z * Z^U);
   Append (~Rels, D = S * s1 * s2 * s3);

   // express U as words in conjugates of S and T
   if p eq 2 then 
      s4 := S;
   else 
      k := Eltseq (R!(-w^(-(q + 1) div 2)));
      k := [I!x: x in k];
      s4 := &*[(S^(D^(i-1)))^k[i]: i in [1..#k]]; 
   end if;
   Append (~Rels, U = (s4^(Z^U))^-1 * s4^(Z) * (s4^(Z^U))^-1 * Z^2);

   // R11 
   Append (~Rels, (D, D^V) = 1);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels cat:= R6;
   Rels cat:= R7;

   if original then
      return F, Rels;
   else 
      W, Rels := ConvertToStandard (n, q, Rels);
      if Projective then
         z := GeneratorOfCentre (n, q, W);
         Append (~Rels, z);
      end if;
      return W, Rels;
   end if;
end function;

/* construct generator of centre of SU(d, q) as 
   SLP in standard generators */

GeneratorOfCentre := function (d, q, W)

   m := (q + 1) div Gcd (d, q + 1);

   v := W.2; u := W.5;
   y := W.7;

   // order of centre of SU(d, q)
   // o := Gcd (d, q + 1);
   
   if IsEven (d) then 
      n := d div 2;
      y := y^(v^2);
      w := v^2 * u * v^-1;
      term := (y^(q-1))^(u * v^-1);
      scalar := term;
      for i in [1..n - 2] do 
         term := term^w;
         scalar *:= term;
      end for;
      z := scalar^m;
   
      if IsOdd (q) then
         G := SU (d, q);
         E := SUChosenElements (G);
         matrix := Evaluate (z, E);
         if not IsScalar (matrix) then
            delta := W.4;
            a := (delta^(v^-1))^((q - 1) div 2); 
            z *:= a; 
          end if;
      end if;

      return z;
   end if;
   
   n := d div 2;
   term := y^(q-1);
   scalar := term;
   for i in [1..n - 1] do 
       term := term^(v^-1);
       scalar *:= term;
   end for;
   z := scalar^m;
   return z;
end function;

Transvection := function (d, q, i, j, alpha)
   F := GF (q);
   M := MatrixAlgebra (F, d);
   E := Identity (M);
   E[i][j] := alpha;
   return GL(d, F) ! E;
end function;

Sigma := function (d, q, i, j, k, l, a)

   M := MatrixAlgebra (GF(q^2), d);
   A := Identity (M);
   B := [A[i]: i in [1..d]];
   C := B;
   C[i] := B[i] + a * B[l];
   C[k] := B[k] - a^q * B[j];
   C := &cat ([Eltseq (x): x in C]);
   return GL(d, q^2)!C, M!C;
end function;

Vmatrix := function (d, q, i, j, alpha)
   F := GF (q^2);
   w := PrimitiveElement (F);
   abar := alpha^q;
   x := alpha * abar * w^((q + 1) div 2);
   a := MatrixAlgebra (F, 3)![1, alpha, x, 0, 1, -abar, 0, 0, 1];
   A := Identity (MatrixAlgebra (F, d));
   InsertBlock (~A, a, i, j);
   return A;
end function;

/* May 2010: presentation paper generators for SU(d, q)*/

EvenSUPresentationGenerators := function (d, q) 

   G := GL (d, q^2);
   d := Degree (G);
   E := BaseRing (G); 

   f := Degree (E) div 2;
   p := Characteristic (E);
   q := p^f;
   F := GF(p, f);

   w := PrimitiveElement (E);
   w0 := w^(q + 1); 
   if p eq 2 then 
      alpha := w0; 
   else 
      alpha := w^((q + 1) div 2); 
   end if;

   M := MatrixAlgebra (E, d);

   if p eq 2 then 
      tau := Transvection (d, q^2, 1, 2, 1);
   else 
      tau := Transvection (d, q^2, 1, 2, alpha);
   end if;

   if d ge 4 then 
      sigma := Sigma (d, q^2, 2,1,4,3, 1);
   else
      sigma := tau^0;
   end if;
   
   Z := Zero (M);
   if p eq 2 then 
      Z[1][2] := 1;
      Z[2][1] := 1; 
   else 
      Z[1][2] := alpha;
      Z[2][1] := -alpha^-1;
   end if;
   for i in [3..d] do Z[i][i] := 1; end for;

   delta := Identity (M);
   delta[1][1] := w^q;
   delta[2][2] := w^-1;
   delta[3][3] := w;
   delta[4][4] := w^-q;

   if d ge 4 then 
      u := Zero (M);
      u[1][3] := 1; u[2][4] := 1; u[3][1] := 1; u[4][2] := 1;
      for i in [5..d] do u[i][i] := 1; end for;
   else
      u := Identity (M);
   end if;

   if d ge 4 then 
      v := Zero (M);
      n := d div 2;
      for i in [1..2 * n - 2 by 2] do
         v[i][i + 2] := 1;
      end for; 
      v[2 * n - 1][1] := 1;
      for i in [2..2 * n - 2 by 2] do
          v[i][i + 2] := 1;
     end for; 
      v[2 * n][2] := 1;
      if IsOdd (d) then v[d][d] := 1; end if;
   else 
      v := Identity (M);
   end if;

   P := GL(d, E);
   tau := P!tau; sigma := P!sigma; 
   delta := P!delta; Z := P!Z;u := P!u; v := P!v; 

   return [tau, sigma, delta, Z, u, v]; 
end function;

/* write presentation generators as SLPs in standard generators of SU(d, q) */

SUStandardToPresentation := function (d, q: Gens := [])
   if Gens cmpeq [] then 
      S := SLPGroup (7);
      E := [S.i: i in [1..7]];
   else
      E := Gens; 
   end if;
   
   s := E[1]; v := E[2]; t := E[3];
   delta := E[4]; u := E[5]; x := E[6]; y := E[7];

   Delta := ((y^(v^2))^s)^-1;

   if d eq 4 and q mod 4 eq 1 then
      F<w> := GF(q^2);
      R := sub<F | w^2>;
      alpha := w^((q + q^2) div 2);
      a := Eltseq (R!alpha);
      a := [Integers () ! x: x in a];
      sigma := &*[((x^s)^(Delta^(i-1)))^-a[i]: i in [1..#a]];
   elif d eq 4 and IsEven (q) then 
      C := s * Delta^(q^2 - 1);
      sigma := (x^C);
   elif q mod 4 eq 3 then 
      C := s * Delta^((q + 1) div 4);
      sigma := (x^(v^2))^C;
   else 
      if IsPowerOf (q, 2) then 
         A := Delta^(q^2 - 1) * (s, u);
      else 
         A := Delta^(-(q + 1) div 2) * (s, u);
      end if;
      B := A^(u^v);
      sigma := (x^(v^2))^(B^-1);
   end if;

   return [t, sigma, Delta, s, u, v];
end function;
   
/* write standard generators as SLPs in presentation generators of SU(d, q) */

SUPresentationToStandard := function (d, q)

   if d eq 4 then n := 5; else n := 6; end if;
   S := SLPGroup (n);
   P := [S.i: i in [1..n]];

   T := P[1]; S := P[2]; Delta := P[3]; Z := P[4]; U := P[5];
   if d eq 4 then V := P[5]; else V := P[6]; end if;

   delta := (Z, Delta);

   y := ((Delta^-1)^(Z^-1))^(V^-2);

   if d eq 4 and q mod 4 eq 1 then
      F<w> := GF(q^2);
      R := sub <F | w^(q - 1)>;
      alpha := w^((q + q^2) div 2);
      a := Eltseq (R!alpha^-1);
      a := [Integers () !x: x in a];
      x := &*[((S^Z)^(Delta^(i-1)))^-a[i]: i in [1..#a]];
   elif q mod 4 eq 3 then 
      C := Z * Delta^((q + 1) div 4);
      x := (S^(C^-1))^(V^-2);
   elif d eq 4 and IsEven (q) then 
      C := Z * Delta^(q^2 - 1);
      x := S^(C^-1);
   else 
      if IsPowerOf (q, 2) then 
         A := Delta^(q^2 - 1) * (Z, U);
      else 
         A := Delta^(-(q + 1) div 2) * (Z, U);
      end if;
      B := A^(U^V);
      x := (S^B)^(V^-2);
   end if;

   return [Z, V, T, delta, U, x, y];
end function;

/* relations are on presentation generators; 
   convert to relations on standard generators */

ConvertToStandard := function (d, q, Rels) 
   if IsEven (d) then 
      A := SUStandardToPresentation (d, q);
   else 
      A := OddSUStandardToPresentation (d, q);
      if d eq 3 then A cat:= [A[1]^0: i in [1..4]]; end if;
   end if;
   Rels := Evaluate (Rels, A);
   W := Universe (Rels);
   if IsEven (d) then 
      B := SUPresentationToStandard (d, q);
   else 
      B := OddSUPresentationToStandard (d, q);
   end if;
   C := Evaluate (B, A);
   U := Universe (C);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

/* 
AttachSpec ("spec");
import "standard.m": SUChosenElements;
for d in [4..20 by 2] do 
for q in [2,3,4,5,7,8,9,11,13,16, 25,27,32, 49, 64, 81] do 
d, q;
G := SU(d, q);
E := SUChosenElements (G);
 Q, W := EvenSU (d, q);
  X := Evaluate (W, E);
assert #Set (X) eq 1;
end for;
end for;
*/

/* 
Attach ("sl2q.m");
Attach ("standard.m");
Attach ("even-su.m");
import "standard.m": SUChosenElements;
import "even-su.m":SUStandardToPresentation;
import "even-su.m": SUPresentationToStandard;
import "even-su.m": EvenSUPresentationGenerators;

for d in [4..20 by 2] do 
for q in [2,3,4,5,7,8,9,11,13,16, 25,27,32, 49, 64, 81] do 
d, q;
G := SU(d, q);
E := SUChosenElements (G);
 Q, W := EvenSU (d, q);
  X := Evaluate (W, E);
 "**** ", #Set (X), #Set (X) eq 1;
assert #Set (X) eq 1;
W := SUStandardToPresentation (d, q);
 P := EvenSUPresentationGenerators(d, q);
Y := Evaluate (W, E);
assert Y eq P;
W := SUPresentationToStandard (d, q);
Y := Evaluate (W, P);
assert Y eq E;
end for;
end for;
*/
