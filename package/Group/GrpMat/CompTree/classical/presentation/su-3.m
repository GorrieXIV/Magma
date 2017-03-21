freeze;

/* May 2010 -- presentation for SU(3, q) */

// import "standard.m": SUChosenElements;
 
VMatrix := function (q, alpha, beta)
   F := GF (q^2);
   w := PrimitiveElement (F);
   MA := MatrixAlgebra (F, 3); 
   if IsEven (q) then
      phi := Trace(w, GF(q))^(-1) * w;
   else
      phi := -1/2;
   end if;
   gamma := phi * alpha^(1 + q) + beta;
   v := MA![1, alpha, gamma, 0, 1, -alpha^q, 0, 0, 1];
   return GL(3, F) ! v;
end function;

DeltaMatrix := function (q, alpha)
   delta := DiagonalMatrix ([alpha, alpha^(q - 1), alpha^-q]);
   return GL(3, q^2) ! delta;
end function;

TauMatrix := function (q, gamma)
   F := GF (q^2);
   MA := MatrixAlgebra (F, 3); 
   tau := MA![1, 0, gamma, 0, 1, 0, 0, 0, 1];
   return GL(3, F) ! tau;
end function;

UMatrix := function (q)
   MA := MatrixAlgebra (GF (q^2), 3);
   t := Zero (MA);
   t[1][3] := 1; t[2][2] := -1; t[3][1] := 1;
   return t;
end function;
  
BorelGenerators := function (q)
   F := GF (q^2);
   p := Characteristic (F);
   w := PrimitiveElement (F);

   v := VMatrix (q, 1, 0);
   if IsEven (p) then
      tau := TauMatrix (q, 1);
   else 
      tau := TauMatrix (q, w^((q+1) div 2));
   end if;
   delta := DeltaMatrix (q, w);

   return [GL(3, q^2) | v, tau, delta];
end function;

SU3Generators := function (q)
   F := GF (q^2);
   p := Characteristic (F);
   w := PrimitiveElement (F);
   value := IsEven (p) select 1 else w^((q+1) div 2); 
   return 
   [GL(3, q^2) | VMatrix (q, 1, 0),
   TauMatrix (q, value),
   DeltaMatrix (q, w),
   UMatrix (q)];
end function;

/* g is arbitrary upper-triangular matrix;
   write as word in Borel subgroup generators */

EvenSLPForElement := function (g, q, W)
   v := W.1;
   tau := W.2;
   delta := W.3;

   I := Integers ();
   E := GF (q^2);
   F := GF (q);
   w := PrimitiveElement (E);

   Gens := SU3Generators (q);
   V := Gens[1]; Tau := Gens[2]; Delta := Gens[3]; 

   word := Identity (W);
   x := g[1][1];
   if x ne 1 then
      k := Log (x);
      word := delta^k;
      g := Delta^-k * g;
      assert g[1][1] eq 1;
   end if;

   y := g[1][2];
   if y ne 0 then
      theta := w^(q - 2);
      R := sub< E | theta>;
      c := Eltseq (R!y);
      c := [I!x: x in c];
      word *:= &*[(v^(delta^(i-1)))^c[i]: i in [1..#c]];
      matrix := &*[(V^(Delta^(i-1)))^c[i]: i in [1..#c]];
      g := matrix^-1 * g;
      assert g[1][2] eq 0 and g[1][3] in F;
   end if;
   
   z := g[1][3];
   if z ne 0 then
      theta := w^-(q + 1);
      R := sub< E | theta>;
      c := Eltseq (R!z);
      c := [I!x: x in c];
      word *:= &*[(tau^(delta^(i-1)))^c[i]: i in [1..#c]];
      matrix := &*[(Tau^(Delta^(i-1)))^c[i]: i in [1..#c]];
      g := matrix^-1 * g;
      assert g[1][3] eq 0; 
   end if;

   return word, g;
end function;

EvenR2Relations := function (q, W)
   F := GF (q^2);
   w := PrimitiveElement (F);
   theta := w^-(q + 1);
   
   v := W.1;
   tau := W.2;
   delta := W.3;
   u := W.4;
   
   Rels := [];
   
   Gens := SU3Generators(q);
   V := Gens[1]; Tau := Gens[2]; Delta := Gens[3]; U := Gens[4];
   
   I := Integers ();
   
   // first of long relations starts here 
   beta := (1 + w^(q- 1))^-1;
   // "Discrete log"; time 
   kk := Log (beta);
   
   phi := beta^-q;
   R := sub <F | w^(q - 2)>;
   k := Eltseq (R!phi);
   k := [I!x: x in k];
   mat1 := &*[(V^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w1 := &*[(v^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   gamma := mat1[1][3];
   theta := gamma + beta^-1;
   // assert theta in GF (q);
   
   w0 := w^(-(q + 1));
   
   R := sub < F | w0>;
   k := Eltseq (R!theta);
   I := Integers ();
   k := [I!x: x in k];
   mat2 := &*[(Tau^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w2 := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   psi := beta^-1;
   R := sub < F | w^(q - 2)>;
   k := Eltseq (R!psi);
   k := [I!x: x in k];
   mat3 := &*[(V^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w3 := &*[(v^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   gamma := mat3[1][3];
   zeta := beta^-1 + gamma;
   // assert zeta in R;
   
   R := sub <F | w0>;
   k := Eltseq (R!zeta);
   k := [I!x: x in k];
   mat4 := &*[(Tau^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w4 := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   /* 
   LHS := V^U;
   RHS := mat1 * mat2 * U * Delta^kk * mat3 * mat4;
   assert LHS eq RHS;
   */
   
   lhs := v^u;
   rhs := w1 * w2 * u * delta^kk * w3 * w4;
   Append (~Rels, lhs = rhs);
   
   // relation 2 starts here 
   theta := theta + beta^-1 + beta^-q;
   
   w0 := w^(-(q + 1));
   
   R := sub <F | w0>;
   // assert theta in R;
   k := Eltseq (R!theta);
   k := [I!x: x in k];
   mat2a := &*[(Tau^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w2a := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   zeta := zeta + beta^-1 + beta^-q;
   
   R := sub <F | w0>;
   // assert zeta in R;
   k := Eltseq (R!zeta);
   k := [I!x: x in k];
   mat4a := &*[(Tau^(Delta^(i-1)))^k[i]: i in [1..#k]];
   w4a := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
   
   /* 
   LHS := (V * Tau)^U;
   RHS := mat3 * mat4a * U * Delta^(kk * q) * mat1 * mat2a;
   assert LHS eq RHS;
   */
   
   lhs := (v * tau)^u;
   rhs := w3 * w4a * u * delta^(kk * q) * w1 * w2a;
   Append (~Rels, lhs = rhs);

   Append (~Rels, tau^u = u^tau); 
   
   return Rels;
end function;

SetupMatrices := function (q, m)
   E := GF (q^2);
   MA := MatrixAlgebra (E, 3);

   x := m[1][3]; y := m[1][2];

   g := Identity (MA);
   g[1][2] := y; g[1][3] := x; g[2][3] := y^q;
   
   g1 := Identity (MA);
   g1[1][2] := x^-1 * y; g1[1][3] := x^-1; g1[2][3] := y^q * x^-q;

   g2 := Identity (MA);
   g2[1][1] := x; g2[2][2] := x^(q-1); g2[3][3] := x^-q;

   g3 := Identity (MA);
   g3[1][2] := x^-q * y; g3[1][3] := x^-1; g3[2][3] := y^q * x^-1;

   return [GL(3, q^2) | g, g1, g2, g3];
end function;

FindPoly := function (q, theta)
   d := 2;
   repeat
      A := AllIrreduciblePolynomials (GF(2), d);
      for j in [1..q^2 - 1] do
         if Gcd (j, q^2 - 1) eq 1 then
            flag := exists(f){f : f in A |
                 (1 + Evaluate (f, theta^j))^((q^2 - 1) div 3) eq 1};
            if flag then return f, j; end if;
         end if;
      end for;
      d +:= 1;
   until 1 eq 0;
end function;

EvenSU3Presentation := function (q)
   assert IsEven (q);

   W := SLPGroup (4);
   v := W.1;
   tau := W.2;
   delta := W.3;
   u := W.4;

   I := Integers ();
   E := GF (q^2);
   F := GF (q);
   f := Degree (F);
   w := PrimitiveElement (E);
   w0 := w^(q + 1);
   theta := w^(q - 2);

   Gens := SU3Generators (q);
   V := Gens[1]; Tau := Gens[2]; Delta := Gens[3]; U := Gens[4];

   Rels := [];
   if IsEven (f) then 
      k1 := Log (theta, theta + 1);
      lhs := v^k1 * (v * v^delta)^-1;
      rhs := EvenSLPForElement (V^k1 * (V * V^Delta)^-1, q, W);

      Append (~Rels, lhs = rhs);

      lhs := (v^delta, v);
      rhs := EvenSLPForElement ((V^Delta, V), q, W);
      Append (~Rels, lhs = rhs);

      R2 := EvenR2Relations (q, W);
      Rels cat:= R2;
   else 
      if exists(j){j : j in [1..q^2 - 1] | Gcd (j, q^2 - 1) eq 1
               and (1 + theta^j)^((q^2 - 1) div 3) eq 1} then 
         k1 := Log (theta^j, theta^j + 1);
         ell := 1;
         lhs := v^k1 * (v * v^(delta^j))^-1;
         rhs := EvenSLPForElement (V^k1 * (V * (V^Delta^j))^-1, q, W);
         Append (~Rels, lhs = rhs);
      else 
         f, j := FindPoly (q, theta);
         b := Coefficients (f);
         b := [I!x: x in b];

         phi := Evaluate (f, theta^j);
         assert phi^((q^2 - 1) div 3) eq 1;

         k1 := Log (theta, phi);
         ell := Degree (f);
         lhs := v^k1 * (&*[v^(delta^(b[i] * (i-1))): i in [1..#b]])^-1;

         rhs := EvenSLPForElement
         (V^k1 * (&*[V^(Delta^(b[i] * (i-1))): i in [1..#b]])^-1, q, W);

         Append (~Rels, lhs = rhs);
      end if;

      for i in [1..ell] do 
         lhs := (v^(delta^(i*j)), v);
         rhs := EvenSLPForElement ((V^(Delta^(i*j)), V), q, W);
         Append (~Rels, lhs = rhs);
      end for;

      R2 := EvenR2Relations (q, W);
   end if;
   Rels cat:= R2;

   Append (~Rels, v^2 = tau);

   m := MinimalPolynomial (theta);
   b := Coefficients (m);
   b := [I!x: x in b];
   lhs := &*[(v^(delta^(i-1)))^b[i]: i in [1..#b]];
   matrix := &*[(V^(Delta^(i-1)))^b[i]: i in [1..#b]];
   rhs := EvenSLPForElement (matrix, q, W);

   Append (~Rels, lhs = rhs);
      
   k2 := Log (w0, w0^-1 + 1);
   k2 := -k2;

   Append (~Rels, delta^(q^2 - 1));
   Append (~Rels, tau^(delta^(k2)) * (tau^-1)^delta * tau^-1 = 1);

   m2 := MinimalPolynomial (w0^-1);
   b := Coefficients (m2);
   b := [I!x: x in b];
   Append (~Rels, &*[(tau^(delta^(i-1)))^b[i]: i in [1..#b]] = 1);

   Append (~Rels, tau^2 = 1);
   Append (~Rels, (tau^delta, tau) = 1);
   
   Append (~Rels, u^2 = 1);
   Append (~Rels, delta^u = delta^-q);
   Append (~Rels, tau^u = u^tau);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   return Rels;
end function;

SolveCubeEquation := function (q)
   E := GF (q^2);
   w := PrimitiveElement (E);
   p := Characteristic (E);
   F := GF (p);
   theta := w^(q - 2);
   if q mod 3 eq 1 then
      flag := exists(a){a: a in F | a ne 0 and IsPower (a + a * theta^1, 3)};
      if flag then triple := <a,a,1>; end if;
   else  
      flag := exists(triple){<a, b,j> : a in F, b in F, j in [1..q^2 - 2] |
         a ne 0 and b ne 0 and Gcd (j, q^2 - 1) eq 1 and 
                  IsPower (a + b * theta^j, 3)};
   end if;
   if flag then return flag, triple; else return flag, _;  end if;
end function;

BorelPresentation := function (q)
   assert IsOdd (q);
  
   F := GF (q^2);
   p := Characteristic (F);
   
   w := PrimitiveElement (F);
   theta := w^(q - 2);

   W := SLPGroup (3);
   v := W.1;
   tau := W.2;
   delta := W.3;

   I := Integers ();

   Rels := [];
   
   w0 := w^(q + 1);
   R := sub <F | w0^-1>;

   value := -(w^((q - 5) div 2) - w^((-5*q + 1) div 2));

   Gens := BorelGenerators (q);
   V := Gens[1]; Delta := Gens[3];

   if IsPrime (q) eq false then 
      k1 := Log (theta, theta + 1);
      if k1 ne -1 then 
         val := value / 2;
         k := Eltseq (R!val);
         k := [I!x: x in k];
         product := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
         Append (~Rels, v^(delta^k1) = v * v^delta * product);
      else 
         flag, triple := SolveCubeEquation (q);
         assert flag;
         a := I!triple[1]; b := I!triple[2]; j := I!triple[3];
         k1 := Log (theta, b * theta^(j) + a);
         assert k1 ne -1;

         lhs := v^(delta^k1);

         /* explicit matrix */
         matrix := V^(Delta^k1) * (V^a * (V^b)^(Delta^j))^-1;
         val := matrix[1][3];
         s := val / (w^((q+1) div 2));

         c := Eltseq (R!s);
         c := [I!x: x in c];
         rhs := v^a * (v^b)^(delta^j) * (&*[(tau^(delta^(i-1)))^c[i]: i in [1..#c]]);
         Append (~Rels, lhs = rhs);
      end if;
   end if;

   Append (~Rels, v^p = 1);
   val := value;
   k := Eltseq (R!val);
   k := [I!x: x in k];
   product := &*[(tau^(delta^(i-1)))^k[i]: i in [1..#k]];
   Append (~Rels, (v^delta, v) = product);
   
   m := MinimalPolynomial (theta);
   b := Coefficients (m);
   b := [I!x: x in b];

   lhs := &*[(v^(delta^(i-1)))^b[i]: i in [1..#b]];

   /* explicit matrix */
   matrix := &*[(V^(Delta^(i-1)))^b[i]: i in [1..#b]];
   val := matrix[1][3];
   s := val / (w^((q+ 1) div 2));

   c := Eltseq (R!s);
   c := [I!x: x in c];

   rhs := &*[(tau^(delta^(i-1)))^c[i]: i in [1..#c]];
   Append (~Rels, lhs = rhs);

   if q gt 3 then 
      k2 := Log (w0, w0^-1 + 1);
      k2 := -k2;

      m2 := MinimalPolynomial (w0^-1);
      b := Coefficients (m2);
      b := [I!x: x in b];
      Append (~Rels, &*[(tau^(delta^(i-1)))^b[i]: i in [1..#b]] = 1);

      Append (~Rels, tau^(delta^(k2)) * (tau^-1)^delta * tau^-1 = 1);
   end if;

   Append (~Rels, delta^(q^2 - 1));
   Append (~Rels, tau^(p) = 1);
   Append (~Rels, (tau^delta, tau) = 1);
   Rels := [LHS (r) * RHS (r)^-1: r in Rels];

   return W, Rels;
end function;

IdentifyParameters := function (A)
   if Type (A) eq AlgMatElt or Type (A) eq GrpMatElt then A := A[1]; end if;
   F := BaseRing (Parent (A));
   q := Isqrt (#F);
   w := PrimitiveElement (F);
   alpha := A[2];
   if IsEven (q) then
      phi := Trace(w, GF(q))^(-1) * w;
   else
      phi := -1/2;
   end if;
   beta := A[3] - phi * (alpha^(1 + q));
   return [alpha, beta];
end function;

TupleToMatrix := function (q, v)
   return VMatrix (q, v[1], v[2]);
end function;

MatrixToTuple := function (A)
   if Type (A) eq AlgMatElt or Type (A) eq GrpMatElt then A := A[1]; end if;
   return IdentifyParameters (A);
end function;

ComputeRight := function (q, U)
   V := Parent (U[1]);
   r := V!Reverse (Eltseq (U[1]));
   s := Normalise (r);
   s[2] := -s[2];
   t := MatrixToTuple (s); 
   m := TupleToMatrix (q, t);
   assert MatrixToTuple (m) eq t;
   return  m, t;
end function;

ProcessRelation := function (G, v)
   q := Isqrt (#BaseRing (G));
   t := UMatrix (q);
   U := TupleToMatrix (q, v);
   right, rv := ComputeRight (q, U);
   rest := t^-1 * U * t * right^-1 * t^-1;
   d := DiagonalMatrix (BaseRing (G), [rest[i][i] : i in [1..Nrows (rest)]]); 
   left := rest * d^-1;
   // assert IsUpperTriangular (left);
   lv := MatrixToTuple (left);
   // assert t^-1 * U * t eq left * d * t * right;
   return lv, rv, left, d, t, right;
end function;

/* construct v-matrix whose 1, 2 entry is w^power, as word
   in delta = Delta (w) and v = VMatrix(1, 0), 
   where w is primitive element for GF(q^2) */

ConstructVMatrix := function (q, delta, v, power)
   z, n, m := ExtendedGreatestCommonDivisor (q - 2, q^2 - 1);
   F := GF (q^2);
   w := PrimitiveElement (F);
   nu := w^z;
   E := sub <F | nu>;
   A := Eltseq (E!power); 
   Z := Integers ();
   A := [Z!a: a in A];
   return &*[(v^(delta^(n * i)))^A[i + 1]: i in [0..#A - 1]];
end function;

/* construct tau-matrix whose 1, 3 entry is power, as word
   in tau = TauMatrix (w^((q+ 1) div 2)) and delta = Delta (w),  
   where w is primitive element for GF(q^2) */

ConstructTauMatrix := function (q, delta, tau, power)
   F := GF (q^2);
   Z := Integers ();
   w := PrimitiveElement (F);
   w0 := w^(q + 1);
   E := sub <F | w0>;
   gamma := power / w^((q + 1) div 2);
   assert gamma in E;
   A := Eltseq (E!gamma); 
   A := [Z!a: a in A];
   return &*[(tau^(delta^(-i)))^A[i + 1]: i in [0..#A - 1]];
end function;

SLPForElement := function (F, delta, v, tau, lv, l, wdelta, wv, wtau) 
   q := Isqrt (#F);
   w := PrimitiveElement (F);

   a := lv[1];
   if a ne 0 then 
      A := ConstructVMatrix (q, delta, v, a);
      wA := ConstructVMatrix (q, wdelta, wv, a);
   else
      A := v^0;
      wA := wv^0;
   end if;

   m := A * l^-1;
   b := m[1][3];
   B := ConstructTauMatrix (q, delta, tau, m[1][3]);
   wB := ConstructTauMatrix (q, wdelta, wtau, m[1][3]);

   // assert l eq A * B^-1;
   return wA, wB^-1, A, B^-1;
end function;

R2Relations := function (q)
   F := GF (q^2);
   w := PrimitiveElement (F);
   V := VectorSpace (F, 2);

   G := SU (3, q);
   t := UMatrix (q);
   v := VMatrix (q, 1, 0);
   tau := VMatrix (q, 0, w^((q+1) div 2));
   delta := DeltaMatrix (q, w);

   W := SLPGroup (4);
   wv := W.1; wtau := W.2; wdelta := W.3; wt := W.4;

   if q mod 3 eq 2 then 
      mats := [Generic (G) | VMatrix (q, w^i, 0): i in [0..2]]
          cat [Generic (G) | VMatrix (q, w^i, w^((q + 1) div 2)): 
               i in [0..2]] cat [tau];
      U := {@ V| MatrixToTuple (m): m in mats @};
   else 
      U := {@ V| [1,0], [0, w^((q + 1) div 2)], MatrixToTuple (v * tau) @};
   end if;

   Z := Integers ();

   R := [];
   for u in U do 
      lv, rv, left, d, t, right := ProcessRelation (G, u);
      pow := Log (d[1][1]);
      m := TupleToMatrix (q, u);
      a, b, a1, b1 := SLPForElement (F, delta, v, tau, u, m, wdelta, wv, wtau);
      x, y, x1, y1 := SLPForElement (F, delta, v, tau, lv, left, wdelta, wv, wtau);
      z, w, z1, w1 := SLPForElement (F, delta, v, tau, rv, right, wdelta, wv, wtau);
      // lhs := t^-1 * a1 * b1 * t;
      // rhs := (x1 * y1) * delta^pow * t * z1 * w1;
      wlhs := wt^-1 * a * b * wt;
      wrhs := (x * y) * wdelta^pow * wt * z * w;
      // assert lhs eq rhs;
      Append (~R, wlhs = wrhs);
   end for;
   return W, R;
end function;

/* presentation for SU(3, 2) on its standard generators */

SU32Presentation := function ( : Projective := false)
   F := FreeGroup (7);
   Q := quo < F |
    F.1^2 = Id(F),
    F.2 = Id(F),
    F.3^2 = Id(F),
    F.4^-1 * F.3 * F.4^-1 = Id(F),
    F.6^-1 * F.3 * F.6^-1 = Id(F),
    F.4^-1 * F.6^-1 * F.4 * F.6^-1 = Id(F),
    F.5 = Id (F),
    (F.3 * F.1)^3 = Id(F),
    F.1 * F.4 * F.1 * F.4^-1 * F.1 * F.6^-1 * F.1 * F.6 = Id(F),
    F.1 * F.6^-1 * F.1 * F.4^-1 * F.1 * F.4 * F.6^-1 * F.7 = Id(F)>;
   W := SLPGroup (7);
   R := Relations (Q);
   Rels := [LHS (r) * RHS (r)^-1: r in R];
   phi := hom<Q -> W | [W.i: i in [1..7]]>;
   Rels := [phi (r): r in Rels];
   if Projective then Append (~Rels, W.7^2); end if;
   return W, Rels;
end function;

ExceptionalCases := function (q)
   X := SU3Generators (q);
   G := sub<GL(3, q^2) | X>;
   F, phi := FPGroup (G);
   Q := SLPGroup (4);
   R := Relations (F);
   Rels := [LHS (r) * RHS (r)^-1: r in R];
   phi := hom<F -> Q | [Q.i: i in [1..4]]>;
   Rels := [phi (r): r in Rels];
   return Q, Rels;
end function;

SU3Presentation := function (q)
   if q eq 2 then Q, R := ExceptionalCases (q); return Q, R; end if;

   if IsEven (q) then 
      R := EvenSU3Presentation (q); return Universe (R), R; 
   end if;

   W := SLPGroup (4);
   v := W.1;
   tau := W.2;
   delta := W.3;
   u := W.4;

   /* relations of type R1 */
   Q, R1 := BorelPresentation (q);
   phi := hom<Q -> W | [W.i: i in [1..3]]>;
   Rels := [phi (r) = 1: r in R1];
   
   /* relations of type R2 */
   Q, R2 := R2Relations (q);
   phi := hom<Q -> W | [W.i: i in [1..4]]>;
   Rels cat:= [phi (r): r in R2];
 
   Append (~Rels, u^2 = 1);
   Append (~Rels, delta^u = delta^-q);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   
   return W, Rels;
end function;

/* 
load "su-3.m";

import "su-3.m": SU3Generators;
import "su-3.m": SU3Presentation;
d := 3;
for q in [2..1000] do
if IsPrimePower (q) then
d, q;
G, R := SU3Presentation (q);
X := SU3Generators (q);
S := Evaluate (R, X); assert #Set (S) eq 1;
end if;
end for;

*/
