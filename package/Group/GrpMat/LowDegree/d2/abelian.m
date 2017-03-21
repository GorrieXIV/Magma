freeze;

/* Singer cycle and its normaliser in GL(d, q) */

SingerCycle := function (d, q)
   if not IsPrimePower (q) then
      error "Input field size must be prime power";
   end if;

   F := GF (q);
   f := PrimitivePolynomial (F, d);
   MA := MatrixAlgebra (GF (q), d);
   S := Zero (MA);
   for i in [1..d - 1] do
      S[i][i+1] := 1;
   end for;
   R := Coefficients (f);
   V := VectorSpace (GF (q), d);
   R := V![-R[i] : i in [1..#R - 1]];
   S[d] := R;
   // assert Order (S) eq q^d - 1;

   /* extra generator for normaliser of S */
   a := Zero (MA);
   b := Identity (MA);
   term := S^q;
   for i in [1..d] do
      a[i] := b[1];
      b *:= term;
   end for;
   // assert Order (a) eq d;

   return S, a;

end function;

/* irreducible abelian subgroups of GL(d, q) for arbitrary d, q */

AbelianList := function (d, q)

   if not IsPrimePower (q) then
      error "Input field size must be prime power";
   end if;

   F := GF (q); 
   X := SingerCycle (d, q);
   qm1 := q - 1; 
   other := [q^m - 1: m in [1..d - 1]];
   v := q^d - 1; 
   D := Divisors (v);
   D := [m : m in D | forall {x : x in other | x mod m ne 0}];
   return [sub <GL(d, F) | X^(v div m)>: m in D]; 
end function;

/* absolutely irreducible primitive subgroups of the normaliser 
   of a prime degree d Singer cycle S for all prime-powers q; 
   description follows Short LNM p. 61 */

SingerCycleList := function (d, q)

   if not IsPrimePower (q) then
      error "Input field size must be prime power";
   end if;

   if not IsPrime (d) then error "Degree must be prime"; end if;

   F := GF (q); 

   /* generator for Singer cycle and extra generator for its normaliser */
   S, a := SingerCycle (d, q);

   /* write q - 1 as d^alpha * ell where gcd (d, ell) = 1 */
   qm1 := q - 1;
   alpha := Valuation (qm1, d);
   ell := qm1 div d^alpha;
   
   /* subgroups of S of order not dividing d * qm1 */
   o := Order (S);
   DS := Divisors (o);
   value := d * qm1;
   DS := {@ x : x in DS | value mod x ne 0 @};
   C := {@ S^(o div x) : x in DS @};
   L := [sub <GL(d, F) | c, a>: c in C];
   
   /* order of Sylow d-subgroup of S */
   pow := Valuation (o, d);
   ord := d^pow;
   
   D := Divisors (o);  
   D := {@ x : x in D | x mod ord ne 0 @};
   D := {@ x : x in D | qm1 mod x ne 0 @};
   D := {@ x : x in D | x mod d eq 0 @};

   LP := []; M := []; 
   for i in [1..#D] do 
      index := Position (DS, D[i]);
      if index eq 0 then m := S^(o div D[i]); else m := C[index]; end if;
      M[i] := m;
      _, gamma := ProjectiveOrder (m);
      LP[i] := Valuation (Order (gamma), d); 
   end for;
   
   one := S^ell; tmp := one;
   for r in [1..d - 1] do 
      for j in [1..#D] do
         i := LP[j];
         X := sub <GL (d, F) | a * tmp^(d^(alpha - i)), M[j]>;
         Append (~L, X);
      end for;
      tmp *:= one;
   end for;
  
   return L;
end function;
