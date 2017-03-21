freeze;

import "../gl-list.m": BackTrack;

/* imprimitive monomial non-abelian subgroups of GL(2, q) 
   for arbitrary q */

/* generate odd order group H2' for given prime q */
	
GenerateH2dash := function (q)

   d := 2;

   F := GF (q);
   w := PrimitiveElement (F);
   qm1 := q - 1; 
   factors := Factorisation (q - 1);
   distinct := [f[1]: f in factors];

   P := PrimeBasis (q - 1);
   Exclude (~P, 2);

   Z := []; W := [];
   for i in [1..#P] do
      r := P[i];
      tr := factors [Position (distinct, r)][2];
      alpha := w^(qm1 div r^tr);
      // assert Order (alpha) eq r^tr;
      Z[i] := [DiagonalMatrix ([alpha^(r^i), alpha^(r^i)]): i in [0..tr]];
      W[i] := [DiagonalMatrix ([alpha^(r^i), alpha^(-r^i)]): i in [0..tr]];
   end for;

   M := [];
   for k in [1..#Z] do
      M[k] := [];
      for i in [1..#Z[k]] do 
         for j in [1..#W[k]] do 
            Append (~M[k], sub <GL (d, F) | Z[k][i], W[k][j]>);
         end for;
      end for;
   end for;

   X := BackTrack ([#M[i] : i in [1..#M]]);
   R := [sub <GL(d, F) | [M[i][x[i]]: i in [1..#x]]>: x in X];
   return R, M;

end function;

H21 := function (q: Scalar := false)

   if q mod 4 ne 1 then return []; end if;

   bound := Scalar select 1 else 0;

   d := 2;

   F := GF (q);
   w := PrimitiveElement (F);
   qm1 := q - 1; 
   factors := Factorisation (q - 1);
   distinct := [f[1]: f in factors];

   r := 2;
   t := factors [Position (distinct, r)][2];
   beta := w^(qm1 div r^t);

   /* perm matrix */
   a1 := GL(2, q) ! [0,1,1,0];

   Z := [DiagonalMatrix ([beta^(r^(t - i - 1)), beta^(r^(t - i - 1))]): 
         i in [0..t - 1]];
   W := [DiagonalMatrix ([beta^(r^(t - i - 1)), beta^(-r^(t - i - 1))]): 
                i in [0..t - 1]];

   L := Scalar select [] else [sub < GL (2, F) | a1 >];

   L cat:= &cat[[sub <GL (2, F) | a1, Z[i + 1], W[j + 1]>: 
                 j in [bound..t - 1]]: i in [0..t - 1]];

   L cat:= &cat(&cat[[[sub < GL(d, F) | a1 * Z[i + 2], W[j + 1]>]: 
                      j in [bound..t - 1]]: i in [0..t - 2]]);
 
   x := a1 * DiagonalMatrix ([beta, 1]);
   L cat:= [sub < GL(2, F) | x, W[j + 1] > : j in [bound..t - 1]]; 

   L cat:= &cat(&cat[[[sub < GL(d, F) | a1, Z[i + 2] * W[j + 2], W[j + 1]>]: 
           j in [bound..t - 2]]: i in [0..t - 2]]);

   L cat:= [sub <GL(2, F) | a1, DiagonalMatrix ([beta, 1]), W[t- 1]>];

   return L;
end function;

H23 := function (q: Scalar := false)

   if q mod 4 ne 3 then return []; end if;

   F := GF (q);

   /* perm matrix */
   a1 := GL(2, F) ! [0,1,1,0];
   x  := GL(2, F) ! [1,0,0,-1];
   y  := GL(2, F) ! [-1,0,0,1];

   L := [sub < GL(2, F) | a1, x, y>];
   if not Scalar then 
      L cat:= [sub < GL(2, F) | a1 * x>, sub < GL(2, F) | a1, x * y>, 
               sub < GL(2, F) | a1>]; 
   end if;

   return L;

end function;

/* generate 2-group */

GenerateH2 := function (q : Scalar := false)
   if IsEven (q) then 
      return [sub <GL(2, q) | [0,1,1,0]>];
   elif q mod 4 eq 1 then 
      return H21 (q : Scalar := Scalar); 
   elif q mod 4 eq 3 then 
      return H23 (q: Scalar := Scalar); 
   end if;

end function;

IsScalarGroup := function (G)

   return forall {x : x in Generators (G) | IsScalar (x)};

end function;

/* imprimitive monomial subgroups of GL(2, q) for all q */

Degree2MonomialList := function (q)
   assert IsPrimePower (q);
   L := [];
   F := GF (q);
   X := GenerateH2dash (q);
   if IsEven (q) then
      X := [x : x in X | not IsScalarGroup (x)];
   end if;
   for i in [1..#X] do
      Y := GenerateH2 (q: Scalar := IsScalarGroup (X[i])); 
      S := [sub <GL(2, F) | X[i], y> : y in Y]; 
      Append (~L, S);
   end for;
   return &cat(L);
end function;
