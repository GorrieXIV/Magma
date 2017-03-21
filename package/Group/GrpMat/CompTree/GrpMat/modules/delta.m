/* code to decompose V \otimes V^\delta representation 
   of H where SL(d, q) \leq H \leq GL(d, q) 
   Kay Magaard, Eamonn O'Brien, and Akos Seress */

/* choose suitable basis for Singer cycle g;
    e_1 \otimes e_1, ..., e_1 \otimes e_d,
    e_2 \otimes e_1, ..., e_2 \otimes e_d,

     e_d \otimes e_1, ..., e_d \otimes e_d;

   return change-of-basis matrix CB, definitions 
   of basis elements defs, and g */

import "basics.m": RecognitionError;

import "../sl2q/decompose.m": ScaleMatrix;

ChooseBasis := function (G, e) 
   
   n := Degree (G);
   flag, d := IsSquare (n);

   F := BaseRing (G);

   q := #F;
   p := Characteristic (F);

   /* find Singer cycle in G */
   count := 1; 
   NmrTries := 100;
   LIMIT := 3;

   o := (q^d - 1) div (q - 1); 
   order := o div Gcd (o, p^e + 1);

   repeat 
      flag, g := RandomElementOfOrder (G, order: MaxTries := count * NmrTries);
      count +:= 1;
   until flag or count eq LIMIT;

   if flag eq false then 
      vprint SmallDegree: "Failed to find Singer cycle"; 
      return false, _;
   end if;

   /* regard Singer cycle as over sufficiently larger 
      field to ensure we can diagonalise */
   E := GF (q^d);
   MA := MatrixAlgebra (E, n); 
   s := MA ! Eltseq (g);
   
   /* diagonalise s */
   EV := Eigenvalues (s);
   if #EV ne n then
      vprint SmallDegree: "Element of order " cat IntegerToString (order) cat
       " does not have " cat IntegerToString (n) cat " distinct eigenvalues";
      return false, _;
   end if;

   EV := [e[1]: e in EV];

   Z := Integers ();
   
   O := [];

   /* construct Frobenius orbits on products 
      of eigenvectors l_i l_j */
   for i in [1..#EV] do
      v := EV[i]; 
      if v in &join (O) then continue; end if;
      orbit := {@ v^(q^j): j in [0..d - 1] @};
      Append (~O, orbit);
   end for;

   vprint SmallDegree: "Orbits are ", [#x: x in O];

   MA := MatrixAlgebra (GF(q^d), d);
   
   R := [];

   for f in O do 
      /* choose first orbit */
      v := f[1]; 

      C := [x: x in EV | v^(q + 1) / x in EV and x^(1 + p^e) eq v^(1 + q * p^e)];
      /* candidates for l_1 l_2 */
      C := [x : x in C | not x in [f[1], f[2]]];
      vprint SmallDegree: "Length of C is ", #C;

      if #C eq 0 then continue; end if;

      good := true;

      first := {@ v^(q^j): j in [0..d - 1] @};

      L := Zero (MA);
  
      /* diagonal entries */
      for i in [1..d] do 
         L[i][i] := first[i]; 
      end for;
   
      Original := L;
      for c in C do 
         L := Original;
         L[1][2] := c;
         L[2][1] := L[1][1] * L[2][2] / L[1][2];
         for i in [2..d - 1] do
            L[i][i + 1] := L[i - 1][i]^q;
         end for;
         L[d][1] := L[d - 1][d]^q;
         for i in [2..d - 1] do
            L[i + 1][1] := (L[1][1] * L[i][i] * L[i + 1][i + 1]) / 
                           (L[i][i + 1] * L[1][i]);
            if not (L[i+1][1] eq L[1][1] * 
               (L[2][1] / L[1][1])^((q^i - 1) div (q - 1))) then 
               good := false; continue c; 
            end if;
            L[1][i + 1] := L[1][1] * L[i + 1][i + 1] / L[i+1][1];
         end for;
         for i in [3..d - 1] do
            for j in [1..d - i] do
               L[j + 1][j + i] := L[j][j + i - 1]^q;
            end for;
         end for;
         for i in [2..d - 1] do
            for j in [2..d - i + 1] do
               L[i - 1 + j][j] := L[i - 2 + j][j - 1]^q;
            end for;
         end for;
      end for;
      if good then break f; end if;
   end for;

   if not assigned L then return false, _; end if;

   L := Eltseq (L);
   ES := [Eigenspace (s, e).1: e in L];
   CB := GL (n, E) ! &cat ([Eltseq (x): x in ES]);
   // assert IsDiagonal (CB * s * CB^-1);
   return true, CB, g;
end function;

FindIndex := function (i, j, d)
   return (i - 1) * d + j;
end function;

FindRatio := function (K, A, C, p, e, i, j, k, l)
   d := Nrows (A);
   a := FindIndex (i, j, d);
   b := FindIndex (k, l, d);
   c := FindIndex (j, j, d);
   e := FindIndex (j, l, d);
   f := FindIndex (i, k, d);
   g := FindIndex (k, k, d);
   return (C[j][j] * K[a][b] * K[g][g] * A[j][j])/ 
          (C[k][k] * K[c][e] * K[f][g] * A[k][k]);
end function;

/* G is tensor product; e is degree of Frobenius */
 
DetermineConstants := function (G, CB, e)
   F := BaseRing (G);
   n := Degree (G);
   d := Isqrt (n);
   q := #F;
   p := Characteristic (F);

   R := RandomProcess (G);
   P := Parent (CB);
   repeat 
      g := Random (R);
      K := CB * P ! g * CB^-1;
   until &*[K[i][i]: i in [1..d]] ne 0 and K[1][2] ne 0;

   index := FindIndex (1, 1, d);
   /* a_11^(p^e + 1) */
   k := K[index][index];

   E := GF (q^d);
   MA := MatrixAlgebra (E, d);

   A := Zero (MA);
   /* choose a root to give a_11 */

   A[1][1] := Root (E ! k, p^e + 1);
   
   for i in [1..d] do
      index := FindIndex (i, 1, d);
      ell := K[index][index];
      r := (ell / k);
      A[i][i] := A[1][1] * r;
   end for;

   w := PrimitiveElement (E);

   for k in [0..p^e] do 
      C := Zero (MA);
      C[1][1] := w^k;
      for i in [2..d] do
         C[i][i] := C[i - 1][i - 1]^q;
      end for;
   
      // record (p^e + 1)-th power of A[i][j] 
      i := 1; j := 2;
      a := FindIndex (1, 1, d);
      b := FindIndex (1, 2, d);
      c := FindIndex (2, 2, d);
      P12 := (K[b][c] * K[a][b] )/ (A[j][j]^(p^e) * A[i][i]) * C[j][j] / C[i][i];

      a := FindIndex (1, 2, d);
      b := FindIndex (2, 2, d);
      X := K[a][b]^(p^e + 1) * C[2][2]^(p^e + 1) / (P12 * A[2][2]^(p^e*(p^e + 1)));

      R := AllRoots (X, p^e + 1);

      for r in R do 
         C[1][2] := r;
    
         for ell in [3..d] do 
            C[1][ell] := C[1][2] * C[1][ell - 1]^q / (C[ell][ell] * 
                        FindRatio (K, A, C, p, e, 1, 2, ell, ell));
         end for;
         C[2][1] := C[1][d]^q;
    
         /* check */
         if C[1][1] ne C[1,2] * C[2,1] / 
            (C[1,1] * FindRatio (K, A, C, p, e, 1, 2, 1, 1)) then 
            continue; 
         end if;

         for j in [2..d - 1] do
            C[j][j + 1] := C[j - 1][j]^q;
         end for;
         C[d][1] := C[d - 1][d]^q;

         for ell in [3..d] do 
            for j in [2..d + 1 - ell] do
               C[j][j + ell - 1] := C[j - 1][j + ell-2]^q;
            end for;
            C[d + 2 - ell][1] := C[d + 1 - ell][d]^q;
            for j in [d + 3 - ell..d] do
               C[j][j -(d + 1 - ell)] := C[j - 1][j - (d + 1 - ell) - 1]^q;
            end for;
         end for;
         return true, C;
      end for;
   end for;

   return false, _;
end function;

/* decompose g in G; CB is change-of-basis;
   C is matrix of constants; e is degree of Frobenius */

Reconstruct := function (G, g, C, CB, e)

   F := BaseRing (G);
   n := Degree (G);
   d := Isqrt (n);
   p := Characteristic (F);

   P := Parent (CB);

   K := CB * P!g * CB^-1;

   index := FindIndex (1, 1, d);
   /* a_11^(p^e + 1) */
   k := K[index][index];

   E := BaseRing (P);
   MA := MatrixAlgebra (E, d);

   A := Zero (MA);
   /* choose a root to give a_11 */
   A[1][1] := Root (E ! k, p^e + 1);
   
   for i in [1..d] do
      index := FindIndex (i, 1, d);
      ell := K[index][index];
      if k eq 0 then return false; end if;
      r := (ell / k);
      A[i][i] := A[1][1] * r;
   end for;
   
   for i in [1..d] do 
      for j in [1..d] do 
         if i eq j then continue; end if;
         a := FindIndex (i, j, d);
         b := FindIndex (j, j, d);
         A[i][j] := (K[a][b]  * C[j][j]) / (C[i][j] * A[j][j]^(p^e));
      end for;
   end for;

   return A;
end function;

/* we cannot evaluate f(x) directly because some
   of its entries are zero; instead choose a random
   element y and evaluate f(x) from f(xy) = f(x) f(y)  */

UseHomomorphism := function (G, x, C, CB, e)
   P := Parent (CB);
   y := Random (G);
   y := P ! (CB * P ! y * CB^-1);
   rxy := Reconstruct (G, (P!x) * y, C, CB^0, e);
   if Type (rxy) eq BoolElt then return false; end if;
   ry := Reconstruct (G, y, C, CB^0, e);
   if Type (ry) eq BoolElt then return false; end if;
   return rxy * ry^-1;
end function;

intrinsic RecogniseDelta (G :: GrpMat: FrobeniusDegree := []) -> 
  BoolElt, GrpMat, RngIntElt  
{G is absolutely irreducible representation of H \tensor H^(p^e), 
 where SL(d, q) <= H <= GL(d, q) and d >= 4,
 and e is degree of Frobenius map; reconstruct H; 
 return true and H and e, otherwise false }
 
   n := Degree (G);
   flag, d := IsSquare (n);

   if flag eq false then 
      vprint SmallDegree: "Representation is not tensor product";
      return false, _, _;
   end if;

   if d le 3 then 
      error Error (rec<RecognitionError |
      Description := "Recognition for tensor product representation of SL", 
      Error := "Does not apply to small cases">); 
   end if;

   F := BaseRing (G);
   f := Degree (F);

   if FrobeniusDegree cmpeq [] then 
      for deg in [1..f - 1] do 
         found, CB := ChooseBasis (G, deg);
         if found then e := deg; break; end if;
      end for;
   else
      if not (FrobeniusDegree in [1..f - 1]) then return false, _, _; end if;
      found, CB := ChooseBasis (G, FrobeniusDegree);
      if found then e := FrobeniusDegree; end if;
   end if;
      
   if found eq false then 
      vprint SmallDegree: "Representation is probably not tensor product of SL"; 
      return false, _, _; 
   end if;
   
   found, C := DetermineConstants (G, CB, e);
   if found eq false then 
     vprint SmallDegree: "Representation is probably not tensor product of SL"; 
      return false, _, _; 
   end if;

   X := [Reconstruct (G, G.i, C, CB, e):  i in [1..Ngens (G)]];

   q := #F;
   H := sub <GL(d, q^d) | X >;
   flag, A := IsOverSmallerField (H: Scalars := true);

   if not flag then 
      error Error (rec<RecognitionError |
      Description := "Recognition for delta representation of SL", 
      Error := "Representation cannot be written over smaller field">);
   end if;

   // addition March 2011 to deal with non-trivial scalars 
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      A := sub<Generic (A) | [ScaleMatrix (A.i): i in [1..Ngens (A)]]>;
   end if;

   SCB := H`SmallerFieldChangeOfBasis;      

   G`Delta := <CB, e, C, SCB>;

   return true, A, e;
end intrinsic;

/* G is delta representation of H, where
   SL(d, q) <= H <= GL(d, q); find preimage of g in H */

intrinsic DeltaPreimage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt 
{G is absolutely irreducible representation of H \tensor H^(p^e), 
 where SL(d, q) <= H <= GL(d, q) and d >= 4; 
 SL(d, q) <= H <= GL(d, q); find preimage of g in H} 

   if not assigned G`Delta then
      error Error (rec<RecognitionError |
      Description := "Recognition for delta representation of SL", 
      Error := "Must first apply RecogniseDelta">);
   end if;

   R := G`Delta; 
   CB := R[1];  e := R[2]; C := R[3]; SCB := R[4];
   h := Reconstruct (G, g, C, CB, e); 
   K := BaseRing (h);
   d := Nrows (h);
   h := GL(d, K) ! (SCB^-1 * h * SCB);
   E := Eltseq (h);
   v := VectorSpace (K, d^2) ! E;
   depth := Depth (v);
   if depth eq 0 then error "Matrix is zero"; end if;
   alpha := v[depth];
   S := ScalarMatrix (d, alpha^-1);

   // addition March 2011 to deal with non-trivial scalars 
   im := GL(d, BaseRing (G)) ! (h * S);
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      im := GL(d, BaseRing (G)) ! ScaleMatrix (im);
   end if;

   return im, alpha;
end intrinsic;

DeltaTestHom := function (G)
   R := G`Delta;
   g1 := Random (G);
   h1 := DeltaPreimage (G, g1);
   g2 := Random (G);
   h2 := DeltaPreimage (G, g2);
   h := DeltaPreimage (G, g1 * g2);
   m := (h1 * h2)^-1 * h;
   return IsScalar (m); 
end function;
