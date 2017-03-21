/* code to decompose alternating representation of H
   where SL(d, q) <= H <= GL(d, q); 
   Kay Magaard, Eamonn O'Brien, and Akos Seress; 
   version October 2008 */

import "basics.m": RecognitionError;

import "../sl2q/decompose.m": ScaleMatrix;

forward MainReconstruct;

/* find position of <i, j> in defs */

CreateList := function (d)
   X := [];
   for i in [1..d - 1] do
      for j in [i + 1..d] do
         y := <i, j>;
         Append (~X, y);
      end for;
   end for;
   return X;
end function;

IndexPosition := function (defs, i, j)
   pair := i lt j select <i, j> else <j, i>;
   return Position (defs, pair);
end function;

/* is n = d (d - 1)/ 2? */
DetermineDegree := function (n)
   n := 2 * n;
   N := Divisors (n);
   flag := exists (d){d : d in N | (d - 1) in N and d * (d - 1) eq n};
   if flag then return true, d; else return false, _; end if;
end function;

/* extract from g rows & columns listed in index */

ExtractAction := function (g, index)
   E := [];
   F := BaseRing (Parent (g));
   if Type (index) eq SetEnum then
      index := Sort (SetToSequence (index));
   end if;
   for i in index do
      for j in index do
         Append (~E, g[i][j]);
      end for;
   end for;
   return MatrixAlgebra(F, #index) ! (E);
end function;

/* choose suitable basis for Singer cycle g;
   return change-of-basis matrix CB, and g */

ChooseBasis := function (G)
   n := Degree (G);
   flag, d := DetermineDegree (n);

   F := BaseRing (G);
   q := #F;

   /* find Singer cycle in G */
   count := 1; 
   NmrTries := 100;
   LIMIT := 3;

   if IsOdd (q) and IsEven (d) then
      order := (q^d - 1) div (2 * (q - 1));
   else
      order := (q^d - 1) div (q - 1);
   end if;

   repeat 
      flag, g := RandomElementOfOrder (G, order: MaxTries:= count * NmrTries);
      count +:= 1;
   until flag or count eq LIMIT;

   if flag eq false then
      vprint SmallDegree: "Failed to find Singer cycle";
      return false, _, _;
   end if;

   /* regard Singer cycle as over sufficiently larger 
      field to ensure we can diagonalise */
   E := GF (q^d);
   MA := MatrixAlgebra (E, n); 
   s := MA ! Eltseq (g);
   
   /* diagonalise s */
   EV := Eigenvalues (s);
   if #EV ne n then
      str := "Element of order " cat IntegerToString (order) cat
       " does not have " cat IntegerToString (n) cat " distinct eigenvalues";
      vprint SmallDegree: str;
      return false, _, _;
   end if;

   EV := [e[1]: e in EV];
   O := [];
   
   /* eigenvalues in natural repn are l_i where l_i^q = l_(i + 1); 
      we know products l_i l_j, want to identify them;
      l_i = w^{q^(i - 1)} 1 <= i <= n */

   /* construct Frobenius orbits on products of eigenvectors l_i l_j */
   for i in [1..#EV] do
      v := EV[i]; 
      if v in &join (O) then continue; end if;
      orbit := {@ v^(q^j): j in [0..d - 1] @};
      Append (~O, orbit);
   end for;

   long := [i : i in [1..#O] | #O[i] eq d];
   
   vprint SmallDegree: "Length of orbits ", [#o : o in O];

   /* long orbit */
   for m in long do 
      orbit := O[m];

      /* construct l_1 * l_2i for i <= n / 2 */
      l12 := orbit[1];
      l23 := orbit[2];
      l34 := orbit[3];
      assert l34 eq l12^(q^2);
      a := orbit[1]; assert a^(q^2) eq orbit[3];
      l14 := l12 * l34 / l23;

      if IsOdd (d) then 
         if d le 3 then 
            S := [l12];
         else 
            S := [l12, l14];
            /* we now generate l_{1, 2k} using 
               S_n S_n^(q^2) / S_{n - 1}^(q^2) */
            for k in [3..d div 2] do
               a := S[k - 1]; b := a^(q^2); c := S[k - 2]^(q^2);
               S[k] := a * b / c;
            end for;
         end if;
       
         /* l_1 * l_2k where 2k + 1 = d */
         a := S[#S]; 
         /* a^(q^2) = l_3 * l_1 */
         b := a^(q^2);
         /* now evaluate w^2 = (l_1 * l_3) / (l_1 l_2)^(q - 1) */
         w2 := b / S[1]^(q - 1);
         w := SquareRoot (w2);
         X := [];
         for i in [0..d - 1] do
            for j in [i + 1..d - 1] do
               x := w^((q^i) + (q^j));
               Append (~X, x);
            end for;
         end for;
         if Set (X) eq Set (EV) then 
            vprint SmallDegree: m, "is good orbit"; 
            index := [Position (EV, X[i]): i in [1..#X]]; break m; 
         end if;
      end if;

      if IsEven (d) then 
         /* a = l_1 l_2 * l_3 l_4  = (l_1 l_3)^(q + 1) */
         a := orbit[1] * orbit[3]; 
         if d eq 4 then short := 2; else short := d; end if;
         Other := [k : k in [1..#O] | #O[k] eq short and k ne m];
         if #Other eq 0 then return false, _, _; end if;
         for k in Other do 
            for x in O[k] do 
              if x^(q + 1) eq a then 
                 w2 := x / (orbit[1])^(q - 1);
                 w := SquareRoot (w2);
                 X := [];
                 for i in [0..d - 1] do
                    for j in [i + 1..d - 1] do
                       y := w^((q^i) + (q^j));
                       Append (~X, y);
                    end for;
                 end for;
                 if Set (X) eq Set (EV) then 
                    index := [Position (EV, X[i]): i in [1..#X]]; 
                    // m, k, "is good orbit"; 
                    break m; 
                 end if;
               end if;
            end for;
         end for;
      end if;
   end for;
      
   L := [EV[i]: i in index];
   ES := [Eigenspace (s, e).1: e in L];

   /* construct change-of-basis matrix */
   CB := GL (n, E) ! &cat ([Eltseq (x): x in ES]);
   // assert IsDiagonal (CB * s * CB^-1);
   return true, CB, g;
end function;

/* modify signs of odd entries of 3 x 3 matrix and transpose */

ModifySigns := function (X)
   P := Parent (X);
   d := Degree (P);
   F := BaseRing (P);
   MA := MatrixAlgebra (F, d);
   Y := MA ! X;
   Y[1][2] := -1 * Y[1][2];
   Y[2][1] := -1 * Y[2][1];
   Y[2][3] := -1 * Y[2][3];
   Y[3][2] := -1 * Y[3][2];
   return Transpose (Y);
end function;

/* extract and modify submatrices determined by index1 and index2 */

ConstructSubmatrix := function (G, P, CB, index1, index2)
   repeat 
      repeat 
         g := P ! Random (G);
         h := CB * g * CB^-1;
         K1 := ExtractAction (h, index1); 
         K1 := ModifySigns (K1);
         K2 := ExtractAction (h, index2); 
         K2 := ModifySigns (K2);
      until Determinant (K1) ne 0 and Determinant (K2) ne 0; 
      d1 := Determinant (K1); d2 := Determinant (K2); 
      sqr1 := SquareRoot (d1); sqr2 := SquareRoot (d2); 
      K1 := (sqr1) * K1^-1;
      K2 := (sqr2) * K2^-1;
      flag := K1[1][1] ne 0 and K2[2][1] ne 0;
      if flag and (K1[1][1] ne K2[1][1]) then K2 := -K2; end if;
   until flag;
   return K1, K2;
end function;

/* n-th root of x */

MyRoot := function (x, n)
   try
      return true, Root (x, n);
   catch e
      return false, _;
   end try;
end function;

/* determine constants for basis determined by CB */

DetermineConstants := function (G, CB)
   P := Parent (CB);
   F := BaseRing (G);
   q := #F;
   n := Degree (G);
   flag, d := DetermineDegree (n);
   
   MA := KMatrixSpace (BaseRing (P), 1, d);
   L := CreateList (d);
   K := Zero (MA);
   K[1][2] := 1;

   if IsOdd (d) then bound := (d - 3);
   elif d mod 4 eq 0 then bound := d div 2;
   elif d mod 4 eq 2 then bound := (d - 2) div 2; 
   end if;

   for m in [2..bound by 2] do 
      a := Position (L, <m, m + 1>);
      b := Position (L, <m + 1, m + 2>);
      A, B := ConstructSubmatrix (G, P, CB, [a, m, m - 1], [b, m + 1, m]);
      x := A[3][1]; y := B[2][1];
      K[1][m + 2] := K[1][m] * x / y;
   end for;

   E := BaseRing (P);
   w := PrimitiveElement (E);

   MA := MatrixAlgebra (E, d);
   C := Zero (MA);

   /* compute 1, 2 entry */
   if d mod 4 eq 2 then 
      value := K[1][(d + 2) div 2]^(1 - q^(d div 2)); 
      n := (q^d - 1) div (q + 1);
      flag, val := MyRoot (value, n);
      if not flag then return false, _; end if;
      C[1][2] := val;
   elif d mod 4 eq 0 then 
      value := K[1][d div 2] * K[1][d div 2 + 2]^(-q^((d - 2) div 2));
      n := (q^d - 1) div (q + 1);
      flag, val := MyRoot (value, n);
      if not flag then return false, _; end if;
      C[1][2] := val;
   else 
      // C[1][2] := PrimitiveElement (BaseRing (P));
      C[1][2] := +1;
   end if;

   /* update K array by multiplying each entry by C[1][2]^ */
   value := C[1][2];
   for i in [2..bound + 2 by 2] do
      K[1][i] *:= value^((q^(i - 1) + 1) div (q + 1));
   end for;

   /* K is now first row of C */
   for i in [1..d] do
      C[1][i] := K[1][i];
      C[i][1] := C[1][i];
   end for;
   for m in [2..(bound + 2) by 2] do
      for i in [2..d - m + 1] do
         C[i][m + i - 1] := C[i - 1][m + i - 2]^q;
         C[m + i - 1][i] := C[i][m + i - 1];
      end for;
      C[d - m + 2][1] := C[d - m + 1][d]^q;
      C[1][d - m + 2] := C[d - m + 2][1];
      for i in [d - m + 3..d] do
         C[i][i - (d - m + 1)] := C[i - 1][i - (d - m + 1) - 1]^q;
         C[i - (d - m + 1)][i] := C[i][i - (d - m + 1)]; 
      end for;
   end for;
  
   if IsOdd (d) then return true, C; end if;
   
   A, B := ConstructSubmatrix (G, P, CB, [d, 2, 1], [d + 1, 3, 1]);

   /* now fill in K[1, 3] */ 
   x := A[2][1]; y := B[2][1];
   v := C[2][3] * C[1][4] * x^-1 * y;

   flag, r := MyRoot ((E ! v), q + 1);
   if not flag then return false, _; end if;
   K[1][3] := r;

   if d mod 4 eq 2 then bound := d div 2;
   elif d mod 4 eq 0 then bound := (d - 2) div 2; end if;

   for m in [3..bound by 2] do 
      a := Position (L, <m, m + 1>);
      b := Position (L, <m + 1, m + 2>);
      A, B := ConstructSubmatrix (G, P, CB, [a, m, m - 1], [b, m + 1, m]);
      x := A[3][1]; y := B[2][1];
      K[1][m + 2] := K[1][m] * x * y^-1 * C[1][2]^(q^m - q^(m - 1));
   end for;

   /* K is now first row of C */
   for i in [3..d by 2] do
      C[1][i] := K[1][i];
      C[i][1] := C[1][i];
   end for;
   for m in [3..(bound + 2) by 2] do
      for i in [2..d - m + 1] do
         C[i][m + i - 1] := C[i - 1][m + i - 2]^q;
         C[m + i - 1][i] := C[i][m + i - 1];
      end for;
      C[d - m + 2][1] := C[d - m + 1][d]^q;
      C[1][d - m + 2] := C[d - m + 2][1];
      for i in [d - m + 3..d] do
         C[i][i - (d - m + 1)] := C[i - 1][i - (d - m + 1) - 1]^q;
         C[i - (d - m + 1)][i] := C[i][i - (d - m + 1)]; 
      end for;
   end for;

   return true, C;
end function;

/* C is matrix of constants; use it to write diagonal matrix 
   which acts as multipliers for wedges */

SmallToLarge := function (G, d, C)
   M := MatrixAlgebra (BaseRing (Parent (C)), Degree (G));
   if IsIdentity (C) then return Identity (M); end if;
   D := Zero (M);
   L := CreateList (d);
   for i in [1..#L] do 
      index := L[i];
      a := index[1]; b := index[2];
      D[i][i] := C[a][b];
   end for;
   return D^-1;
end function;

/* if we can't evaluate preimage of x directly, then evalute 
    preimages of x * y and y and so obtain value for x */

UseHomomorphism := function (G, CB, x)
   P := Parent (CB);
   y := Random (G);
   y := CB^1 * P ! y * CB^-1;
   rxy := MainReconstruct (G, CB, P ! x * P ! y);
   if Type (rxy) eq BoolElt then return false, _; end if;
   ry := MainReconstruct (G, CB, P ! y); 
   if Type (ry) eq BoolElt then return false, _; end if;
   return rxy * ry^-1, y;
end function;

/* extract and modify submatrix of g determined by index */

SingleSubmatrix := function (g, index)
   K := ExtractAction (g, index); 
   K := ModifySigns (K);
   d := Determinant (K); 
   if d eq 0 then return false, _; end if;
   R := AllRoots (d, 2);
   if #R eq 0 then return true, _; end if;
   sqr := SquareRoot (d); 
   K := (sqr) * K^-1;
   return K, d;
end function;

/* insert matrix B into matrix A in rows & colums determined by index */
procedure MyInsertBlock (~A, B, index)
   for i in [1..#index] do 
      for j in [1..#index] do 
         A[index[i]][index[j]] := B[i][j];
      end for;
   end for;
end procedure;

/* CB is change-of-basis matrix: find preimage of g  */

MainReconstruct := function (G, CB, g)

   F := BaseRing (G);
   q := #F;
   n := Degree (G);
   flag, d := DetermineDegree (n);

   E := ext <F | d>;
   A := SingleSubmatrix (g, [d, 2, 1]);
   if Type (A) eq BoolElt then 
      repeat 
         X := UseHomomorphism (G, CB, g); 
      until Type (X) cmpeq GrpMatElt;  
      return GL(d, E) ! X;
   end if;

   MA := MatrixAlgebra (E, d);
   h := Zero (MA);
   MyInsertBlock (~h, A, [1, 2, 3]);

   defs := CreateList (d);

   /* complete first two rows */
   M := RMatrixSpace (GF(q^d), 3, 2);
   A := M![-h[2][1], h[1][1], -h[2][2], h[1][2], -h[2][3], h[1][3]];
   B := Zero (RMatrixSpace (GF(q^d), 3, 1)); 
   x := Position (defs, <1, 2>);
   for k in [4..d] do 
      y := Position (defs, <1, k>);
      B[1][1] := g[x][y]; 
      y := Position (defs, <2, k>);
      B[2][1] := g[x][y]; 
      y := Position (defs, <3, k>);
      B[3][1] := g[x][y]; 
      flag, v := IsConsistent (Transpose (A), Transpose (B));
      if not flag then vprint SmallDegree: "Error 2"; return false; end if;
      h[1][k] := v[1][1];
      h[2][k] := v[1][2];
   end for;

   /* complete first two columns */
   M := RMatrixSpace (E, 3, 2);
   A := M![-h[1][2], h[1][1], -h[2][2], h[2][1], -h[3][2], h[3][1]];
   B := Zero (RMatrixSpace (E, 3, 1)); 
   y := Position (defs, <1, 2>);
   for k in [4..d] do 
      x := Position (defs, <1, k>);
      B[1][1] := g[x][y]; 
      x := Position (defs, <2, k>);
      B[2][1] := g[x][y]; 
      x := Position (defs, <3, k>);
      B[3][1] := g[x][y]; 
      flag, v := IsConsistent (Transpose (A), Transpose (B));
      if not flag then vprint SmallDegree: "Error 3"; return false; end if;
      h[k][1] := v[1][1];
      h[k][2] := v[1][2];
   end for;

   flag := exists(t){<i,j> : i in [1..2], j in [1..2] | h[i][j] ne 0};
   if not flag then vprint SmallDegree: "Error 4"; return false; end if;
   i := t[1]; j := t[2];

   for x in [3..d] do 
      a := Position (defs, <i, x>);
      for y in [3..d] do 
          b := Position (defs, <j, y>);
          h[x][y] := (g[a][b] + h[i][y] * h[x][j]) / h[i][j];
      end for;
   end for;

   return GL(d, E) ! h;
end function;

/* G is alternating square repn of H where SL(d, q) <= H <= GL(d, q); 
   find preimage of g */

Reconstruct := function (G, CB, C, g)
   F := BaseRing (G);
   q := #F;
   n := Degree (G);
   flag, d := DetermineDegree (n);
   D := SmallToLarge (G, d, C);
   CB := D * CB;
   E := ext <F | d>;
   g := CB * GL(n, E) ! g * CB^-1;
   return MainReconstruct (G, CB, g);
end function;

AltTestHom := function (G)
   R := G`AltSquare;
   CB := R[1]; C := R[2]; SCB := R[3];
   g1 := Random (G);
   h1 := Reconstruct (G, CB, C, g1);
   g2 := Random (G);
   h2 := Reconstruct (G, CB, C, g2);
   h := Reconstruct (G, CB, C, g1 * g2);
   m := (h1 * h2)^-1 * h;
   return IsScalar (m) and Order (m) in {1, 2}, g1, g2;
end function;

intrinsic RecogniseAlternatingSquare (G :: GrpMat: Verify := false) -> BoolElt, GrpMat
{G is alternating square representation of H, where
 SL(d, q) <= H <= GL(d, q) and d >= 3; reconstruct H; 
 return true and H, otherwise false;
 if Verify then check that G is as claimed}
 
   n := Degree (G);
   flag, d := DetermineDegree (n);

   if flag eq false then
      vprint SmallDegree: "Representation is not alternating square";
      return false, _;
   end if;

   if d le 2 then      
      error Error (rec<RecognitionError |
      Description := "Recognition for alternating square of SL",
      Error := "Does not apply to small cases">);
   end if;

   F := BaseRing (G);

   if Verify then 
      p := Characteristic (F);
      flag, type := LieType (G, p);
      if not flag or type[1] ne "A" then 
         vprint SmallDegree: "Representation is not alternating square";
         return false, _; 
      end if;
   end if;

   repeat 
      flag, CB := ChooseBasis (G);
      if flag then 
         flag, C := DetermineConstants (G, CB);
      else
         vprint SmallDegree: 
            "Probably not alternating square representation of SL";
         return false, _;
      end if;
   until flag eq true;

   gens := [Reconstruct (G, CB, C, G.i): i in [1..Ngens (G)]];;
   F := BaseRing (Parent (Rep (gens))); 
   H := sub <GL (Nrows (Rep (gens)), F) | gens >;
   flag, A := IsOverSmallerField (H);

   if not flag then
      error Error (rec<RecognitionError |
      Description := "Recognition for alt square representation of SL",
      Error := "Representation cannot be written over smaller field">);
   end if;

   // addition March 2011 to deal with non-trivial scalars 
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      A := sub<Generic (A) | [ScaleMatrix (A.i): i in [1..Ngens (A)]]>;
   end if;

   SCB := H`SmallerFieldChangeOfBasis;
   G`AltSquare := <CB, C, SCB>;
   return true, A;
end intrinsic;

intrinsic AlternatingSquarePreimage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt
{G is alternating square representation of H, where
 SL(d, q) <= H <= GL(d, q); find preimage of g in H} 

   if not assigned G`AltSquare then
      error Error (rec<RecognitionError |
      Description := "Recognition for alternating square of SL",
      Error := "Must first apply RecogniseAlternatingSquare">);
   end if;

   R := G`AltSquare;
   CB := R[1]; C := R[2]; SCB := R[3];
   h := Reconstruct (G, CB, C, g);

   im := GL(Nrows (h), BaseRing (G)) ! (SCB^-1 * h * SCB);

   // addition March 2011 to deal with non-trivial scalars 
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      im := GL(Nrows (h), BaseRing (G)) ! ScaleMatrix (im);
   end if;

   return im;
end intrinsic;
