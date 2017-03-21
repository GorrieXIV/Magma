/* code to decompose symmetric power representation of GL(d, q); 
   Kay Magaard, Eamonn O'Brien, and Akos Seress; October 2008 */

import "basics.m": RecognitionError;
import "../sl2q/decompose.m": ScaleMatrix;

forward Reconstruct;

/* find position of <i, j> in defs */
CreateList := function (d)
   X := [<i, i>: i in [1..d]];
   for i in [1..d - 1] do
      for j in [i + 1..d] do
         y := <i, j>;
         Append (~X, y);
      end for;
   end for;
   return X;
end function;

/* wedge of two vectors a & b */
SymmetricWedge := function (a, b)
   d := Degree (a);
   L := CreateList (d);
   A := [];
   for l in [1..d] do
       pair := L[l];
       m := pair[1]; n := pair[2];
       entry := a[m] * b[n]; 
       A[l] := entry;
   end for;
   for l in [d + 1..#L] do
      pair := L[l];
      m := pair[1]; n := pair[2];
      entry := a[m] * b[n] + a[n] * b[m];
      A[l] := entry;
   end for;
   F := BaseRing (Parent (a));
   V := VectorSpace (F, #L);
   w := V ! A;
   i := Depth (w);
   return w, w[i]^-1 * w;
end function;

/* is n = d (d + 1) / 2? */

DetermineDegree := function (n)
   n := 2 * n;
   N := Divisors (n);
   flag := exists (d){d : d in N | (d + 1) in N and d * (d + 1) eq n};
   if flag then return true, d; else return false, _; end if;
end function;

/* choose suitable basis for Singer cycle g;
   return change-of-basis matrix CB, definitions 
   of basis elements defs, and g */

ChooseBasis := function (G)
   
   n := Degree (G);
   flag, d := DetermineDegree (n);

   F := BaseRing (G);
   q := #F;
   f := Degree (F);

   /* find Singer cycle in G */
   count := 1; 
   NmrTries := 100;
   LIMIT := 3;

   if IsEven (d) then 
      order := (q^d - 1) div (2 * (q - 1));
   else 
      order := (q^d - 1) div (q - 1);
   end if;
if d eq 4 and q eq 3 then 
   order := (q^d - 1) div 2;
end if;

   repeat 
      flag, g := RandomElementOfOrder (G, order: MaxTries := count * NmrTries);
      count +:= 1;
   until flag or count eq LIMIT;

   if flag eq false then 
      vprint SmallDegree: "Failed to find Singer cycle";
      return false, _, _, _;
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
      return false, _, _, _;
   end if;

   EV := [e[1]: e in EV];
   ev := [];
   /* construct Frobenius orbits on products of eigenvectors l_i l_j */
   for i in [1..#EV] do
      v := EV[i];
      if v in &join (ev) then continue; end if;
      orbit := {@ v^(q^j): j in [0..d - 1] @};
      Append (~ev, orbit);
   end for;

   index := [i : i in [1..#ev] | #ev[i] eq d];

   /* possible orderings of basis vectors */
   good := [];
   for k in index do 
      X := ev[k]; 
      list := [j : j in [1..#ev] | j ne k];
      for i in [1..#X] do 
         for j in [i + 1..#X] do 
            val := X[i] * X[j];
            if not IsSquare (val) then break k; end if;
            root := Sqrt (val);
            if not exists {l: l in list | -root in ev[l] or root in ev[l]} then 
               continue k;
            end if;
         end for;
      end for;
      Append (~good, k);
   end for;
            
   vprint SmallDegree: "Possible choices for basis are ", good;

   /* select ordering */
   for m in [1..#good] do 
      k := good[m];
      list := [j : j in [1..#ev] | j ne k];
      X := ev[k];
      e := X[1];
      X := [e^(q^i): i in [0..d - 1]];
      L := X;
      defs := [<i, i> : i in [1..d]]; 
      for i in [1..d] do
         for j in [i + 1..d] do
            val := X[i] * X[j];
            root := Sqrt (val);
            if exists (l) {l: l in list | root in ev[l]} then
               pos := Position (ev[l], root);
            elif exists (l) {l: l in list | -root in ev[l]} then
               pos := Position (ev[l], -root);
            else 
               vprint SmallDegree: "Problem for ordering ", m, i ,j;
               break m;
            end if;
            Append (~L, ev[l][pos]);
            Append (~defs, <i, j>);
         end for;
      end for;
   end for;

   if #good eq 0 or #defs ne n then 
      vprint SmallDegree: "No choice of basis works";
      return false, _, _, _;
   end if;

   ES := [Eigenspace (s, e).1: e in L];

   /* construct change-of-basis matrix */
   CB := GL (n, E) ! &cat ([Eltseq (x): x in ES]);

   // assert IsDiagonal (CB * s * CB^-1);

   return true, CB, defs, g;
end function;

/* find position of <i, j> in defs */

IndexPosition := function (defs, i, j)
   pair := i lt j select <i, j> else <j, i>;
   return Position (defs, pair);
end function;

/* evaluate A[i][l] * C[i][j] / C[j][l] */

ACdivC := function (T, defs, A, AdivC, C2, i, j, l)
   b := IndexPosition (defs, i, j);
   c := IndexPosition (defs, j, l);
   return (T[b][c] - AdivC[i][j] * AdivC[j][l] * C2[i][j]) / A[j][j];
end function;
   
/* given matrix g in symmetric square repn of GL(d, q),
   reconstruct it as d x d matrix; CB is change-of-basis
   matrix; defs is sequence of definition of the 
   d + (d choose 2) basis vectors of symmetric square */

DetermineConstants := function (G, CB, defs)
   F := BaseRing (G);
   q := #F;

   n := Degree (G);
   flag, d := DetermineDegree (n);
   E := GF (q^d);
   M := MatrixAlgebra (E, n);

   defs := CreateList (d);

   /* choose random g to determine constants */
   g := Random (G);

   /* write wrt to the new basis */
   T := CB * M!g * CB^-1;

   MA := MatrixAlgebra (E, d);
   A := Zero (MA);

   C := Identity (MA);

   /* compute A(i, j) A(j, i) */
   AijAji := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         b := IndexPosition (defs, i, j);
         if T[a][a] ne 0 then 
            AijAji[i][j] := T[a][b] * T[b][a] / (2 * T[a][a]);
         else
            vprint SmallDegree: "Division by zero"; return false, _;
         end if;
      end for;
   end for;
   AijAji +:= Transpose (AijAji);

   /* compute A(i, i) A(j, j) */ 
   AiiAjj := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         b := IndexPosition (defs, i, j);
         AiiAjj[i][j] := T[b][b] - AijAji[i][j];
      end for;
   end for;

   /* compute C(i, j)^2 */
   C2 := Zero (MA);
   for i in [1..d] do 
      c := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         a := IndexPosition (defs, i, j);
         b := IndexPosition (defs, j, j);
         if T[b][b] * T[c][b] ne 0 then 
            C2[i][j] := T[a][b]^2 / (T[b][b] * T[c][b]);
         else
            vprint SmallDegree: "Division by zero"; return false, _;
         end if;
      end for;
   end for;

   /* alternative computation for C(i, j)^2 */
   /* 
   D2 := Zero (MA);
   for i in [1..d] do 
      c := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         a := IndexPosition (defs, i, j);
         b := IndexPosition (defs, j, j);
         D2[i][j] := T[a][c]^2 / (T[b][c] * T[c][c]);
      end for;
   end for;
   assert C2 eq D2;
   */

   /* choose sign A(1, 1) */
   root := Sqrt (T[1][1]);
   A[1][1] := root;
   rootm1 := root^-1;
   
   /* now determine A[j][j] */
   for j in [2..d] do
      A[j][j] := rootm1 * AiiAjj[1][j]; 
   end for;

   /* record A[i][j] / C[i][j] */
   AdivC := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [1..d] do
         b := IndexPosition (defs, i, j);
         AdivC[i][j] := T[a][b] / (2 * A[i][i]);
      end for;
   end for;

   /* determine entries in first row of A */
   i := 1;
   bound := IsEven (d) select (d div 2) else d; 
   for j in [2..bound] do
      ell := (2 * j - 1); 
      while ell gt d do ell -:= d; end while;
      value := ACdivC (T, defs, A, AdivC, C2, i, j, ell);
      exp := (q^(j - 1) - 1) div 2;
      A[i][ell] := value * C2[1][j]^exp;
      C[i][ell] := A[i][ell] / AdivC[i][ell];
      a := IndexPosition (defs, i, ell);
      A[ell][i] := (T[a][a] - A[i][i] * A[ell][ell]) / A[i][ell];
   end for;

   /* remaining entries in row 1 for even d */
   if IsEven (d) then 
      /* choose sign A(1, 2) */
      root2 := Sqrt (T[1][2]);

      A[1][2] := root2; 

      ell := 2;
      a := IndexPosition (defs, i, ell);
      A[ell][i] := (T[a][a] - A[i][i] * A[ell][ell]) / A[i][ell];

      for ell in [4..d by 2] do
         index := Position (defs, <ell - 2, ell>);
         value := (T[1][index] * C[1][3]^(q^(ell-3))) / (2 * C[1][1]);
         A[1][ell] := value / A[1][ell - 2]; 
         a := IndexPosition (defs, i, ell);
         A[ell][i] := (T[a][a] - A[i][i] * A[ell][ell]) / A[i][ell];
      end for;
   end if;

   /* determine C[1][j] */
   for j in [2..d] do
      C[1][j] := A[1][j] / AdivC[1][j];
   end for;

   /* now determine A[i][j] and A[j][i] when i, j <> 1 */
   for i in [2..d] do 
      for j in [i + 1..d] do 
         a := IndexPosition (defs, 1, i);
         b := IndexPosition (defs, 1, j);
         A[i][j] := ((C[1][j] / C[1][i]) * T[a][b] - A[i][1] * A[1][j]) / A[1][1];
         a := IndexPosition (defs, i, j);
         A[j][i] := (T[a][a] - A[i][i] * A[j][j]) / A[i][j];
      end for;
   end for;

   for i in [2..d] do
      C[i][1] := C[1][i];
      for j in [i + 1..d] do
         C[i][j] := C[i-1][j - 1]^q; 
         C[j][i] := C[i][j];
      end for;
      // C[i][1] := C[i - 1][d]^q;
   end for;
   
   /* squares of all entries in A equal values of T? */
   // assert Set (&cat[[A[i][j]^2 eq T[i][j]: j in [1..d]]: i in [1..d]]) eq {true};

   // return true, C, GL(d, E) ! A, g;
   return true, C;
end function;

/* we cannot evaluate f(x) directly because some
   of its entries are zero; instead choose a random
   element y and evaluate f(x) from f(xy) = f(x) f(y)  */

UseHomomorphism := function (G, x, C, CB, defs)
   P := Parent (CB);
   y := Random (G);
   y := P ! (CB * P ! y * CB^-1);
   rxy := Reconstruct (G, (P!x) * y, C, CB^0, defs);
   if Type (rxy) eq BoolElt then return false; end if;
   ry := Reconstruct (G, y, C, CB^0, defs);
   if Type (ry) eq BoolElt then return false; end if;
   return rxy * ry^-1;
end function;

/* given matrix g in symmetric square repn of GL(d, q),
   reconstruct it as d x d matrix; CB is change-of-basis
   matrix; defs is sequence of definition of the 
   d + (d choose 2) basis vectors of symmetric square */

Reconstruct := function (G, g, C, CB, defs)
   F := BaseRing (G);
   q := #F;

   n := Degree (G);
   flag, d := DetermineDegree (n);
   E := GF (q^d);
   M := MatrixAlgebra (E, n);

   /* write wrt to the new basis */
   T := CB * M!g * CB^-1;

   MA := MatrixAlgebra (E, d);
   A := Zero (MA);

   /* compute A(i, j) A(j, i) */
   AijAji := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         b := IndexPosition (defs, i, j);
         if T[a][a] ne 0 then 
            AijAji[i][j] := T[a][b] * T[b][a]  / (2 * T[a][a]);
         else
            repeat 
               // "Division by zero";  
               A := UseHomomorphism (G, g, C, CB, defs);
               if Type (A) eq AlgMatElt then return A; end if;
            until 1 eq 0;
         end if;
      end for;
   end for;
   AijAji +:= Transpose (AijAji);

   /* compute A(i, i) A(j, j) */ 
   AiiAjj := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [i + 1..d] do 
         b := IndexPosition (defs, i, j);
         AiiAjj[i][j] := T[b][b] - AijAji[i][j];
      end for;
   end for;

   /* choose sign A(1, 1) */
   root := Sqrt (T[1][1]);
   A[1][1] := root;
   rootm1 := root^-1;
   
   /* now determine A[j][j] */
   for j in [2..d] do
      A[j][j] := rootm1 * AiiAjj[1][j]; 
   end for;

   /* record A[i][j] / C[i][j] */
   AdivC := Zero (MA);
   for i in [1..d] do 
      a := IndexPosition (defs, i, i);
      for j in [1..d] do
         b := IndexPosition (defs, i, j);
         AdivC[i][j] := T[a][b] / (2 * A[i][i]);
      end for;
   end for;

   for i in [1..d] do
      for j in [1..d] do
         if i ne j then 
            A[i][j] := AdivC[i][j] * C[i][j];
         end if;
      end for;
   end for;

   return A;
end function;

/* G is symmetric square representation of H, where
   SL(d, q) <= H <= GL(d, q); reconstruct H */

intrinsic RecogniseSymmetricSquare (G :: GrpMat) -> BoolElt, GrpMat  
{G is symmetric square representation of H, where
 SL(d, q) <= H <= GL(d, q) and d >= 4; reconstruct H;
 return true and H, otherwise false }
 
   n := Degree (G);
   flag, d := DetermineDegree (n);

   if flag eq false then 
      vprint SmallDegree: "Representation is not symmetric square"; 
      return false, _;
   end if;

   q := #BaseRing (G);

   if d le 3 or (d eq 4 and q eq 3 and 
                 forall{g : g in Generators (G) | Determinant (g) eq 1}) then 
      error Error (rec<RecognitionError |
      Description := "Recognition for symmetric square of SL", 
      Error := "Does not apply to special small cases">); 
   end if;

   found, CB, defs := ChooseBasis (G);
   if found eq false then
      vprint SmallDegree: 
         "Representation is probably not symmetric square of SL";
      return false, _;
   end if;

   found, C := DetermineConstants (G, CB, defs);
   if found eq false then
      vprint SmallDegree: 
         "Representation is probably not symmetric square of SL";
      return false, _;
   end if;

   X := [Reconstruct (G, G.i, C, CB, defs):  i in [1..Ngens (G)]];

   H := sub <GL(d, q^d)  | X >;
   flag, A := IsOverSmallerField (H);
   if not flag then
      error Error (rec<RecognitionError |
      Description := "Recognition for symmetric square representation of SL",
      Error := "Representation cannot be written over smaller field">);
   end if;

   // addition March 2011 to deal with non-trivial scalars 
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      A := sub<Generic (A) | [ScaleMatrix (A.i): i in [1..Ngens (A)]]>;
   end if;

   SCB := H`SmallerFieldChangeOfBasis;      

   G`SymSquare := <CB, defs, C, SCB>;
   return true, A;
end intrinsic;

/* G is symmetric square representation of H, where
   SL(d, q) <= H <= GL(d, q); find preimage of g in H */

intrinsic SymmetricSquarePreimage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt 
{G is symmetric square representation of H, where
 SL(d, q) <= H <= GL(d, q); find preimage of g in H} 

   if not assigned G`SymSquare then
      error Error (rec<RecognitionError |
      Description := "Recognition for symmetric square of SL", 
      Error := "Must first apply RecogniseSymmetricSquare">);
   end if;

   R := G`SymSquare; 
   CB := R[1]; defs := R[2]; C := R[3]; SCB := R[4];
   h := Reconstruct (G, g, C, CB, defs);
   im := GL(Nrows (h), BaseRing (G)) ! (SCB^-1 * h * SCB);

   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      im := GL(Nrows (h), BaseRing (G)) ! ScaleMatrix (im);
   end if;

   return im;
end intrinsic;

Test := function (g, d, q)
   m := q^d * &*[d div j * (q^j - 1): j in Divisors (d) | j ne d];
   return g^m ne 1;
end function;

SymTestHom := function (G)
   R := G`SymSquare;
   g1 := Random (G);
   h1 := SymmetricSquarePreimage (G, g1);
   g2 := Random (G);
   h2 := SymmetricSquarePreimage (G, g2);
   h := SymmetricSquarePreimage (G, g1 * g2);
   m := (h1 * h2)^-1 * h;
   return IsScalar (m) and Order (m) in {1, 2}, g1, g2;
end function;
