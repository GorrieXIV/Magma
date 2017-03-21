/* code to decompose adjoint representation of H
   where SL(d, q) <= H <= GL(d, q);
   Kay Magaard, Eamonn O'Brien, and Akos Seress;
   this July 2009 version corrects errors in 
   the algorithm described in our paper */

import "basics.m": RecognitionError;
import "../sl2q/decompose.m": ScaleMatrix;

forward Reconstruct;

DetermineDegree := function (n)
   flag, d := IsSquare (n + 1);
   if not flag then 
     flag, d := IsSquare (n + 2); 
     def := 2;
   else 
     def := 1;
   end if;
   if not flag then 
      return false, _, _; 
   else 
      return true, d, def; 
   end if;
end function;

/* choose suitable basis for Singer cycle g;
   return change-of-basis matrix CB and g */

ChooseBasis := function (G) 
   
   flag, d, def := DetermineDegree (Degree (G));

   n := Degree (G);
   F := BaseRing (G);
   q := #F;
   p := Characteristic (F);

   /* find Singer cycle in G */
   count := 1; 
   NmrTries := 100;
   LIMIT := 10;

   order := (q^d - 1) div (q - 1);
   order := order div Gcd (d, q - 1);

   repeat 
      flag, g := RandomElementOfOrder (G, order);
      count +:= 1;
   until flag or count eq LIMIT;

   if count eq LIMIT then 
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
   if #EV lt n - d + 1 then 
      str := "Element of order " cat IntegerToString (order) cat
       " does not have " cat IntegerToString (n) cat " distinct eigenvalues";
      vprint SmallDegree: str;
      return false, _;
   end if;

   EV := [e[1]: e in EV | e[1] ne 1];

   Z := Integers ();

   /* eigenvalues in natural repn are known */

   O := [];

   /* construct Frobenius orbits on products 
      of eigenvectors l_i l_j */
   for i in [1..#EV] do
      v := EV[i]; 
      if v in &join (O) then continue; end if;
      orbit := {@ v^(q^j): j in [0..d - 1] @};
      Append (~O, orbit);
   end for;

   MA := MatrixAlgebra (E, d);

   for o in [1..#O] do 
      T := Zero (MA);
      first := O[o];
      for i in [1..d - 1] do
        T[i][i+1] := first[i];
      end for;
      T[d][1] := first[d];
      for k in [2..d - 1] do
         v := T[1][k] * T[1][2]^(q^(k - 1));
         if v in EV and not (v in first) then 
            T[1][k + 1] := v;
            for j in [2..d - k] do
               T[j][j + k] := T[j - 1][j + k - 1]^q;
            end for;
            T[d + 1 - k][1] := T[d - k][d]^q;
            for j in [d + 2 - k..d] do
               T[j][j -(d - k)] := T[j - 1][j - (d - k) - 1]^q;
            end for;
         else 
            continue o;
         end if;
      end for;
      break;
   end for;

   MA := MatrixAlgebra (E, n); 
   l := Eltseq (T);
   l := [x : x in l | x ne 0]; 
   ES := [Eigenspace (s, e).1: e in l] cat 
         [Eigenspace(s, 1).i : i in [1..d - def]];
   CB := GL (n, E) ! &cat ([Eltseq (x): x in ES]);
   // assert IsDiagonal (CB * s * CB^-1);

   return true, CB;
end function;

FindIndex := function (i, j, d)
   if (j le i) then 
      return (i - 1) * (d - 1) + j;
   else 
      return (i - 1) * (d - 1) + (j - 1);
   end if;
end function;

/* construct the matrix of constants C */

DetermineConstants := function (G, CB)

   flag, d, def := DetermineDegree (Degree (G));

   P := Parent (CB);
   E := BaseRing (P);
   n := Degree (G);

   F := BaseRing (G);
   q := #F;

   M := MatrixAlgebra (E, n);
   CBinv := CB^-1;
   repeat
      h := Random (G);
      K := CB * M!h * CB^-1;
   until K[d + 1][d + 1] * K[2][2] ne 0 and
   forall{j: j in [4..d] | K[FindIndex(1, j - 1, d)][FindIndex (1, j, d)] ne 0};

   A11A22 := K[2][2]/K[d+1][d+1];

   MA := MatrixAlgebra (E, d);
   w := PrimitiveElement (E);

   for kk in [0..q - 1] do
      C := Zero (MA);
      if d ge 3 then C[1][3] := 1; end if;
      C[1][2] := w^kk;
      for j in [4..d] do 
         C[1][j]:=(C[1][j-1])^(q+1)* A11A22 * 
             K[FindIndex(2,j-1,d)][FindIndex(2,j,d)]/
            ((C[1][j-2])^q*K[FindIndex(1,j-1,d)][FindIndex(1,j,d)]);
      end for;
      for j in [2..d] do
         for k in [1..d] do
            if k eq 1 then C[j][k] := C[j- 1][d]^q;
            else C[j][k] := C[j- 1][k - 1]^q; end if;
         end for;
      end for;
      /* is this a good matrix C? */
      g := Random (G);
      a := Reconstruct(G, g, C, CB);
      c := Reconstruct(G, h, C, CB);
      u := Reconstruct(G, g * h, C, CB);
      if Determinant (u) ne 0 and IsScalar (a*c*u^(-1)) then 
         return true, C;
      end if;
   end for;
   
   vprint SmallDegree: "No choice worked in ChooseConstants";
   return false, _;

end function;

/* we cannot evaluate f(x) directly because some
   of its entries are zero; instead choose a random
   element y and evaluate f(x) from f(xy) = f(x) f(y)  */

UseHomomorphism := function (G, x, C, CB)
   // "Division by zero";
   y := Random (G);
   rxy := Reconstruct (G, x * y, C, CB);
   if Type (rxy) eq BoolElt then return false; end if;
   ry := Reconstruct (G, y, C, CB);
   if Type (ry) eq BoolElt then return false; end if;
   return rxy * ry^-1;
end function;

/* given change of basis matrix  CB and constants matrix C, and
   element g, construct corresponding A and A^* */

Reconstruct := function (G, g, C, CB)

   flag, d, def := DetermineDegree (Degree (G));
   
   F := BaseRing (G);
   n := Degree (G);

   P := Parent (CB);
   K := CB * P ! g * CB^-1;

   E := BaseRing (P);
   M := MatrixAlgebra (E, d);
   A := Zero (M);

   MA := MatrixAlgebra (E, d);

   a := FindIndex (3, 1, d); b := FindIndex (3, 2, d);
   if d ge 4 then 
      ell := FindIndex (4, 1, d); m := FindIndex (4, 2, d); 
   end if;
   if K[b][b] * K[a][a] ne 0 then
      A11A22st := K[a][a]/ K[b][b];
   elif d ge 4 and K[m][m] * K[ell][ell] ne 0 then 
       A11A22st := K[ell][ell] / K[m][m];
   else 
      repeat
         A := UseHomomorphism (G, g, C, CB);
         if Type (A) eq AlgMatElt then return A; end if;
      until 1 eq 0;
   end if;

   i := FindIndex(2, 3, d); 
   if d ge 4 then j := FindIndex(4, 3, d); end if;
   if K[i][i] ne 0 then
      ell := FindIndex(2, 1, d);
      A11A33st := K[ell][ell]/ K[i][i];
   elif d ge 4 and K[j][j] ne 0 then
      m := FindIndex(4, 1, d);
      A11A33st := K[m][m]/ K[j][j];
   else 
      repeat
         A := UseHomomorphism (G, g, C, CB);
         if Type (A) eq AlgMatElt then return A; end if;
      until 1 eq 0;
   end if;

   for i in [2..d] do
      for j in [2..d] do
        A[i][j] := K[FindIndex(i,1,d)][FindIndex(j,1,d)]*C[j][1]/C[i][1];
     end for;
   end for;
   for j in [1] cat [3..d] do
      A[1][j] := K[FindIndex(1,2,d)][FindIndex(j,2,d)]*C[j][2]*A11A22st/C[1][2];
      A[j][1] := K[FindIndex(j,2,d)][FindIndex(1,2,d)]*C[1][2]*A11A22st/C[j][2];
   end for;

   a := FindIndex(1, 3, d);
   b := FindIndex(2, 3, d);
   A[1][2] := K[a][b]*C[2][3]*A11A33st/C[1][3];
   A[2][1] := K[b][a]*C[1][3]*A11A33st/C[2][3];

   return A;
end function;

intrinsic RecogniseAdjoint (G :: GrpMat) -> BoolElt, GrpMat
{G is adjoint representation of H, where
 SL(d, q) <= H <= GL(d, q) and d >= 3; reconstruct H; 
 return true and H, otherwise false }
 
   n := Degree (G);
   flag, d := DetermineDegree (n);

   if flag eq false then
      vprint SmallDegree: "Input representation is not adjoint";
      return false, _;
   end if;

   if d le 2 then      
      error Error (rec<RecognitionError |
      Description := "Recognition for adjoint representation of SL",
      Error := "Does not apply to small cases">);
   end if;

   F := BaseRing (G);

   found, CB := ChooseBasis (G);
   if found eq false then
      vprint SmallDegree:
         "Input is probably not adjoint representation of SL";
      return false, _;
   end if;

   found, C := DetermineConstants (G, CB);
   if not found then 
      vprint SmallDegree: 
         "Input is probably not adjoint representation of SL";
      return false, _;
   end if;

   gens := [Reconstruct (G, G.i, C, CB): i in [1..Ngens (G)]];;
   F := BaseRing (Parent (Rep (gens))); 
   H := sub <GL (Nrows (Rep (gens)), F) | gens >;
   flag, A := IsOverSmallerField (H: Scalars := true);
   if not flag then
      error Error (rec<RecognitionError |
      Description := "Recognition for adjoint representation of SL",
      Error := "Representation cannot be written over smaller field">);
   end if;

   // addition March 2011 to deal with non-trivial scalars 
   if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      A := sub<Generic (A) | [ScaleMatrix (A.i): i in [1..Ngens (A)]]>;
   end if;

   SCB := H`SmallerFieldChangeOfBasis;
   G`Adjoint := <CB, C, SCB>;
   return true, A;
end intrinsic;

intrinsic AdjointPreimage (G :: GrpMat, g :: GrpMatElt) -> GrpMatElt
{G is adjoint representation of H, where
 SL(d, q) <= H <= GL(d, q); find preimage of g in H} 

   if not assigned G`Adjoint then
      error Error (rec<RecognitionError |
      Description := "Recognition for adjoint representation of SL",
      Error := "Must first apply RecogniseAdjoint">);
   end if;

   R := G`Adjoint;
   CB := R[1]; C := R[2]; SCB := R[3];
   h := Reconstruct (G, g, C, CB);
   h := (SCB^-1 * h * SCB);
   
   /* element is now over smaller field mod scalars */
   E := Eltseq (h);
   K := BaseRing (Parent (h));
   d := Nrows (h);
   v := VectorSpace (K, d^2) ! E;
   depth := Depth (v);
   if depth eq 0 then error "Matrix is zero"; end if;
   alpha := v[depth];
   S := ScalarMatrix (d, alpha^-1);

   im := GL(Nrows (h), BaseRing (G)) ! (h * S);

  if forall{x : x in Generators (G) | Determinant (x) eq 1} then
      im := GL(Nrows (h), BaseRing (G)) ! ScaleMatrix (im);
   end if;

   return im;
end intrinsic;

/* 
for d in [3..10] do 
for q in [2,3,4,3^2,5,5^2, 7, 7^2] do 
d, q;
G := MyAdjointRepresentation (d, q);
G:=RandomConjugate (G);

f, H := RecogniseAdjoint (G);
assert f;

for k in [1..100] do
g:=Random(G);
h:=Random(G);
a:=AdjointPreimage(G,g);
c:=AdjointPreimage(G,h);
u:=AdjointPreimage(G,g * h);
assert IsScalar (a*c*u^(-1));
end for;
end for;
end for;
*/
