freeze;

forward PreimageOfElement;

import "decompose.m": FindAPs, ScalarMultiple;
import "special-cases.m":SpecialIsSymmetricPower;

/* G is a group of degree N; 
   find an element g having N distinct eigenvalues; 
   if G is symmetric power of SL(2, q), then the eigenvalues satisfy
   a geometric progression; organise corresponding eigenspaces to give
   a basis exhibiting diagonalisation of g */

DiagonalBasis := function (G)

   F := BaseRing (G);
   q := #F;
   p := Characteristic (F);
   n := Degree (G) - 1;
   N := Degree (G);

   trial := 0; 
   NmrTries := 100;
   found := false;
   repeat 
      // g := ElementOfOrder (G, (q - 1) div 2, NmrTries:
                           // Word := false, Fct := ProjectiveOrder);  
      flag, g := RandomElementOfOrder (G, (q - 1) div 2: 
                     MaxTries:= NmrTries, Central := true);  
      if flag then 
         EV := Eigenvalues (g);
      else 
         EV := [];
      end if;
      trial +:= 1;
      found := #EV eq N;
   until found or trial gt NmrTries;
   
   vprint sl2q: "Trial is ", trial, "found is", found;
   if not found then return false, false; end if;

   EV := SetToSequence ({ev[1]: ev in EV});
   Z := Integers ();
   Zq := quo <Z | q - 1>;
   E := [Zq ! Log (ev): ev in EV];
   A := FindAPs (E, N, p : MaxAP := true);
   len := [#a : a in A];
   if #len ne 0 then 
      max, index := Maximum (len); 
   end if;
   if #len eq 0 or max ne N then 
      "No geometric progression of length ", N, " found "; 
      return false, false;
   end if;

   A := A[index]; 
   w := PrimitiveElement (F);
   ev := [w^(Z!a) : a in A];

   /* setup matrix to diagonalize g - so CB * g * CB^-1 is
     diagonal with entries the eigenvalues of g */

   T := &cat[Eltseq (Rep (Generators (Eigenspace (g, e)))): e in ev];
   CB := GL(N, F) ! T;
   assert IsDiagonal (CB * g * CB^-1);

   return true, CB;

end function;

/* we cannot evaluate f(x) directly because some
   of its entries are zero; instead choose a random
   element y and evaluate f(x) from f(xy) = f(x) f(y)  */

UseHomomorphism := function (G, x, CB) 
   y := Random (G);  
   m := Degree (G);
   P := Parent (CB);
   y := GL (m, BaseRing (P)) ! y;
   // assert Determinant (y) eq 1;
   y := CB * y * CB^-1;
   flag, rxy := PreimageOfElement (G, x * y, CB);
   if flag eq false then return false, _; end if;
   flag, ry := PreimageOfElement (G, y, CB);
   if flag eq false then return false, _; end if;
   return true, rxy * ry^-1;
end function;

/* h is element of symmetric power of SL(2, q) rewritten to 
   basis determined by CB; determine preimage of h in SL(2, q) */

PreimageOfElement := function (G, h, CB)

   n := Nrows (h) - 1;
   if n eq 1 then return true, h; end if;

   F := BaseRing (Parent (CB));

   p := Characteristic (F);
   zero := Zero (F);

   /* in its natural representation, h = [ a b ] 
                                         [ c d ] 
      we know h wrt symmetric powers basis 
      theta0 x^n, theta1 x^(n - 1) y, ..., theta_n y^n; 
      we want to find a, b, c, d */
   
   theta0 := F!1; theta1 := F!1;

   /* examine image of first basis vector theta0 x^(n) under h */

   /* first entry of matrix determines a^n */
   one := h[1][1];
   if one eq zero then return UseHomomorphism (G, h, CB); end if;
 
   /* second entry determines (theta0/theta1) a^(n - 1) b 
                               theta1 x^(n - 1) y */
   two := h[1][2];

   if two eq zero then return UseHomomorphism (G, h, CB); end if;
   
   /* now obtain (b/a) (theta0 / theta1) */
   three := (two * one^-1) / (F!n);

   /* now examine image of second basis vector 
      theta1 x^(n - 1) y under h */
   
   /* first entry determines a^(n - 1) c (theta1 / theta0) */
   four := h[2][1];
   
   /* product of three and four gives b c a^(n - 2) */
   five := three * four;

   /* quotient of five by one gives bc / a^2 */
   if one ne 0 then 
      six := five / one;
   else 
      six := 0;
   end if;

   /* second entry determines (n - 1) a^(n - 2) bc + a^(n - 1) d */
   seven := h[2][2];

   /* now divide seven by one to obtain (n - 1) bc/a^2 + d/a */
   eight := seven / one;

   /* subtract (n - 1) * six from eight to get d / a */
   nine := eight - (n - 1) * six;
   
   /* now bc/ a^2 divided by b/a is c/a */
   ten := six / three;

   /* now we know the matrix [1 b/a : c/a d/a] */
   a := Root (one, n);
   // im := GL(2, F) ! [a, three * a, ten * a, nine * a];
   MA := MatrixAlgebra (F, 2);
   im := MA ! [a, three * a, ten * a, nine * a];
   if Determinant (im) eq 0 then return false, _; end if;
   det := Determinant (im);
   if not IsSquare (det) then return false, _; end if;
   y := Root (det, 2);
   im := ScalarMultiple (im, y^-1);
   if Determinant (im) ne 1 then return false, _; end if;

   return true, GL(2, F)!im;
end function;

/* decide if G is absolutely irreducible symmetric power of SL(2, q);
   if so, construct the images of each of its generators in SL(2, q)  */

IsSymmetricPower := function (G)

   n := Degree (G) - 1;
   if n eq 1 then return false, _, _; end if;

   F := BaseRing (G);
   p := Characteristic (F);

   if n ge p then 
      vprint sl2q: "Symmetric power algorithm does not apply"; return false, _, _; 
   end if;

   if (IsAbsolutelyIrreducible (G) eq false) then 
      vprint sl2q: "G must be absolutely irreducible";
      return false, _, _;
   end if;

   if exists {x : x in Generators (G) | Determinant (x) ne 1} then
      vprint sl2q: "Input is not (projective or linear) representation of SL2 over minimal field";
      return false, _, _;
   end if;

   if (#F le 5) or (p eq #F and n ge ((p - 5) div 2)) then 
      flag, CB := SpecialIsSymmetricPower (G); 
      vprint sl2q: "Used special symmetric power code";
   else 
      flag, CB := DiagonalBasis (G);
   end if;

   if flag eq false then 
      vprint sl2q: "No change of basis found"; 
      return false, _, _;
   end if;

   /* determine images of generators of G */
   im := [Identity (GL(2, BaseRing (G)))];
   U := UserGenerators (G);
   for i in [1..#U] do
      flag, value := PreimageOfElement (G, CB * U[i] * CB^-1, CB); 
      if flag eq false then return false, value, _; end if;
      im[i] := value;
   end for;

   return true, CB, im;
end function;
