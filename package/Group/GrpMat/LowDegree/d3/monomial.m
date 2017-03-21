freeze;

import "../gl-list.m": BackTrack;

/* monomials of degree 3 for characteristic at least 5 */

MonomialList := function (q)

   F := GF (q);
   q := #F;
   primes := PrimeBasis (q - 1);
   
   rou_set := {@ 1 @};
   rou_list := [* F!1 *];

   for r in primes do
    v := Valuation(q-1,r);
    if r in {2,3} then v +:= 1; end if;
    for i := 1 to v do
	Include(~rou_set, r^i);
	Append(~rou_list, RootOfUnity(r^i,F));
    end for;
   end for;

    root_of_unity := function(r, F)
	ind := Index(rou_set, r);
	if ind eq 0 then
	    return RootOfUnity(r, F);
	else
	    return rou_list[ind];
	end if;
    end function;

Z := function (F, i, r)
   w := root_of_unity (r^i, F);
   z := ScalarMatrix (3, w);
   return z;
end function;

U := function (F, i, r)
   w := root_of_unity (r^i, F);
   return DiagonalMatrix ([w, w^-1, 1]);
end function;

W := function (F, i, r)
   w := root_of_unity (r^i, F);
   return DiagonalMatrix ([1, w, w^-1]);
end function;

C := function (F, i, j, k, e)
   c := MatrixAlgebra (F, 3) ! [0,1,0,0,0,1,1,0,0];
   if k eq 1 then 
      return sub <GL(3, F) | c * Z(F, i + 1, 3)^e, Z(F, i, 3),
                                              U(F, j, 3), W(F, j, 3)>; 
   elif k eq 2 then  
      return sub <GL(3, F) | c * Z(F, i + 1, 3)^e, Z(F, i, 3),
             U(F, j + 1, 3)^2 * W(F, j + 1, 3), U(F, j, 3), W(F, j, 3)>; 
   elif k eq 3 then
      return sub <GL(3, F) | c, U(F, j, 3), W(F, j, 3), 
                      Z(F, i + 1, 3) * U(F, j + 1, 3)^2 * W(F, j + 1, 3)>; 
   elif k eq 4 then
      return sub <GL(3, F) | c, U(F, j, 3), W(F, j, 3), 
                  Z(F, i + 1, 3)^2 * U(F, j + 1, 3)^2 * W(F, j + 1, 3)>; 
   elif k eq 5 then
     return sub <GL(3, F) | c, U(F, j, 3), W(F, j, 3), 
          Z(F, i + 1, 3) * U(F, j + 1, 3), U(F, j + 1, 3)^2 * W(F, j + 1, 3)>; 
   else 
      error "call value for k";
   end if;
end function;

/* Thm 5.14 (i) list of G3 */

ListC := function (F : Scalar := false)

   q := #F;
   t := Valuation (q - 1, 3);

   c := GL (3, F) ! [0,1,0,0,0,1,1,0,0];

   L := [sub <GL(3, F ) | c>];

   /* use restricted list for this case */
   restrict := [1];
   /* corresponding C-submodule should be non-scalar */
   nonscalar := [1];

   if t eq 0 then return L, restrict, nonscalar; end if;

   alpha := RootOfUnity (3^t, F);
   a := GL(3, F) ! [alpha,0,0,0,1,0,0,0,1];
   ca := c * a;

   for i in [1..t] do 
      for j in [1..t] do 
         Append (~L, C(F, i, j, 1, 0));
         Append (~restrict, #L);
         if i lt t then Append (~L, C(F, i, j, 1, 1)); end if;
      end for;
   end for;

   for j in [1..t] do 
      Append (~L, sub <GL(3, F) | ca, U(F, j, 3), W(F, j, 3)>);
   end for;

   if Scalar eq true then lower := 1; else lower := 0; end if;
   for i in [1..t] do 
      for j in [lower..t - 1] do 
         Append (~L, C(F, i, j, 2, 0));
         if j eq 0 then Append (~nonscalar, #L); end if;
         Append (~restrict, #L);
         if i lt t then 
            Append (~L, C(F, i, j, 2, 1)); 
            if j eq 0 then Append (~nonscalar, #L); end if;
         end if;
      end for;
   end for;

   for j in [lower..t - 1] do 
      Append (~L, sub <GL(3, F) | ca, 
             U(F, j + 1, 3)^2 * W(F, j + 1, 3), U(F, j, 3), W(F, j, 3)>);
      if j eq 0 then Append (~nonscalar, #L); end if;
   end for;
   
   for i in [1..t - 1] do 
      for j in [1..t - 1] do 
         Append (~L, C(F, i, j, 3, 0));
         Append (~restrict, #L);
         Append (~L, C(F, i, j, 4, 0));
         Append (~restrict, #L);
      end for;
   end for;
   Append (~L, C(F, t, t, 3, 0));
   Append (~restrict, #L);

   for i in [1..t - 1] do 
      for j in [lower..t - 1] do 
         Append (~L, C(F, i, j, 5, 0));
         if j eq 0 then Append (~nonscalar, #L); end if;
      end for;
   end for;

   return L, restrict, nonscalar;

end function;

T := function (F, i, j, m)
   if m eq 1 then 
      if i * j gt 0 then 
         return C(F, i, j, 1, 0); 
      else 
         c := GL(3, F) ! [0,1,0,0,0,1,1,0,0];
         return sub <GL(3, F) | c>;
      end if;
   elif m eq 2 then 
      return C(F, i, j, 2, 0); 
   elif m in [3, 4] and i * j gt 0 then 
      return C(F, i, j, m, 0); 
   else 
      "i j m =", i, j, m;
      error "error in input parameters for T";
   end if;
end function;

S := function (F, i, j, k, l, m, n)
   d := MatrixAlgebra (F, 3) ! [0,1,0,1,0,0,0,0,1];
   return sub < GL (3, F) | 
   T(F, i, j, m), d * Z(F, k + 1, 2)^n, Z (F, k, 2), U(F, l, 2), W(F, l, 2)>;
end function;

/* Thm 5.14 (ii) list of S3 */

ListS := function (F : Scalar := false)
   q := #F;
   s := Valuation (q - 1, 2);
   t := Valuation (q - 1, 3);

   L := [];

   m := 1; i := 0; j := 0;
   for k in [0..s] do
      if k eq s then upper := 0; else upper := 1; end if;
      for l in [0..s] do
         for n in [0..upper] do 
            if Scalar eq false or l ge 1 then 
               Append (~L, S (F, i, j, k, l, m, n)); 
            end if;
         end for;
      end for;
   end for;

   m := 1;
   for i in [1..t] do
      for j in [1..t] do
         for k in [0..s] do
            if k eq s then upper := 0; else upper := 1; end if;
            for l in [0..s] do
               for n in [0..upper] do 
                   Append (~L, S (F, i, j, k, l, m, n));
               end for;
            end for;
         end for;
      end for;
   end for;

   m := 2;
   for i in [1..t] do
      for j in [0..t - 1] do
         for k in [0..s] do
            if k eq s then upper := 0; else upper := 1; end if;
            for l in [0..s] do
               for n in [0..upper] do 
                  if Scalar and l eq 0 and j eq 0 then continue; end if;
                  Append (~L, S (F, i, j, k, l, m, n));
               end for;
            end for;
         end for;
      end for;
   end for;

   for m in [3..4] do 
      for i in [1..t - 1] do
         for j in [1..t - 1] do
            for k in [0..s] do
               if k eq s then upper := 0; else upper := 1; end if;
               for l in [0..s] do
                  for n in [0..upper] do 
                     Append (~L, S (F, i, j, k, l, m, n));
                  end for;
               end for;
            end for;
         end for;
      end for;
   end for;

   if t eq 0 then return L; end if;

   m := 3;
   for k in [0..s] do
      if k eq s then upper := 0; else upper := 1; end if;
      for l in [0..s] do
          for n in [0..upper] do 
             Append (~L, S (F, t, t, k, l, m, n));
          end for;
      end for;
   end for;

   return L;

end function;

/* C-modules from Thm 5.5 (i) */

CModules := function (F, r)
   assert r ne 3;

   q := #F;
   ell := Valuation (q - 1, r);
   L := [];
   for i in [0..ell] do
      for j in [0..ell] do
         Append (~L, sub <GL(3, F) | Z(F, i, r), U(F, j, r), W(F, j, r)>); 
         for s in [1..ell - j] do
            if r mod 3 eq 1 then 
               K := GF (r^s);
               P := PolynomialRing (K); t := P.1;
               f := P!(t^2 - t + 1);
               roots := Roots (f);
               roots := [Integers () ! x[1] : x in roots];
               assert #roots eq 2;
               for t in roots do 
                  Append (~L, sub <GL(3, F) | Z(F, i, r), U(F, j, r), 
                     W(F, j, r), U(F, j + s, r)^t * W(F, j + s, r)>);
               end for;
            end if;
         end for;
      end for;
   end for;
            
   return L;

end function;

/* Thm 5.6 S3-conjugacy between C-submodules of D(3, q) of 3'-order */

SpecialList := function (F)

   q := #F;
   R := PrimeBasis (q - 1);
   Exclude (~R, 3);
   Sort (~R);
   E := [Valuation (q - 1, r): r in R];
   R1 := [r : r in R | r mod 3 eq 1];
   Sort (~R1);
   E1 := [Valuation (q - 1, r): r in R1];

   C1 := [[] : r in R];
   for m in [1..#R] do 
      r := R[m]; 
      for i in [0..E[m]] do
         for j in [0..E[m]] do
            Append (~C1[m], sub <GL(3, F) | Z(F, i, r), U(F, j, r), W(F, j, r)>); 
         end for;
      end for;
   end for;

   C2 := [[]: r in R1];
   for m in [1..#R1] do 
      r := R1[m]; 
      for i in [0..E1[m]] do
         for j in [0..E1[m]] do
            for k in [1..E1[m] - j] do 
               K := GF (r^k);
               P := PolynomialRing (K); t := P.1;
               f := P!(t^2 - t + 1);
               roots := Roots (f);
               roots := [Integers () ! x[1] : x in roots];
               assert #roots eq 2;
               t := roots[1];
               Append (~C2[m], sub <GL(3, F) | Z(F, i, r), 
               U(F,j + k, r)^t * W(F, j + k, r), U(F, j, r), W(F, j, r)>); 
            end for;
         end for;
      end for;
   end for;

   C3 := [[] : r in R1];
   for m in [1..#R1] do 
      r := R1[m]; 
      for i in [0..E1[m]] do
         for j in [0..E1[m]] do
            for k in [1..E1[m] - j] do 
               K := GF (r^k);
               P := PolynomialRing (K); t := P.1;
               f := P!(t^2 - t + 1);
               roots := Roots (f);
               roots := [Integers () ! x[1] : x in roots];
               assert #roots eq 2;
               t := roots[1];
               Append (~C3[m], sub <GL(3, F) | Z(F, i, r), 
                U(F,j + k,r)^t * W(F,j + k,r), U(F,j,r), W(F,j,r)>); 
               Append (~C3[m], sub <GL(3, F) | Z(F, i, r), 
                U(F,j + k,r)^(1-t) * W(F,j + k,r), U(F,j,r), W(F,j,r)>); 
            end for;
         end for;
      end for;
   end for;

   L := [];

   /* all direct products where primes are distinct */
   M := [#C1[i] : i in [1..#R]];
   S := BackTrack (M);
   for index in S do 
      D := sub <GL(3, F) | [C1[j][index[j]]: j in [1..#index]]>;
      Append (~L, D);
   end for;

   /* run over primes in R_1 */
   for r1 in R1 do
      T := [];
      for r in R do 
         if r lt r1 then
            pos := Position (R, r);
            Append (~T, C1[pos]); 
         elif r gt r1 then 
            pos := Position (R, r);
            t := C1[pos];
            if r in R1 then 
               pos1 := Position (R1, r);
               t cat:= C3[pos1];
            end if;
            Append (~T, t);
         else 
            pos1 := Position (R1, r);
            Append (~T, C2[pos1]);
         end if;
      end for;
      /* all direct products */
      M := [#T[i] : i in [1..#T]];
      S := BackTrack (M);
      for index in S do 
         D := sub <GL(3, F) | [T[j][index[j]]: j in [1..#index]]>;
         Append (~L, D);
      end for;
   end for;

   return L;
end function;

/* S3-modules from Thm 5.5 (ii) */

S3Modules := function (F, r)

   q := #F;
   ell := Valuation (q - 1, r);

   if r ne 3 then 
      L := [];
      for i in [0..ell] do
         for j in [0..ell] do
            Append (~L, sub <GL(3, F) | Z(F, i, r), U(F, j, r), W(F, j, r)>); 
         end for;
      end for;
      return L; 
   end if;

   /* case i = j = 0 */
   L := [sub < GL(3, F) | >];

   for i in [1..ell] do
      for j in [1..ell] do
         Append (~L, sub <GL(3, F) | Z(F, i, 3), U(F, j, 3), W(F, j, 3)>); 
      end for;
   end for;

   for i in [1..ell] do
      for j in [0..ell] do
         Append (~L, sub <GL(3, F) | Z(F, i, 3), 
             U(F, j + 1, 3)^2 * W(F, j + 1, 3), U(F, j, 3), W(F, j, 3)>); 
      end for;
   end for;

   for i in [1..ell] do
      for j in [1..ell] do
         Append (~L, sub <GL(3, F) | Z(F, i + 1, 3) *
             U(F, j + 1, 3)^2 * W(F, j + 1, 3), U(F, j, 3), W(F, j, 3)>); 
         Append (~L, sub <GL(3, F) | Z(F, i + 1, 3)^2 *
             U(F, j + 1, 3)^2 * W(F, j + 1, 3), U(F, j, 3), W(F, j, 3)>); 
      end for;
   end for;

   return L;

end function;

/* List described by Thm 5.14 */


   flag, p, n := IsPrimePower (q);
   if not flag then error "Input must be field size"; end if;
   if p eq 2 then
      "For monomial list, field must have odd characteristic"; 
      return [];
   end if;

   rou_set := {@ @};
   rou_list := [* *];

   F := GF (q);
   q := #F;
   primes := PrimeBasis (q - 1);
   t := Valuation (q - 1, 3);

   /* non-trivial {2, 3}'-modules for S3 */
   M := [S3Modules (F, r): r in primes | r ne 2 and r ne 3];
   LM := [#M[i] : i in [1..#M]];

   /* all direct products where primes are distinct */
   S := BackTrack (LM);
   L := [];
   for index in S do
      D := sub <GL(3, F) | [M[j][index[j]]: j in [1..#index]]>;
      Append (~L, D);
   end for;

   if exists {l : l in L | IsScalarGroup (l)} then 
      scalar := ListS (F : Scalar := true);
   end if;
   if exists {l : l in L | not IsScalarGroup (l)} then 
      non := ListS (F : Scalar := false);
   end if;

   /* complete list where pi G = S_3 following Thm 5.14 (ii) */
   K := [];
   for l in L do 
      if IsScalarGroup (l) then X := scalar; else X := non; end if;
      for i in [1..#X] do 
         x := X[i];
         Append (~K, sub <GL(3, F) | Generators (l), Generators (x)>);
      end for;    
      // "len is now ", #K;
   end for;

   /* restricted list of non-trivial 3'-modules for C */
   RestrictedL := SpecialList (F);
         
   c := GL(3, F) ! [0,1,0,0,0,1,1,0,0];
   K cat:= [sub <GL(3, F ) | c, l > : l in RestrictedL | not IsScalarGroup (l)];
   if t eq 0 then return K; end if;

   /* non-trivial 3'-modules for C */
   M := [CModules (F, r): r in primes | r ne 3];
   LM := [#M[i] : i in [1..#M]];

   /* all direct products where primes are distinct */
   S := BackTrack (LM);
   L := [];
   for index in S do
      D := sub <GL(3, F) | [M[j][index[j]]: j in [1..#index]]>;
      Append (~L, D);
   end for;

   /* first entry in Complete is c and we've already processed it */
   Complete, restrict, nonscalar := ListC (F : Scalar := false);

   /* set up list following Thm 5.14 (i) */
   for i in [2..#Complete] do 
       x := Complete[i];
       if i in restrict then
          for j in [1..#RestrictedL] do 
             l := RestrictedL[j]; 
             if IsScalarGroup (l) and i in nonscalar then continue; end if;
             Append (~K, sub <GL(3, F) | Generators (l), Generators (x)>);
          end for;
       else 
          for j in [1..#L] do 
             l := L[j]; 
             if IsScalarGroup (l) and i in nonscalar then continue; end if;
             Append (~K, sub <GL(3, F) | Generators (l), Generators (x)>);
          end for;
       end if;
   end for;

   return K;

end function;
