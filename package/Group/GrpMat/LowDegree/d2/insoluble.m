freeze;

/* insoluble with central quotient A5 for characteristic p >= 5 */

A5List := function (q)

   F := GF (q);
   p := Characteristic (F);

   if IsEven (p) then 
      "For A5 list, field must have odd characteristic"; return []; 
   end if;

   if p eq 3 then 
      /* one of q - 1, q + 1, q must be divisible by 5 
         for order of group to be divisible by 60;
         for char 3, this can only be true if n is even */
      n := Ilog (p, q);
      if IsEven (n) then 
         "A5 list not complete for characteristic 3"; 
         return []; 
      end if;
   end if;

   if (q mod 5 in {2, 3}) then return []; end if;

   f := PrimitiveElement (F);
   qm1 := q - 1;
   D := Divisors (qm1);
   E := [f^(qm1 div x) : x in D | IsEven (x)];

   if p eq 5 then
      S := SL (2, 5);
      S := [Eltseq (x) : x in Generators (S)];
      return [sub < GL(2, F) | S, ScalarMatrix (2, x)>: x in E];
   end if;

   K := GF (p^2);

   m := Lcm (Degree (F), Degree (K));
   M := GF (p, m); 

   w := RootOfUnity (4, K);
   beta := SquareRoot (K!5);

   /* subgroup generated by s, d, v is SL(2, 5) */
   s := GL(2, K)! [(w - 1)/2, (w - 1)/2, (1+w)/2, -(1 + w)/2];
   v := GL(2, K)! [(w)/2, ((1 - beta)/ 2 - w * (1 + beta)/2)/2, 
          ((-1 + beta)/2 - w * (1 + beta)/2)/2, (-w)/2];
   d := GL(2, K)! DiagonalMatrix ([w, -w]);
   
   X := [sub <GL(2, M) | s, d, v, ScalarMatrix (2, e)>: e in E];

   L := [];
   for x in X do
      if BaseRing (x) ne F then 
         flag, G := IsOverSmallerField (x, Degree (F) : Scalars := false);
      else 
         flag := true; G := x; 
      end if;
      if flag then Append (~L, G); end if;
   end for;

   return L;
     
end function;

/* insoluble with central quotient PGL (2, p^k) and PSL (2, p^k),
   for p^k dividing q = p^ell, p odd */

ProjectiveList := function (q)

   F := GF (q);
   p := Characteristic (F);
   if IsEven (p) then 
      "For PGL and PSL list, field must have odd characteristic"; 
      return []; 
   end if;

   if q eq 3 then return []; end if;

   if q eq 5 then 
      S := SL (2, 5);
      return [S, sub <GL(2, F) | S, DiagonalMatrix ([4, 1])>, GL(2, 5)];
   end if;
   
   alpha := PrimitiveElement (F);
   ell := Ilog (p, q);
   min := 3;
   qbar := Divisors (ell);
   qbar := [p^x: x in qbar];
   qbar := [x : x in qbar | x gt min];

   qm1 := q - 1;
   divqm1 := [j : j in Divisors (qm1) | IsEven (qm1 div j)];

   L := [];
   for m in qbar do 
      S := SL(2, m);
      S := [Eltseq (x): x in Generators (S)];
      r := qm1 div (m - 1); 
      for j in divqm1 do 
         b := ScalarMatrix (2, alpha^(j));
         if p ne 5 or m ne 5 then 
            H := sub <GL(2, F) | b, S>;
            Append (~L, H);
         end if;
         if IsEven (r) then 
            a := DiagonalMatrix ([alpha^(r div 2), alpha^(-r div 2)]);
            H := sub <GL(2, F) | a, b, S>;
            Append (~L, H);
         end if;
         if IsEven (j + r) then 
            a := DiagonalMatrix ([alpha^((j + r) div 2), alpha^((j - r) div 2)]);
            H := sub <GL(2, F) | a, b, S>;
            Append (~L, H);
         end if;
      end for;
   end for;
         
   return L;
end function;
      
/* insoluble list for char p >= 5; only A5 list is missing for p = 3 */

Degree2InsolubleList := function (q)

   if IsEven (q) then 
      "For insoluble list, field must have odd characteristic"; 
      return [];
   end if;

   /* coincidences in the two lists for q = 5 */
   if q eq 5 then 
       S := SL (2, 5);
       return [S, sub <GL(2, 5) | S, DiagonalMatrix ([4, 1])>, GL(2, 5)], [];
   end if;

   return A5List (q) cat ProjectiveList (q);

end function;
