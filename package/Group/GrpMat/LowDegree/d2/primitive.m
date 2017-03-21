freeze;

/* does there exist n-th root of a which is not a power of a? */

DistinctRoot := function (a, n)
   R := AllRoots (a, n);
   o := Order (a);
   if exists (r) {r : r in R | o mod Order (r) ne 0} then 
      return true, r;
   else 
      return false, _;
   end if;
end function;

/* soluble absolutely irreducible primitive subgroups 
   of GL(2, q) extensions of A_4, characteristic >= 5  */

PrimitiveListI := function (q)

   if IsEven (q) then return []; end if;

   if q mod 3 eq 0 then 
      "Primitive absolutely irreducible list for A_4 and char 3 not available"; 
      return []; 
   end if;

   F := GF (q);
   alpha := PrimitiveElement (F);

   qm1 := q - 1;
   D := Divisors (qm1);
   E := [alpha^(qm1 div x) : x in D | IsEven (x)];

   L := [];
   if q mod 4 eq 1 then 
      w := alpha^(qm1 div 4); 
      W := DiagonalMatrix ([w, -w]);
      s := GL(2, F) ! [(w - 1)/2, (w - 1)/2, (w + 1)/2, -(w + 1)/2];
      for z in E do 
         Append (~L, sub <GL(2, F) | W, s, DiagonalMatrix ([z, z])>); 
         flag, v := DistinctRoot (F!z, 3);
         if flag then 
            v := GL(2, F) ! DiagonalMatrix ([v, v]);
            Append (~L, sub <GL(2, F) | W, v * s>);
         end if;
      end for;
   end if;

   if q mod 4 eq 3 then 
      N := ext <F | 2>;
      beta := PrimitiveElement (N);
      w := beta^((q^2 - 1) div 4); 
      W := DiagonalMatrix ([w, -w]);
      s := GL(2, N) ! [(w - 1)/2, (w - 1)/2, (w + 1)/2, -(w + 1)/2];
      for z in E do 
         G := sub <GL(2, N) | W, s, DiagonalMatrix ([z, z])>; 
         flag, H := IsOverSmallerField (G: Scalars := false);
         if flag then Append (~L, H); end if;
         flag, v := DistinctRoot (F!z, 3);
         if flag then 
            v := GL(2, N) ! DiagonalMatrix ([v, v]);
            G := sub <GL(2, N) | W, v * s>;
            flag, H := IsOverSmallerField (G: Scalars := false);
            if flag then Append (~L, H); end if;
         end if;
      end for;
   end if;

   return L;

end function;

/* soluble absolutely irreducible primitive subgroups 
   of GL(2, q), extensions of S_4, characteristic >= 5 */

PrimitiveListII := function (q)

   if IsEven (q) then return []; end if;
   if q mod 3 eq 0 then 
      "Primitive absolutely irreducible list for S_4 and char 3 not available"; 
      return []; 
   end if;

   F := GF (q);
   eta := PrimitiveElement (F);
   N := ext <F | 2>;
   qm1 := q - 1;
   D := Divisors (qm1);
   E := [eta^(qm1 div x) : x in D | IsEven (x)];

   alpha := Root (N!2, 2); member := alpha in F;
   w := Root (N!-1, 2);

   s := [(1 - w)/2, (-w - 1)/2, (-w + 1)/2, (w + 1)/2];
   u := GL (2, N) ! [(1 - w)/alpha, 0, 0, (w + 1)/alpha];

   L := [];
   if q mod 4 eq 1 then 
      for z in E do 
         m := DiagonalMatrix ([z, z]); 
         if member then 
            Append (~L, sub <GL(2, F) | s, u, m>);
         end if;
         flag, v := DistinctRoot (N!z, 2);
         if flag and alpha * v in F then 
            v := GL(2, N) ! DiagonalMatrix ([v, v]);
            Append (~L, sub <GL(2, F) | s, v * u, m>);
         end if;
      end for;
   end if;

   if q mod 4 eq 3 then 
      for z in E do 
         m := DiagonalMatrix ([z, z]); 
         if member then
            G := sub <GL(2, N) | s, u, m>;
            flag, H := IsOverSmallerField (G: Scalars := false);
            if flag then Append (~L, H); end if;
         end if; 
         flag, v := DistinctRoot (N!z, 2);
         if flag and alpha * v in F then 
            v := N!v;
            v := GL(2, N) ! DiagonalMatrix ([v, v]);
            G := sub <GL(2, N) | s, v * u, m>;
            flag, H := IsOverSmallerField (G: Scalars := false);
            if flag then Append (~L, H); end if;
         end if;
      end for;
   end if;

   return L;

end function;

/* soluble absolutely irreducible primitive subgroups 
   of GL(2, q) for characteristic at least 5 */

Degree2PrimitiveList := function (q)

   flag, p, n := IsPrimePower (q);
   if not flag then error "Input must be field size"; end if;
   if p le 3 then 
      "For primitive list, field must have characteristic at least 5"; return []; 
   end if;

   return PrimitiveListI (q) cat PrimitiveListII (q);

end function;
