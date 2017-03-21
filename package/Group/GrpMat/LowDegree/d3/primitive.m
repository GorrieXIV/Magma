freeze;

/* Schur covers for C4 [case 1] and Q8 */

Covers := function (q: Case1 := true)
   F := GF (q);
   eta := PrimitiveElement (F);
   omega := RootOfUnity (3, F);
   E := F;
   gl := GL(3, E);

   MA := MatrixAlgebra (E, 3);
   c := MA![0,1,0,0,0,1,1,0,0];
   z := ScalarMatrix (3, omega);
   w := DiagonalMatrix ([1, omega, omega^2]);
   u := DiagonalMatrix ([omega, omega^2, 1]);
   v := MA ! [1, 1, 1, 1, omega, omega^2, 1, omega^2, omega];
   v := (omega - omega^2)^-1 * v;

   if Case1 eq true then 
      v2 := v;
      S := [sub< gl | v, c, z, u, w>, sub< gl | -v, c, z, u, w>];
      if q mod 4 eq 1 then 
         i := Root (F!-1, 2);
         S[3] := sub< gl | i * v, c, z, u, w>;
      end if;
   else 
      v2 := MA ! [1, omega, omega, omega^2, omega, omega^2, 
                  omega^2, omega^2, omega];
      v2 := (omega - omega^2)^-1 * v2;
      S := [sub< gl | v, v2, c, z, u, w>, sub< gl | v, -v2, c, z, u, w>];
   end if;
   
   return S, v, v2, c, u;
end function;

/* C_4 case for odd characteristic */

PrimitiveListI := function (q) 

   if IsEven (q) then return []; end if;
   if q mod 3 ne 1 then return []; end if;

   F := GF (q);
   p := Characteristic (F);

   S, v, v2, c, u := Covers (q);
   eta := PrimitiveElement (F);
   qm1 := q - 1;
   D := Divisors (qm1);
   L := [eta^(qm1 div x): x in D];

   X := [ScalarMatrix (3, x) : x in L | IsOdd (Order (x)) and 
         Valuation (Order (x), 3) ne 1];
   Y := [ScalarMatrix (3, x) : x in L | Order (x) mod 4 eq 2
         and Valuation (Order (x), 3) ne 1];
   Z := [ScalarMatrix (3, x) : x in L | Order (x) mod 4 eq 0 
         and Valuation (Order (x), 3) ne 1];

   P := BaseRing (Rep (S));
   gl := GL(3, P);
   if q mod 8 eq 1 then 
      mu := RootOfUnity (8, F);
   end if;

   L := [];

   for x in X do 
      L cat:= [sub <gl | S[1], x>];
      L cat:= [sub <gl | S[2], x>];
      if q mod 4 eq 1 then 
         L cat:= [sub <gl | S[3], x>];
      end if;
   end for;

   for x in Y do 
      L cat:= [sub <gl | S[1], x>];
      if q mod 4 eq 1 then 
         L cat:= [sub <gl | S[3], x>];
      end if;
      if q mod 8 eq 1 then 
         L cat:= [sub <gl | mu * v, c, u, x>];
      end if;
   end for;

   for x in Z do 
      L cat:= [sub <gl | S[1], x>];
      if q mod 8 eq 1 then 
         K := AllRoots (F!x[1][1], 4);
         if #K ne 0 then 
            kappa := Rep (K); 
            L cat:= [sub <gl | kappa * v, c, u, x>];
            L cat:= [sub <gl | kappa^2 * v, c, u, x>];
         end if;
      end if;
   end for;

   return L;
end function;

/* Q_8 case for odd characteristic */

PrimitiveListII := function (q) 

   if IsEven (q) then return []; end if;
   if q mod 3 ne 1 then return []; end if;

   F := GF (q);
   p := Characteristic (F);

   S, v, v2, c, u := Covers (q: Case1 := false);
   eta := PrimitiveElement (F);
   qm1 := q - 1;
   D := Divisors (qm1);
   L := [eta^(qm1 div x): x in D];

   X := [ScalarMatrix (3, x) : x in L | IsOdd (Order (x)) and 
         Valuation (Order (x), 3) ne 1];
   Y := [ScalarMatrix (3, x) : x in L | IsEven (Order (x))
         and Valuation (Order (x), 3) ne 1];

   P := BaseRing (Rep (S));
   gl := GL(3, P);

   L := [];

   for x in X do 
      L cat:= [sub <gl | S[1], x>];
      L cat:= [sub <gl | S[2], x>];
   end for;

   for x in Y do 
      L cat:= [sub <gl | S[1], x>];
      if q mod 4 eq 1 then 
         R := AllRoots (F!x[1][1], 2);
         if #R gt 0 then 
            tau := Rep (R);
            L cat:= [sub <gl | tau * v, v2, c, u, x>];
         end if;
      end if;
   end for;

   return L;
end function;

/* Schur covers for SL(2, 3) */

CoversIII := function (q) 
   F := GF (q);

   eta := PrimitiveElement (F);
   omega := RootOfUnity (3, F);
   E := GF(q^3);
   gl := GL(3, E);

   MA := MatrixAlgebra (E, 3);
   c := MA![0,1,0,0,0,1,1,0,0];
   z := ScalarMatrix (3, omega);
   w := DiagonalMatrix ([1, omega, omega^2]);
   u := DiagonalMatrix ([omega, omega^2, 1]);
   v := MA ! [1, 1, 1, 1, omega, omega^2, 1, omega^2, omega];
   v := (omega - omega^2)^-1 * v;

   v2 := MA ! [1, omega, omega, omega^2, omega, omega^2, omega^2, omega^2, omega];
   v2 := (omega - omega^2)^-1 * v2;

   epsilon := Root (E!omega^2, 3);
   v3 := DiagonalMatrix ([epsilon * omega^-1, epsilon, epsilon]);

   t := Valuation (q - 1, 3);
   
   L := []; Mu := [];
   for i in [1..t] do 
      x := ScalarMatrix (3, eta^((q - 1) div (3^i)));
      mu := Root (E!x[1][1]^(1 - 2 * 3^(i - 1)), 3);
      S := [sub< gl | v, v2, v3, c, x, u, w>,
            sub< gl | v, v2, mu * v3, c, x, u, w>,
            sub< gl | v, v2, mu^2 * v3, c, x, u, w>];
      L cat:= S;
      Append (~Mu, mu);
   end for;

   return L, Mu, epsilon;
end function;

/* SL23 case */

PrimitiveListIII := function (q) 

   if q mod 3 ne 1 then return []; end if;

   F := GF (q);
   p := Characteristic (F);

   S, Mu, epsilon := CoversIII (q);
   eta := PrimitiveElement (F);
   qm1 := q - 1;
   D := Divisors (qm1);
   L := [eta^(qm1 div x): x in D];

   X := [ScalarMatrix (3, x) : x in L | Valuation (Order (x), 3) eq 0];

   P := BaseRing (Rep (S));
   gl := GL(3, P);
   small := GL(3, F);

   L := [];

   for x in X do 
      for i in [1..#S div 3] do 
         if q mod 9 eq 1 then 
            H := sub <gl | S[3 * (i - 1) + 1], x>;
            L cat:= [sub <small | [Eltseq (H.i): i in [1..Ngens (H)]]>];
         end if;
         mu := Mu[i]; 
         if epsilon * mu in F then 
            H := sub <gl | S[3 * (i - 1) + 2], x>;
            L cat:= [sub <small | [Eltseq (H.i): i in [1..Ngens (H)]]>];
         end if;
         if epsilon * mu^2 in F then 
            H := sub <gl | S[3 * (i - 1) + 3], x>;
            L cat:= [sub <small | [Eltseq (H.i): i in [1..Ngens (H)]]>];
         end if;
      end for;
   end for;

   return L;
end function;

/* return list of soluble absolutely irreducible primitive
   subgroups of GL(3, q) for odd characteristic */

PrimitiveList := function (q)

   flag, p, n := IsPrimePower (q);
   if not flag then error "Input must be field size"; end if;
   if p eq 2 then
      "For primitive list, field must have odd characteristic"; return [];
   end if;
   return PrimitiveListI (q) cat PrimitiveListII (q) 
          cat PrimitiveListIII (q);
end function;
