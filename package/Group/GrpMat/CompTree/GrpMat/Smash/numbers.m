freeze;

/* return set of proper divisors of n */

ProperDivisors := function (n)

  return Set (Divisors (n)) diff {1, n};

end function;

/* return prime factorisation p^a * q^b * .. as sequence [p, a, q, b, ..]  */

PrimePowers := function (n)

   local i, f, factors;

   f := Factorisation (n);
   factors := [];
   for i in [1..#f] do
      factors[2 * i - 1] := f[i][1];
      factors[2 * i] := f[i][2];
   end for;

   return factors;

end function;

/* given [a, b, c, d, ..], return a^b * c^d * .. */

FactorsToInteger := function (S)

   if #S eq 0 then return 0; end if;
   return &*[S[i]^S[i + 1] : i in [1..#S by 2]];

end function;

/* compute gcd of two numbers given by their prime factorisations A and B */

GcdSeq := function (A, B)

   local found, prime, C, D, i, j, lenA, lenB;

   D := A;

   lenA := #A div 2;
   lenB := #B div 2;

   for i in [1..lenA] do
      
      found := false;
      prime := D[2 * i - 1];
      j := 1;
      while (j le lenB) and (not found) do
         if B[2 * j - 1] eq prime then
            D[2 * i] := Minimum (D[2 * i], B[2 * j]); 
            found := true;
         end if;
         j +:= 1;
      end while;
      if not found then 
         D[2 * i] := 0;
      end if;
   end for;

   C := [1, 1];
   j := 1;
   for i in [1..lenA] do
      if D[2 * i] ne 0 then
         C[j] := D[2 * i - 1];
         C[j + 1] := D[2 * i];
         j +:= 2;
      end if; 
   end for; 
  
   return C;

end function; 

/* compute lcm of two numbers given by their prime factorisations A and B */

LcmSeq := function (A, B) 
   
   local found, D, i, j, prime, lenA, lenB;

   lenA := #A div 2;
   lenB := #B div 2;

   D := A;
   for i in [1..lenA] do
      found := false;
      prime := D[2 * i - 1];
      j := 1;
      while (j le lenB) and not found do
         if B[2 * j - 1] eq prime then
            D[2 * i] := Maximum (D[2 * i], B[2 * j]); 
            found := true;
         end if; 
         j +:= 1;
      end while; 
   end for;

   /* add in any primes which occur in B but not in A */

   for i in [1..lenB] do
      found := false;
      prime := B[2 * i - 1];
      j := 1;
      while (j le lenA) and not found do
         found := (D[2 * j - 1] eq prime);
         j +:= 1;
      end while; 

      if (not found) then 
         D[2 * lenA + 1] := prime;
         D[2 * lenA + 2] := B[2 * i];
         lenA +:= 1;
      end if; 
   end for; 

   return D;

end function;

/* given sequence x, return sorted sequence which contains
   an entry of x together with its multiplicity */

Collected := function (x)

   local k, list, y, z, i, l;

   k := Set (x);
   list := [];
   l := [];

   for i in k do 
      l[1] := i;
      l[2] := #[ z : z in x | z eq i];
      Append (~list, l);
   end for;

   return Sort (list);

end function;

/* restricted partions of n -- those which can be obtained 
   from elements of Q */

RestrictedPartitions := function (n, Q)

    local p, i, x, xQ, nn;

    if n eq 0 then
        return [[]];
    end if;

    p := [];
    for i := #Q to 1 by -1 do
        x := Q[i];
        Prune (~Q);
        nn := n;
        xQ := [];
        while nn ge 0 do
            nn -:= x;
            Append (~xQ, x);
            p cat:= [xQ cat p: p in $$(nn, Q)];    
        end while;
    end for;

    return p;

end function;

/* compute the inverse mod d of each element of Set */
 
InverseSet := function (d, Set)
   
   return {d div x: x in Set};

end function;

/* given n and prime p, write n = p^alpha * m, return alpha and m */

PairOfFactors := function (n, p)

   /* find p'-part of n */

   f := Factorisation (n);
   primes := [f[i][1] : i in [1..#f]];

   index := Position (primes, p);
   if index gt 0 then
      alpha := f[index][2];
      Remove (~f, index);
   else
      alpha := 0;
   end if;

   /* p'-part of n */
   m := FactorizationToInteger (f);

   return alpha, m;

end function;

/* compute the order of m mod n */

OrderMod := function (m, n)

   if n eq 1 then return 0; end if;
   if Gcd (m, n) ne 1 then
        return 0;
   end if; 
   return Order (m, n);

end function;

/* return factorisations of n into ordered pairs */

FactorList := function (n)
   D := Divisors (n);
   s := Isqrt (n);
   return [[x, n div x]: x in D | x le s];
end function;

/* find co-prime factorisations of n */

CoPrimeFactorisations := function (n)

   /* find co-prime factorisations of n */
   L := FactorList (n);
   return [x : x in L | Gcd (x[1], x[2]) eq 1];

end function;

/* return primitive root of GF (n) */

Z := function (n)

   F := GF (n);
   return PrimitiveElement (F);

end function;

/* return the log of x in the field F */

LogQ := function (F, x)

   if x eq F!0 then return #F - 1; end if;
   return Log (x);

end function;
