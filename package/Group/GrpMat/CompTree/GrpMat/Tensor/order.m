freeze;

import "../Smash/numbers.m": OrderMod, PrimePowers, CoPrimeFactorisations;
// import "../Smash/random.m": RandomElement;
import "is-projectivity.m": IsMatrixProjectivity;

/* return partitions of set S into subsets */

SetPartitions := function (SS)

   S := SS;

   if #S eq 1 then 
      return {{S}};
   else
      x := Random (S);
      Exclude (~S, x);
      P := $$(S);
      Q := {};
      for X in P do 
         for T in X do 
            Q := Q join {X diff {T} join {T join {x}}}; 
         end for;
         Q := Q join {X join {{x}}};
      end for;
      return Q;
   end if;

end function;

/* return the sum of the lcms of the elements of X */

Score := function (X)

   return &+[Lcm (SetToSequence (T)) : T in X];

end function;

/* returns the least d such that GL(d, q) has an element 
   of order n and the corresponding factorisation of n;
   Gcd (n, q) = 1 */

LeastLinearSemiSimple := function (n, q)

   p := Factorisation (q)[1][1];

   f := Factorisation (n);
   
   /* for each prime-power factor of n, store the least d
      such that GL(d, q) has an element of this order */
      
   orders := {OrderMod (q, f[i][1]^f[i][2]) : i in [1..#f]};

   /* also need to remove divisors */
   for x in orders do 
      for y in orders do 
         if x lt y and y mod x eq 0 then Exclude (~orders, x); end if;
      end for;
   end for;

   if #orders eq 0 then return 1, 1; end if;

   S := SetPartitions (orders);
   S := SetToSequence (S);

   scores := [Score (x) : x in S];
   
   /* minimise partition score subject to maximising number of parts */

   least := scores[1]; nparts := #S[1];
   for i in [2..#scores] do 
      if (scores[i] le least) and (#S[i] gt nparts) then 
         least := scores[i];
         nparts := #S[i];
      end if;
   end for;

   return least, nparts;

end function;

LeastProjectiveSemiSimple := function (n, q)

   if Gcd (n, q) ne 1 then return false; end if;

   if n eq 1 then return 1; end if;
   
   u, m := LeastLinearSemiSimple (n, q);

   if m gt 1 then return u; end if;

   if ((q^u - 1) div (q - 1)) mod n eq 0 then return u; end if;

   return u + 1;

end function;

/* find smallest d such that PGL(d, q) can contain an element 
   of projective order n */

LeastProjective := function (n, q)

   /* write n = p^alpha * m */
  
   p := Factorisation (q)[1][1];

   /* find p'-part of projective order n */

   f := Factorisation (n);
   primes := [f[i][1] : i in [1..#f]];

   index := Position (primes, p);
   if index gt 0 then 
      alpha := f[index][2];
      factor := 1 + p^(alpha - 1);
      Remove (~f, index);
   else 
      alpha := 0;
      factor := 1;
   end if;
    
   /* p'-part of projective order */
   m := FactorizationToInteger (f);

   if alpha eq 0 then 
      return LeastProjectiveSemiSimple (m, q);
   elif m eq 1 then 
      return factor; 
   else 
      return factor + LeastLinearSemiSimple (m, q);
   end if;

end function;

/* take prime powers of n; compute scores for elements having 
   these prime power orders; choose prime with largest score 
   as best prime */

FindBestPrime := function (n, q)
   
   D := PrimePowers (n);

   Score := [LeastProjective (D[i] * D[i + 1], q) : i in [1..#D by 2]];
   max, index := Maximum (Score);

   p := D[2 * (index - 1) + 1];
   s := D[2 * index];

   return p, s;

end function;

/* is there a co-prime factorisation of n as k * l such 
   that Score (k * m) <= DimU and Score (l * m) <= DimW ? */

ExistsFactorisation := function (n, m, d, q, DimU, DimW: Limit := 10^3)

   /* find co-prime factorisations of n */
   P := CoPrimeFactorisations (n);

   vprintf Tensor: "Number of coprime factorisations is %o\n", #P;

   if #P gt Limit then return "unknown"; end if;

   /* is there is a valid co-prime factorisation of n? 
      -- that is, one whose components fit into each side */

   for x in P do
      vprintf Tensor: "Processing order factorisation %o\n", x;
      u := [LeastProjective (x[i] * m, q) : i in [1..2]];

      y := [x[i] * m : i in [1..2]];
      vprintf Tensor: "Score for %o = %o\n", y, u; 

      // is DimU >= u[1] and DimW >= u[2] or vice versa? 
      // EOB -- fix to include both options Nov 2012 
      if ((u[1] le DimU) and (u[2] le DimW)) or
         ((u[1] le DimW) and (u[2] le DimU)) then 
         return true;
      end if;

   end for;

   return false;
end function;

/* can an element g of order n rule out possible tensor 
   factorisation DimU x DimW of a subgroup of GL (d, q)? 
   TestedPrimes records the prime order elements obtained 
   as powers of g which are not projectivities */

PossibleFactorisation := function (G, g, nn, d, q, DimU, DimW, List, 
                                   TestedPrimes)

   n := nn; m := 1; Primes := TestedPrimes; 

   flag := ExistsFactorisation (n, m, d, q, DimU, DimW);
   if flag cmpeq "unknown" then return "unknown", _; end if;

   while flag do 

      p, s := FindBestPrime (n, q);
      h := g^((m * n) div p);
      vprintf Tensor: "Projective order of possible scalar element is %o\n", 
            ProjectiveOrder (h); 

      // Result, T := SmashElement (G, h);

      if not (h in Primes) then 
         D := Set (&cat List);
         IsMatrixProjectivity (G, h, D, ~Result, ~CB);
         if Result cmpeq true then return CB, Primes; end if;
         if Result cmpeq "unknown" then return "unknown", Primes; end if;
         Include (~Primes, h);
      end if;

      /* we can now conclude that if there is such a tensor decomposition, 
         then an element of order m acts as a non-scalar on both factors */
      n := n div p^s; m := m * p^s;
      vprintf Tensor: "n is now %o m is now %o\n", n, m;

      flag := ExistsFactorisation (n, m, d, q, DimU, DimW);

   end while;

   return flag, Primes;
   
end function;

/* generate random elements and try to decide whether an element 
   of projective order n rules out any possible tensor factorisation
   of a subgroup of GL (d, q) */

procedure OrderTest (G, N, ~List, ~Record, ~Result) 

   F := BaseRing (G);
   d := Degree (G);
   q := #F;

   Result := false;
   NmrElts := 0; 
   Record := []; 
   Tested := [];

   TestedPrimes := {};

   /* generate N random elements and compute their scores */
   P := RandomProcess (G);
   repeat
      g := Random (P);
      NmrElts +:= 1;
      n := ProjectiveOrder (g);

      if Position (Tested, n) ne 0 then continue; end if;

      vprintf Tensor: "\nProcessing Element #%o of projective order %o\n", NmrElts, n;

      /* what is smallest dimension which can contain 
         element of projective order n? */
      MinScore := LeastProjective (n, q);
      Append (~Record, <g, n>);
      Append (~Tested, n);

      /* now consider each possible factorisation of d as u x w
         and decide whether such a factorisation of d is compatible 
         with an element of projective order n */

      for f in List do
         u := f[1]; w := f[2];
         vprintf Tensor: "\nConsider dimension factorisation u = %o  w = %o\n",u, w;

         /* does the element fit into each factor? */
         if (MinScore le u) and (MinScore le w) then 
            vprintf Tensor: "Element of projective order %o fits into both factors\n", n;
            /* then the element fits into all other factors as well */
            break f;
         else 
            /* the element doesn't fit into both factors; 
               however, there may exist a coprime factorisation; 
               we may also be able to conclude that the element can't 
               act in desired manner by calls to IsProjectivity */

            Result, TestedPrimes := PossibleFactorisation 
                    (G, g, n, d, q, u, w, List, TestedPrimes); 

            /* may have found a tensor decomposition */
            if Type (Result) eq Tup then
               return;

            /* or ruled out a possible decomposition */
            elif Result cmpeq false then 
               vprint Tensor: "No valid score exists for dimension factorisation ", f;
               Exclude (~List, f);

            elif Result cmpeq "unknown" then
               TestedPrimes := {}; break f; 
            end if;

         end if;
      end for;
   until (#List eq 0) or (NmrElts ge N) or (Result cmpeq true);
end procedure;
