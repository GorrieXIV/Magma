freeze;

/***************************************************************/
/*   Recognise quasi-simple group of Lie type when             */
/*   characteristic is given                                   */
/*                                                             */
/*   Babai, Kantor, Palfy and Seress (2002) J. Group Theory;   */
/*   Altseimer & Borovik (2001) Ohio Conference Proceeding     */
/*   provide theoretical basis for algorithms
/*                                                             */
/*   this version developed by Malle & O'Brien March 2001      */
/*   latest version May 2007                                   */
/*                                                             */
/***************************************************************/

import "identify.m": IsGoodInput;
import "../../GrpMat/util/order.m": MyCentralOrder;

SampleSize := 250; /* largest sample considered */
NmrTrials := 10;   /* repeated sampling */

// classical type output converted to LieType output 
ClassicalTypeToLieType := function (G)
   type := ClassicalType(G);

   case type:
   when "linear":
      name := <"A", Degree(G) - 1, #CoefficientRing(G)>;
   when "symplectic":
      name := <"C", Degree(G) div 2, #CoefficientRing(G)>;
   when "unitary":
      name := <"2A", Degree(G) - 1, Isqrt (#CoefficientRing(G))>;
   when "orthogonalcircle":
      name := <"B", (Degree(G) - 1) div 2, #CoefficientRing(G)>;
   when "orthogonalplus":
      name := <"D", Degree(G) div 2, #CoefficientRing(G)>;
   when "orthogonalminus":
      name := <"2D", Degree(G) div 2, #CoefficientRing(G)>;
   end case;

   return name;
end function;


NoGood := function (n)
//  if n eq 5 then return "too many tries in Distinguish";
//  elif n eq 6 then return "not unitary";
//  elif n eq 8 then return "v3 is wrong";
//  elif n eq 9 then return "maxprime";
//  else
   return false, n;
//  end if;
//     return "not characteristic p-type group";
end function;  // NoGood

LargestPrimeOccurs := function (r, orders);
   f := Factorization (r);
   maxp := Maximum ({i[1] : i in f});
   return {i : i in orders | i mod maxp eq 0} ne {};
end function; // LargestPrimeOccurs

/* check whether the computed orders all divide permitted orders  */

VerifyOrders := function (type, n, q, orders)

   p := Factorization (q)[1][1];
   allowed := orders; maxprime := true;

   if type eq "L" then
      if n eq 2 then
         if p eq 2 then
	   allowed := {2, q-1, q+1};
	else
	   allowed := {p, (q-1) div 2, (q+1) div 2};
	end if;
      elif n eq 3 then
         if (q-1) mod 3 ne 0 then
	   allowed := {4, p * (q-1), q^2-1, q^2+q+1};
         else
            allowed := {4, p * (q-1) div 3, q-1, (q^2-1) div 3, (q^2+q+1) div 3};
         end if;
      elif n eq 4 then
         if p eq 2 then
            allowed := {4 * (q-1), p * (q^2-1), q^3-1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
         elif p eq 3 then
            allowed := {9, p * (q^2-1), q^3-1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
         elif (q-1) mod 2 ne 0 then
	   allowed := {p * (q^2-1), q^3-1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
	elif (q-1) mod 4 eq 2 then
	   allowed := {p * (q^2-1), (q^3-1) div 2, (q^2+1) * (q-1) div 2, 
	              (q^2+1) * (q+1) div 2 };
	else
	   allowed := {p * (q^2-1), (q^3-1) div 4, (q^2+1) * (q-1) div 4, 
	              (q^2+1) * (q+1) div 4 };
	end if;
      elif n eq 5 and q eq 2 then
         allowed := {8, 12, 14, 15, 21, 31};
      elif n eq 6 and q eq 3 then
         allowed := {36, 78, 80, 104, 120, 121, 182};
	maxprime := 91 in orders or 121 in orders;
      else
         maxprime := LargestPrimeOccurs (q^n-1, orders)
	           and LargestPrimeOccurs (q^(n-1)-1, orders)
		   and Maximum (orders) le (q^n-1)/ (q-1)/Gcd (n, q-1);
         if n eq 8 and q eq 2 then
	   maxprime := maxprime and LargestPrimeOccurs (7, orders);
	end if;
      end if;
          
   elif type eq "U" then
      if n eq 3 then
         if (q+1) mod 3 ne 0 then
	   allowed := {4, p * (q+1), q^2-1, q^2-q+1};
         else
            allowed := {4, p * (q+1) div 3, q+1, (q^2-1) div 3, (q^2-q+1) div 3};
         end if;
      elif n eq 4 then
         if p eq 2 then
            allowed := {8, 4 * (q+1), p * (q^2-1), q^3+1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
         elif p eq 3 then
            allowed := {9, p * (q^2-1), q^3+1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
	   if q eq 3 then
	      maxprime := {8, 9} subset orders;
	   end if;
         elif (q+1) mod 2 ne 0 then
	   allowed := {p * (q^2-1), q^3+1, (q^2+1) * (q-1), (q^2+1) * (q+1)};
	elif (q+1) mod 4 eq 2 then
	   allowed := {p * (q^2-1), (q^3+1) div 2, (q^2+1) * (q-1) div 2, 
	              (q^2+1) * (q+1) div 2 };
	   if q eq 5 then
	      maxprime := Maximum (orders) gt 21;
            end if;
	else
	   allowed := {p * (q^2-1), (q^3+1) div 4, (q^2+1) * (q-1) div 4, 
	              (q^2+1) * (q+1) div 4 };
	end if;
      else
         r := 2 * ((n-1) div 2)+1;
         maxprime := LargestPrimeOccurs (q^r+1, orders)
                     and Maximum (orders) le (q^(r+1)-1)/ (q-1);
         if n eq 6 and q eq 2 then
            maxprime := maxprime and 18 in orders;
         end if;
      end if;

   elif type eq "S" then
      if n eq 4 then
        if q mod 2 eq 0 then
	   allowed := {4, p * (q-1), p * (q+1), q^2-1, q^2+1};
	elif q mod 3 eq 0 then
	   allowed := {9, p * (q-1), p * (q+1), (q^2-1) div 2, (q^2+1) div 2};
	else
	   allowed := {p * (q-1), p * (q+1), (q^2-1) div 2, (q^2+1) div 2};
	end if;
      elif n eq 6 and q eq 2 then
         allowed := { 7, 8, 9, 10, 12, 15 };
         maxprime := 8 in orders and 15 in orders;
      else
         maxprime := LargestPrimeOccurs (q^(n div 2)+1, orders) and
	             LargestPrimeOccurs (q^(n div 2)-1, orders);
      end if;
         
   elif type eq "O^+" and n eq 8 and q eq 2 then
      allowed := { 7, 8, 9, 10, 12, 15 };
      maxprime := 8 in orders and 15 in orders;
      
   elif type eq "O^+" and n eq 10 and q eq 2 then
      allowed := { 18, 24, 31, 42, 45, 51, 60};
      
   elif type eq "O^-" then
       maxprime := LargestPrimeOccurs (q^(n div 2)+1, orders) and
	           LargestPrimeOccurs (q^(n div 2 -1)-1, orders);
		 
   elif type eq "2B" then
      rq := Round (Sqrt (2 * q));
      allowed := {4, q-1, q-rq+1, q+rq+1};

   elif type eq "2G" then
      rq := Round (Sqrt (3 * q));
      allowed := {9, 3 * (q-1), q+1, q-rq+1, q+rq+1};

   elif type eq "G" then
      if p eq 2 then
         allowed := {8, 4 * (q-1), 4 * (q+1), q^2-1, q^2-q+1, q^2+q+1};
      elif p le 5 then
         allowed := {p^2, p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1};
      else
         allowed := {p * (q-1), p * (q+1), q^2-1, q^2-q+1, q^2+q+1};
      end if;

   elif type eq "2F" and q eq 2 then
      allowed := {10, 12, 13, 16};

   elif type eq "2F" and q eq 8 then
      allowed := {12, 16, 18, 20, 28, 35, 37, 52, 57, 63, 65, 91, 109};
      maxprime := Maximum (orders) gt 37;

   elif type eq "3D" and q eq 2 then
      allowed := {8, 12, 13, 18, 21, 28 };
      maxprime := Maximum (orders) gt 13;

   elif type eq "F" and q eq 2 then
      allowed := {13, 16, 17, 18, 20, 21, 24, 28, 30};

   elif type eq "2E" and q eq 2 then
      allowed := {13, 16, 17, 18, 19, 20, 21, 22, 24, 28, 30, 33, 35};

   elif type eq "E" and n eq 7 and q eq 2 then
      maxprime := Maximum (orders) le 255;
   end if;
   
   // output information according to Chevalley group classification
   case type:
      when   "L": type := "A";  n := n-1;
      when   "U": type := "2A"; n := n-1;
      when   "S": type := "C";  n := n div 2;
      when   "O": type := "B";  n := (n-1) div 2;
      when "O^+": type := "D";  n := n div 2;
      when "O^-": type := "2D"; n := n div 2;	 
      // EOB -- change in return value due to Taylor redefinition of 
      // ChevalleyGroup intrinsic -- both cases now take q as field size 
      // when  "2E": q := q^2;
      // when  "3D": q := q^3;
   end case;	
   
   if not maxprime then return NoGood (9); end if;

   for i in allowed do
      orders := {o : o in orders | i mod o ne 0};
   end for;
   if orders eq {} then
      return true, <type, n, q>;
   else
      return NoGood (1);
   end if;
  
end function; // VerifyOrders

forward ppdset;

/* version of Altseimer and Borovik algorithm to distinguish 
   orthogonal group B_n(q) = Omega(2n + 1, q) from symplectic group 
   C_n(q) = Sp(2n, q), where q = p^e, q odd, n >= 3;  
   this follows revised paper circulated by Borovik July 2001 */

DistinguishSpO := function (P, n, p, e, orders: Factor := 20, Effort := 10)

   vprint Identify: "Distinguish Sp from O";

   if n lt 3 then 
      "Lie rank must be at least 3"; 
      return "unknown", _;
    end if;

   q := p^e;
   if IsEven (q) then 
      "Characteristic must be odd"; 
      return "unknown", _;
   end if;

   // calculates 2-height of the order of element u
   twopart := function (u)
      k := 1;
      while (u mod 2) eq 0 do
         u div:= 2; k *:= 2;
      end while;
      return k;
   end function;
   
   // offset = -1 
   // finds the largest divisor of the number q^n-1 which
   // has no non-trivial divisors in common with any of the
   // numbers q^l-1 for l < n
   PrimitiveDivisor := function (q, n, offset)
      pd := q^n + offset;
      for i in [1..n-1] do
         l := q^i + offset;
         gcd := Gcd (pd, l);
         while gcd gt 1 do
            pd div:= gcd;
            gcd := Gcd (pd, gcd);
         end while;
      end for;
      
      return pd;
   end function;
   
   // finds all integers k where m is divisible by a 
   // primitive prime divisor of q^k-1
   OccurrencesOfPrimitiveDivisors := function (m)
      tuple := [0*x : x in [1..2*n]];
      for k in [1..2*n] do
         if Gcd (PrimitiveDivisor (q, k, -1), m) gt 1 then
            tuple[k] := k;
         end if;
      end for;
      return tuple;
   end function;
   
   // finds the maximal integer k <= 2n such that the order
   // of g is divisible by a primitive prime divisor of q^k-1 
   PDRankOfElement := function (g)
      return Max (OccurrencesOfPrimitiveDivisors (
             MyCentralOrder (Parent (g), g)));
   end function;
   
   // tests whether the element g is good or not
   IsGood := function (g)
      if (q^n-1) mod 4 eq 0 then 
         return (PDRankOfElement (g) eq n and
          twopart (MyCentralOrder (Parent (g), g)) eq (twopart ((q^n-1) div 2)));
      elif (q^n+1) mod 4 eq 0 then 
         return (PDRankOfElement (g) eq 2*n and
          twopart (MyCentralOrder (Parent (g), g)) eq (twopart ((q^n+1) div 2)));  
      else 
         return false;
      end if;	   
   end function;
   
   // find a good element 
   GoodElement := function (P, n)
      nmr := 0;
      repeat 
         g := Random (P);
         nmr +:= 1;
         flag := IsGood (g);
      until flag or nmr gt n; 
      return flag, g;
   end function;

   // returns an element from the centraliser C_G (j) 
   // most of the elements produced by this function are involutions;
   // their distribution in C_G (j) is invariant under action of 
   // C_G (j) by conjugation
   InCentralizer := function (j)
      g := Random (P);
      y := j * j^g;
      o := MyCentralOrder (Group (P), y);
      if j^4 ne j^2 then
         if ((o eq 1) or (o eq 2) or (o eq 4)) then
            z := y;
         end if;
         if o mod 4 eq 0 then
            if y^(o div 2) eq j^2 then 
               z := y^(o div 4); 
            else 
               z := y^(o div 2);
            end if;
         elif o mod 4 eq 2 then
            if y^(o div 2) eq j^2 then
   	       z := g*y^(((o div 2)-1) div 2);
            else 
   	       z := j;
            end if;
         elif o mod 2 eq 1 then 
            z := g*y^((o-1) div 2);
         end if;
      elif o mod 2 eq 0 then
         z := y^(o div 2);
      else 
         z := g*y^((o-1) div 2);
      end if;
   
      return z;
   end function;
   
   // decide if involution i is of type t_1, t_n-1 or t_n;
   // return true if 'big' element is found in C_G (i) i.e. 
   // g with PrimitiveDivisor (q^(n-1)-1)| o(g) or 
   // PrimitiveDivisor (q^(2(n-1))-1) | o(g)

   TypeOfCentralizer := function (j)
      x := InCentralizer (j);
      maxppd := 0;
      type := {};
      counter := 0;
      // EOB -- changed Oct 2012 
      // while type eq {} and counter lt n do
      while type eq {} and counter lt Effort*n do
         x *:= InCentralizer (j);
         maxppd := PDRankOfElement (x);
         if maxppd eq n-1 then
            Include (~type, 1);
         end if;
         if maxppd eq 2*(n-1) then
            Include (~type, 2);
         end if;
         counter +:= 1;
      end while;
      return #type gt 0;
   end function;
   
   // determines primitive divisor rank of the product j*j^x
   // of the element j and its random conjugate j^x
   ProductsOfConjugates := function (j)
      maxppd := 0;
      counter := 0;
      while (maxppd lt 8) and (counter lt Effort*n) do
         x := Random (P);
         y := j*j^x;
         maxppd := Max (maxppd, PDRankOfElement (y));
         counter +:= 1;
      end while;
      return maxppd;
   end function;
   
   // special case for n = 3
   if n eq 3 then
      vprint Identify: "Rank 3 case";
      flag, g := GoodElement (P, Factor * n);
      if flag eq false then 
         vprint Identify: "Failed to find good element"; 
         return false, _; 
      end if;
      o := MyCentralOrder (Group (P), g);
      j := g^(o div 2);
      conj := ProductsOfConjugates (j);
      counter := 0;
      while conj lt 3 and counter lt Factor * n do
         conj2 := ProductsOfConjugates (j);
         conj := Max (conj, conj2);
         counter +:= 1;
      end while;
      if conj lt 3 then
         return true, <"B", n, q>;
      else 
         return true, <"C", n, q>;
      end if;
   end if;

   // general case
   // distinguish between easy case (n odd) and hard case (n even)

   if n mod 2 eq 1 then	// easy case
      vprint Identify: "Odd case of DistinguishSpO: n = ", n;
      // steps (1) and (2) as in the paper; 
      // find element of good order and compute involution
      flag, g := GoodElement (P, Factor * n);
      if flag eq false then 
         vprint Identify: "Failed to find good element"; 
         return false, _; 
      end if;
      o := MyCentralOrder (Group (P), g);
      i := g^(o div 2);
      h := Random (P);  // steps (4) and (5) implemented
      o := MyCentralOrder (Group (P), i*i^h);
      if (q*(q+1) mod o ne 0) and (q*(q-1) mod o ne 0) then 
         return true, <"C", n, q>;
      else 
         return true, <"B", n, q>;
      end if;
   else // n even - hard case
      vprint Identify: "Even case of DistinguishSpO: rank = ", n;
      counter := 0;
      while counter le n do
         // steps (1) and (2) as in the paper; 
         // find element of good order and compute involution
         flag, g := GoodElement (P, Effort * n);
         if flag eq true then 
            o := MyCentralOrder (Group (P), g);
            i := g^(o div 2);
            // step (3): try to find big elements in C_G (i) 
            // to conclude that involution is of type t_1, t_n-1 or t_n
            vprint Identify: "Try to find big element in centraliser";
            found := TypeOfCentralizer (i);
            vprint Identify: "Found big element in centraliser?", found;
            if found then  
               // found big element in centralizer
               counter +:= 1;
               for k in [1..Effort*n] do  // step (4)
                  h := Random (P);
                  pdrank := PDRankOfElement (i*i^h);
                  if pdrank gt 6 then 
                     return true, <"C", n, q>;
                  end if;
               end for;
            end if;
         else 
            counter +:= 1;
            vprint Identify: "Failed to find good element"; 
         end if;
      end while; 
      return true, <"B", n, q>;	// step (5), no witness against G=Omega (2n+1, q)
   end if;	
end function; //DistinguishSpO

/* is n a Fermat prime? this test uses the fact that 
   if 2^m+1 is a prime, then m=2^n and hence is a Fermat prime */
IsFermat := function (n)
   return IsPrime (n) and IsPowerOf (n - 1, 2); 
end function;

/* is n a Mersenne prime? */
IsMersenne := function (n)
   return IsPrime (n) and IsPowerOf (n + 1, 2);
end function;

ppdset := function (o, p)
   primes := PrimeBasis (o);
   Exclude (~primes, p);
   return {Order (p, x): x in primes};
end function;

/* compute Artin invariants for element of order o;
   p is characteristic */

ComputeArtin := function (o, p)
   primes := PrimeBasis (o);
   Exclude (~primes, p);
   Exclude (~primes, 2);
   orders := {Order (p, x): x in primes};

   if IsFermat (p) and o mod 4 eq 0 then
      Include (~orders, 1);
   end if;
   if IsMersenne (p) and o mod 4 eq 0 then
      Include (~orders, 2);
   end if;
   if p eq 2 and o mod 9 eq 0 then
      Include (~orders, 6);
   end if;

   return orders;
end function;

/* partition at most Nmr elements according to their 
   projective orders listed in values; we consider
   at most NmrTries elements; P is a random process */

ppdSample := function (P, ppd, p, values, SampleSize)

   Bins := [0: i in [1..#values]];

   for i in [1..#ppd] do
      for j in [1..#values] do
         if values[j] in ppd[i] then
            Bins[j] +:= 1;
         end if;
      end for;
   end for;
   original := #ppd;

   ppd := [{Integers () |}];

   NmrTries := 0;
   while NmrTries le SampleSize do 
      NmrTries +:= 1;
      g := Random (P);
      o := MyCentralOrder (Group (P), g);
      list := ComputeArtin (o, p);
      Append (~ppd, list);
      for j in [1..#values] do
         if values[j] in list then
            Bins[j] +:= 1;
         end if;
      end for;
   end while;

   Remove (~ppd, 1);

   return [(x + 0.0) / (original + SampleSize) : x in Bins], ppd, Bins;

end function;

OrderSample := function (P, p, orders, values, SampleSize)

   Bins := [0: i in [1..#values]];

   for i in [1..#orders] do
      for j in [1..#values] do
         if orders[i] mod values[j] eq 0 then
            Bins[j] +:= 1;
         end if;
      end for;
   end for;
   original := #orders;

   NmrTries := 0;
   while NmrTries le SampleSize do
      NmrTries +:= 1;
      g := Random (P);
      o := MyCentralOrder (Group (P), g);
      Append (~orders, o);
      for j in [1..#values] do
         if o mod values[j] eq 0 then
            Bins[j] +:= 1;
         end if;
      end for;
      Total := &+Bins;
   end while;

   return [ (x + 0.0) / (SampleSize + original): x in Bins], orders, Bins;

end function;

// PSL (2, p^k) vs PSp (4, p^(k / 2))
PSLvsPSP := function (P, ppd, q, SampleSize, NmrTrials, orders)

   p := Factorisation (q)[1][1];
   if q eq 2 then  
      repeat
         SampleSize -:= 1;
         g := Random (P);
         o := MyCentralOrder (Group (P), g);
         if o eq 4 then
            return VerifyOrders ("L", 2, 9, orders);
         end if;
      until SampleSize eq 0;
      return VerifyOrders ("L", 2, 4, orders);
   end if;

   v1 := Maximum (ppd);
   ppd := [];
   values := [v1];
   repeat
      prob, ppd := ppdSample (P, ppd, p, values, SampleSize);
      prob := prob[1];
      if prob ge 1/3 and prob lt 1/2 then
         return VerifyOrders ("L", 2, q^2, orders);
      elif prob ge 1/5 and prob lt 1/4 then
         return VerifyOrders ("S", 4, q, orders);
      end if;
      NmrTrials -:= 1;
   until NmrTrials eq 0;

   if NmrTrials eq 0 then
      return NoGood (12);
   end if;

end function;

// O+ (8, 2) vs S (6, 2) -- elements of order 15
// suggested sample size = 250
OPlus82vsS62 := function (P, orders, SampleSize)
   values := [15];
   prob, orders := OrderSample (P, 2, [], values, SampleSize);
   prob := prob[1];
   if Abs (1/5 - prob) lt Abs (1/15 - prob) then
      return VerifyOrders ("O^+", 8, 2, orders );
   else
      return VerifyOrders ("S", 6, 2, orders );
   end if;
end function;

// O+(8, 3) vs O (7, 3) vs Sp (6, 3) -- elements of order 20
// suggested sample size = 250
OPlus83vsO73vsSP63 := function (P, orders, SampleSize: Factor := 20)
   values := [20];
   prob, orders := OrderSample (P, 3, [], values, SampleSize);
   prob := prob[1];
   if Abs (3/20 - prob) lt Abs (1/20 - prob) then
      return VerifyOrders("O^+", 8, 3, orders);
   else 
      return DistinguishSpO (P, 3, 3, 1, orders: Factor := Factor);
   end if;
end function;

// O+(8, p^e) vs O(7, p^e) vs S (6, p^e) 
// suggested sample size = 50
OPlus8vsO7vsSP6 := function (P, orders, p, e, SampleSize: Factor := 20)

   for i in [1..SampleSize] do
      g := Random (P);
      o := MyCentralOrder (Group (P), g);
      list := ComputeArtin (o, p);
      if {e, 2 * e, 4 * e} subset list then
         return VerifyOrders ("O^+", 8, p^e , orders);    
      end if;
   end for;
   if p eq 2 then
      return VerifyOrders ("S", 6, 2^e, orders);
   else
      return DistinguishSpO (P, 3, p, e, orders: Factor := Factor);
   end if;

end function;

// O-(8, p^e) vs Sp(8, p^e) vs O(9, p^e)
OMinus8vsSPvsO := function (P, v1, p, e, orders, SampleSize, NmrTrials:
                            Factor := 20)
   ppd := [];
   values := [v1];
   epsilon := 1/50;
   repeat 
      prob, ppd := ppdSample (P, ppd, p, values, SampleSize);
      prob := prob[1];
      if prob ge 1/5 - epsilon and prob lt 1/4 + epsilon then
         return VerifyOrders ("O^-", 8, p^(v1 div 8), orders);
      elif prob ge 1/10 - epsilon and prob lt 1/8 + epsilon then
         if p eq 2 then
	    return VerifyOrders ("S", 8, 2^e, orders);
	 else
            return DistinguishSpO (P, 4, p, e, orders: Factor := Factor);
	 end if;
      end if;
      NmrTrials -:= 1;
   until NmrTrials eq 0;

   if NmrTrials eq 0 then 
      return NoGood (13); 
   end if;
end function;

/* determine Artin invariants for group of Lie type */

ArtinInvariants := function (P, p, Nmr)
   orders := {}; combs := {};
   if p gt 2 then 
      invariants := {0, 1, 2};
   else 
      invariants := {0, 1};
   end if;
   newv1 := Maximum (invariants);
   repeat
      v1 := newv1;
      for i in [1..Nmr] do
         g := Random (P);
         o := MyCentralOrder (Group (P), g);
         Include (~orders, o);
         if o mod 3 eq 0 then Include (~orders, 3); end if;
         if o mod 4 eq 0 then Include (~orders, 4); end if;
         ppds := ppdset (o, p);
         if p eq 2 and o mod 9 eq 0 then
            Include (~ppds, 6);
            Include (~orders, 9);
         end if;
         invariants join:= ppds;
         combs join:= Subsets (ppds, 2);
      end for;
      newv1 := Maximum (invariants);
   until newv1 eq v1;

   return invariants, combs, orders;
end function; // ArtinInvariants

// Recognize a quasi-simple group of Lie type in characteristic p

LieTypeOfCharpGroup := function (G, p, orders: NumberRandom := 50,
                                 Exceptional := false, OmegaFactor := 20)

   P := RandomProcess (G);
   invar, combs, orders2 := ArtinInvariants (P, p, NumberRandom);
   orders := orders join orders2;

   vprint Identify: "Artin invariants are ", invar;
   
   v1 := Maximum (invar);
   Exclude (~invar, v1);

   if v1 eq 2 then
      return VerifyOrders ("L", 2, p, orders);
   end if;

   if v1 eq 3 then
      if p gt 2 then
         return VerifyOrders ("L", 3, p, orders);
         /* statement is probably never executed; 
            we compute v1 but the code is actually behaving 
            as if we deal with the value of v1 * */
      elif 8 in orders then
         return VerifyOrders ("U", 3, 3, orders);
      else
         return VerifyOrders ("L", 3, 2, orders);
      end if;
   end if;

   if v1 eq 4 then
      if 3 in invar then
         if p gt 2 then
            return VerifyOrders ("L", 4, p, orders);
         elif 15 in orders then
	    return VerifyOrders ("L", 4, 2, orders);
         else
            return VerifyOrders ("L", 3, 4, orders);
         end if; 
      else
         // if the given group is quasi-simple with characteristic 2, 
	 // then it must be isomorphic to SL(2, 4) since 
         // Sp(4, 2) and ("2B", 2, 2) are not quasi-simple
         return PSLvsPSP (P, {1, 2, 4}, p, SampleSize, NmrTrials, orders);
      end if;
   end if; // v1 = 4

   v2 := Maximum (invar);
   w := v1 / (v1 - v2);
   vprintf Identify: "v1, v2, w: %o %o %o\n", v1, v2, w; 
   
   if v1 eq 12 and v2 eq 4 and p eq 2 then
      if 21 in orders then
         return VerifyOrders ("G", 2, 4, orders);
      elif 16 in orders then
         return VerifyOrders ("2F", 4, 2, orders);
      elif 7 in orders then
         return VerifyOrders ("2B", 2, 8, orders);
      elif 15 in orders then
         return VerifyOrders ("U", 3, 4, orders);
      else
         return NoGood (1);
      end if;
   end if; // v2 = 4

   Exclude (~invar, v2);
   if #invar eq 0 then return false, _; end if;
   v3 := Maximum (invar);

   vprintf Identify: "v1, v2, v3, w: %o %o %o\n", v1, v2, v3, w; 

   if w eq 3/2 then
      if p eq 2 and not 3 in orders then
      	 if v1 mod 8 ne 4 then
	    return NoGood (1);
	 end if;
	 return VerifyOrders ("2B", 2, 2^(v1 div 4), orders);
      end if;
      if v1 mod 6 ne 0 then
         return NoGood (1);
      end if;
      if p eq 3 and not 4 in orders then
         // original v1 gt 6 changed into v1 ge 6
	 if v1 ge 6 then
            if v1 mod 12 ne 6 then
	       return NoGood (1);
	    end if;
	    return VerifyOrders ("2G", 2, 3^(v1 div 6), orders);
         end if;
      end if;
      return VerifyOrders ("U", 3, p^(v1 div 6), orders);
   end if; 

   if w eq 4/3 then
      if p eq 2 and v1 mod 8 eq 4 then
	 return VerifyOrders ("2B", 2, 2^(v1 div 4), orders);
      end if;
      return NoGood (1);
   end if;

   if w eq 2 then // exceptional groups
      if v1 mod 12 eq 0 and not ({v1 div 3, v1} in combs) then
         if 4 * v3 eq v1 then
            return VerifyOrders ("3D", 4, p^(v1 div 12), orders);
	 // please check again the case p eq 2 and v1 eq 24 
	 // --> there is a comment in the paper about it but I don't 
	 // understand why this case is implemented here   
         elif (v1 div 4) in invar or (p eq 2 and v1 eq 24) then
            return VerifyOrders ("G", 2, p^(v1 div 6), orders);
         else
	    if p eq 2 and v1 mod 24 eq 12 and 12 * v3 eq 4 * v1 then
               return VerifyOrders ("2F", 4, 2^(v1 div 12), orders);
	    else return NoGood (1);
	    end if;
         end if; 
      /* next clause is replacement for error in draft of paper */
      elif v1 mod 12 eq 6 and Maximum (orders) le p^(v1/3) + p^(v1/6) + 1 then
         return VerifyOrders ("G", 2, p^(v1 div 6), orders);
      end if;

      if v1 mod 4 eq 2 then
	 return VerifyOrders ("L", 2, p^(v1 div 2), orders);
      else
         return PSLvsPSP (P, invar join {v1, v2}, p^(v1 div 4), 
                          SampleSize, NmrTrials, orders);
      end if;
   end if;  // w = 2


   // following code distinguishes exceptional groups from 
   // classical groups and then distinguishes among exceptional ones
   if w eq 3 then
      if v1 mod 18 eq 0 and 18 * v3 eq 10 * v1 then
         if 8 * (v1 div 18) in invar then
            return VerifyOrders ("2E", 6, p^(v1 div 18), orders);
	 else return NoGood (10);
	 end if;
      elif v1 mod 12 eq 0 then
         if v1 gt 12 or p gt 2 then
            if v1 eq 2 * v3 and not ({v1 div 2, v1} in combs)
               and not ({v1 div 3, v1} in combs) then
               return VerifyOrders ("F", 4, p^(v1 div 12), orders);
            end if;
	 // paper only says that there exists x in orders such 9 | x  
	 // to check if 9 is in orders is a little demanding
	 // but we know that F4_2 contains elements of order 9
         elif 9 in orders and not ({4, 12} in combs) then
            return VerifyOrders ("F", 4, 2, orders);
         end if;  
      end if;
   end if; // w = 3

   // value of w already distinguishes exceptional from classical groups
   if w eq 4 and 8 * v1 eq 12 * v3 then
      if v1 mod 12 eq 0 then
         return VerifyOrders ("E", 6, p^(v1 div 12), orders);
      end if;
      return NoGood (1);
   end if;

   if w eq 9/2 and 12 * v1 eq 18 * v3 then
      if v1 mod 18 eq 0 then
         return VerifyOrders ("E", 7, p^(v1 div 18), orders);
      end if;
      return NoGood (1);
   end if;

   if w eq 5 and 20 * v1 eq 30 * v3 then
      if v1 mod 30 eq 0 then
         return VerifyOrders ("E", 8, p^(v1 div 30), orders);
      end if;
      return NoGood (1);
   end if; // exceptional groups
   
   // all exceptional groups are extracted - from now on 
   // distinguish only among classical groups

   vprint Identify: "Now excluded exceptional groups";
   if Exceptional then return false, 10; end if;

   if v1 mod (v1 - v2) ne 0 then // unitary groups
      if (v1-v2) mod 4 ne 0 or 2 * v1 mod (v1 - v2) ne 0 then 
         return NoGood (3);
      end if;
      e := (v1-v2) div 4;
      m := (2 * v1) div (v1-v2);
      if ((m + 1) mod 4 eq 0 and e * (m + 1) in invar) or
         ((m + 1) mod 4 ne 0 and e * (m + 1) div 2 in invar) then
         if (m gt 7 and v2-v3 eq 4 * e) or (m le 7 and v2-v3 eq 2 * e) then
            return VerifyOrders ("U", m + 1, p^e, orders);
         end if;
      else
         if (m gt 5 and v2-v3 eq 4 * e) or (m eq 5 and v2-v3 eq 2 * e) then
            return VerifyOrders ("U", m, p^e, orders);
	 end if;
      end if;
      return NoGood (6);
   end if;   // unitary groups

   if (v1 - v2) mod 2 ne 0 then
      e := v1 - v2;  m := v1 div (v1 - v2);
      // extra check for PSL(8, 2), PSL(4, 2^3), p = 2 and e * (m-2) = 6 
      if v3 eq e * (m-2) or (p eq 2 and e * (m-2) eq 6) or (m le 3) then
         return VerifyOrders ("L", m, p^e, orders);
      else
         return NoGood (7);
      end if;
   end if;
   
   // m does not always equal the m used in the paper
   e := (v1 - v2) div 2; m := v1 div (v1 - v2);  

   if p eq 2 and e * m eq 6 and e le 2 and 91 in orders then
      if v3 eq 10-2 * e  or  m eq 3 then
         return VerifyOrders ("L", m, 2^(2 * e), orders);
      else
         return NoGood (7);
      end if;
   end if;

   // test for {m * e, v1} equivalent to test for {me, 2me} in combs
   if {m * e, v1} in combs then
      if v3 eq 2 * e * (m-2) or m le 3 then
         return VerifyOrders ("L", m, p^(2 * e), orders);
      else
         return NoGood (7);
      end if;
   end if;

   // distinguish POmega+(8, p^e); PSp(6, p^e); 
   //             Omega(7, p^e); POmega-(6, p^e)
   if m eq 3 then
      if 3 * v3 eq v1 then
         return VerifyOrders ("U", 4, p^(v1 div 6), orders);
      else
         if p^e eq 2 then
            return OPlus82vsS62 (P, orders, SampleSize);
         end if;
         if p^e eq 3 then
            return OPlus83vsO73vsSP63 (P, orders, SampleSize:
               Factor := OmegaFactor);
         else
            return OPlus8vsO7vsSP6 (P, orders, p, e, SampleSize:
               Factor := OmegaFactor);
         end if;
      end if;
   end if;

   // tests for v3 <> 2e(m'-3); m = m'-1, m calculated earlier 
   if v3 ne 2 * e * (m-2) and (m gt 4 or v3 ne 5 * e) then   
      // wrong characteristic
      return NoGood (8);
   end if;

   // hard to distinguish "O-" from "Sp"
   // if Type (G) eq GrpMat then nmr := 20 * Degree (G); else nmr := 100; end if;
   if Type (G) eq GrpMat then nmr := 5 * Degree (G); else nmr := 100; end if;
   invar, combs2, orders2 := ArtinInvariants (P, p, nmr);
   combs := combs join combs2;
   orders := orders join orders2;
   if m mod 2 eq 0 then
      if {m * e, (m + 2) * e} in combs then
          return VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
      elif m eq 4 then
         return OMinus8vsSPvsO (P, v1, p, e, orders, SampleSize, NmrTrials:
                                Factor := OmegaFactor);
      else /* m ge 6 */
         if { (m - 2) * e, (m + 2) * e} in combs then
            if p eq 2 then
               return VerifyOrders ("S", 2 * m, 2^e, orders);
            else
               return DistinguishSpO (P, m, p, e, orders: Factor := OmegaFactor);
            end if;
         else
            return VerifyOrders ("O^-", 2 * m, p^e, orders);
         end if; 
      end if;  // m even
   // from here we have m >= 5, m odd
   elif {(m - 1) * e, (m + 3) * e} in combs then
      return VerifyOrders ("O^+", 2 * m + 2, p^e, orders);
   elif {(m - 1) * e, (m + 1) * e} in combs then
      if p eq 2 then
         return VerifyOrders ("S", 2 * m, 2^e, orders);
      end if;
      // p <> 2 case 
      vprint Identify:"Distinguish Sp from Omega";
      return DistinguishSpO (P, m, p, e, orders: Factor := OmegaFactor);
   else
      return VerifyOrders ("O^-", 2 * m, p^e, orders);
   end if; 

   error "Could not identify this group";
end function;

MyLieType := function (G, p, NumberRandom: Exceptional := false, Perfect := false, OmegaFactor := 20)

   if IsTrivial (G) then return false, _; end if;

   if not IsPrime (p) then 
      "Must supply defining characteristic"; 
      return false, _;
   end if;

   // use this only for degree at least 9 -- avoid coincidence of names 
   if Type (G) eq GrpMat and Degree (G) gt 8 and IsIrreducible (G) 
      and RecogniseClassical (G) cmpeq true then
      return true, ClassicalTypeToLieType (G);
   end if;

   if not Perfect then 
      flag, G0 := IsGoodInput (G);
      if not flag then return false, _; end if;
   else
      G0 := G;
   end if;

   return LieTypeOfCharpGroup(G0, p, {}: NumberRandom := NumberRandom, 
             Exceptional := Exceptional,  OmegaFactor := OmegaFactor);
end function;

intrinsic LieType (G :: GrpMat, p:: RngIntElt: NumberRandom := 50,
Exceptional := false, OmegaFactor := 20, Perfect := false)-> BoolElt, Tup 
{If the non-abelian composition factor of a nearly simple group G is isomorphic 
 to a group of Lie type in the given characteristic p, then return true and 
 its standard Chevalley group name, else return false; if Exceptional is true 
then G is assumed to be an exceptional group; if Perfect is true, then the algorithm assumes that G is perfect} 

   return MyLieType(G, p, NumberRandom: Perfect := Perfect, Exceptional := Exceptional);

end intrinsic;

intrinsic LieType (G :: GrpPerm, p:: RngIntElt: NumberRandom := 50,
Exceptional := false, Perfect := false)-> BoolElt, Tup 
{If the non-abelian composition factor of a nearly simple group G is 
 isomorphic to a group of Lie type in the given characteristic p, 
 then return true and its standard Chevalley group name, else return false; 
 if Exceptional is true then G is assumed to be an exceptional group; 
 if Perfect is true, then the algorithm assumes that G is perfect} 

   return MyLieType(G, p, NumberRandom: Perfect := Perfect, Exceptional := Exceptional);

end intrinsic;
