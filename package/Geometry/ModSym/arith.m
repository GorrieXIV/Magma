freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                            
                   HECKE:  Modular Symbols in Magma                          
                            William A. Stein                                 
                                                                            
   FILE: arith.m (Generic arithmetic helper functions for modsym package)   

   $Header: /home/was/modsym/RCS/arith.m,v 1.1 2001/04/20 04:42:54 was Exp $

   $Log: arith.m,v $
   Revision 1.1  2001/04/20 04:42:54  was
   Initial revision

   Revision 1.12  2001/02/04 16:24:12  was
   Made the error message in ReductionMap slightly more helpful.

   Revision 1.11  2001/02/04 15:49:58  was
   Slight modification to "ReductionMap".

   Revision 1.10  2001/02/04 15:36:02  was
   Added  function ReductionMap(K,F)

   Revision 1.9  2001/02/04 00:01:24  was
   Fixed the comment to ToLowerCaseLetter.

   Revision 1.8  2000/09/09 21:00:18  was
   *** empty log message ***

   Revision 1.7  2000/09/09 21:00:05  was
   +++

   I was poking around in Hecke's arith.m and here's some random comments:

   NthPrime can be made a lot more efficient by, if n># precomputed primes,
   then just start counting from the last precomputed prime rather than from
   2: let p be the _last_ elt of PRIMES and then apply NextPrime lots of
   times.

   ToNth doesn't work for 21 ;-)

   You say Round had gone but it might have come back :-)

   +++

   Revision 1.6  2000/06/19 09:54:21  was
   added freeze

   Revision 1.5  2000/06/03 04:09:46  was
   Added a "Round" function.

   Revision 1.4  2000/05/02 17:49:17  was
   Changed the name of the Norm() function to NormPolResElt and added better error checking.

   Revision 1.3  2000/05/02 07:55:14  was
   Added $Log: arith.m,v $
   Added Revision 1.1  2001/04/20 04:42:54  was
   Added Initial revision
   Added
   Added Revision 1.12  2001/02/04 16:24:12  was
   Added Made the error message in ReductionMap slightly more helpful.
   Added
   Added Revision 1.11  2001/02/04 15:49:58  was
   Added Slight modification to "ReductionMap".
   Added
   Added Revision 1.10  2001/02/04 15:36:02  was
   Added Added  function ReductionMap(K,F)
   Added
   Added Revision 1.9  2001/02/04 00:01:24  was
   Added Fixed the comment to ToLowerCaseLetter.
   Added
   Added Revision 1.8  2000/09/09 21:00:18  was
   Added *** empty log message ***
   Added
   Added Revision 1.7  2000/09/09 21:00:05  was
   Added +++
   Added
   Added I was poking around in Hecke's arith.m and here's some random comments:
   Added
   Added NthPrime can be made a lot more efficient by, if n># precomputed primes,
   Added then just start counting from the last precomputed prime rather than from
   Added 2: let p be the _last_ elt of PRIMES and then apply NextPrime lots of
   Added times.
   Added
   Added ToNth doesn't work for 21 ;-)
   Added
   Added You say Round had gone but it might have come back :-)
   Added
   Added +++
   Added
   Added Revision 1.6  2000/06/19 09:54:21  was
   Added added freeze
   Added
   Added Revision 1.5  2000/06/03 04:09:46  was
   Added Added a "Round" function.
   Added
   Added Revision 1.4  2000/05/02 17:49:17  was
   Added Changed the name of the Norm() function to NormPolResElt and added better error checking.
   Added

                                                                            
 ***************************************************************************/

ALPHABET := {@ "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L",
     "M", "N", "O", "P", "Q", "R", "S", "T", "U", "V", "W", "X", "Y", "Z" @};
alphabet := {@ "a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l",
     "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z" @};


function ToIsogenyCode(n)
// Returns the n-th isogeny coding.  The coding goes A,B,C,...,Z,AA,BB,...
   if n eq 0 then return "?"; end if;
   return &cat[ALPHABET[((n-1)mod 26)+1]: i in [0..((n-1) div 26)]];
end function;


function ToLowerCaseLetter(n)
// Returns the n-th isogeny coding.  The coding goes a,b,c,...,z,aa,bb,...
   if n eq 0 then return "?"; end if;
   return &cat[alphabet[((n-1)mod 26)+1]: i in [0..((n-1) div 26)]];
end function;


function IsogenyCodeToInteger(s)
// Returns the number n so that s = ToIsogenyCode(n).
   return 26*(#s-1)+Index(ALPHABET,s[1])+Index(alphabet,s[1]);
end function;


function SmallestPrimeNondivisor(N,p)
  // Return the smallest prime number ell not dividing N and
  // such that ell >= p.
   if not IsPrime(p) then
      p := NextPrime(p);
   end if;
   while N mod p eq 0 do
      p := NextPrime(p);
   end while;
   return p;
end function;


PRIMES := {@ p : p in [1..10000] | IsPrime(p) @};
function NthPrime(n)
// Returns the nth prime.
   if n lt #PRIMES then
      return PRIMES[n];
   end if;
   p:=PRIMES[#PRIMES];
   for i in [#PRIMES+1..n] do
      p := NextPrime(p);
   end for;
   return p;
end function;


function PrimePos(p)
// Returns the integer n so that p is the nth prime.
   i := Index(PRIMES,p);
   if i ne 0 then
      return i;
   else
      ell := NextPrime(PRIMES[#PRIMES]);
      i   := #PRIMES+1;
   end if;
   while ell lt p do
      ell := NextPrime(ell);
      i  +:= 1;
   end while;
   return i;
end function;


function PrimeDivPos(p, N)
// Returns the position of the divisor p of N, or 0 if p does not divide N.
   if N mod p ne 0 then 
      return 0 ;
   end if;
   return Index([x[1] : x in Factorization(N)], p);
end function;


function OddPart(n)
// Returns the odd part of n.
   return n eq 0 select 0 else Parent(n)!(n / 2^Valuation(n,2));
end function;


function DotProd(a,b)
   return &+[a[i]*b[i] : i in [1..#Eltseq(a)]];
end function;


function NormPolResElt(x)
// Compute the norm of an element of a quotient of a polynomial ring.
   assert Type(x) eq RngUPolResElt;
   if Type(x) eq FldRatElt then
      return x;
   end if;
   return Resultant(PreimageRing(Parent(x))!x,Modulus(Parent(x)));
end function;


function ToNth(n)
// Returns the English word for "nth".
   assert n ge 0;
   if n mod 100 in [11,12,13] then 
      return IntegerToString(n) cat "th"; 
   end if;
   case n mod 10:
      when 1:
         return IntegerToString(n) cat "st";
      when 2:
         return IntegerToString(n) cat "nd";
      when 3:
         return IntegerToString(n) cat "rd";
      else 
         return IntegerToString(n) cat "th";
   end case;
end function;


function PrimeSeq(p1,p2) 
// The sequence of primes [p1 ... p2].
   return [p : p in [p1..p2] | IsPrime(p)];
end function;


function idxG0(n)
   return 
      &*[Integers()| t[1]^t[2] + t[1]^(t[2]-1) : t in Factorization(n)];
end function;
   

function idxG1(n)
   return EulerPhi(n)*idxG0(n);
end function;


// Round seems to have returned. 
/*
function Round(x)   // this function disappeared from MAGMA!!!!!!!!!!
   n := Floor(x);
   return (x-n) ge 0.5 select n+1 else n;
end function;
*/



function ReductionMap(K,F)
   /* Attempt to compute some "reduction map" from K to F. 
      If necessary, the base field is extended.  Note that, 
      of course, this map is only defined on a subset of K! */
   phi := hom<K->F | x :-> F!x>;
    // program some common special cases
   if Type(K) eq FldCyc and Type(F) eq FldFin then
      r := CyclotomicOrder(K);
      n := #F;
      f := MinimalPolynomial(K.1);
      R := PolynomialRing(F); y := R.1;
      g := R!f;
      roots := Roots(g);
      if #roots eq 0 then
         fac := Factorization(g);
         mindeg := Min([Degree(factor[1]) : factor in fac]);
         error "There is no appropriate reduction map into the finite field of size", n,". Please use a bigger finite field, such as", GF(#F^mindeg);
      end if;
      phi := hom<K -> F | roots[1][1]>;
   end if;
   return phi;
end function;


function GetModulus(K)
    if ISA(Type(K), FldNum) then
	return DefiningPolynomial(K);
    end if;
    return Modulus(K);
end function;
