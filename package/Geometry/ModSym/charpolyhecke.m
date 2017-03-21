freeze;
 
/****-*-magma-* EXPORT DATE: 2004-03-08 ************************************
                                                                          
                  HECKE:  Modular Symbols in Magma                         
                           William A. Stein                              
           (the first version of this file written by Kevin Buzzard.)
                                                                         
   FILE: charpolyhecke.m (Characteristic polynomials of Hecke operators)
        A more efficient way to compute char polys using Deligne's
        bounds and the knowledge that the char poly is in Z[x].

   $Header: /home/was/magma/packages/modsym/code/RCS/charpolyhecke.m,v 1.5 2001/07/13 02:33:25 was Exp $

   $Log: charpolyhecke.m,v $
   Revision 1.5  2001/07/13 02:33:25  was
   Fixed the comment to look like the one in modform.

   Revision 1.4  2001/07/13 02:31:09  was
   Changed some intrinsics to functions, as they should be, and changed
   the main command name to HeckePolynomial, like in the modular forms package.

   Revision 1.3  2001/05/21 11:55:12  was
   Fixed first line of intrinsic CharacteristicPolynomialOfHeckeOperator.

   Revision 1.2  2001/05/13 03:45:15  was
   Changed verbose flag.

   Revision 1.1  2001/04/20 04:44:37  was
   Initial revision

   Revision 1.2  2001/01/21 09:01:39  was
   Creation and initial editing and clean-up.

   Revision 1.1  2001/01/21 06:18:27  was
   Initial revision

   

   Version 1.5: 23/09/2000: Stylistic modifications by William Stein, such as changing
   the functions into intrinsics.

   Version 1.4: 18/8/2000: Optimised the calculation of coefficients:
   e.g. the coefft of x^n for n<<d only needs a CRT calculation for
   far fewer primes, and so we use fewer primes.

   Version 1.3: 8/8/2000: added Timings parameter---set to true if
   you want to see how long it's all taking.

   Version 1.2: 7/8/2000: fixed the problem that
   charpoly doesn't like 0x0 matrices.

   Version 1.1, 5/8/2000, original version, by K Buzzard.

 ***************************************************************************/

forward CharacteristicPolynomialWithBound;

intrinsic HeckePolynomial(M::ModSym, n::RngIntElt:
                                 Proof := true) -> RngUPolElt
{The characteristic polynomial of the n-th Hecke operator on M.}

   require n ge 1: "Argument 2 must be at least 1.";

   if Type(BaseField(M)) eq FldRat then
      if IsCuspidal(M) and IsPrime(n) and GCD(n,Level(M)) eq 1 then
         T := DualHeckeOperator(M,n);
         k := Weight(M);
         bound := 2*n^((k-1)/2);
         return CharacteristicPolynomialWithBound(T, bound);
         // TO DO: for non-prime, bound := d(n)*n^((k-1)/2)
         // TO DO: non-cuspidal
      else
         return CharacteristicPolynomial(DualHeckeOperator(M,n) : 
                       Proof := Proof, Al := "Modular");
      end if;
   end if;
   return CharacteristicPolynomial(DualHeckeOperator(M,n));
end intrinsic;
 


function CharacteristicPolynomialWithBound (T, maxeig)
   assert Type(T) eq AlgMatElt;

// {The characteristic polynomial of T.  Expect garbage if
// the following assumptions are not all satisfied:
//  (1) T has rational entries,  
//  (2) the characteristic polynomial of T has integer coefficients,
//  (3) all the eigenvalues of T have absolute values <= maxeig.

   /*************************************************************
      The implementation works by using MAGMA to
   compute the char polys mod p for enough primes p and then
   using magma's CRT command to glue them together. The point
   is that under our restrictive assumptions above, and knowing
   maxeig, the number of primes needed to pull this off can be
   bounded _much_ more efficiently than the bound apparently
   used in the internal MAGMA command CharacteristicPolynomial,
   which of course doesn't know maxeig, and hence this routine
   appears to be sometimes much more efficient.
   Note of course that if these assumptions fail then the
   routine will either crash or produce garbage (one can easily
   get it to produce garbage by making maxeig much too small,
   for example).

   ***************************************************************/

   assert (BaseRing(Parent(T)) cmpeq RationalField()) or 
           (BaseRing(Parent(T)) cmpeq IntegerRing()) ;
//                  : "Argument 1 must be defined over the rationals or integers.";
   assert maxeig gt 0;// : "Argument 2 must be positive.";

   if IsVerbose("ModularSymbols") then 
      tt := Cputime();
   end if;

   R := PolynomialRing(Rationals()); x := R.1;  
   d := NumberOfRows(T);
   if d eq 0 then 
      return R!1;
   end if;
   if d eq 1 then 
      return R![-T[1,1],1];    // x - T[1,1].
   end if;

   fudge := GCD([Numerator(e) : e in ElementToSequence(T)]); // we can divide
                                                            // that factor out!
   if fudge gt 1 then
      f := CharacteristicPolynomialWithBound(
                T/fudge,
                maxeig/fudge);
                                 // This gives us the char
                                 // poly with x/fudge instead of x.

      return hom<Parent(f)->Parent(f)|x/fudge>(f)*fudge^Degree(f);
   end if; 

   // Note that the fudge above could be worth doing in some cases---for
   // example, for modular forms in level 1, fudge could well be something 
   // like 24, and so for high weight this decreases the variable "max" (the 
   // bound on the coeffts of the char poly) below by 24^d which gives us some
   // savings.

   den := LCM([Denominator(t) : t in ElementToSequence(T)]); // primes dividing
                                                             // den are bad, so
                                                             // we avoid them.
   maxvec := [Binomial(d,i)*maxeig^i : i in [1..d]];
   // i'th entry of maxvec is bound for coefft of x^(d-i).

   max := Maximum(maxvec);   // this tells us just how far we have to go.
                             // Perhaps a slightly smarter program would
                             // check that we are in the 99.9% of cases
                             // (for high weight) where this max is 
                             // just the bound for the constant coefft,
                             // and compute the char poly for fewer primes,
                             // and just the det for all primes after this.

   /* I'm not sure I believe this now: this will probably only speed the thing
      up by a few minutes at k=2000 N=1 T2 where it's taking _hours_ to do
      the computation. -- KB */
                         
   l  := 2;  
   pr := 1;
   v  := [];

   // l is the prime after the one we're up to. pr is the product of the
   // good primes we've had so far. v is the list of char polys mod p for
   // all good primes so far.

   // I am *mildly* concerned about precision. I want to make sure
   // that the product of the first n good primes really is at least 2*max.
   // But can I make pr a real variable known to a few DPs? This would
   // probably make things a lot quicker...

   // Now build up a table of char polys mod p for as many good primes as
   // possible, (i.e. avoid primes in the denominator of elts of T),
   // collecting the results as <p,charpoly mod p> in the vector v,
   // and continuing until the product of the primes is sufficiently
   // large that an integer t with |t|<=max is uniquely determined
   // by t mod this product.

   vprint ModularSymbols, 3: "Bounded charpoly: We shouldn't have taken any time yet, apart from ";
   vprint ModularSymbols, 3: "that LCM calculation; we've actually taken",Cputime(tt),
                            "seconds and now start looping through primes.";
   if IsVerbose("ModularSymbols", 2) then
      lb := 500; // for prime printing.
   end if;

   while pr le 2.0001*max do // Note that I didn't go for 2 because
                             // of rounding errors: e.g. consider
                             // the following "weird" magma output:
                             // > SquareRoot(2)^2000 + 1 lt 2^1000;
                             // true  
                             // caused of course by rounding errors.

      if IsVerbose("ModularSymbols", 2) then
         if l gt lb then
            print "Up to p=",l,".";
            lb +:= 500; // for prime printing.
            print "Time so far:",Cputime(tt),"seconds.";
            print "Log(2*max/pr) is",Log((2*max)/pr);
        end if;
      end if;

      while den mod l eq 0 do
         l := NextPrime(l);
      end while;

      pr *:= l;
      Append(~v,<l,PolynomialRing(Integers())!CharacteristicPolynomial(MatrixRing(GF(l),d)!T)>);
      l := NextPrime(l);
   end while;

   vprintf ModularSymbols, 2: "Bounded charpoly: Looped over sufficiently many primes now. All primes used were less than %o. Time taken so far: %o seconds.",
               l, Cputime(tt);
   vprint ModularSymbols, 2: "Now doing all", d, "of the CRTs.";

   // v is certainly all the data we need. Now rebuild.
   // The calculation so far used to take about 50% of the total
   // time but from V1.4 we're now probably over half way there,
   // because we're computing the coefficients of the char poly more sensibly.

   // Note that we have computed far too much data to compute,
   // for example, the trace! We have far too many primes in general.
   // Rather surprisingly, tests on CRT seem to indicate it's better
   // to work with lots of small primes in CRT rather than fewer bigger ones.

   // Maybe. I was surprised by the following test (from memory, so I hope
   // I have this right): choose a large random 100 digit number. First of
   // all multiply all primes starting with 2 until the product is > than
   // the 100 digit number. Then reduce the number mod p for all these
   // primes and time how long CRT takes to glue them back together. Then
   // do the same experiment but start with p=much bigger than 2. CRT appeared
   // to take just as long if not longer, even though there were fewer primes
   // to work with.

   maxlist:=[<d-i,maxvec[i]>:i in [1..d]];
   // Note that maxvec[i] is a bound for the coefft of x^(d-i).

   Sort(~maxlist,func<a,b|a[2]-b[2]>); // Sorts the list out into
                                       // order of size of maxvec,
                                       // with smallest first.

   pr := 1; // Start counting again!
   m  := [e[1] : e in v]; // list of primes we used.
   coeffts := [0 : i in [0..(d-1)]]; // coeffts[i] will be coefft of x^(i-1).
   for j in [1..#v] do 
      p   := v[j][1];
      pr *:= p;
      while #maxlist gt 0 and pr gt 2.0001*maxlist[1][2] do // We can compute
                                                            // a coefft now!
         cf := maxlist[1][1]; // That coefft.
         c  := CRT([Coefficient(v[i][2],cf):i in [1..j]],[m[i]:i in [1..j]]);
         coeffts[cf+1] := c lt pr/2 select c else c-pr;
         // That last line is because we want the unique soln in [-pr/2,pr/2].
         // Now kill 1st elt of maxlist.
         maxlist := Reverse(Prune(Reverse(maxlist)));
         vprintf ModularSymbols, 3: "Bounded charpoly: Just evaluated coefft of x^%o and time taken so far is %o.\n",
                   cf,Cputime(tt);
      end while;
   end for;

   if #maxlist gt 0 then 
      error("Oops, we missed a coefft."); 
   end if;

   vprint ModularSymbols, 2: "Bounded charpoly: Should be just about done now; time taken so far is",Cputime(tt);
   return x^d+Parent(x)!coeffts;

end function;



/*****************************************************************************

  FURTHER DIRECTION: Could one really go over the top and think
  hard about bounds, recomputing them along the way in some cases?
  For example, at level 1 all eigenvalues are _real_, so once one
  knows the coeffts of x^(d-1) and x^(d-2) in the char poly, one can
  easily evaluate the sum of the squares of the eigenvalues.  By
  Sato-Tate the eigenvalues are *much* more likely to be small than
  big, and hence already the sum of the squares should be in practice
  much smaller than d*max^2---and this information could be used, in
  the cases where one knows the eigenvalues are totally real, to
  re-compute better bounds on the eigenvalues and hence on the
  coefficients. For example the sum of the 4th powers will be at most
  the square of the sum of the squares!  It seems to me that when one
  knows the evalues are totally real this should give some real
  savings, but I haven't tested this at all in practice.  It might
  just be over the top.

 ****************************************************************************/

