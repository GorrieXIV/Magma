freeze;

// Last revised October 2007 

import "classical.m": InfoRecog;
///////////////////////////////////////////////////////////////////////////////
//
//  StandardAssociate( <R>, <f> ) . . . . return the standard associate of <f>
//
StandardAssociate := function(R,f)
    coeffs := Coefficients(f);
    if #coeffs eq 0 then
        return Zero(R);
    end if;
    return f * coeffs[#coeffs]^-1; // makes f monic
end function;

///////////////////////////////////////////////////////////////////////////////
//
//  PPDPartPDM1( <d>, <p> ) . . . . . . compute the ppd part in <p>^<d>-1
//
PPDPartPDM1B := function(d,p)

   //compute the (repeated) gcd with p^d-1
   n := p^d - 1;
   x := 1;
   q := 1;
   for i in [1..d-1] do
       q *:= p; //q = p^i
       if d mod i eq 0 then
          repeat
            m := Gcd(n,q-1);
            n div:= m;
            x *:= m;
          until m eq 1;
       end if;
   end for;

   // and return as ppds the product of all ppds and as
   // noppds the quotient p^d-1/ppds
   RF := recformat<noppds,ppds>;
   return rec<RF|noppds := x, ppds := n>;

end function;


///////////////////////////////////////////////////////////////////////////////
//
//  PPDIrreducibleFactor( <R>, <f>, <d>  ) . . . large factors of <f>
//
//  Let <R> be a ring and <f> a polynomial of degree <d>.
//  This function returns false if <f> does not have an irreducible
//  factor of degree > d/2 and it returns the irreducible factor if it does.
//
PPDIrreducibleFactor := function(R,f,d)

   // handle trivial case
     //   if Degree(f) le 2 then
     //      return false;
     //   end if;

   irrfac := false;
   allfactors := Factorisation(f);
   for somefactor in allfactors do
       if Degree(somefactor[1]) gt (d div 2) then
          irrfac := StandardAssociate(R,somefactor[1]);
          break;
       end if;
   end for;
   return irrfac;

end function;    

/////////////////////////////////////////////////////////////////////////
// 
//  IsPpdElement( <F>, <m>, <d>, <p>, <a> ) . . . . is m a ppd-element
// 
//  This function takes as input:
//
//  <F>  field
//  <m>  a matrix or a characteristic polynomial
//  <d>  degree of <m>
//  <p>  a prime power
//  <a>  an integer
//
//  It tests whether <m> has order divisible by a primitive prime divisor of
//  p^(e*a)-1 for some e with d/2 < e <= d and returns false if this is not
//  the case. If it is the case it returns a list with two entries,
//  the first being e and the second being a boolean islarge, where
//  islarge is true if the order of <m> is divisible by a large ppd of
//  p^(e*a)-1 and false otherwise. 
//
//  Note that if q = p^a with p a prime then a call to
//  IsPpdElement( <F>, <m>, <d>, <q>, 1 ) will test whether m is a
//  ppd(d, q; e) element for some e > d/2 and a call to
//  IsPpdElement( <F>, <m>, <d>, <p>, <a> ) will test whether m is a
//   basic ppd(d, q; e) element for some e > d/2.
//

IsPpdElement := function( F, m, d, p, a )


    // compute the characteristic polynomial
    if Type (m) eq RngUPolElt then
        c := m;
    else
        c := CharacteristicPolynomial( m );
    end if;

    // try to find a large factor
    R := PolynomialRing(F);
    c := PPDIrreducibleFactor( R, c, d);

    // return if we failed to find one
    if Type (c) eq BoolElt  then
        return false;
    end if;

    e  := Degree(c);
    // find the noppds and ppds parts
    pm := PPDPartPDM1B( e*a, p );
    // pm contains two fields, noppds and ppds.
    // ppds is the product of all ppds of p^(ae)-1
    // and noppds is p^(ae)-1/ppds.
  
    // get rid of the non-ppd part
    // g will be x^noppds in F[x]/<c>
    g := Modexp(R![0,1],pm`noppds,c);

    // if g is one there is no ppd involved
    if g eq One(R)  then
        return false;
    end if;

    // now we know that <m> is a ppd-element

    // bug fix 31.Aug.2007 ACN
    if pm`ppds mod (e+1) ne 0 then
        // we know that all primes dividing pm`ppds are large
        // and hence we know <m> is a large ppd-element
        islarge := true;
        return [* e, islarge *];
    end if;

     // Now we know (e+1) divides pm`ppds and (e+1) has to be
     // a prime since all ppds are at least (e+1)
    if not IsPrime (e+1) then
	return false;
    end if;

     g := Modexp( g, e+1, c );
    // so g := g^(e+1) in F[x]/<c>
    if g eq One (R) then
        // (e+1) is the only ppd dividing |<m>| and only once
        islarge := false;
        return [* e, islarge *];
    else
        // Either another ppd also divides |<m>| and this one is large or
        // (e+1)^2 divides |<m>| and hence still large
        islarge := true;
        return [* e, islarge  *];
    end if;

end function;

/////////////////////////////////////////////////////////////////////////////
//
//  PPDIrreducibleFactorD2( <R>, <f>, <d>  )  . . . .  d/2-factors of <f>
//
//  Let <R> be a ring and <f> a polynomial of degree <d>.
//  This function returns false if <f> does not have an irreducible
//  factor of degree = d/2 and it returns the irreducible factor if it does.

PPDIrreducibleFactorD2 := function ( R, f, d  )


    if d mod 2 ne 0 then 
       InfoRecog(1, "d must be divisible by 2\n" );
       return false; 
    end if;

    irrfac := false;
    allfactors := Factorization( f );

    for somefactor in  allfactors do
        if Degree( somefactor[1] ) eq (d div 2) then
           irrfac := StandardAssociate(R,somefactor[1]);
           break;
        end if;
    end for;

   return irrfac;

end function;


/////////////////////////////////////////////////////////////////////////////
//
//  IsPpdElementD2 ( <F>, <m>, <d>, <p>, <a> )
//
//  This function takes as input:
//
//  <F>  field
//  <m>  a matrix or a characteristic polynomial
//  <d>  degree of <m>
//  <p>  a prime power
//  <a>  an integer
//
//  It tests whether <m> has order divisible by a primitive prime divisor 
//  of p^(e*a)-1 for e = d/2 and returns false if this is not
//  the case. If it is the case it returns a list with three entries,
//  the first being e=d/2; the second being a boolean islarge, where
//  islarge is true if the order of <m> is divisible by a large ppd of
//  p^(e*a)-1 and false otherwise; and the third is noppds (the first
//  return value of PPDPartPDM1B).
//
//  Note that if q = p^a then a call to
//  IsPpdElement( <F>, <m>, <d>, <q>, 1 ) will test whether m is a
//  ppd(d, q; e) element for e = d/2 and a call to
//  IsPpdElement( <F>, <m>, <d>, <p>, <a> ) will test whether m is a
//   basic ppd(d, q; e) element for e = d/2.
//

IsPpdElementD2 := function( F, m, d, p, a )
     local   c, e,  R,  pm,  g, ppd, lppd;

     // compute the characteristic polynomial
     if Type (m) eq RngUPolElt then
       c := m;
     else
       c := CharacteristicPolynomial( m );
     end if;

     // try to find a large factor
     R := PolynomialRing(F);
     c := PPDIrreducibleFactorD2( R, c, d );

     // return if we failed to find one
     if Type (c) eq BoolElt  then
         return false;
     end if;

     // find the nonppds and ppds parts
     pm := PPDPartPDM1B( Degree(c)*a, p );
     // pm contains two fields, noppds and ppds.
     // ppds is the product of all ppds of p^(ad/2)-1
     // and noppds is p^(ad/2)-1/ppds.

     // get rid of the non-ppd part
     g := Modexp(R![0,1],pm`noppds,c);

     // if it is one there is no ppd involved
     if g eq One(R)  then
         return false;
     end if;

     // now we know that g is a ppd-element
     // compute the possible gcd with <e>+1
     e  := Degree(c); // which is d/2
     if pm`ppds mod (e+1) ne 0 then
	// we know that all primes dividing pm`ppds are large
        // and hence we know g is a large ppd-element
        islarge := true;
        return [* e, islarge, pm`noppds *];
     end if;

     // Now we know (e+1) divides pm`lppd and (e+1) has to be
     // a prime since all ppds are at least (e+1)
     if not IsPrime (e+1) then
	return false;
     end if;

     g := Modexp( g, e+1, c );
     if g eq One (R) then
        // (e+1) is the only ppd dividing |<m>| and only once
        islarge := false;
        return [* e, islarge, pm`noppds *];
     else
        // Either another ppd also divides |<m>| and this one is large or
        // (e+1)^2 divides |<m>| and hence still large
	islarge := true;
        return [* e, islarge, pm`noppds *];
     end if;

end function;

// new function July 2010
// Test whether p is a primitive prime divisor of b^a-1

IsPrimitivePrimeDivisor := function( b, a, p )

    // Test that p is a prime integer and b and a are integers
    // both at least 2
    if not IsPrime (p) then return false; end if;
    if not IsIntegral (b) or b le 1 then return false; end if;
    if not IsIntegral (a) or a le 1 then return false; end if;

    // if p does not divide b^a-1 then it is not a ppd
    if (b^a-1) mod p ne 0 then return false; end if;

    // if p divides a term b^i-1 for i < a then it is not a ppd
    for i in [ 1 .. a-1 ] do
        if (b^i-1) mod p eq 0 then return false; end if;
    end for;

    return true;
end function;
