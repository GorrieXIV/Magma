////////////////////////////////////////////////////////////////////
//                                                                //
//                  MISCELLANEOUS FUNCTIONS FOR                   //
//              ELLIPTIC CURVES OVER FINITE FIELDS                //
//                         David Kohel                            //
//                   Last modified March 2004                     //
//                                                                //
////////////////////////////////////////////////////////////////////

freeze;

forward ExtensionTrace, Ellap;

// Point Counting Intrinsics:
// TraceOfFrobenius, Trace, Order, ZetaFunction, EulerFactor

/****************** Changes/Additions *****************************

  Additions by Mike Harrison, March 2004.
  
  Added utility functions CryptographicCurve and
  ValidateCryptographicCurve for users to generate or validate
  cryptographically secure random curves with associated data.
  
********************************************************************/

////////////////////////////////////////////////////////////////////
//                                                                //
//                      POINT COUNTING                            //
//                                                                //
////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////
//                    TRACE OF FROBENIUS                          //
////////////////////////////////////////////////////////////////////

/* Full-length synonym for Trace. */

intrinsic TraceOfFrobenius(E::CrvEll[FldFin]) -> RngIntElt
    {The trace of the Frobenius endomorphism of E, where
    E is defined over a finite field.}

    return Trace(E);
end intrinsic;

intrinsic Trace(E::CrvEll[FldFin], r::RngIntElt) -> RngIntElt
    {The trace of the r-th power Frobenius endomorphism, where 
    E is defined over a finite field.}

    return ExtensionTrace(Trace(E),#BaseRing(E),r);
end intrinsic;

intrinsic TraceOfFrobenius(E::CrvEll[FldFin], r::RngIntElt) -> RngIntElt
    {"} // "
    return ExtensionTrace(Trace(E),#BaseRing(E),r);
end intrinsic;

intrinsic Trace(E::CrvEll,K::FldFin) -> RngIntElt
    {The trace of Frobenius of the base extension of E to K.}
    F := BaseRing(E);
    p := Characteristic(K);
    if Type(F) eq FldFin then
       require Characteristic(F) eq p and
          Degree(K) mod Degree(F) eq 0 : "Arguments are incompatible";
       return ExtensionTrace(Trace(E),#F,Degree(K) div Degree(F));
    elif Type(F) eq FldRat then
       return ExtensionTrace(Ellap(E,p),p,Degree(K));
    end if;
    require false : "Base ring must be the rationals or a finite field";
end intrinsic;

intrinsic TraceOfFrobenius(E::CrvEll,K::FldFin) -> RngIntElt
    {The trace of Frobenius of the base extension of E to K.}
    F := BaseRing(E);
    p := Characteristic(K);
    if Type(F) eq FldFin then
       require Characteristic(F) eq p and
          Degree(K) mod Degree(F) eq 0 : "Arguments are incompatible";
       return ExtensionTrace(Trace(E),#F,Degree(K) div Degree(F));
    elif Type(F) eq FldRat then
       return ExtensionTrace(Ellap(E,p),p,Degree(K));
    end if;
    require false : "Base ring must be the rationals or a finite field";
end intrinsic;

intrinsic ReductionType(E::CrvEll, p:: RngIntElt) -> MonStgElt
   {Returns a string "Good", "Additive", "Split multiplicative"
   or "Nonsplit multiplicative" describing the reduction type
   of a minimal model for E.}

   require Type(BaseRing(E)) eq FldRat :
      "Base ring of argument 1 must be the rationals.";
   N := Conductor(E);
   ep := Valuation(N,p);
   if ep eq 0 then
      return "Good";
   elif ep gt 1 then
      return "Additive";
   end if;
   tp := Ellap(E,p);
   if tp eq -1 then
      return "Nonsplit multiplicative";
   elif tp eq 1 then
      return "Split multiplicative";
   end if;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                         ORDER                                  //
////////////////////////////////////////////////////////////////////

intrinsic Order(E::CrvEll, r::RngIntElt) -> RngIntElt
    {The order of the group of rational points on the degree r
    extension of the base ring, where E is defined over a
    finite field.}

    F := BaseRing(E);
    require Type(F) eq FldFin :
       "The base ring of argument 1 must be a finite field.";
    return #F^r + 1 - ExtensionTrace(Trace(E),#F,r);
end intrinsic;

intrinsic Order(E::SetPtEll, r::RngIntElt) -> RngIntElt
    {The order of the group of rational points on the degree r
    extension of the ring of E, where E is defined over a
    finite field.}

    F := Ring(E);
    require Type(F) eq FldFin :
       "The ring of argument 1 must be a finite field.";
    return #F^r + 1 - ExtensionTrace(Trace(E),#F,r);
end intrinsic

intrinsic Order(E::CrvEll, K::FldFin) -> RngIntElt
    {The order the group of rational points on E over K, where
    E is defined over the rationals or a finite field.}

    F := BaseRing(E);
    if Type(F) eq FldFin then
       "The base ring of argument 1 must be a finite field.";
    end if;
    F := BaseRing(E);
    p := Characteristic(K);
    if Type(F) eq FldFin then
       require Characteristic(F) eq p and
          Degree(K) mod Degree(F) eq 0 : "Arguments are incompatible";
       return #K + 1 - ExtensionTrace(Trace(E),#F,Degree(K) div Degree(F));
    elif Type(F) eq FldRat then
       return #K + 1 - ExtensionTrace(Ellap(E,p),p,Degree(K));
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                     EULER FACTOR                               //
////////////////////////////////////////////////////////////////////

intrinsic EulerFactor(E::CrvEll) -> RngUPolElt
    {The Euler factor of E, i.e. the reciprocal characteristic
    polynomial of the Frobenius endomorphism.}
    K := BaseRing(E);
    p := Characteristic(K);
    require Type(K)eq FldFin :
       "Base ring of argument must a finite field";
    return 1 - Trace(E)*X + #K*X^2
       where X is PolynomialRing(Integers()).1;
end intrinsic;

intrinsic EulerFactor(E::CrvEll,K::FldFin) -> RngUPolElt
    {The Euler factor of the base extension of E to K.}
    Q := BaseRing(E);
    p := Characteristic(K);
    require Type(Q) eq FldRat or Type(Q) eq FldFin :
       "Base ring must be the rationals or a finite field";
    if Type(Q) eq FldFin then
       require Characteristic(Q) eq p and Degree(K) mod Degree(Q) eq 0 :
          "Arguments are incompatible";
    end if;
    return 1 - Trace(E,K)*X + #K*X^2
       where X is PolynomialRing(Integers()).1;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                      ZETA FUNCTION                             //
////////////////////////////////////////////////////////////////////

intrinsic ZetaFunction(E::CrvEll[FldFin]) -> FldFunRatUElt
    {The zeta function of E.}
    K := BaseRing(E);
    return (1 - Trace(E)*X + #K*X^2)/((1 - X)*(1 - #K*X))
       where X is FunctionField(Integers()).1;
end intrinsic;

intrinsic ZetaFunction(E::CrvEll[FldRat],K::FldFin) -> FldFunRatUElt
    {The zeta function of the base extension of E to K.}
    Q := BaseRing(E);
    p := Characteristic(K);
    return (1 - Trace(E,K)*X + #K*X^2)/((1 - X)*(1 - #K*X))
       where X is FunctionField(Integers()).1;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                    ACCESSORY FUNCTIONS                         //
////////////////////////////////////////////////////////////////////

function ExtensionTrace(t, q, r)
   if r eq 1 then return t; end if;
   P := PolynomialRing(Integers());
   x := P.1;
   R := quo< P | x^2 - t*x + q >;
   pi := R.1;
   return Trace(pi^r);
end function;

function Ellap(E, p)
   E := MinimalModel(E);
   ep := Valuation(Conductor(E),p);
   if ep eq 0 then
      return p+1-#ChangeRing(E,GF(p));
   elif ep gt 1 then
       // Additive reduction:
       return 0;
   end if;
   a1, a2, a3, a4, a6 := Explode(ChangeUniverse(aInvariants(E),GF(p)));
   // Multiplicative reduced model in characteristic 2:
   // y^2 + a1*x*y + (a1*a2 + a3)/a1*x^2 = x^3 + D/a1^6
   if p eq 2 then
      if (a1*a2 + a3) eq 0 then
	  // split multiplicative
	  return 1;
      else // nonsplit multiplicative
	  return -1;
      end if;
   end if;
   // Multiplicative reduced model in characteristic 3:
   // y^2 - b2*x^2 = x^3 + D/b2^3, where b2 = a1^2 + a2
   if p eq 3 then
      if IsSquare(a1^2 + a2) then
	  // split multiplicative
	  return 1;
      else // nonsplit multiplicative
	  return -1;
      end if;
   end if;
   c4, c6 := Explode(ChangeUniverse(cInvariants(E),GF(p)));
   // Multiplicative reduced model in characteristic p > 3:
   // y^2 = x^3 - c4/48*x - c6/864 = x^3 - t^2/48*x - t^3/864
   //    where c4^3 = c6^2 = t^6 -> y^2 + t/4*x^2 = x^3
   if IsSquare(-c6/c4) then
       // split multiplicative
       return 1;
   else // nonsplit case
       return -1;
   end if;
end function;

////////////////////////////////////////////////////////////////////
//                   EC DOMAIN FUNCTIONS                          //
//   Utilities for the user to generate/validate data for a       //
//   cryptographically secure elliptic curve domain as defined    //
//       in Technical report CORR 99-34 and ANSI X9.62            //    
////////////////////////////////////////////////////////////////////

declare verbose ECDom,2;

intrinsic CryptographicCurve(F::FldFin :
                      OrderBound := 2^160, Proof := true, UseSEA := false)
	-> CrvEll,PtEll,RngIntElt,RngIntElt
{ Returns a randomly-generated elliptic curve E over the finite field F,
  a point P on E, a large prime ord (greater than OrderBound : default 2^160)
  such that P has order ord on E and (E, <cyclic subgroup generated by P>)
  satisfy standard security requirements, and finally #E/ord.
  If the parameter 'Proof' is true (the default), ord will be proved to be
  prime. If false, ord is only guaranteed to be a strong pseudo-prime.
  If parameter 'UseSEA' is set to true (not recommended!), the use of the
  SEA algorithm for computing #E is forced, and advantage can be taken of
  the early abort mechanism.}

  requirege OrderBound,0;
  q := #F;
  char := Characteristic(F);
  if (char eq 2) then
     error if (q lt 2*OrderBound), 
      "Field size q must be at least twice parameter OrderBound",
      "when q is a power of 2";
     if (q lt 4*OrderBound) then 
         bNotDivBy4 := true; 
     else
         bNotDivBy4 := false;
     end if;
  else
     error if (q lt OrderBound), 
      "Field size q must be at least parameter OrderBound",
      "when q is an odd prime power";
  end if;
  MaxS := (q+1+Isqrt(4*q)) div OrderBound;
  //main loop
  cnt := 0;
  tyme := Cputime();
  while true do
     b := Random(F);
     a := Random(F);
     if char eq 2 then
        if bNotDivBy4 and (Trace(a) eq F!0) then continue; end if;
        boo, E := IsEllipticCurve([F!1,a,F!0,F!0,b]);
     else if char eq 3 then
        boo, E := IsEllipticCurve([F!0,a,F!0,F!0,b]);
     else
        boo, E := IsEllipticCurve([a,b]);
     end if; end if;
     if not boo then continue; end if;
     cnt +:=1;
     vprintf ECDom,2: "Random curve %o:\n",cnt;
     vprint ECDom,2: " Computing order...";
     vtime ECDom,2: ordE := SEA(E : MaxSmooth := MaxS, UseSEA := UseSEA);
     if ordE le 1 then continue; end if; // #E too smooth or #E=1
     if IsDivisibleBy(q+1-ordE,char) then  // E supersingular
         continue;
     end if;
     // sieve small primes out of the order.
     vprint ECDom,2: " Looking for large prime divisor of #E...";
     f1,f2 := TrialDivision(ordE,Min(10000,MaxS+1): Proof := false);
     if #f2 gt 0 then //remainder after trial division is composite
        continue;
     end if;
     p := f1[#f1][1];//remainder after trial division (pseudo-prime)
     if p lt OrderBound then continue; end if; //p too small
     if p^2 le 16*q then continue; end if;     //p too small
     // at this point p | ordE is big enough and E is ordinary.
     // now check security conditions
     vprint ECDom,2: " Checking security conditions...";
     if IsDivisibleBy(p,char) then continue; end if;//vulnerable to Smart's attack
       // check for possible MOV attack
     R := ResidueClassRing(p);
     qres := R!q;
     one := R!1;
     res := one;
     bOK := true;
     for k in [1..20] do
       res *:= qres;
       if res eq one then // q^k = 1 mod p
           bOK := false; break;
       end if;
     end for;
     if not bOK then continue; end if;
     if Proof then
        vprint ECDom,2: " Verifying primality...";
        vtime ECDom,2: boo := not IsPrime(p);
        if boo then continue; end if;  // p not actually prime
     end if;
     // found good E and prime order p - now find point
     vprint ECDom,2: " Finding good point...";
     n := ordE div p;
     notdone := true;
     while notdone do
         P := Random(E);
         Q := n*P;
         notdone := (Q eq E!0);
     end while;
     vprintf ECDom: "Finished! Tried %o curves.\n",cnt;
     vprintf ECDom: "Total time: %o\n",Cputime(tyme);
     return E,Q,p,n;
  end while;
  
end intrinsic;

intrinsic ValidateCryptographicCurve
                (E::CrvEll,P::PtEll,ordP::RngIntElt,h::RngIntElt :
                        OrderBound := 2^160, Proof := true)
                        -> BoolElt
{ Checks that ordP is a prime and that P is a point on E of exact order ordP.
  It also checks that #E is h*ordP and that (E,P) satisfies the standard
  security conditions for cryptographic use, including ordP >= OrderBound
  (default 2^160). If parameter Proof is true (the default), ordP is proved
  to be prime. Otherwise, it is only verified to be a strong pseudo-prime. }
  
    if not (P in E) then return false; end if;
    if IsId(P) then return false; end if; // P = 0
    q := #BaseRing(E);
    if (ordP lt OrderBound) or (ordP^2 le 16*q) then
        return false;
    end if;
    if not IsId(ordP*P) then return false; end if;// order P  != ordP
    if h ne ((q+1+Isqrt(4*q)) div ordP) then
        return false;  //#E != h*ordP
    end if;
    // check security requirements
    if IsDivisibleBy(ordP,Characteristic(BaseRing(E))) then
        return false; //vulnerable to Smart's attack
    end if;
       // check for possible MOV attack
    R := ResidueClassRing(ordP);
    qres := R!q;
    one := R!1;
    res := one;
    for k in [1..20] do
       res *:= qres;
       if res eq one then // q^k = 1 mod p
           return false;
       end if;
    end for;
    // finally, verify that ordP is prime
    vprint ECDom: " Verifying primality of the order of P...";
    return IsPrime(ordP: Proof := Proof);
    
end intrinsic;
