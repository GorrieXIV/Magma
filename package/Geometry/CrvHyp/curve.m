freeze;
// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

/*******************************************
 * Hyperelliptic/curve.m                   *
 *                                         *
 * Functions for hyperelliptic curves      *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 22-Jun-1998                     *


 modified by Paulette Lieby, November 1999
13/7/01	nicole	HyperEllipticCurve - removed extra return type, 
		FunctionField - comment unreachable
		EquationOrder - add return type

2001-07-30  EquationOrder() should return the equation order, not the
	    maximal order.  Geoff.
 
  changes:
  --------
 
  Attribute changes:
  ******************

  CoefficientRing,  
  Genus,
  Degree,
  IsOddDegree,
  Size                 disappear


  Points:
  this attribute cannot be set anymore: it is now set 
  internally; it is set when actually computing 
  (or enumerating) the points
  (Note: `Points is only used in Random, so we may 
  want to see how to rewrite this so to 
  remove this attribute as well -- work in progress)


  ==> Points need not to be declared anymore



  PointsAtInfinity:  removed

  
  Intrinsic changes:
  ******************

  CoefficientRing,
  BaseField,
  Genus,
  Degree,
  IsOddDegree,
  Size                -->  all in kernel


  HyperellipticCurve(f::RngUPolElt, h::RngUPolElt)  -->  in kernel
  HyperellipticCurveRaw                : is the same as HyperellipticCurve
                                       and has been removed
  PointsAtInfinity                     -->  in kernel
  #                                    -->  in kernel
  Points                               -->  in kernel


  New:
  ****

  NumberOfPointsAtInfinity             -->  in kernel

  FunctionField -- added attribute, June 2000, DRK   

  ------------------------------------------------------------------
  
  Changed by Michael Stoll 2000-03-24, merged into 2.7-1 version 2000-08-08:
  
    Some cleaning up of the code in functions affected by the precious
      changes.
    
    Removed HyperellipticCurveNoCheck (no point in keeping it since
      kernel does the check anyway)
    
    Corrected a bug in Random (Random did only find points with
      x-coordinate in the prime field)
    
  ------------------------------------------------------------------
  
  Changed by Michael Stoll 2000-08-08:
 
    Functions that used to return two maps C1 -> C2, C2 -> C1 now
      only return the map C1 -> C2; this map can be inverted.
    
    New creation intrinsic: HyperellipticCurveOfGenus(g, ...)
      to construct a hyperelliptic curve of specified genus
      (this is necessary to obtain good behaviour of base change functions).
  
  2000-08-09:
  
    Moved SimplifiedModel to new file models.m
  
  2000-08-10:
  
    Removed attribute SimplifiedModel (it doesn't appear to be particularly
      useful).
  
  2000-08-16:
  
    Moved BadPrimes here from selmer.m
  
  2000-08-17:
  
    Extended BadPrimes to take a parameter Badness -> returns only
      primes p such that p^Badness divides the discriminant
  
    Improvement in ZetaFunction(C, F) (no need to factor the discriminant)
    
   2000-08-25:
   
     In BaseExtend/BaseChange -- allow Rng type (instead of Fld)
       (reason: Laurent series fields are NOT of type Fld!)
   
   2000-09-29:
   
     Made Factor1 work on negative integers.
   
   2001-01-28:
     
     Fixed two small bugs in IsHyperellipticCurve (and ...OfGenus) --
     (1) Return false when deg_even is zero (does not define a reduced
         and geometrically irreducible curve in this case); additional 
         check by P. Gaudry to catch trivial cases, like h=f=0.
     (2) ChangeUniverse(s, R) --> ChangeUniverse(s, PolynomialRing(R))


   2001-06:

   Scheme merge:
   *************
   
     Removed HomogeneousEquation/Polynomial
     (Equation on SchHyp does the trick)
     Removed Random(SchHyp): now in kernel (see 04/12/01 below)
     (that was a mistake of mine)
     Removed BaseChange/BaseExtend for SchHyp, Ring, Map and nth extension:
	 superseeded by the Sch protos
     Removed RationalPoints(C::SchHyp : Bound := 0) since
         RationalPoints(<Sch> X) is defined first
	 (anyway, no big deal here, Points achieves the same and
	 is in the kernel

   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   HyperellipticCurve & Curve fix


   2001-12-04: (Paulette)
   
   Fixed (once again) Random so that abscissa are taken in the
   finite field instead of the prime field only.
   
   2001-05: David Kohel
   Replaced HyperellipticCurve(::CrvEll) with intrinsic
   returning scheme maps (MapSch).   
   
   2002-06: David Kohel
   Points/RationalPoints, signatures

   2002-10: Paulette
   swap f & h in HyperellipticCurve creation and everywhere where relevant:
   HyperellipticCurve(f, h)

   2003-02: Paul van Wamelen
   IsHyperellipticCurve and IsHyperellipticCurveOfGenus wanted the sequence
   in the order h, f. Swapped to respect the previous change. Wasn't
   documented either way. Fixed.
   
   2004-03: Mike Harrison
   #C and ZetaFunction(C) updated to consider the genus 1 case and for
   genus >= 2 to use fast p-adic methods if applicable (currently
   Kedlaya in odd characteristic and Mestre/Lercier/Lubicz in char 2).
   A number of related point-counting subroutines (also used by #J) have
   been isolated and added.
   A set of helper functions have been added at the end to handle checking
   for and carrying out the new point-counting methods in a uniform way
   (used by #C, ZetaFunction(C), #J, EulerFactor(J)).

   2004-07: Mike Harrison
   Added special case caode for genus 0 to #C and ZetaFunction(C) and
   made slight change to GoodEquation function to reflect the
   jacobian group law having been generalised.

   2005-02: Nicole Sutherland
   Use of extended types in signatures for ZetaFunction to stop ambiguity with
   ZetaFunction(Crv) signature.
  ------------------------------------------------------------------
  
  TO DO:
  
    + Optional parameter UseMordellWeilGroup to (Rational)Points.
      If set to true, compute MW group (if not already done) and
      use it for the search (can go up to _much_ larger height in
      this way).
      
  2001-06-14: Require statements in RationalPoints.

  2003-09-16: (Nils Bruin) HyperellipticCurve from Conic installed
  
  *******************************************/

// We view a hyperelliptic curve of genus g as living in weighted
// projective space with coordinate ring K[x,y,z], where x and z have
// weight 1 and y has weight g+1. The equation
//  y^2 + h(x,z)*y = f(x,z)
// is then homogeneous of degree 2g+2.

////////////////////////////
//                        //
//      declarations      //
//                        //
////////////////////////////

forward UseZetaMethod, ApplyZetaMethod;

import "kedlaya.m" : KedCharPolyOdd;
import "Canonlift_char2/mestre_main.m" : Mestre_CharPoly_Char2;
import "kedlaya_char2.m" : KedlayaChar2;
import "jac_count.m" : GroupLawEquation;

declare attributes CrvHyp:
    // the following attributes are assigned when needed
    // SimplifiedModel,     // a model of the form y^2 = f(x)
    // HomogeneousEquation, // a weighted homogeneous equation as above
    Discriminant,        // the discriminant
    BadPrimes;           // information on bad primes

////////////////////////////
//                        //
//  Hyperelliptic Curves  //
//                        //
////////////////////////////

// intrinsics SetNormalize & Point & attribute NormalizePoint 
// have disappeared: this is now taken in charge 
// via the coercion C!P or C![a,b,c] -- see hc_coerce


///////////////////////////
//                       //
//       creation        //
//                       //
///////////////////////////

intrinsic HyperellipticCurve(s::[RngUPolElt]) -> CrvHyp
    {The hyperelliptic curve given by the polynomial sequence s.}
    require #s eq 2: "Argument must have length 2";
    return HyperellipticCurve(s[1], s[2]);
end intrinsic;

//*** Let the following directly refer to the kernel function
//*** MS 2000-03-24

intrinsic HyperellipticCurve(f::RngUPolElt, h::RngElt) -> CrvHyp
    {The hyperelliptic curve given by y^2 + h y = f.}
    return HyperellipticCurve(f, Parent(f)!h);
end intrinsic;

intrinsic HyperellipticCurve(f::RngElt, h::RngUPolElt) -> CrvHyp
    {The hyperelliptic curve given by y^2 + h y = f.}
    return HyperellipticCurve(Parent(h)!f, h);
end intrinsic;

//*** Check is done by the kernel function, so remove it here
//*** MS 2000-03-24
intrinsic HyperellipticCurve(f::RngUPolElt) -> CrvHyp
    {The hyperelliptic curve given by y^2 = f.}
    return HyperellipticCurve(f, Parent(f)!0);
end intrinsic;

//*** New variants with given genus
//*** MS 2000-08-08
intrinsic HyperellipticCurveOfGenus(g::RngIntElt, f::RngUPolElt, h::RngUPolElt)
  -> CrvHyp
    {The hyperelliptic curve of genus g given by y^2 + h y = f.}
    require g ge 0: "Genus g cannot be negative.";
    require CoefficientRing(Parent(h)) cmpeq CoefficientRing(Parent(f)):
            "Polynomials must have the same coefficient ring.";
    R := CoefficientRing(Parent(f));
    require Degree(f) le 2*g+2 and Degree(h) le g+1:
            "Degrees of the polynomials are too large.";
    if Characteristic(R) eq 2 then
      require Coefficient(h,g+1) ne 0 or
              Coefficient(h,g)^2*Coefficient(f,2*g+2) ne Coefficient(f,2*g+1)^2:
              "Singularity at infinity.";
    else
      require Degree(h^2+4*f) ge 2*g+1: "Singularity at infinity.";
    end if;
    return HyperellipticCurve(f, h);
end intrinsic;

intrinsic HyperellipticCurveOfGenus(g::RngIntElt, s::[RngUPolElt]) -> CrvHyp
    {The hyperelliptic curve of genus g given by y^2 + s[2] y = s[1].}
    require #s eq 2: "Argument must have length 2";
    return HyperellipticCurveOfGenus(g, s[1], s[2]);
end intrinsic;

intrinsic HyperellipticCurveOfGenus(g::RngIntElt, f::RngUPolElt, h::RngElt)
  -> CrvHyp
    {The hyperelliptic curve of genus g given by y^2 + h y = f.}
    return HyperellipticCurveOfGenus(g, f, Parent(f)!h);
end intrinsic;

intrinsic HyperellipticCurveOfGenus(g::RngIntElt, f::RngElt, h::RngUPolElt)
  -> CrvHyp
    {The hyperelliptic curve of genus g given by y^2 + h y = f.}
    return HyperellipticCurveOfGenus(g, Parent(h)!f, h);
end intrinsic;

intrinsic HyperellipticCurveOfGenus(g::RngIntElt, f::RngUPolElt)
  -> CrvHyp
    {The hyperelliptic curve of genus g given by y^2 = f.}
    return HyperellipticCurveOfGenus(g, f, Parent(f)!0);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//               Constructor from Conic Curve                     //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic HyperellipticCurve(C::CrvCon)->CrvHyp,MapSch
  {Returns the curve C as a hyperelliptic curve}
  P2:=Ambient(C);
  Cd,M:=DiagonalForm(C);
  Cd:=Curve(P2,Cd);
  CtoCd:=Restriction(Inverse(Automorphism(P2,M)),C,Cd);
  X:=P2.1;Y:=P2.2;Z:=P2.3;
  R:=BaseRing(Cd);
  P:=PolynomialRing(R);
  f:=DefiningEquation(Cd);
  scl:=-Coefficient(f,Y,2);
  Hpol:=[Evaluate(g,[P.1,0,1]):g in
      [Coefficient(f,Y,0)/scl,Coefficient(f,Y,1)/scl]];
  H:=HyperellipticCurveOfGenus(0,Hpol);
  AH:=Ambient(H);
  return H,CtoCd*map<Cd->H|[X,Y,Z],[AH.1,AH.2,AH.3]>;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//               Constructor from Elliptic Curve                  //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic HyperellipticCurve(E::CrvEll) -> CrvHyp, MapSch, MapSch
    {The hyperelliptic curve E specified by the elliptic curve C,
    followed by the morphism E -> C and its inverse.}

    P := PolynomialRing(BaseRing(E)); x := P.1;
    a1,a2,a3,a4,a6 := Explode(Eltseq(E));
    C := HyperellipticCurve(P![a6,a4,a2,1], P![a3,a1]);
    CAE := CoordinateRing(Ambient(E));
    X := CAE.1; Y := CAE.2; Z := CAE.3;
    f1 := [ X, Y*Z, Z ];
/******** As far as I can see, f1 is defined everywhere on E, so we don't need a
second patch.
    X3onZ := Y*(Y+a1*X+a3*Z)-(a2*X^2+a4*X*Z+a6*Z^2);
    f2 := [ X3onZ, X*Y*X3onZ, X^2 ];
**********/
    CAC := CoordinateRing(Ambient(C));
    U := CAC.1; V := CAC.2; W := CAC.3;
    g1 := [ U*W, V, W^2 ];
    g2 := [ U*(V+a1*U*W+a3*W^2),
           (U^3+a2*U^2*W+a4*U*W^2+a6*W^3),
           (V+a1*U*W+a3*W^2)*W ];
    return C, hom< E -> C | f1,g1 >, hom< C -> E | [g1, g2] >;
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                      Creation predicate                        //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic IsHyperellipticCurve(s::[RngUPolElt]) -> BoolElt, CrvHyp
    {Returns true if and only if the equation y^2 + s[2]*y = s[1] defines 
    a hyperelliptic curve. In this case, the curve is returned as a 
    second value.}

    if #s ne 2 then return false, _; end if;
    R := CoefficientRing(Universe(s));
    if not IsField(R) then
      R := FieldOfFractions(R);
      s := ChangeUniverse(s, PolynomialRing(R));
    end if;
    f := s[1]; h := s[2];
    degree := Max(Degree(f), 2*Degree(h));
    deg_even := (IsOdd(degree)) select degree + 1 else degree;
    if deg_even eq 0 then return false, _; end if;
    if Characteristic(R) eq 2 then
      if h eq 0 then return false, _; end if;
      hx := Derivative(h);
      fx := Derivative(f);
      gcdx := GCD(h, hx^2*f - fx^2);
      if Degree(gcdx) gt 0 then return false, _; end if;
      d2 := deg_even div 2;
      if Degree(h) eq d2 then 
         return true, HyperellipticCurve(f, h); 
      end if;
      if Coefficient(h, d2-1)^2*Coefficient(f, deg_even)
          eq Coefficient(f, deg_even-1)^2
      then return false, _; end if;
    else
      k := h^2 + 4*f;
      if Degree(k) le deg_even-2 or Degree(k) eq 0 then
         return false, _; 
      end if;
      if Discriminant(k) eq R!0 then return false, _; end if;
    end if;
    return true, HyperellipticCurve(f, h);
end intrinsic;

//*** Variant with specified genus
//*** MS 2000-08-08
intrinsic IsHyperellipticCurveOfGenus(g::RngIntElt, s::[RngUPolElt])
   -> BoolElt, CrvHyp
    {Returns true if and only if the equation y^2 + s[2]*y = s[1]
    defines a hyperelliptic curve of genus g. In this case, the curve is
    returned as a second value.}

    if #s ne 2 then return false, _; end if;
    R := CoefficientRing(Universe(s));
    if not IsField(R) then
      R := FieldOfFractions(R);
      s := ChangeUniverse(s, PolynomialRing(R));
    end if;
    h := s[2]; f := s[1];
    degree := Max(Degree(f), 2*Degree(h));
    deg_even := (IsOdd(degree)) select degree + 1 else degree;
    if deg_even ne 2*g+2 then return false, _; end if;
    if Characteristic(R) eq 2 then
      // homogenize
      if h eq 0 then return false, _; end if;
      hx := Derivative(h);
      fx := Derivative(f);
      gcdx := GCD(h, hx^2*f - fx^2);
      if Degree(gcdx) gt 0 then return false, _; end if;
      d2 := deg_even div 2;
      if Degree(h) eq d2 then 
         return true, HyperellipticCurve(f, h); 
      end if;
      if Coefficient(h, d2-1)^2*Coefficient(f, deg_even)
          eq Coefficient(f, deg_even-1)^2
      then return false, _; end if;
    else
      k := h^2 + 4*f;
      if Degree(k) le deg_even-2 or Degree(k) eq 0 then
         return false, _; 
      end if;
      if Discriminant(k) eq R!0 then return false, _; end if;
    end if;
    return true, HyperellipticCurve(f, h);
end intrinsic;

////////////////////////////////////////////////////////////////////
//                                                                //
//                         Attribute Access                       //
//                                                                //
////////////////////////////////////////////////////////////////////

intrinsic EvaluatePolynomial(C::CrvHyp, a::RngElt, b::RngElt, c::RngElt)
    -> RngElt
    {Evaluates the homogeneous defining polynomial of C at s = [a,b,c].} 
    return Evaluate(DefiningPolynomial(C), [a,b,c]);
end intrinsic;

intrinsic EvaluatePolynomial(C::CrvHyp, s::[RngElt])
    -> RngElt
    {"} // "
    require #s eq 3 : "Argument 2 must be a sequence of length 3.";
    return Evaluate(DefiningPolynomial(C), s);
end intrinsic;

//////////////
//          //
//  Points  //
//          //
//////////////


intrinsic IsPoint(C::CrvHyp, S::SeqEnum) -> BoolElt, PtHyp
    {Returns true if and only if S specifes a point on C, and, 
    if so, returns the point as a second value.}
    R := CoefficientRing(C);
    require #S le 3 and #S ge 2:
       "Argument 2 must have length 2 or 3";
    a := S[1]; b := S[2]; c := (#S eq 3) select S[3] else R!1;
    if EvaluatePolynomial(C, a, b, c) eq 0 then
       if a eq 0 and c eq 0 then return false, _; end if;
       return true, C![R | a, b, c];
    else
       return false, _;
    end if;
end intrinsic;

///////////////////////////
//                       //
//  basic arithmetic     //
//                       //
///////////////////////////

intrinsic Involution(P::PtHyp) -> PtHyp
{The application of the hyperelliptic involution to P.}
    C := Scheme(P);
    R := Ring(Parent(P));
    _, h := HyperellipticPolynomials(C);
    // Map (x, y, z) to (x, -h(x,z)-y, z)
    if h eq 0 then return C(R)! [P[1], -P[2], P[3]]; end if;
    P2 := PolynomialRing(CoefficientRing(Parent(h)), 2);
    x := P2.1; z := P2.2;
    d := Genus(C) + 1;
    hhom := &+[ Coefficient(h,i)*x^i*z^(d-i) : i in [0..d] ];
    return C(R)! [P[1], -Evaluate(hhom, [P[1],P[3]])-P[2], P[3]];
end intrinsic;


intrinsic '-'(P::PtHyp) -> PtHyp
{The application of the hyperelliptic involution to P. }
    return Involution(P);
end intrinsic;


intrinsic Discriminant(C::CrvHyp) -> RngElt
{The discriminant of the curve C.}
    if assigned C`Discriminant then return C`Discriminant; end if;
    f, h := HyperellipticPolynomials(C);
    R := CoefficientRing(C);
    if Characteristic(R) eq 2 then
      require R eq FiniteField(2):
          "Can't compute the discriminant in characteristic 2 in general.\n",
	  "Need an implementation of Witt vectors to do it.";
      // if R = GF(2), then disc = 1 (since non-zero)
      C`Discriminant := R!1;
      return R!1;
    else
      k := h^2 + 4*f;
      g := Genus(C);
      if Degree(k) lt 2*g + 2 then
        disc := LeadingCoefficient(k)^2*Discriminant(k)/2^(4*g+4);
        C`Discriminant := disc;
        return disc;
      else
        disc := Discriminant(k)/2^(4*g+4);
        C`Discriminant := disc;
        return disc;
      end if;
    end if;
end intrinsic;

TrialDivisionBound := 10^6;

function Factor1(n, expo)
  // Find the part of the factorisation of n (non-zero integer) with
  // exponents at least expo.
  // Returns (at least) this part of the factorisation
  // and the remaining factor of n.
  n := Abs(n); // avoid problems with negative numbers
  flag, root := IsPower(n, expo);
  if flag then
    // special case
    return [ <a[1], expo*a[2]> : a in Factorisation(root) ], 1;
  end if;
  // now there must be prime divisors less than n^(1/(expo+1)).
  bound := Floor((RealField()!n)^(1/(expo+1)));
  fact, r := TrialDivision(n, Minimum(bound, TrialDivisionBound));
  n := IsEmpty(r) select 1 else r[1];
  flag, root := IsPower(n, expo);
  if flag then
    // special case
    return fact cat [ <a[1], expo*a[2]> : a in Factorisation(root) ], 1;
  end if;
  if n le TrialDivisionBound^(expo+1) then
    // no prime divisor less than n^(1/(expo+1))
    return fact, n;
  end if;
  if IsPrime(n) then
    return fact cat [ <n, 1> ], 1;
  end if;
  // at this point, we have to do the complete factorisation.
  return fact cat Factorisation(n : TrialDivisionLimit := 0), 1;
end function;

intrinsic BadPrimes(C::CrvHyp : Badness := 1) -> SeqEnum
{Returns the sequence of primes where the given model of C has bad reduction.
 C must be defined over a number field, and the defining polynomials must
 have integral coefficients. 
 If C is defined over the rationals, the parameter Badness can be given;
 then only primes are returned such that the valuation of the discriminant
 at the prime is at least Badness.}
  K := BaseField(C);
  require K cmpeq Rationals() or ISA(Type(K), FldAlg):
          "BadPrimes is only implemented for curves over number fields.";
  require IsIntegral(C):
          "BadPrimes is only implemented for curves defined by polynomials",
          "with integral coefficients.";
  require Type(Badness) eq RngIntElt and Badness ge 1:
          "Badness must be a positive integer.";
  disc := Integers(K)!Discriminant(C);
  if K cmpeq Rationals() then
    if assigned C`BadPrimes then
      b := C`BadPrimes[2];
      if b le Badness then
        return [ pr[1] : pr in C`BadPrimes[1] | pr[2] ge Badness ];
      end if;
      // factor remaining part
      fact, n := Factor1(C`BadPrimes[3], Badness);
      fact := C`BadPrimes[1] cat fact;
      C`BadPrimes := < fact, n gt 1 select Badness else 1, n >;
      return [ pr[1] : pr in fact | pr[2] ge Badness ];
    else
      // factor disc
      fact, n := Factor1(disc, Badness);
      C`BadPrimes := < fact, n gt 1 select Badness else 1, n >;
      return [ pr[1] : pr in fact | pr[2] ge Badness ];
    end if;
  else
    if assigned C`BadPrimes then return [pr[1] : pr in C`BadPrimes[1]]; end if;
    fact := Factorization(ideal< Integers(K) | disc >);
    C`BadPrimes := <fact>;
    return [ x[1] : x in  fact ];
  end if;
end intrinsic;

///////////////////////////////
//                           //
//   Enumeration of points   //
//                           //
///////////////////////////////

intrinsic RationalPoints(C::CrvHyp, x::RngElt) -> SetIndx
   {Same as Points(C,x)}

   R := CoefficientRing(C);
   bool, x := IsCoercible(R, x);
   require bool: 
      "The given x-value must be coercible to the base field of the curve";

   return Points(C,x);
end intrinsic;

intrinsic RationalPoints(C::CrvHyp, x::Infty) -> SetIndx
   {"} // "
   return PointsAtInfinity(C);
end intrinsic;

intrinsic Points(C::CrvHyp, x::RngElt) -> SetIndx
   {Returns the indexed set of all rational points on the 
   hyperelliptic curve C with x-coordinate equal to x
   (where rational means rational over the base field of C)}

   R := CoefficientRing(C);
   bool, x := IsCoercible(R, x);
   require bool: 
      "The given x-value must be coercible to the base field of the curve";

   f, h := HyperellipticPolynomials(C);
   if h eq 0 then
      fx := Evaluate(f, x);
      if fx eq 0 then
         return {@ C(R)![R | x,0,1] @};
      else
         iss, sqrt := IsSquare(fx); 
         if iss then
            return {@ C(R)![R | x,sqrt,1], C(R)![R | x,-sqrt,1] @};
         else
            return {@ @};
         end if;
      end if;
   else
      P := PolynomialRing(R);
      hx := Evaluate(h, x); fx := Evaluate(f, x);
      return {@ C(R)![R | x,r[1],1] :  r in Roots(P.1^2 + hx*P.1 - fx) @};
   end if;
end intrinsic;

intrinsic Points(C::CrvHyp, x::Infty) -> SetIndx
   {Returns the rational points at infinity on C}
   return PointsAtInfinity(C);
end intrinsic;

//////////////////////////////////////////
//                                      //
//   Zeta functions / Counting points   //
//                                      //
//////////////////////////////////////////

function NaiveEulerFactor(C)
 
   q := #BaseRing(C);
   g := Genus(C);
   pi := [ q^n + 1 - InternalOrder(BaseExtend(C, n)) : n in [1..g] ];
   s := [ Integers() |
          (n eq 0) select 1 else -&+[ s1[k+1]*pi[n-k] : k in [0..n-1] ]/n
                        where s1 := Self()
	      : n in [0..g] ];
   s := s cat [ q^k*s[g-k+1] : k in [1..g] ];
   return PolynomialRing(Integers())!s;
   
end function;

function EulerFactorOverExtn(e_fact,ext_deg)

    cp := Parent(e_fact) ! Reverse(Eltseq(e_fact));
    MP<X,Y> := PolynomialRing(Rationals(),2);
    cp := Evaluate( Resultant( Evaluate(cp,X), Y-X^ext_deg, X ),
                       [0,Parent(cp).1] );
    return Parent(cp) ! Reverse(Eltseq(cp));

end function;

intrinsic '#'(C::CrvHyp[FldFin]) -> RngIntElt
{The number of rational points on the curve over a finite field.}

   R := CoefficientRing(C);
   //require IsFinite(R): "Base field of argument must be finite.";

   if Genus(C) eq 0 then return (#R + 1); end if;
   
   if #R le 1000000 then 
      vprint JacHypCnt: "Using naive counting algorithm.";
      return InternalOrder(C);
   end if;
   
   J := Jacobian(C);
   if assigned J`EulerFactor then
       return #R + 1 + Coefficient(J`EulerFactor,1);
   end if;
   usezeta,meth,C1,tw := UseZetaMethod(C);
   ext_deg := Degree(R) div Degree(BaseRing(C1));
   if usezeta then // can use fast methods to compute the Euler factor
       charpol := ApplyZetaMethod(meth,C1,tw,ext_deg);
       J`EulerFactor := charpol;
       return #R + 1 + Coefficient(charpol,1);
   else   // back to naive count
       if ext_deg gt Genus(C) then
          charpol := ApplyZetaMethod(1,C1,tw,ext_deg);
          J`EulerFactor := charpol;
          return #R + 1 + Coefficient(charpol,1);
       else
          vprint JacHypCnt: "Using naive counting algorithm.";
          return InternalOrder(C);
       end if;
   end if;

end intrinsic;

intrinsic ZetaFunction(C::CrvHyp[FldFin]) -> FldFunRatUElt
   {The zeta function of C, with finite base field, as a rational 
   function of one variable.}
   R := CoefficientRing(C);
   require HasFunctionField(C): "Function field of curve must be computable";
   if Genus(C) eq 0 then //easy case!
       charpol := 1;  
   else
       J := Jacobian(C);
       if assigned J`EulerFactor then
           charpol := J`EulerFactor;
       else
           usezeta,meth,C1,tw := UseZetaMethod(C);
           ext_deg := Degree(R) div Degree(BaseRing(C1));
           if usezeta then
               charpol := ApplyZetaMethod(meth,C1,tw,ext_deg);
           else // Use naive count. Urrgh!!
               charpol := ApplyZetaMethod(1,C1,tw,ext_deg);
           end if;
       end if;
       if not assigned J`EulerFactor then
           J`EulerFactor := charpol;
       end if;
   end if;
   F := FunctionField(Integers()); T := F.1;
   return (F!charpol)/((1 - T)*(1 - #R*T));

end intrinsic;

intrinsic ZetaFunction(C::CrvHyp[FldRat],K::FldFin) -> FldFunRatUElt
   {The zeta function of the base extension of C to K, as a rational 
   function of one variable.}
   require Valuation(Discriminant(C), Characteristic(K)) eq 0:
       "Argument 1 must have good reduction over argument 2";
   F := FunctionField(Integers()); T := F.1;
   return EulerFactor(BaseExtend(Jacobian(C),K))/((1 - T)*(1 - #K*T));
end intrinsic;


//// a good random function (one that doesn't require to compute all
//// the points on the curve


intrinsic Random(C::CrvHyp[FldFin]) -> PtHyp
{ Find a random point on C. Base field must be finite. If the set of all
  points on C has already been computed, this gives a truly random point,
  otherwise the ramification points have a slight advantage. }
    R := CoefficientRing(C);
    //require IsFinite(R): "Base field must be finite:\n",C;
    if PointsKnown(C) then
      require not IsEmpty(Points(C)): "Curve has no rational point:\n",C;
      return Random(Points(C));
    end if;
    q := #R;
    if (1+q)^2 le 4*Genus(C)^2*q then
      // curve might have no rational point
      require #C ne 0: "Curve has no rational point:\n",C;
    end if;
    while true do
      r := Random(q);
      if r eq q then
        pts := PointsAtInfinity(C);
      else
        pts := Points(C, Random(R));
      end if;
      if not IsEmpty(pts) then return Random(pts); end if;
    end while;
end intrinsic;

///////////////////////////////////////////////////////////////////////////
//
// Euler Factor Method Utilities
//
///////////////////////////////////////////////////////////////////////////
//
// Functions to decide whether point-counting methods (over finite
// fields) which yield the Euler factor of C are applicable and
// appropriate (for C or Jacobian(C)). In particular, pAdic methods
// are considered here.
//
// For small(ish) base characteristics the pAdic ones are the preferred 
// algorithms (unless the base field is small enough for naive counting),
// being currently the fastest (and also giving the full Euler Factor).
//
///////////////////////////////////////////////////////////////////////////

// Function to decide whether 
//  a hyper elliptic curve C in char 2 of genus g is ordinary <=>
//  J=Jacobian(C) is an ordinary abelian variety              <=>
//  J[2] is maximal ( = (Z/2Z)^g)                             <=>
//  C has the maximal number of Weierstrass points (g).
// This is a necessary precondition for algorithms derived from
// Mestre's to apply.

function IsOrdinaryChar2(C)

  g := Genus(C);
  f,h := HyperellipticPolynomials(C);
  d1 := Degree(h); d2 := Degree(f);
  if d1 lt g then return false; end if;
  if Discriminant(h) eq 0 then return false; end if;
  return true;
  
end function;

// Utility function to see whether J=Jacobian(C) is of a type having
// an implememented group law (Genus(C) > 1) . If not, tries to find an
// isomorphic C or quadratic twist for which this is true.
// BIT OF A HACK! ASSUMES CURRENT GROUP LAW TYPES - 0,1-5,11-15.
// Returns 0,* if no good C1 is found, else 1,C1 (C1 good IM to C)
//    or -1,C1 (C1 good IM to standard quadratic twist of C).
// Note (07/04): with the group law extended, now the only case of
// no group law is for odd genus and 0 rational points at infinity.

function GoodEquation(C);

  inf := NumberOfPointsAtInfinity(C);
  g := Genus(C);
  if (inf ge 1) or (g eq 2) then
     return 1,C;
  end if;
  if IsEven(g) then
     // use the right quadratic twist with 0 points at infinity.
     if inf eq 0 then 
        return 1,C; 
     else	 
        return -1,QuadraticTwist(C);	 
     end if;
  end if;
  // last case : 0 points at infinity and g odd!
  boo, C1 := GroupLawEquation(C);
  if boo then // in fact boo will always be true now!!
      return 1,C1;
  else
      return 0,0;
  end if;
  
end function;

// Function to see whether a p-adic lift method (Kedlaya or Mestre)
// can be used.
// Return value is as for the GoodEquation function + methodnumber,
// 0,*,_ meaning "don't use pAdic algorithm".

function UsePAdicMethods(C)

  p := Characteristic(BaseRing(C));
  if p gt 1000 then 
     return 0,0,0;    // characteristic too large
  elif p gt 2 then
     return 1,C,3;    // kedlaya (odd char)
  else       // char = 2 - Mestre or Kedlaya.
    if (Genus(C) gt 4)  or (Degree(BaseRing(C))+1 lt Genus(C)) or
            (not IsOrdinaryChar2(C)) then
        return 1,C,5; // kedlaya (char 2)
    end if;
    twist,C1 := GoodEquation(C);
    if twist eq 0 then return 1,C,5; end if;
    // last check on whether to use Kedlaya over Mestre -
    //  if g=4 and J(C) two torsion isn't rational
    if Genus(C) eq 4 then
	_,h := HyperellipticPolynomials(C1);
	if #Roots(h) lt 4 then return 1,C,5; end if;
    end if;
    return twist,C1,4;
  end if;
  
end function;

// Function to determine whether one of the preferred methods
// yielding the full euler factor should be used for point
// counting on C or Jacobian(C). The return value is
//    true/false, method number(0 if false), C1, twist
// where
//    twist = +/-1 indicates a quadratic twist (or not)
//    C1 IM to C or its quad twist/Fq (depending on twist) but 
//  possibly with a better equation (eg,for Jacobian group law)
//   [Fq is a subfield of BaseRing(C) over which C can be
//  defined]
// and the method numbers are (lower numbers <-> higher priority)
//  1 - use naive counting on C1,C1/Fq(2),...
//  2 - C of genus 1 - use elliptic curve methods.
//  3 - use Kedlaya odd char
//  4 - use Mestre/Lercier (char 2)
//  5 - use Kedlaya char 2

function UseZetaMethod(C)

    Fq := BaseRing(C);
    p := Characteristic(Fq);
    g := Genus(C);
    if (#Fq)^g lt 1000000 then  // use naive count
      return true,1,C,1;
    end if;
    if g eq 1 then // convert to elliptic curve and use SEA
      if NumberOfPointsAtInfinity(C) ne 0 then
        twist := 1;
        C1 := C;
      else
        twist := -1;
        C1 := QuadraticTwist(C);
      end if;
      E := EllipticCurve(C1,PointsAtInfinity(C1)[1]);
      return true,2,E,twist;
    end if;
    // try to find a smaller base field    
    n := Degree(Fq);
    C1 := C;
    if n gt 1 then
	f, h := HyperellipticPolynomials(C);
	current_ext := 1;
	for x in Coefficients(f) cat Coefficients(h) do
	    divisors := Divisors(n div current_ext);
	    Reverse(~divisors); Prune(~divisors);
	    y := x^(p^current_ext);
            c := 1;
	    while y ne x do
		assert(#divisors ne 0);
		c := divisors[#divisors];
		Prune(~divisors);
		y := x^(p^(current_ext*c));
	    end while;
	    current_ext *:= c;
	    if current_ext eq n then break; end if;
	end for;

	if current_ext ne n then
            F_new := FiniteField(p,current_ext);
	    Embed(F_new, Fq);
            Fq := F_new;
            C1 := HyperellipticCurve([R!f,R!h]) where R is 
                     PolynomialRing(Fq);
            //recheck for naive
            if (#Fq)^g lt 1000000 then
               return true,1,C1,1;
            end if;
	end if;
    end if;
    //check for padic methods
    twist,C2,methno := UsePAdicMethods(C1);
    if twist eq 0 then 
        return false,0,C1,1;
    else
        return true,methno,C2,twist;
    end if;
    /* expected upcoming additions: Genus2 methods for full euler factor.
    */

end function;

function ApplyZetaMethod(method_number, C, twist, ext_deg)                                    

  if ext_deg gt 1 then
      vprintf JacHypCnt: "Working over smaller field (degree %o).\n",
                                 Degree(BaseRing(C));
  end if;
  if twist eq -1 then
     vprint JacHypCnt: "Working with quadratic twist.";
  end if;  
  case method_number:

    when 1: //use naive count
      vprint JacHypCnt: "Using naive counting algorithm.";
      vtime JacHypCnt,2: charpol := NaiveEulerFactor(C);
 
    when 2: // C is a CrvEll
      vprint JacHypCnt: "Using elliptic curve point counting.";
      charpol := PolynomialRing(IntegerRing())![1,twist*(#C-q-1),q] where
                         q is #BaseRing(C);

    when 3: // use Kedlaya
      vprint JacHypCnt: "Using Kedlaya's algorithm.";
      charpol := KedCharPolyOdd(C);
      
    when 4: // use Mestre (char = 2)
      vprint JacHypCnt: "Using Mestre's method.";
      charpol := Mestre_CharPoly_Char2(C);			 

    when 5: // use Kedlaya (char = 2)
      vprint JacHypCnt: "Using Kedlaya/Vercauteren's algorithm.";
      charpol := KedlayaChar2(C);
			 
  end case;
  if twist eq -1 then
     charpol := Parent(charpol)![Coefficient(charpol,i)*(-1)^i :
                                   i in [0..Degree(charpol)]];
  end if;
  if ext_deg gt 1 then // go back to original base field
      charpol := EulerFactorOverExtn(charpol,ext_deg);
  end if;
  return charpol;
  
end function;

 
