freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!
/*******************************************
 * Hyperelliptic/models.m                  *
 *                                         *
 * Various models of hyperelliptic curves  *
 *                                         *
 * Michael Stoll                           *
 *                                         *
 * started 09-Aug-2000                     *
 *******************************************/

/*-------------------------------------------------------------------
  All the functions computing other models of a curve C return three 
  values --
    (1) the new curve C'
    (2) the map on points C -> C' (invertible)
    (3) the transformation leading from C to C'
  -------------------------------------------------------------------*/

/*-------------------------------------------------------------------
  CHANGES
  =======

  M. Stoll, 2000-08-17:
    
      Modified MinimalWeierstrassModel
       + Uses Badness parameter to BadPrimes
       + Has a parameter Bound to restrict the primes that are checked
   
  2000-09-29:
   
     Small change in ModelForTSG -- in the even degree case, the
       absolute value of the leading coefficient is used when computing
       the transformation (instead of the lcf itself).
  
  2001-04-23:
  
     Fixed a bug in pMinimalWeierstrassModell (did think wrongly that
       model is minimal in some cases).
  
  2001-05-07:
  
     Fixed a bug in IspMinimal (fred was clobbered).
  
 
  P. Gaudry, 2001-03-19:
    Quick fix: make SimplifiedModel work for finite fields.
  
  M. Stoll, 2001-05-25:
  
    New intrinsic HasOddDegreeModel(SchHyp): Checks whether there
      is a model of type y^2 = f(x), deg(f) odd; returns model, map,
      transformation if it exists.

  David Kohel, June 2001:

  Changed over all constructors of transformations to a new datatype
  for hyperelliptic isomorphisms. 

  N.B. The isomorphisms have been changed from their definition as
  records, in that the defining data of the map on points is stored,
  which is the inverse of the isomorphism data in the records.

  Change in parity of isomorphisms (now consistent with morphisms
  of schemes) implies that every creation instance should have been
  replaced with the inverse data.


  2001-07: scheme merge. PL.

  2001-07: Paulette
  Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)

  2001-08 : Nicole Sutherland
  Scheme map types

  2001-09: David Kohel
  Incorporation of some bug fixes of Michael Stoll and compatibility
  with scheme map constructors

  2001-10, M. Stoll:
  Changes to allow rational function fields as base fields.
  Compare also places.m.

  2002-05, D. Kohel
  Require g > 1 in HasOddDegreeModel.
  Require statements in untype-checked intrinsics (for places)
  Import of Wamelen reduction algorithm (implemented by Paulette Lieby)
     as alternative to Stoll reduction algorithm in ReducedModel.  


  2002-09 N. Sutherland
  Look at the use of places. They seem to be all rational (incl rational
  function field). This can be replaced substituting the places for prime
  integers or polynomials (or 1/x as a valuation ring element). 
  Replacement valuation and residue field functions
  can be found at the end of the file. Uniformizing element is the prime. 

  2002-11 N. Bruin
  ReducedModel: genus at least 1 should be tested with Genus(..) ge 1.
  Now correct.

  2003-01 P. van Wamelen
  IsSimplifiedModel checked f eq 0 not h. Fixed.

  17/04/03 Nicole Sutherland
  Starting to deal with those rational places.
  
  27/08/03 Nils Bruin
  Fixed BadPrimes call in MinimalModel
  
  2007-07-02 Michael Stoll
  Bug fix in pMinimalWeierstrassModelfunction
  (computation of lambda' was wrong,in particular when fred was a constant)
  
  This fixes the following bug reported by Nils:
  > _<x>:=PolynomialRing(Rationals());
  > C:=HyperellipticCurve(15*x^4 + 220*x^3 + 510*x^2 + 1380*x + 3615);
  > MinimalWeierstrassModel(C);

  2010-04 Steve Donnelly
  Wamelen should never have been an option in ReducedModel. 
  It returns a quadratic twist, not an isomorphic curve.
  Adding a warning message, and new intrinsic ReducedWamelenModel
  
  -------------------------------------------------------------------*/

// Declarations

declare verbose CrvHypMinimal, 3;

import "../CrvG2/wam_red.m": WamelenReduction;
import "places.m" : MakePlaceIntElt, MakePlaceRatElt, MakePlaceUPolElt, 
			MakePlaceFunRatElt, MakePlaceFunRatInfty;

forward IspIntegralfunction, IspNormalfunction, IspMinimalfunction, 
	pIntegralModelfunction, pNormalModelfunction, 
	pMinimalWeierstrassModelfunction;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                             Predicates                             //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic IsSimplifiedModel(C::CrvHyp) -> BoolElt
    {Returns true if C is of the form y^2 = f(x).}
    _,h := HyperellipticPolynomials(C);
    return h eq 0;
end intrinsic;

intrinsic IsIntegral(C::CrvHyp) -> BoolElt
    {Returns true if C has integral coefficients.}
    f, h := HyperellipticPolynomials(C);
    check := Type(BaseField(C)) eq FldFunRat
              select func< x | Denominator(x) eq 1 >
              else IsIntegral;
    return forall{c : c in Coefficients(h) | check(c)}
            and forall{c : c in Coefficients(f) | check(c)};
end intrinsic;

function IntegerPrimeCheck(K, p)

    if Type(K) ne FldRat then
	return false, 
	       "Curve must be defined over the field of fractions of the prime";
    end if;

    if not IsPrime(p : Proof := false) then
	return false, "Argument 2 must be prime";
    end if;

    return true, MakePlaceIntElt(p);
end function;

function RationalPrimeCheck(K, p)

    if Type(K) ne FldRat then
	return false, 
	       "Curve must be defined over the field of fractions of the prime";
    end if;

    if not IsOne(Denominator(p)) then
	return false, "Argument 2 must be prime";
    end if;

    if not IsPrime(Integers()!p : Proof := false) then
	return false, "Argument 2 must be prime";
    end if;

    return true, MakePlaceRatElt(p);
end function;

function PolynomialPrimeCheck(K, p)

    if Integers(K) ne Parent(p) then
	return false, 
	       "Curve must be defined over the field of fractions of the prime";
    end if;

    if not IsIrreducible(p) then
	return false, "Argument 2 must be prime";
    end if;

    return true, MakePlaceUPolElt(p);
end function;

function RationalFunctionPrimeCheck(K, p)

    if K ne Parent(p) then
	return false, 
	       "Curve must be defined over the field of fractions of the prime";
    end if;

    if not IsOne(Denominator(p)) then
	return false, "Argument 2 must be prime";
    end if;

    if not IsIrreducible(Numerator(p)) then
	return false, "Argument 2 must be prime";
    end if;

    return true, MakePlaceFunRatElt(p);
end function;

function InfinityPrimeCheck(K, p)

    if Type(K) ne FldFunRat then
	return false, "Curve must be defined over a rational function field";
    end if;

    if Type(Integers(K)) ne RngUPol then
	return false, 
	       "Curve must be defined over a univariate rational function field";
    end if;

    return true, MakePlaceFunRatInfty(K, p);
end function;

function IspIntegralfunction(C, p)
    f, h := HyperellipticPolynomials(C);
    return forall{c : c in Coefficients(h) | Valuation(c, p) ge 0}
            and forall{c : c in Coefficients(f) | Valuation(c, p) ge 0};
end function;

intrinsic IspIntegral(C::CrvHyp, p::RngIntElt) -> BoolElt
{Returns true if C has p-adically integral coefficients.}
    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return IspIntegralfunction(C, place);
end intrinsic;

intrinsic IspIntegral(C::CrvHyp, p::FldRatElt) -> BoolElt
{Returns true if C has p-adically integral coefficients.}
    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return IspIntegralfunction(C, place);
end intrinsic;

intrinsic IspIntegral(C::CrvHyp, p::RngUPolElt) -> BoolElt
{Returns true if C has p-adically integral coefficients.}
    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return IspIntegralfunction(C, place);
end intrinsic;

intrinsic IspIntegral(C::CrvHyp, p::FldFunRatUElt) -> BoolElt
{Returns true if C has p-adically integral coefficients.}
    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return IspIntegralfunction(C, place);
end intrinsic;

intrinsic IspIntegral(C::CrvHyp, p::Infty) -> BoolElt
{Returns true if C has p-adically integral coefficients.}
    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return IspIntegralfunction(C, place);
end intrinsic;

// Should really know residue field characteristic ...
function IspNormalfunction(C, p)
// Returns true if C is p-adically normal.

    if not IspIntegralfunction(C, p) then return false; end if;
    f, h := HyperellipticPolynomials(C);
    val := func< pol | pol eq 0 select 10*(Genus(C) + 2) else
        Minimum([Valuation(c,p) : c in Coefficients(pol) | c ne 0]) >;
    RF, mRF, lRF := ResidueClassField(p);
    if Characteristic(RF) ne 2 then
        if h ne 0 then f := 4*f + h^2; end if;
        return val(f) le 1;
    else // residue char eq 2
        if val(h) eq 0 then return true; end if;
        if exists{i : i in [1..Degree(f) by 2] |
                mRF(Coefficient(f,i)) ne 0} then
            return true;
        end if;
        r := Parent(f)![lRF(mRF(Coefficient(f,2*i)))
                        : i in [0..Degree(f) div 2]];
        return val(f + r*h - r^2) eq 1;
    end if;
end function;

intrinsic IspNormal(C::CrvHyp, p::RngIntElt) -> BoolElt
{Returns true if C is p-adically normal.}
    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return IspNormalfunction(C, place);
end intrinsic;

intrinsic IspNormal(C::CrvHyp, p::FldRatElt) -> BoolElt
{Returns true if C is p-adically normal.}
    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return IspNormalfunction(C, place);
end intrinsic;

intrinsic IspNormal(C::CrvHyp, p::RngUPolElt) -> BoolElt
{Returns true if C is p-adically normal.}
    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return IspNormalfunction(C, place);
end intrinsic;

intrinsic IspNormal(C::CrvHyp, p::FldFunRatUElt) -> BoolElt
{Returns true if C is p-adically normal.}
    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return IspNormalfunction(C, place);
end intrinsic;

intrinsic IspNormal(C::CrvHyp, p::Infty) -> BoolElt
{Returns true if C is p-adically normal.}
    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return IspNormalfunction(C, place);
end intrinsic;

function IspMinimalfunction(C, p)

    if not IspNormalfunction(C, p) then return false, false; end if;
    f, h := HyperellipticPolynomials(C);
    x := Parent(f).1;
    g := Genus(C);
    l := func< pol | pol eq 0 select 10*(g+2) else
                     Minimum([i + Valuation(c,p) : i in [0..Degree(pol)]
                                  | c ne 0 where c := Coefficient(pol,i) ]) >;
    unique := true;
    RF, mRF, lRF := ResidueClassField(p);
    unif := UniformizingElement(p);
    P := PolynomialRing(RF);
    if Characteristic(RF) ne 2 then
        if h ne 0 then f := 4*f + h^2; end if;
        fred := P![mRF(c) : c in Coefficients(f)];
        if fred eq 0 then
            fred := P![mRF(1/unif*c) : c in Coefficients(f)];
        end if;
        check := function(f)
                 lam := l(f);
                 u := true;
                 if lam gt g then
                   // lambda le g ==> condition for unique minimal model
                   // satisfied here
                   if lam gt 2*((g+1) div 2) + 1 then
                     return false, false;
                   end if;
                   if lam gt 2*(g div 2) + 1 then
                     u := false;
                   end if;
                   f1 := unif^(-2*(lam div 2))*Evaluate(f, unif*x);
                   eps := lam mod 2;
                   fred := eps eq 0
                            select P![mRF(c) : c in Coefficients(f1)]
                            else P![mRF(1/unif*c) : c in Coefficients(f1)];
                   roots := [rt[1] : rt in Roots(fred) | rt[2] ge g+2-eps];
                   for r in roots do
                     lamp := l(Evaluate(f1, x + lRF(r)));
                     if lamp gt g+2 then
                       return false, false;
                     elif lamp eq g+2 then
                       u := false;
                     end if;
                   end for;
                 end if;
                 return true, u;
               end function;
      if Degree(fred) le g+1 then
        // check infinity
        f1 := Parent(f)![ Coefficient(f,2*g+2-i) : i in [0..2*g+2] ];
        a, b := check(f1);
        if not a then return false, false; end if;
        unique := unique and b;
      end if;
      roots := [ rt[1] : rt in Roots(fred) | rt[2] ge g+1 ];
      for r in roots do
        a, b := check(Evaluate(f, x + lRF(r)));
        if not a then return false, false; end if;
        unique := unique and b;
      end for;
      return true, unique;
    else // residue char eq 2
      assert IsFinite(RF);
      function lambda(h, f)
        while true do
          lh := l(h); lf := l(f);
          if 2*lh le lf or IsOdd(lf)
              or exists{i : i in [0..Degree(f)] | 
                         c ne 0 and i + Valuation(c, p) eq lf
                          and IsOdd(Valuation(c, p))
                         where c := Coefficient(f, i)}
          then
            return Minimum(2*lh, lf);
          else
            b := Parent(f)![ lRF(mRF(unif^(2*i-lf)*Coefficient(f, 2*i)))
                              : i in [0..Degree(f) div 2] ];
            f -:= b*(h+b);
            h +:= 2*b;
          end if;
        end while;
      end function;
      function lambdap(h, f)
        C0 := HyperellipticCurve(Evaluate(f, unif*x),Evaluate(h, unif*x));
        C0 := pNormalModelfunction(C0, p);
        f0, h0 := HyperellipticPolynomials(C0);
        h1 := Evaluate(h, x+1);
        f1 := Evaluate(f, x+1);
        return Maximum([lambda(Evaluate(h, x+lRF(z)), Evaluate(f, x+lRF(z)))
                         : z in RF]);
      end function;
      function check(h, f)
        lam := lambda(h, f);
        u := true;
        if lam gt g then
          // lambda le g ==> condition for unique minimal model
          // satisfied here
          if lam gt 2*((g+1) div 2) + 1 then
            return false, false;
          end if;
          if lam gt 2*(g div 2) + 1 then
            u := false;
          end if;
          lamp := lambdap(h, f);
          if lamp gt g+2 then
            return false, false;
          elif lamp eq g+2 then
            u := false;
          end if;
        end if;
        return true, u;
      end function;
      // check finite x
      for z in RF do
        a, b := check(Evaluate(h, x+lRF(z)), Evaluate(f, x+lRF(z)));
        if not a then return false, false; end if;
        unique := unique and b;
      end for;
      // check infinity
      h := Parent(h)![Coefficient(h, g+1-i) : i in [0..g+1]];
      f := Parent(f)![Coefficient(f, 2*g+2-i) : i in [0..2*g+2]];
      a, b := check(h, f);
      if not a then return false, false; end if;
      unique := unique and b;
      return true, unique;
    end if;
end function;


intrinsic IspMinimal(C::CrvHyp, p::RngIntElt) -> BoolElt, BoolElt
{Returns false, false if C is not a p-integral p-minimal model.
Returns true, false if C is p-integral, p-minimal, but not the
unique p-minimal model (up to the action of GL(2,O_p)).
Returns true, true if C is the unique (up to the action of GL(2,O_p))
p-integral p-minimal model.}

    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return IspMinimalfunction(C, place);
end intrinsic;

intrinsic IspMinimal(C::CrvHyp, p::FldRatElt) -> BoolElt, BoolElt
{Returns false, false if C is not a p-integral p-minimal model.
Returns true, false if C is p-integral, p-minimal, but not the
unique p-minimal model (up to the action of GL(2,O_p)).
Returns true, true if C is the unique (up to the action of GL(2,O_p))
p-integral p-minimal model.}

    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return IspMinimalfunction(C, place);
end intrinsic;

intrinsic IspMinimal(C::CrvHyp, p::RngUPolElt) -> BoolElt, BoolElt
{Returns false, false if C is not a p-integral p-minimal model.
Returns true, false if C is p-integral, p-minimal, but not the
unique p-minimal model (up to the action of GL(2,O_p)).
Returns true, true if C is the unique (up to the action of GL(2,O_p))
p-integral p-minimal model.}

    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return IspMinimalfunction(C, place);
end intrinsic;

intrinsic IspMinimal(C::CrvHyp, p::FldFunRatUElt) -> BoolElt, BoolElt
{Returns false, false if C is not a p-integral p-minimal model.
Returns true, false if C is p-integral, p-minimal, but not the
unique p-minimal model (up to the action of GL(2,O_p)).
Returns true, true if C is the unique (up to the action of GL(2,O_p))
p-integral p-minimal model.}

    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return IspMinimalfunction(C, place);
end intrinsic;

intrinsic IspMinimal(C::CrvHyp, p::Infty) -> BoolElt, BoolElt
{Returns false, false if C is not a p-integral p-minimal model.
Returns true, false if C is p-integral, p-minimal, but not the
unique p-minimal model (up to the action of GL(2,O_p)).
Returns true, true if C is the unique (up to the action of GL(2,O_p))
p-integral p-minimal model.}

    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return IspMinimalfunction(C, place);
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                         Alternate Models                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

intrinsic SimplifiedModel(C::CrvHyp) -> CrvHyp, MapIsoSch
    {Returns an isomorphic curve C' in the form v^2 = f(u) and 
    the isomorphism C -> C'.}

    K := BaseField(C);
    require Characteristic(K) ne 2: 
        "Argument must not be defined over a field of characteristic 2.";
    g := Genus(C);
    f, h := HyperellipticPolynomials(C);
    if h eq 0 then 
        return C, IdentityMap(C);
    end if;
    return Transformation(C, [K|1,0,0,1], K!2, h);
end intrinsic;

intrinsic IntegralModel(C::CrvHyp[FldRat] : Reduce:=false) -> CrvHyp, MapIsoSch
    {Returns an isomorphic curve C' given by polynomials with integral
    coefficients, together with the map C -> C' and the transformation used.
    Base field must be the rationals. If Reduce is set, common divisors of
    the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    require Type(K) in {FldRat,FldFunRat} :
        "Argument must be defined over the rationals " *
        "or a rational function field.";
    g := Genus(C);
    f, h := HyperellipticPolynomials(C);
    // Make polynomial integral
    P := Parent(Numerator(K!1));
    denh := LCM([P | Denominator(c) : c in Coefficients(h)]);
    denf := LCM([P | Denominator(c) : c in Coefficients(f)]);
    if Type(K) eq FldRat then
        d1, d2 := SquarefreeFactorization(denf); // denf = d1 * d2^2
    else
        factors := SquarefreeFactorization(denf);
        d2 := &* [P| t[1]^(t[2] div 2) : t in factors];
        d1 := denf div d2^2;
    end if;
    d := LCM(denh, d1*d2);
    C1, m1 := Transformation(C, K!d);
    if not Reduce then
        return C1, m1;
    end if;
    h := d*h;
    f := d^2*f;
    numh := GCD([P | c : c in Coefficients(h)]);
    numf := GCD([P | c : c in Coefficients(f)]);
    _, num := SquarefreeFactorization(numf);
    C1, m2 := Transformation(C1, K!1/GCD(numh, num));
    return C1, m1*m2;
end intrinsic;

intrinsic HasOddDegreeModel(C::CrvHyp) -> BoolElt, CrvHyp, MapIsoSch
    {Checks whether C has a model of the form y^2 = f(x) with f of odd
    degree.  If so, returns this model together with the map from the
    old to the new model.}

    C1, m1 := SimplifiedModel(C);
    f := HyperellipticPolynomials(C1);
    if IsOdd(Degree(f)) then
        return true, C1, m1; // nothing else to do
    else
        K := BaseField(C);
        flag, root := HasRoot(f);
        if flag then
            require root in K : 
                "Problem with HasRoot -- root not in coefficient domain.";
            C2, m2 := Transformation(C1, [K|0,-1,-1,root]);
            return true, C2, m1*m2;
        else
            return false, _, _;
        end if;
    end if;
end intrinsic;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                     Minimal Weierstrass Models                     //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function pIntegralModelfunction(C, p, Reduce)

    g := Genus(C);
    f, h := HyperellipticPolynomials(C);
    // Make polynomial integral
    denh := -Min([0] cat [Valuation(c, p) : c in Coefficients(h) | c ne 0]);
    denf := -Min([0] cat [Valuation(c, p) : c in Coefficients(f) | c ne 0]);
    d := Max(denh, Ceiling(denf/2));
    unif := UniformizingElement(p);
    C1, m1 := Transformation(C, unif^d);
    if not Reduce then
        return C1, m1;
    end if;
    h := unif^d*h;
    f := unif^(2*d)*f;
    numh := Min([Valuation(c, p) : c in Coefficients(h) | c ne 0]
                  cat [2*Valuation(c, p) : c in Coefficients(f) | c ne 0]);
    d := numh div 2;
    C1, m2 := Transformation(C1, unif^-d);
    return C1, m1*m2;
end function;

intrinsic pIntegralModel(C::CrvHyp, p::RngIntElt : Reduce := false) -> CrvHyp, MapIsoSch
{Returns an isomorphic curve C' given by polynomials with p-integral
coefficients, together with the map C -> C' and the transformation used.
Base field must be the rationals. If Reduce is set, common divisors of
the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return pIntegralModelfunction(C, place, Reduce);
end intrinsic;

intrinsic pIntegralModel(C::CrvHyp, p::FldRatElt : Reduce := false) -> CrvHyp, MapIsoSch
{Returns an isomorphic curve C' given by polynomials with p-integral
coefficients, together with the map C -> C' and the transformation used.
Base field must be the rationals. If Reduce is set, common divisors of
the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return pIntegralModelfunction(C, place, Reduce);
end intrinsic;

intrinsic pIntegralModel(C::CrvHyp, p::RngUPolElt : Reduce := false) -> CrvHyp, MapIsoSch
{Returns an isomorphic curve C' given by polynomials with p-integral
coefficients, together with the map C -> C' and the transformation used.
Base field must be the rationals. If Reduce is set, common divisors of
the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return pIntegralModelfunction(C, place, Reduce);
end intrinsic;

intrinsic pIntegralModel(C::CrvHyp, p::FldFunRatUElt : Reduce := false) -> CrvHyp, MapIsoSch
{Returns an isomorphic curve C' given by polynomials with p-integral
coefficients, together with the map C -> C' and the transformation used.
Base field must be the rationals. If Reduce is set, common divisors of
the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return pIntegralModelfunction(C, place, Reduce);
end intrinsic;

intrinsic pIntegralModel(C::CrvHyp, p::Infty : Reduce := false) -> CrvHyp, MapIsoSch
{Returns an isomorphic curve C' given by polynomials with p-integral
coefficients, together with the map C -> C' and the transformation used.
Base field must be the rationals. If Reduce is set, common divisors of
the coefficients are eliminated as far as possible.}

    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return pIntegralModelfunction(C, place, Reduce);
end intrinsic;

// The following code was written in a first version by Gabriel Herz, 2000
// Modifications by M. Stoll

function pNormalModelfunction(C, p)
// Given a hyperellitpic curve C and a place p, returns 
// a normal Weierstrass model of the curve at p.
    // Verbose flag: CrvHypMinimal

    vprintf CrvHypMinimal: "pNormalModel at p = %o of %o\n", p, C;
    genus := Genus(C);
    C, m := pIntegralModelfunction(C, p, false); // make integral
    RF, mRF, lRF := ResidueClassField(p);
    unif := UniformizingElement(p);
    // See Q. Liu: Modeles entiers..., Trans. AMS 348 (1996), p.4582
    if Characteristic(RF) eq 2 then
        Z2 := PolynomialRing(RF);
        x := PolynomialRing(BaseField(C)).1;
        // Map m accumulates the necessary transformations
        C1 := C;
        while true do
            P, Q := HyperellipticPolynomials(C1);
            // consider reduction mod 2.
            if Z2![mRF(c) : c in Coefficients(Q)] ne 0
                or exists{i : i in [1..Degree(P) by 2] |
                              mRF(Coefficient(P, i)) ne 0}
            then
                return C1, m;
            end if;
            R := Parent(P)![ lRF(mRF(Coefficient(P,2*i)))
                              : i in [0..Degree(P) div 2] ];
            S := P + R*Q - R^2;
            if exists{c : c in Coefficients(S) | Valuation(c, p) eq 1} then
                return C1, m;
            end if;
            // Now transform
            vprintf CrvHypMinimal, 2:
                    " Set y_new = (y_old + (%o))/%o\n", R, unif;
            C1, m1 := Transformation(C1, 1/unif, 1/unif*R);
            m := m*m1;
        end while;
        // we never get here...
    end if;
    // else residue char is odd
    f, h := HyperellipticPolynomials(C);
    if h ne 0 then
        vprintf CrvHypMinimal, 2: " Set y_new = 2*y_old + %o\n", h;
        f := 4*f + h^2;
        C1, m1 := Transformation(C, 2, h);
    else
        C1 := C;
        m1 := IdentityMap(C);
    end if;
    m := m*m1;
    val := Minimum([Valuation(c,p) : c in Coefficients(f) | c ne 0]);
    w := unif^(val div 2);
    if w ne 1 then
        vprintf CrvHypMinimal, 2: " Set y_new = y_old/%o\n", w;
        C1, m1 := Transformation(C1, 1/w);
        m := m*m1;
    end if;
    return C1, m;
end function;

intrinsic pNormalModel(C::CrvHyp, p::RngIntElt) -> CrvHyp, MapIsoSch
{Given a hyperellitpic curve C and a place p, returns 
a normal Weierstrass model of the curve at p.}

    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return pNormalModelfunction(C, place);
end intrinsic;

intrinsic pNormalModel(C::CrvHyp, p::FldRatElt) -> CrvHyp, MapIsoSch
{Given a hyperellitpic curve C and a place p, returns 
a normal Weierstrass model of the curve at p.}

    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return pNormalModelfunction(C, place);
end intrinsic;

intrinsic pNormalModel(C::CrvHyp, p::RngUPolElt) -> CrvHyp, MapIsoSch
{Given a hyperellitpic curve C and a place p, returns 
a normal Weierstrass model of the curve at p.}

    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return pNormalModelfunction(C, place);
end intrinsic;

intrinsic pNormalModel(C::CrvHyp, p::FldFunRatUElt) -> CrvHyp, MapIsoSch
{Given a hyperellitpic curve C and a place p, returns 
a normal Weierstrass model of the curve at p.}

    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return pNormalModelfunction(C, place);
end intrinsic;

intrinsic pNormalModel(C::CrvHyp, p::Infty) -> CrvHyp, MapIsoSch
{Given a hyperellitpic curve C and a place p, returns 
a normal Weierstrass model of the curve at p.}

    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return pNormalModelfunction(C, place);
end intrinsic;


// This finds a minimal Weierstrass model in residue char 2

function MinimalWeierstrassModel2(C, pl)
    f, h := HyperellipticPolynomials(C);
    P := Parent(f); x := P.1;
    RF, mRF, lRF := ResidueClassField(pl);
    unif := UniformizingElement(pl);
    P2 := PolynomialRing(RF); u := P2.1;
    genus := Genus(C);
    C1 := C;
    // functions for later use
    l := func<pol | pol eq 0 select 10*(genus+2) else
                    Minimum([i + Valuation(c, pl) : i in [0..Degree(pol)]
                        | c ne 0 where c := Coefficient(pol, i) ])>;
    function lambda(h, f)
        while true do
            lh := l(h); lf := l(f);
            if 2*lh le lf or IsOdd(lf)
                or exists{i : i in [0..Degree(f)] | 
                     c ne 0 and i + Valuation(c, pl) eq lf
                     and IsOdd(Valuation(c, pl))
                         where c := Coefficient(f, i)} then
                return Minimum(2*lh, lf);
            else
                b := P![ lRF(mRF(unif^(2*i-lf)*Coefficient(f, 2*i)))
                          : i in [0..Degree(f) div 2] ];
                f -:= b*(h+b);
                h +:= 2*b;
            end if;
        end while;
    end function;
    function lambdap(h, f)
        C0 := HyperellipticCurve(Evaluate(f, unif*x), Evaluate(h, unif*x));
        C0 := pNormalModelfunction(C0, pl);
        f0, h0 := HyperellipticPolynomials(C0);
        h1 := Evaluate(h, x+1);
        f1 := Evaluate(f, x+1);
	return Maximum([ lambda(Evaluate(h, x+lRF(z)),
                         Evaluate(f, x+lRF(z))) : z in RF]);
    end function;
    // Map m accumulates the necessary transformations.
    // C1 := C;
    m := IdentityMap(C);
    while true do
        // first normalize
        C1, m1 := pNormalModelfunction(C1, pl);
        vprintf CrvHypMinimal, 2: "  Normalize --> %o\n", C1;
        m := m*m1;
        // now check the points in the special fiber
        flag := true;
        for mat in [[1,lRF(z),0,1] : z in RF] cat [[0,-1,-1,0]] do
            C2, m2 := Transformation(C1, mat);
            f, h := HyperellipticPolynomials(C2);
            l := lambda(h, f);
            vprintf CrvHypMinimal, 3:
                "  Lambda at (%o : %o) = %o\n", mat[2], mat[1], l;
            if l gt 2*((genus+1) div 2) + 1 or 
                (l gt genus + 1 and lambdap(h, f) gt genus + 2) then
                // to new model
                C1 := C2;
                m := m*m2;
                C1, m2 := Transformation(C1, [1/unif,0,0,1]);
                m := m*m2;
                vprintf CrvHypMinimal, 2: "  New model: %o\n", C1;
                flag := false;
                break;
            end if;
        end for;
        if flag then
            // no reduction possible --> current model is minimal
            return C1, m;
        end if;
    end while;
    // we never get here...
end function;



function check_it(C1,f,xr,p,deg)
    genus:=(deg-2) div 2;
    P := Parent(f); x := P.1;
    RF, mRF, lRF := ResidueClassField(p);
    PF := PolynomialRing(RF);
    unif := UniformizingElement(p);
    x0 := lRF(xr); // first do a shift to bring x0 to zero
    C1, m := Transformation(C1, [1,-x0,0,1]);
    f := Evaluate(f, x + x0);
    vprintf CrvHypMinimal, 2: "  Shift --> %o\n", f;
    // Now find lambda(x0)
    lambda := Minimum([i + Valuation(c, p) : i in [0..deg]
                       | c ne 0 where c := Coefficient(f,i)]);
    vprintf CrvHypMinimal, 3: "    lambda = %o\n", lambda;
    if lambda le genus + 1 then return true,_,_; end if;
    // transform to new model
    C2, m1 := Transformation(C1, [1/unif,0,0,1]);
    m:=m*m1;
    f1 := Evaluate(f, unif*x);
    vprintf CrvHypMinimal, 2: "  Look at new model: %o\n", f1;
    //  normalize
    val := Minimum([Valuation(c, p) : c in Coefficients(f1) | c ne 0]);
    w := unif^(val div 2);
    eps := IsOdd(val) select 1 else 0;
    C2, m2 := Transformation(C2, 1/w);
    m := m*m2;
    f1 := 1/(w^2)*f1;
    vprintf CrvHypMinimal, 2: "  Normalize --> %o\n", f1;
    if lambda gt 2*((genus + 1) div 2) + 1 then return false,C2,m; end if;
    // have to check lambda'
    fred := eps eq 0
            select PF![mRF(c) : c in Coefficients(f1)]
	    else PF![mRF(1/unif*c) : c in Coefficients(f1)];
    // CHANGE (M. Stoll, 2007-07-02)
    r := [rt[1] : rt in Roots(fred) | rt[2] ge genus+2-eps];
    lp := 0;
    for x0 in r do 
      f2 := Evaluate(f1, x + lRF(x0));
      lp := Max(lp, Minimum([i + Valuation(c, p) : i in [0..deg] // Stoll: Min
                             | c ne 0 where c := Coefficient(f2, i)]));
      end for;
    vprintf CrvHypMinimal, 3: "    lambda' = %o\n", lp;
    if lp le genus + 2 then return true,_,_; end if;
    return false,C2,m; end function;

function pMinimalWeierstrassModelfunction(C, p)
// Given a hyperelliptic curve C and a place p,
// returns a minimal Weierstrass model of C at p.}
    // Verbose flag: CrvHypMinimal

    vprintf CrvHypMinimal:
       "pMinimalWeierstrassModel at p = %o of\n %o\n", p, C;
    C, m := pIntegralModelfunction(C, p, false);
    RF, mRF, lRF := ResidueClassField(p);
    unif := UniformizingElement(p);
    if Characteristic(RF) eq 2 then
        assert IsFinite(RF);
        C1, m1 := MinimalWeierstrassModel2(C, p);
        return C1, m*m1;
    end if;

    // See Liu, loc. cit., pp. 4588, 4594f
    genus := Genus(C);
    deg := 2*genus + 2;
    // Let f be the short Weierstrass-Model for C (possible if p not 2).
    f, h := HyperellipticPolynomials(C);
    P := Parent(f); x := P.1;
    // m accumulates the necessary transformations
    if h eq 0 then
        C1 := C;
        back := false;
    else
        f := 4*f + h^2;
        C1, m1 := Transformation(C, 2, h);
        vprintf CrvHypMinimal, 2: "  Eliminate h --> %o\n", f;
        m := m*m1;
        back := BaseField(C) cmpeq Rationals();
    end if;
    // if back is set, we have to transform back to h ne 0
    PF := PolynomialRing(RF);
    // first normalize
    val := Minimum([Valuation(c, p) : c in Coefficients(f) | c ne 0]);
    w := unif^(val div 2);
    eps := IsOdd(val) select 1 else 0;
    C1, m1 := Transformation(C1, 1/w);
    m := m*m1;
    f := 1/(w^2)*f;
    vprintf CrvHypMinimal, 2: "  Normalize --> %o\n", f;
    // Change by MW, Jul 2014, use recursion (not iteration), check both roots
    fred := eps eq 0
            select PF![mRF(c) : c in Coefficients(f)]
            else PF![mRF(1/unif*c) : c in Coefficients(f)]; // fred ne 0
        // Now find zeroes of fred. There must be one of multiplicity >= g+1,
        // if reduction is to be possible. (This root maybe at infinity!)
        // also must handle case where 0,oo both genus+1
     if Valuation(fred) ge genus+1 then // move root away from 0
       C1, m1 := Transformation(C1, [1,1,0,1]);
       m := m*m1; f := Evaluate(f,x-1);
       vprintf CrvHypMinimal, 2: "  Shift (from 0) --> %o\n", f;
       fred := eps eq 0
	 select PF![mRF(c) : c in Coefficients(f)]
         else PF![mRF(1/unif*c) : c in Coefficients(f)]; end if;
     if Degree(fred) le genus+1 then // Root of high mult at oo -- move to 0
       C1, m1 := Transformation(C1, [0,-1,-1,0]);
       m := m*m1; f := P![Coefficient(f, deg-i) : i in [0..deg]];
       vprintf CrvHypMinimal, 2: "  Invert --> %o\n", f;
       fred := eps eq 0
	 select PF![mRF(c) : c in Coefficients(f)]
         else PF![mRF(1/unif*c) : c in Coefficients(f)]; end if;
      r := Roots(fred); // MW: needs to consider all roots with mult >= g+1
      r := [rt[1] : rt in r | rt[2] ge genus+1];
      if #r eq 0 then  // Model is minimal
        vprintf CrvHypMinimal, 2: "  Model is minimal.\n";
        if back then vprintf CrvHypMinimal, 2: "  Get h back\n";
          h := P![IsOdd(Integers()!Coefficient(f,2*i))
		     select 1 else 0 : i in [0..genus+1]];
          C1, m1 := Transformation(C1, 1/2, -h/2); m := m*m1; end if;
          return C1, m; end if;
      for xr in r do // Compute lambda and lambda'
	is_min, C, m1:=check_it(C1,f,xr,p,deg);
        if not is_min then vprintf CrvHypMinimal, 2: "  Nonminimal, recurse\n";
	 C,m2:=pMinimalWeierstrassModelfunction(C,p); return C,m*m1*m2; end if;
        end for; vprintf CrvHypMinimal, 2: "  Model is minimal.\n";
      if back then vprintf CrvHypMinimal, 2: "  Get h back\n";
        h := P![IsOdd(Integers()!Coefficient(f,2*i))
		   select 1 else 0 : i in [0..genus+1]];
        C1, m1 := Transformation(C1, 1/2, -h/2); m := m*m1; end if;
      return C1, m;
end function;


intrinsic pMinimalWeierstrassModel(C::CrvHyp, p::RngIntElt) -> CrvHyp, MapIsoSch
{Given a hyperelliptic curve C and a place p,
returns a minimal Weierstrass model of C at p.}

    K := BaseField(C);
    place_ok, place := IntegerPrimeCheck(K, p);
    require place_ok : place;
    return pMinimalWeierstrassModelfunction(C, place);
end intrinsic;

intrinsic pMinimalWeierstrassModel(C::CrvHyp, p::FldRatElt) -> CrvHyp, MapIsoSch
{Given a hyperelliptic curve C and a place p,
returns a minimal Weierstrass model of C at p.}

    K := BaseField(C);
    place_ok, place := RationalPrimeCheck(K, p);
    require place_ok : place;
    return pMinimalWeierstrassModelfunction(C, place);
end intrinsic;

intrinsic pMinimalWeierstrassModel(C::CrvHyp, p::RngUPolElt) -> CrvHyp, MapIsoSch
{Given a hyperelliptic curve C and a place p,
returns a minimal Weierstrass model of C at p.}

    K := BaseField(C);
    place_ok, place := PolynomialPrimeCheck(K, p);
    require place_ok : place;
    return pMinimalWeierstrassModelfunction(C, place);
end intrinsic;

intrinsic pMinimalWeierstrassModel(C::CrvHyp, p::FldFunRatUElt) -> CrvHyp, MapIsoSch
{Given a hyperelliptic curve C and a place p,
returns a minimal Weierstrass model of C at p.}

    K := BaseField(C);
    place_ok, place := RationalFunctionPrimeCheck(K, p);
    require place_ok : place;
    return pMinimalWeierstrassModelfunction(C, place);
end intrinsic;

intrinsic pMinimalWeierstrassModel(C::CrvHyp, p::Infty) -> CrvHyp, MapIsoSch
{Given a hyperelliptic curve C and a place p,
returns a minimal Weierstrass model of C at p.}

    K := BaseField(C);
    place_ok, place := InfinityPrimeCheck(K, p);
    require place_ok : place;
    return pMinimalWeierstrassModelfunction(C, place);
end intrinsic;

intrinsic MinimalWeierstrassModel(C::CrvHyp : Bound := 0)
    -> CrvHyp, MapIsoSch
    {Given a hyperelliptic Curve C over the rationals, this returns
    a globally minimal Weierstrass model of C. If Bound is set, it
    gives an upper bound for the bad primes that are checked (this
    uses trial division, so Bound should not be much larger than 10^7.)}
    // Verbose flag: CrvHypMinimal.

    require BaseField(C) cmpeq Rationals():
        "Base field of argument must be defined over the rationals.";
    require Type(Bound) eq RngIntElt and Bound ge 0:
        "Bound must be a non-negative integer.";
    vprintf CrvHypMinimal: "MinimalWeierstrassModel of %o\n", C;
    C1 := C;
    // get an integral model
    C1, m := IntegralModel(C1);
    vprintf CrvHypMinimal, 2: "  Integral model: %o\n", C1;
    gg := 4*Genus(C) + 2;
    if IsOdd(Genus(C)) then gg *:= 2; end if;
    if Bound eq 0 then
        P := BadPrimes(C1 : Badness := gg);
    else
        disc := AbsoluteValue(Integers()!Discriminant(C));
        P := [ pr[1] : pr in TrialDivision(disc, Bound) | pr[2] ge gg ];
    end if;
    vprintf CrvHypMinimal, 1: "  Bad primes: %o\n", P;
    for p in P do 
        if p ne 2 then  
            C1, m1 := pMinimalWeierstrassModel(C1, p);
            m := m*m1;
        end if;
    end for;
    C1, m1 := pMinimalWeierstrassModel(C1, 2);
    m := m*m1;
    return C1, m;
end intrinsic


////////////////////////////////////////////////////////////////////////
//                                                                    //
//                           Reduced Models                           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

// Seperating this, because it isn't a ReducedModel of C over Q
// April 2010, SRD

intrinsic ReducedWamelenModel(C::CrvHyp) -> CrvHyp
    {Given a hyperelliptic curve C over Q, returns a reduced and 
    partially minimized model of some quadratic twist of C}

    require Genus(C) le 2 : "Argument must be of genus 2";

    f, h := HyperellipticPolynomials(C);
    if h ne Parent(f)!0 then
        C := SimplifiedModel(C);
        f := HyperellipticPolynomials(C);
    end if;
    return HyperellipticCurve(WamelenReduction(f));

end intrinsic;

// Based on reduce.m
// Verbose flag: CrvHypReduce.

intrinsic ReducedModel(C::CrvHyp :
    Simple := false, Al := "Stoll") -> CrvHyp, MapIsoSch
    {Given a curve with integral coefficients, computes a model
    that is reduced with respect to the action of SL(2,Z).}

    require BaseField(C) cmpeq Rationals():
        "ReducedModel is only implemented over the rationals.";
    require Al in {"Stoll","Wamelen"} : 
        "Parameter Al is deprecated: only allowed option is \"Stoll\"";
    if Al eq "Wamelen" then
        
        "WARNING in ReducedModel: \nThe \"Wamelen\" reduction algorithm "*
        "returns a quadratic twist, not an isomorphic curve.\n"*
        "This option is deprecated: if desired, use ReducedWamelenModel.";

        // no isomorphism returned, so return null argument.
        return ReducedWamelenModel(C), _;
    end if;

    require IsIntegral(C): "Model must be integral.";
    vprintf CrvHypReduce: "%o-ReducedModel of %o\n",
            Simple select "Q_0" else "Julia", C;
    g := Genus(C);
    require Genus(C) ge 1 : "Argument must be of genus at least 1";
    f, h := HyperellipticPolynomials(C);
    if h eq 0 then
        C1 := C;
        m := IdentityMap(C);
        back := false;
    else
        back := true;
        C1, m := Transformation(C, 2, h);
        f := 4*f + h^2;
        vprintf CrvHypReduce: "  Make simple first ==> y^2 = %o\n", f; 
    end if;
    f1, mat := Reduce(2*g+2, f : Simple := Simple);
    C1, m1 := Transformation(C1, Eltseq(mat^-1));
    m := m*m1;
    if back then
        a, b, c, d := Explode(Eltseq(mat));
        x := Parent(h).1;
        x1 := a*x + b; z1 := c*x + d;
        h1 := &+[ Coefficient(h,i)*x1^i*z1^(g+1-i) : i in [0..Degree(h)] ];
        h1 := Parent(h)![ (Integers()!c) mod 2 : c in Coefficients(h1) ];
        C1, m1 := Transformation(C1, 1/2, -h1/2);
        m := m*m1;
        vprintf CrvHypReduce: "  Transform back to mixed form\n";
    end if;
    return C1, m;
end intrinsic;

intrinsic ReducedMinimalWeierstrassModel(C::CrvHyp : Simple := false)
    -> CrvHyp, MapIsoSch
    {Given a hyperelliptic Curve C over the rationals, returns
    a globally minimal Weierstrass model of C that is reduced
    with respect to the action of SL(2,Z). (Compare Reduce.)}
    // Verbose flags: CrvHypMinimal, CrvHypReduce

    require BaseField(C) cmpeq Rationals():
        "Base field of argument must be defined over the rationals.";
    C1, m := MinimalWeierstrassModel(C);
    C1, m1 := ReducedModel(C1 : Simple := Simple);
    return C1, m*m1;
end intrinsic;
