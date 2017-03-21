freeze;

intrinsic Specialization(E::CrvEll[FldFunRat],t::RngElt) -> CrvEll
{Given an elliptic curve over a rational function field F
 and a ring element that coerces into the base ring of F,
 return the specialization of the elliptic curve.}
 b,t:=IsCoercible(BaseRing(BaseRing(E)),t);
 require b: "t does not coerce into the base ring of the function field";
 return EllipticCurve([Evaluate(a,t) : a in aInvariants(E)]); end intrinsic;

intrinsic PointsAtInfinity(E::SchGrpEll) -> SetIndx
{An indexed set containing the points at infinity lying on the elliptic
curve E}
    return {@ E!0 @};
end intrinsic;

intrinsic PointsAtInfinity(H::SetPtEll) -> SetIndx
{An indexed set containing the point at infinity in the point set H
of an elliptic curve}
    return {@ H!0 @};
end intrinsic;

intrinsic Morphism(E::CrvEll, F::CrvEll, psi::RngMPolElt,
				phi::RngMPolElt, omega::RngMPolElt) -> Map
{Returns the isogeny E->F defined by the polynomials psi, phi and omega,
taking (x, y) to (phi / psi^2, omega / psi^3).  Psi and phi must be
univariate (although elements of a multivariate polynomial ring) and the
polynomials need not be coprime. This has been deprecated, since the
function IsogenyFromKernel(psi) should suffice.}
 x:=PolynomialRing(BaseRing(E)).1;
 psi:=&+[Coefficient(psi,1,i)*x^i : i in [0..TotalDegree(psi)]];
 A,m:=IsogenyFromKernel(E,psi); b,m2:=IsIsomorphic(A,F);
 if not b then require false: "Isogeny data are incompatible"; end if;
 return m*m2; end intrinsic;

intrinsic Isogeny(E::CrvEll, F::CrvEll, psi::RngMPolElt,
				phi::RngMPolElt, omega::RngMPolElt) -> Map
{Returns the isogeny E->F defined by the polynomials psi, phi and omega,
taking (x, y) to (phi / psi^2, omega / psi^3).  Psi and phi must be
univariate (although elements of a multivariate polynomial ring) and the
polynomials need not be coprime. This has been deprecated, since the
function IsogenyFromKernel(psi) should suffice.}
 x:=PolynomialRing(BaseRing(E)).1;
 psi:=&+[BaseRing(E)!Coefficient(psi,1,i)*x^i : i in [0..TotalDegree(psi)]];
 A,m:=IsogenyFromKernel(E,psi); b,m2:=IsIsomorphic(A,F);
 if not b then require false: "Isogeny data are incompatible"; end if;
 return m*m2; end intrinsic;

intrinsic EllipticCurve(f::RngUPolElt, h::RngUPolElt) -> CrvEll
{Creates the elliptic curve defined by y^2 + h(x)*y = f(x), where h
must be of degree at most 1 and f must be monic of degree 3}
    require Degree(h) le 1: "h polynomial must have degree at most 1";
    require Degree(f) eq 3 and IsWeaklyZero(1-Coefficient(f,3)):
			    "f polynomial must be monic of degree 3";
    require Parent(f) cmpeq Parent(h):
			    "Polynomials must lie in the same ring";
    P := Parent(f);
    x := P.1;
    a3,a1 := Explode(Eltseq(h + x^2));		// ensure two coeffs
    a6,a4,a2 := Explode(Eltseq(f));
    S := [a1,a2,a3,a4,a6];
    R := Universe(S);
    if not IsField(R) then
	R := FieldOfFractions(R);
	ChangeUniverse(~S, R);
    end if;
    return EllipticCurve(S);
end intrinsic;

intrinsic EllipticCurve(f::RngUPolElt) -> CrvEll
{Creates the elliptic curve defined by y^2 = f(x), where f must be monic
of degree 3}
    require Degree(f) eq 3 and IsWeaklyZero(1-Coefficient(f,3)):
			    "The given polynomial must be monic of degree 3";
    return EllipticCurve(f, Zero(Parent(f)));
end intrinsic;

// TO DO: local!!
intrinsic MinimalModel(E::CrvEll[FldRat], P::RngIntElt) -> CrvEll
{A local minimal model of the elliptic curve E at the prime P}
    return MinimalModel(E);
end intrinsic;

intrinsic RationalPoints(PS::SetPtEll[FldRat] : Bound:=0) -> SetIndx
{Points in the elliptic curve pointset up to the given naive height bound.}
 return Points(Curve(PS) : Bound:=Bound); end intrinsic;

intrinsic Points(PS::SetPtEll[FldRat] : Bound:=0) -> SetIndx
{Points in the elliptic curve pointset up to the given naive height bound.}
 return Points(Curve(PS) : Bound:=Bound); end intrinsic;

intrinsic RationalPoints(E::CrvEll[FldRat] : Bound:=0) -> SetIndx
{Points in the elliptic curve pointset up to the given naive height bound.}
 return Points(E : Bound:=Bound); end intrinsic;

intrinsic Points(E::CrvEll[FldRat] : Bound:=0) -> SetIndx
{Points in the elliptic curve pointset up to the given naive height bound.}
 require Bound gt 0: "Bound must be given and positive";
 require Type(Bound) eq RngIntElt: "Bound must be integral";
 bI:=bInvariants(E);
 P:=[4,bI[1],2*bI[2],bI[3]];
 m:=LCM([Denominator(x) : x in P]);
 a,b:=Squarefree(m); // m = a*b^2
 sb:=[a*m*x : x in P];
 f:=Polynomial(Reverse(sb));
 H:=HyperellipticCurve(f);
 PTS:=Points(H : Bound:=Bound);
 S:=&cat[Points(E,x[1]/x[3]) : x in PTS | x[3] ne 0 and x[2] ge 0];
 return {@ E!0 @} join {@ s : s in S @};
end intrinsic;

////////////////////////////////////////////////////////////////////////////
// TraceOfFrobenius
// SRD, January 2011
////////////////////////////////////////////////////////////////////////////

intrinsic TraceOfFrobenius(E::CrvEll[FldRat], p::RngInt) -> RngIntElt
{The trace of Frobenius a_p for the reduction of E at the prime p}

   require IsPrime(p) : "The second argument should be prime";
   return FrobeniusTraceDirect(E, Generator(p));
end intrinsic;

intrinsic TraceOfFrobenius(E::CrvEll[FldRat], p::RngIntElt) -> RngIntElt
{"} //"
   require IsPrime(p) : "The second argument should be prime";
   return FrobeniusTraceDirect(E, p);
end intrinsic;

intrinsic TraceOfFrobenius(E::CrvEll[FldAlg], p::RngOrdIdl) -> RngIntElt
{"} //"
   F := BaseField(E);
   require NumberField(Order(p)) eq NumberField(F) : 
      "Arguments are not compatible";

   if Valuation(Discriminant(E), p) eq 0 then
      EE := E;
   else
      EE := MinimalModel(E, p);
      require Valuation(Discriminant(EE), p) eq 0: 
             "The curve has bad reduction at the prime";
   end if;

   k, res := ResidueClassField(p);
   Ek := EllipticCurve([k | res(c) : c in Coefficients(EE)]);

   return Trace(Ek);
end intrinsic;

intrinsic TraceOfFrobenius(E::CrvEll[FldFunRat], p::RngElt) -> RngIntElt
{"} //"
   F := BaseField(E);
   ZF := Integers(F);

   // TO DO: case p = (1/t)
   bool, p := IsCoercible(ZF, p);
   require bool : 
      "The second argument must be an integral (prime) element of the base ring";
   require IsPrime(p) : 
      "The second argument must be a prime element";

   if Valuation(Discriminant(E), p) eq 0 then
      EE := E;
   else
      EE := MinimalModel(E, p);
      require Valuation(Discriminant(EE), p) eq 0: 
             "The curve has bad reduction at the prime";
   end if;

   k, res := ResidueClassField(p);
   Ek := EllipticCurve([k | res(c) : c in Coefficients(EE)]);

   return Trace(Ek);
end intrinsic;

intrinsic HodgeStructure(E::CrvEll[FldNum]) -> HodgeStruc
{The Hodge structure of an elliptic curve over a number field}
 return Degree(BaseRing(E))*HodgeStructure([<0,1>,<1,0>]); end intrinsic;

intrinsic HodgeStructure(E::CrvEll[FldRat]) -> HodgeStruc
{The Hodge structure of an elliptic curve over the rationals}
 return HodgeStructure([<0,1>,<1,0>]); end intrinsic;
