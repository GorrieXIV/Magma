// *********************************************************************
// * Package: quadratic.mag                                            *
// * ======================                                            *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 7.12.2007                                                 *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute parametrizations of quadrics in P^3.                    *
// *                                                                   *
// *********************************************************************

freeze;


// ======================================
// = Auxillary functions (not exported) =
// ======================================

// find a rational point on a quadric
// ----------------------------------
// input:  multivariate homogeneous polynomial 'p' of degree 2
// output: a rational projective point on 'p=0' if existent

function PointOnQuadric(p)
	P := Parent(p); Q := BaseRing(P); r := Rank(P);

	error if Type(Q) ne FldRat, "Only implemented over the rationals";
	
	// normalize p to integer coefficients
	lcd := 1; for g in Terms(p) do
		lcd := Lcm(lcd, Denominator(LeadingCoefficient(g)));
	end for; p := lcd*p;
	pp := 0; for g in Terms(p) do
		pp := Gcd(pp, Numerator(LeadingCoefficient(g)));
	end for; p := 1/pp*p;
	
	// find matrix representation of projective surface
	M := MatrixAlgebra(IntegerRing(Q), r) ! (2*SymmetricBilinearForm(p));
	
	// find isotropic vector
	vec := RSpace(Q, r) ! IsotropicVector(M);
	
	// no solution
	if IsZero(vec) then return false, _; end if;
	
	// make primitive
	lcd := 1; for i in [1..r] do
		lcd := Lcm(lcd, Denominator(vec[i]));
	end for; vec := lcd*vec;
	pp := 0; for i in [1..r] do
		pp := Gcd(pp, Numerator(vec[i]));
	end for; vec := 1/pp*vec;
	return true, ElementToSequence(vec);
end function;




// ======================
// = Exported functions =
// ======================

// compute the class of the surface and nice adjoint maps
intrinsic ParametrizeQuadric(X::Sch, P2::Prj : Point:=0)
-> BoolElt, MapSch
{
Given a quadric projective hypersurface X in P^3 and projective plane P2
over the same base field k which is a number field. 
Returns 'false' if X is not parametrizable over k;
otherwise return 'true' and a parametrization. Parameter Point may be
used to specify a point in X(k). A point must be specified if    
k is not the rational field.
}
	p := DefiningPolynomial(X); 
        P := Parent(p); 
        K := BaseRing(P);
	P3 := AmbientSpace(X);

	require IsOrdinaryProjective(X) and (Degree(X) eq 2) and (Dimension(P3) eq 3):
	  "X must be a quadric surface in ordinary projective 3-space";
	require IsOrdinaryProjective(P2) and Dimension(P2) eq 2:
	  "P2 must be an ordinary projective plane";
	require IsIdentical(BaseRing(P2),K):
	  "X and P2 must be both be defined over the same field";
        require Type(K) eq FldRat or ISA(Type(K), FldAlg) :
               "The base field must be Q or a number field";
        require Type(K) eq FldRat or Point cmpne 0 : 
               "When base field is not Q, a 'Point' must be specified";
	if not ISA(Type(X),Srfc) then
	  require IsIrreducible(p):
		"X is not irreducible and reduced";
	end if;
	
	// find a rational point on X
        if Point cmpne 0 then
           bool, pt := IsCoercible(X, Point);
           pt := P3! pt;
           error if not bool, "The given 'Point' does not lie on the quadric";
        else
	   found, pt := PointOnQuadric(p);
	   if not found then return false, _; end if;
	   pt := ElementToSequence(pt);
        end if;
	
	// if it is singular find another point
        if IsSingular(X!pt) then
		// move singularity to origin
		trans := Translation(P3, P3 ! pt,
		                         P3 ! [0,0,0,1]);
		q := DefiningPolynomial(trans(X));
		
		// find point at infinity
		S := PolynomialRing(K, 3);
		q := hom<P -> S | S.1, S.2, S.3, 0>(q);
		found, pt := PointOnQuadric(q);
		if not found then return false, _; end if;
		pt := Append(ElementToSequence(pt), 0);
		
		// backtranslate
		pt := Inverse(trans)(P3 ! pt);
	else
		pt := P3 ! pt;
	end if;
	
	// invert projection map from a point
	_, proj, _ := ProjectionFromNonsingularPoint(X, X ! pt);
	proj := Expand(proj * map<Codomain(proj) -> P2 | [Codomain(proj).1,
	                          Codomain(proj).2, Codomain(proj).3]>);
	proj := Restriction(proj, X, P2); _, inv := IsInvertible(proj);
	
	return true, inv;
end intrinsic;
