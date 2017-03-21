freeze;

//Mattson-Solomon polynomial,			Lancelot Pecquet, 1996

// n is an integer relatively prime to q
// F is a splitting field of (X^n-1) over GF(q)
// a is in F[X]

intrinsic MattsonSolomonTransform(a::RngUPolElt,n::RngIntElt) -> RngUPolElt
{Given a, a polynomial over a finite field containing a primitive n-th root of 
unity, return the Mattson-Solomon transform of parameter n}
	requirege n,2;
	require n mod #PrimeField(CoefficientRing(Parent(a))) ne 0:
	"Argument 2 (",n,") is not coprime to the cardinality of 
	argument 1 (",#CoefficientRing(Parent(a)),")";
	F := CoefficientRing(Parent(a));
	alpha := RootOfUnity(n,F);
	require #Parent(alpha) eq #F:
	"Argument 1 should be over a splitting field of (X ^",n," - 1)";
	return PolynomialRing(F)![Evaluate(a,alpha^-j) : j in [0 .. n-1]];
end intrinsic;


//Inverse Mattson-Solomon transformation,       Lancelot Pecquet, 1996

// q is a power of a prime number
// n is relatively prime to q
// F is a splitting field of (X^n-1) over GF(q)
// A is a polynomial in F[X]

intrinsic InverseMattsonSolomonTransform(A::RngUPolElt,n::RngIntElt) ->
	    RngUPolElt
{Given A, a polynomial over a finite field containing a primitive n-th root of unity, return the inverse Mattson-Solomon transform of parameter n}
	requirege n,2;
	require n mod #PrimeField(CoefficientRing(Parent(A))) ne 0:
	"Argument 2 (",n,") is not coprime to the cardinality of 
	argument 1 (",#CoefficientRing(Parent(A)),")";
	F := CoefficientRing(Parent(A));
	alpha := RootOfUnity(n,F);
	require #Parent(alpha) eq #F:
	"Argument 1 should be over a splitting field of (X ^",n," - 1)";
	return PolynomialRing(F)![Evaluate(A,alpha^i)/n : i in [0 .. n-1]];
end intrinsic;
