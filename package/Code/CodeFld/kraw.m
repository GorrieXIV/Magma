freeze;

// Generalized binomial coefficients		Lancelot Pecquet, 1996
intrinsic BinomialPolynomial(P::RngUPolElt,l::RngIntElt) -> RngUPolElt
{Given a polynomial P over the Rational Field, return the polynomial 
Binomial(P, l)}
	requirege l,0;
	Q := RationalField();
	require BaseRing(Parent(P)) cmpeq  Q:
	"Argument 1 should be over the Rational Field";
	if l eq 0 then
		return Q!1;
	else
		return Factorial(l)^-1 * &*[(P - k) : k in [0 .. l-1]];
	end if;
end intrinsic;

// Krawchouk polynomials		Lancelot Pecquet, 1996
intrinsic KrawchoukPolynomial(K::FldFin,n::RngIntElt,k::RngIntElt)
-> RngUPolElt
{Return the Krawchouk polynomial of parameter k and n in K over the Rational 
Field}
	requirege n,1;
	requirege k,0;
	Q := RationalField();
	qm1 := #K-1;
	TX := PolynomialRing(Q); X := TX.1;
	return TX! &+[(-1)^j * BinomialPolynomial(X,j)
		*BinomialPolynomial(n-X,k-j)
			*qm1^(k-j) : j in [0 .. k]];
end intrinsic;


/*
// Krawchouk polynomials (recursive version),		Lancelot Pecquet, 1996

intrinsic KrawchoukPolynomial(K::FldFin,n::RngIntElt,k::RngIntElt)->RngUPolElt
{Compute the Krawchouk polynomial of parameters n,k,#K}
	requirege n,0;
	requirerange k,0,n;
	Q := RationalField();
	QX := PolynomialRing(Q); X := QX.1;
	q := #K;
	gamma := q-1;
	function K(t)
		if (t eq 0) then
			return QX!1;
		elif (t eq 1) then
			return gamma*n - q*X;
		else
			return t^-1 * (((n-t+1)*gamma + t - 1 - q*X)*K(t-1)
						- gamma*(n-t+2)*K(t-2)); 
		end if;
	end function;
	return K(k);
end intrinsic;

*/


// Krawchouk expansion of a polynomial,		Lancelot Pecquet, 1996

intrinsic KrawchoukTransform(a::RngUPolElt,K::FldFin,n::RngIntElt) -> RngUPolElt
{Return the Krawchouk transform of the polynomial a over the rational field
with respect to the vector space K^n}
	requirege n,0;
	Q := RationalField();
	require BaseRing(Parent(a)) cmpeq Q:
	"Argument 1 should be over the Rational Field";
	q := #K;
	qmn := q^-n;
	t := Degree(a);
	T := qmn*&+[Evaluate(a,i)*KrawchoukPolynomial(K,n,i) : i in [0 .. n]];
	return PolynomialRing(Q)![Evaluate(T,k) : k in [0 .. t]];
end intrinsic;

intrinsic InverseKrawchouk(A::RngUPolElt,K::FldFin,n::RngIntElt) -> Rng
{Return the inverse Krawchouk transform of the polynomial A over the
rational field with respect to the vector space K^n}
	requirege n,0;
	require BaseRing(Parent(A)) cmpeq RationalField():
	"Argument 1 should be over the Rational Field";
	t := Degree(A);
	return &+[Coefficient(A,k)*KrawchoukPolynomial(K,n,k) :k in [0 .. t]];
end intrinsic;
