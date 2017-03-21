freeze;

// Fire code monovariable,			Lancelot Pecquet, 1996

// h is a polynomial of GF(q)[X];  Is that all?

intrinsic FireCode(h::RngUPolElt,s::RngIntElt,n::RngIntElt) -> Code
{Given a polynomial h in GF(q)[X], a nonnegative integer s, 
constructs a Fire code of length n with generator polynomial h*(X^s - 1) 
over GF(q)}
	requirege n,1;
	requirege s,1;
	F := CoefficientRing(Parent(h));
	FX := PolynomialRing(F); X := FX.1;
	g := (X^s-1)*h;
	return CyclicCode(n,g);
end intrinsic;
