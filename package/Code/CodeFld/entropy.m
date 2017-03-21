freeze;

// Entropy function,		Lancelot Pecquet, 1996

intrinsic Entropy(x::FldReElt,S::FldFin) -> FldReElt
{Computes the entropy function for a real number in the interval [0,1-1/q],
where q=#S}
	q := #S;
	require x ge 0:"Argument 1 should be >= 0";
	require x le 1-1/q:"Argument 1 should be <=",1-1/q;
	if x eq 0 then
		return 0;
	else
		return x*(Log(q,(q-1)) - Log(q,x)) - (1-x)*Log(q,1-x);
	end if;
end intrinsic;

// Information rate of a code,		Lancelot Pecquet, 1996

intrinsic InformationRate(C::Code) -> FldRatElt
{Return the information rate of a given code}
	require Type(C) ne CodeQuantum : "Not defined for quantum codes";
	return Dimension(C)/(Length(C));
end intrinsic;
