
freeze;

intrinsic TateLichtenbaumPairing(D1::DivFunElt, D2::DivFunElt, m::RngIntElt) -> RngElt
{The Tate-Lichtenbaum pairing Cl_0[m] x Cl_0/mCl_0 --> k. D1 and
D2 must be coprime};

    require FunctionField(D1) eq FunctionField(D2)
		    : "Divisors not defined over the same function field";

    require m ge 1 : "Argument 3 must be greater than or equal to 1";

    require IsEmpty(Set(Support(D1)) meet Set(Support(D2)))
		    : "Divisors must be coprime";

    require Degree(D1) eq 0 and Degree(D2) eq 0 :
		    "Divisors must be of degree zero";

    ok, a := IsPrincipal(m*D1);

    require ok : "Argument 3 times argument 1 must be principal";

    return &* [ Norm(Evaluate(a, p[i]), k)^e[i] : i in [1..#p] ]
				    where p, e := Support(D2)
				    where k := ConstantField(FunctionField(D2));

end intrinsic;

