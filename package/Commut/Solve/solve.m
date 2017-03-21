freeze;

/*
Solving a polynomial system by multiple evaluations.
AKS, Sep 2013.
*/

intrinsic Solve(B::[RngMPolElt], e::RngIntElt: DL := 0, PairsLimit := 0)
    -> SeqEnum
{Attempt to solve the system given by B by evaluating e variables}

    require BaseRing(Universe(B)) cmpeq GF(2): "Base ring must be GF(2)";

    R := Universe(B);
    K := BaseRing(R);
    n := Rank(R);
    RR<[x]> := PolynomialRing(K, n - e, "grevlex");
    q := #K;
    res := [];

    for i := 0 to q^e - 1 do
	E := IntegerToSequence(i, q);
	E cat:= [0: i in [#E + 1 .. e]];
	E := [IndexToElement(K, x): x in E];
	i, E;

	h := hom<R -> RR | x cat E>;
	BB := h(B);
//RR; //BB;
	if DL eq 0 then
	    time G := GroebnerBasis(
		BB: HFE, Dense := 1, PairsLimit := PairsLimit
	    );
	else
	    time G := GroebnerBasis(
		BB, DL: HFE, Dense := 1, PairsLimit := PairsLimit
	    );
	end if;

	if G ne [1] then
	    "GOOD";
	    E, G;
	    Append(~res, <E, G>);
	end if;
    end for;

    return res;

end intrinsic;
