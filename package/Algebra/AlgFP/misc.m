freeze;

intrinsic MinimalPolynomial(f::AlgFPElt) -> RngUPolElt
{The minimal polynomial of f}
    return MinimalPolynomial(RepresentationMatrix(f));
end intrinsic;

intrinsic IsNilpotent(f::AlgFPElt) -> BoolElt, RngIntElt
{The minimal polynomial of f}
    M := MinimalPolynomial(f);
    d := Degree(M);
    if M eq Parent(M).1^d then
	return true, d;
    else
	return false, _;
    end if;
end intrinsic;

intrinsic IsCommutative(A::AlgFP) -> BoolElt
{Return true iff A is commutative}
    n := Rank(A);
    return forall{1: j in [1 .. i - 1], i in [1 .. n] | A.i*A.j eq A.j*A.i};
end intrinsic;
