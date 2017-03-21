freeze;

function action(f, A)

    F := Parent(f);
    R := BaseRing(F);
    n := Rank(F);

    l, A := IsCoercible(MatrixRing(R, n), A);
    if not l then
	return false, _;
    end if;

    I := [&+[A[i, j]*F.j: j in [1 .. n]]: i in [1 .. n]];

    s := F!0;
    C := Coefficients(f);
    M := Monomials(f);
    for i := 1 to #C do
	s := s + C[i] * &*[I[j]: j in Eltseq(M[i])];
    end for;
    return true, s;

end function;

intrinsic '^'(f::AlgFrElt, A::MtrxSpcElt) -> AlgFrElt
{The action of A on f}
    l, g := action(f, A);
    require l: "Matrix is not over the ring of f";
    return g;
end intrinsic;

intrinsic '^'(f::AlgFPElt, A::MtrxSpcElt) -> AlgFPElt
{The action of A on f}
    l, g := action(f, A);
    require l: "Matrix is not over the ring of f";
    return g;
end intrinsic;
