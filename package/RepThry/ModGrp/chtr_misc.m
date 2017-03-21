freeze;

intrinsic Defect(c::AlgChtrElt, p::RngIntElt) -> RngIntElt
{The p-defect of irreducible character c}

    require Norm(c) eq 1: "character must be irreducible";
    require IsPrime(p): "2nd argument must be prime";

    dG := Valuation(#Group(Parent(c)), p);
    dc := Valuation(Integers()!Degree(c), p);
    return dG - dc;
end intrinsic;

intrinsic BrauerCharacter(c::AlgChtrElt, p::RngIntElt) -> AlgChtrElt
{Restrict the values of  c on p-singular classes to be zero}
    require IsPrime(p): "2nd argument must be prime";
    R := Parent(c);
    G := Group(R);
    cl := ClassesData(G);
    K := Universe(Eltseq(c));
    res := [K|];
    for i := 1 to #cl do
	if cl[i,1] mod p eq 0 then v := K!0; else v := c[i]; end if;
	Append(~res, v);
    end for;
    return R!res;
end intrinsic;

mat_and_vector := function(X, c)
    list := [Eltseq(x):x in X] cat [Eltseq(c)];
    mat := Matrix(list);
    delete list;
    coeffs := Submatrix(mat, 1,1, Nrows(mat)-1, Ncols(mat));
    v := mat[Nrows(mat)];
    return coeffs, v;
end function;

intrinsic Solution(X::SeqEnum[AlgChtrElt], c::AlgChtrElt) -> ModTupRngElt, ModTupRng
{Express c as a linear combination of the elements of X}

    mat, v := mat_and_vector(X, c);
    return Solution(mat, v);

end intrinsic;

intrinsic IsConsistent(X::SeqEnum[AlgChtrElt], c::AlgChtrElt) -> BoolElt, ModTupRngElt, ModTupRng
{If possible, express c as a linear combination of the elements of X. First return value indicates success or failure.}

    mat, v := mat_and_vector(X, c);
    return IsConsistent(mat, v);

end intrinsic;
