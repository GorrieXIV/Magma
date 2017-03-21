freeze;

intrinsic RandomMatrix(R::Rng, m::RngIntElt, n::RngIntElt) -> Mtrx
{A random m by n matrix over the finite ring R};

    require IsFinite(R): "Ring must be finite";

    if m eq n then
	S := MatrixRing(R, m);
    else
	S := RMatrixSpace(R, m, n);
    end if;
    return Random(S);
end intrinsic;

intrinsic RandomLowerTriangularMatrix(n::RngIntElt, r::RngIntElt) -> Mtrx
{Random n*n lower-triangular integral matrix with range given by r}

    L := LowerTriangularMatrix([Random(-r, r): i in [1 .. Binomial(n + 1, 2)]]);
    for i := 1 to n do
	L[i,i] := 1;
    end for;
    return L;
end intrinsic;

intrinsic RandomUpperTriangularMatrix(n::RngIntElt, r::RngIntElt) -> Mtrx
{Random n*n upper-triangular integral matrix with range given by r}

    U := UpperTriangularMatrix([Random(-r, r): i in [1 .. Binomial(n + 1, 2)]]);
    for i := 1 to n do
	U[i,i] := 1;
    end for;
    return U;
end intrinsic;

intrinsic RandomUnimodularMatrix(n::RngIntElt, r::RngIntElt) -> Mtrx
{Random n*n unimodular integral matrix with range given by r}

    L := RandomLowerTriangularMatrix(n, r);
    U := RandomUpperTriangularMatrix(n, r);
    T := L*U;
    return T;
end intrinsic;

intrinsic RandomSparseMatrix(
    R::Rng, m::RngIntElt, n::RngIntElt, density::RngElt, r::RngIntElt
) -> Mtrx
{Random m*n integral matrix with given density, entries in range [-r, r]}

    mn := m*n;

    C := Min(Round(mn*density), mn);
    S := {};
    while #S lt C do
	Include(~S, <Random(1, m), Random(1, n)>);
    end while;

    X := RMatrixSpace(R, m, n) ! 0;
    for t in S do
	repeat
	    x := Random(-r, r);
	until x ne 0;
	X[t[1], t[2]] := x;
    end for;

    return X;
end intrinsic;

intrinsic RandomSparseMatrix(
    m::RngIntElt, n::RngIntElt, density::RngElt, r::RngIntElt
) -> Mtrx
{Random m*n integral matrix with given density, entries in range [-r, r]}

    return RandomSparseMatrix(IntegerRing(), m, n, density, r);

end intrinsic;

intrinsic RandomSparseMatrix(
    R::Rng, m::RngIntElt, n::RngIntElt, density::RngElt
) -> Mtrx
{Random m*n sparse matrix over R with given density}

    require IsFinite(R): "Ring must be finite";

    mn := m*n;

    C := Min(Round(mn*density), mn);
    S := {};
    while #S lt C do
	Include(~S, <Random(1, m), Random(1, n)>);
    end while;

    X := RMatrixSpace(R, m, n) ! 0;
    for t in S do
	repeat
	    x := Random(R);
	until x ne 0;
	X[t[1], t[2]] := x;
    end for;

    return X;
end intrinsic;
