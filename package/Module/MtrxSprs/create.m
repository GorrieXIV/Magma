freeze;

/*******************************************************************************
				Basic constructions
*******************************************************************************/

intrinsic SparseMatrix(R::Rng, m::RngIntElt, n::RngIntElt) -> MtrxSprs
{The m by n zero sparse matrix over R};
    return SparseMatrix(R, m, n, []);
end intrinsic;

intrinsic SparseMatrix(m::RngIntElt, n::RngIntElt) -> MtrxSprs
{The m by n zero sparse matrix over the integer ring Z};
    return SparseMatrix(IntegerRing(), m, n, []);
end intrinsic;

intrinsic SparseMatrix(R::Rng) -> MtrxSprs
{The 0 by 0 zero sparse matrix over R};
    return SparseMatrix(R, 0, 0);
end intrinsic;

intrinsic SparseMatrix() -> MtrxSprs
{The 0 by 0 zero sparse matrix over the integer ring Z};
    return SparseMatrix(0, 0);
end intrinsic;

/*******************************************************************************
				Scalar matrices
*******************************************************************************/

intrinsic ScalarSparseMatrix(R::Rng, n::RngIntElt, s::RngElt) -> MtrxSprs
{The n by n scalar sparse matrix (R!s)*I_n}

    require n ge 0: "n must be non-negative";
    l, s := IsCoercible(R, s);
    require l: "Element is not coercible into ring R";

    S := SparseMatrix(R, n, n);
    if not IsZero(s) then
	for i := 1 to n do
	    S[i, i] := s;
	end for;
    end if;
    return S;
end intrinsic;

intrinsic ScalarSparseMatrix(n::RngIntElt, s::RngElt) -> MtrxSprs
{The n by n scalar sparse matrix s*I_n}

    require n ge 0: "n must be non-negative";
    return ScalarSparseMatrix(Parent(s), n, s);
end intrinsic;

intrinsic IdentitySparseMatrix(R::Rng, n::RngIntElt) -> MtrxSprs
{The n by n identity sparse matrix I_n}

    require n ge 0: "n must be non-negative";

    S := SparseMatrix(R, n, n);
    s := R!1;
    for i := 1 to n do
        S[i, i] := s;
    end for;
    return S;
end intrinsic;

/*******************************************************************************
				Diagonal matrices
*******************************************************************************/

intrinsic DiagonalSparseMatrix(R::Rng, n::RngIntElt, Q::[RngElt]) -> MtrxSprs
{The diagonal sparse matrix over R with n rows and n columns whose
diagonal entries correspond to the the entries of Q}

    require #Q eq n: "Length of argument 3 is not", n;
    l, Q := CanChangeUniverse(Q, R);
    require l: "Element of sequence not coercible into argument 1";

    S := SparseMatrix(R, n, n);
    for i := 1 to n do
	S[i, i] := Q[i];
    end for;
    return S;
end intrinsic;

intrinsic DiagonalSparseMatrix(R::Rng, Q::[RngElt]) -> MtrxSprs
{The diagonal sparse matrix over R with #Q rows and #Q columns whose
diagonal entries correspond to the the entries of Q}

    l, Q := CanChangeUniverse(Q, R);
    require l: "Element of sequence not coercible into argument 1";

    n := #Q;
    S := SparseMatrix(R, n, n);
    for i := 1 to n do
	S[i, i] := Q[i];
    end for;
    return S;
end intrinsic;

intrinsic DiagonalSparseMatrix(Q::[RngElt]) -> MtrxSprs
{The diagonal sparse matrix with #Q rows and #Q columns whose diagonal
entries correspond to the the entries of Q}

    require not IsNull(Q): "Argument 1 must not be null";

    n := #Q;
    S := SparseMatrix(Universe(Q), n, n);
    for i := 1 to n do
	S[i, i] := Q[i];
    end for;
    return S;
end intrinsic;

/*******************************************************************************
				Permutation matrices
*******************************************************************************/

intrinsic PermutationSparseMatrix(R::Rng, p::GrpPermElt) -> MtrxSprs
{The sparse permutation matrix over ring R corresponding to the permutation p}

    n := Degree(Parent(p));
    S := SparseMatrix(R, n, n);
    s := R!1;
    for i := 1 to n do
	S[i, i^p] := s;
    end for;
    return S;
end intrinsic;

intrinsic PermutationSparseMatrix(R::Rng, p::SeqEnum) -> MtrxSprs
{"} // "

    n := #p;
    S := SparseMatrix(R, n, n);
    s := R!1;
    for i := 1 to n do
	S[i, p[i]] := s;
    end for;
    return S;
end intrinsic;

/*******************************************************************************
				Join matrices
*******************************************************************************/

// TO DO: use copy into instead of repeated join

intrinsic HorizontalJoin(Q::SeqEnum[MtrxSprs]) -> MtrxSprs
{Given a sequence Q of sparse matrices over the same coefficient ring,
return the horizontal block joining of the elements of Q}

    require not IsNull(Q): "Argument 1 must not be null";

    M := Q[1];
    n := Nrows(M);

    for i := 2 to #Q do
        Mi := Q[i];
        require Nrows(Mi) eq n : "Matrices have incompatible number of rows";
        M := HorizontalJoin(M, Mi);
    end for;

    return M; 
end intrinsic;

intrinsic VerticalJoin(Q::SeqEnum[MtrxSprs]) -> MtrxSprs
{Given a sequence Q of sparse matrices over the same coefficient ring,
return the vertical block joining of the elements of Q}

    require not IsNull(Q): "Argument 1 must not be null";

    M := Q[1];
    n := Ncols(M);

    for i := 2 to #Q do
        Mi := Q[i];
        require Ncols(Mi) eq n : "Matrices have incompatible number of columns";
        M := VerticalJoin(M, Mi);
    end for;

    return M; 
end intrinsic;

/*******************************************************************************
				Read GAP matrix
*******************************************************************************/

intrinsic SparseMatrixGAP(F::MonStgElt) -> MtrxSprs
{The sparse matrix given by the file F in GAP sparse format}

    F := Open(F, "r");

    S := Gets(F);
    Q := Split(S, " ");
    assert #Q eq 3 and Q[3] eq "M";

    s2i := StringToInteger;
    nr := s2i(Q[1]);
    nc := s2i(Q[2]);

    X := SparseMatrix(nr, nc);
    while true do
	S := Gets(F);
	if IsEof(S) then
	    break;
	end if;
	Q := Split(S, " ");
	i := s2i(Q[1]);
	if i eq 0 then break; end if;
	X[i, s2i(Q[2])] := s2i(Q[3]);
    end while;

    return X;

end intrinsic;
