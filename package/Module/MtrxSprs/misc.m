freeze;

/*******************************************************************************
			    Predicates
*******************************************************************************/

intrinsic IsOne(X::MtrxSprs) -> BoolElt
{True iff X is the identity matrix};
    require Nrows(X) eq Ncols(X): "Matrix is not square";
    l, D := IsDiagonal(X);
    return l and forall{x: x in D | IsOne(x)};
end intrinsic;

intrinsic IsMinusOne(X::MtrxSprs) -> BoolElt
{True iff X is the identity matrix};
    require Nrows(X) eq Ncols(X): "Matrix is not square";
    l, D := IsDiagonal(X);
    return l and forall{x: x in D | IsMinusOne(x)};
end intrinsic;

intrinsic IsScalar(X::MtrxSprs) -> BoolElt
{True iff X is a scalar matrix};
    require Nrows(X) eq Ncols(X): "Matrix is not square";
    l, D := IsDiagonal(X);
    return l and #Set(D) eq 1;
end intrinsic;

intrinsic IsSymmetric(X::MtrxSprs) -> BoolElt
{True iff X is symmetric}
    require Nrows(X) eq Ncols(X): "Matrix is not square";
    return Transpose(X) eq X;
end intrinsic;

// Could be done via supports:
intrinsic IsUpperTriangular(X::MtrxSprs) -> BoolElt
{True iff X is an upper triangular matrix}
    m := Nrows(X);
    n := Ncols(X);
    return forall{1 : j in [1 .. Min(n, i-1)], i in [1 .. m] | X[i, j] eq 0};
end intrinsic;

intrinsic IsLowerTriangular(X::MtrxSprs) -> BoolElt
{True iff X is a lower triangular matrix}
    m := Nrows(X);
    n := Ncols(X);
    return forall{1 : i in [1 .. Min(m, j-1)], j in [1 .. n] | X[i, j] eq 0};
end intrinsic;

/*******************************************************************************
			    Support/Eltseq
*******************************************************************************/

intrinsic Support(X::MtrxSprs) -> BoolElt
{A sequence of all pairs of the form <i, j> such that entry [i, j]
of X is non-zero}

    U := Parent(<1, 1>);
    return [ U | <i, j>: j in Support(X, i), i in [1 .. Nrows(X)]];
end intrinsic;

intrinsic Eltseq(X::MtrxSprs) -> BoolElt
{A sequence of all triples of the form <i, j, x> such that entry [i, j]
of X equals x and x is non-zero}

    R := BaseRing(X);
    U := Parent(<1, 1, R!0>);
    return [ U | <i, j, X[i, j]>: j in Support(X, i), i in [1 .. Nrows(X)]];
end intrinsic;

/*******************************************************************************
			    Tensor Product
*******************************************************************************/

intrinsic TensorProduct(X::MtrxSprs, Y::MtrxSprs) -> BoolElt
{The (matrix) tensor product of X and Y.}

    R := BaseRing(X);
    require BaseRing(Y) cmpeq R: "Sparse matrices are not over the same ring";

    Xm := Nrows(X);
    Xn := Ncols(X);
    Ym := Nrows(Y);
    Yn := Ncols(Y);

    T := SparseMatrix(R, Xm*Ym, Xn*Yn);
    if IsZero(X) or IsZero(Y) then
	return T;
    end if;

    for i := 1 to Xm do
	for j in Support(X, i) do
	    InsertBlock(~T, X[i, j]*Y, (i - 1)*Ym + 1, (j - 1)*Yn + 1);
	end for;
    end for;

    return T;
end intrinsic;
