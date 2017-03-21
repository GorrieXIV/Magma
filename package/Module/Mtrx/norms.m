freeze;

intrinsic Norms(X::Mtrx) -> []
{Norms of matrix X};

    m := Nrows(X);
    return [InnerProduct(X[i], X[i]): i in [1 .. m]];
end intrinsic;

intrinsic LogNorms(X::Mtrx) -> []
{Norms of matrix X};
    m := Nrows(X);
    return [
	n eq 0 select -1 else Ilog2(n) where
	    n is Abs(InnerProduct(X[i], X[i])): i in [1 .. m]
    ];
end intrinsic;

intrinsic Diagonal(X::Mtrx) -> []
{The diagonal of matrix X};
    return [X[i][i]: i in [1 .. Min(Nrows(X), Ncols(X))]];
end intrinsic;

/*
intrinsic Density(X::Mtrx) -> RngElt
{Density of X}
    n := Nrows(X);
    return &+[Weight(X[i]): i in [1 .. n]] / (n * Ncols(X)) + 0.0;
end intrinsic;
*/
