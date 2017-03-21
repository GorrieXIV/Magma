freeze;

intrinsic IsUpperTriangular(X::Mtrx) -> BoolElt
{True iff X is an upper triangular matrix}
    m := Nrows(X);
    n := Ncols(X);
    return forall{1 : j in [1 .. Min(n, i-1)], i in [1 .. m] | X[i, j] eq 0};
end intrinsic;

intrinsic IsLowerTriangular(X::Mtrx) -> BoolElt
{True iff X is a lower triangular matrix}
    m := Nrows(X);
    n := Ncols(X);
    return forall{1 : i in [1 .. Min(m, j-1)], j in [1 .. n] | X[i, j] eq 0};
end intrinsic;
