freeze;

//

intrinsic Rows(X::Mtrx, Q::[RngIntElt]) -> []
{The rows given by Q of X as a seqence};
    if #Q ne 0 then
        require Min(Q) ge 1 and Max(Q) le Nrows(X):
        Sprintf("Argument 2 must take values in the range [1..%o]\n",Nrows(X));
    end if;
    return X[Q];
end intrinsic;

intrinsic Rows(X::Mtrx) -> []
{The rows of matrix X as a sequence}
    return Rows(X, [1..Nrows(X)]);
end intrinsic;

//

intrinsic RowSubmatrix(X::Mtrx, Q::[RngIntElt]) -> Mtrx
{The submatrix of X defined by selecting the rows given by Q}
    return Matrix(Rows(X, Q));
end intrinsic;
