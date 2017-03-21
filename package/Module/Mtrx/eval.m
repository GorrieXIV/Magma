freeze;

intrinsic Evaluate(X::Mtrx, P::.) -> Mtrx
{Evaluate each entry of X at P}

    /*
    if IsNull(P) then
	return X;
    end if;
    */

    try
	EX := Matrix(Nrows(X), Ncols(X), [Evaluate(x, P): x in Eltseq(X)]);
    catch E
	require false: "Evaluation failed:", E`Object;
    end try;

    return EX;
end intrinsic;
