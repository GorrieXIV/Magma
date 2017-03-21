freeze;

Z := IntegerRing();

intrinsic 'div'(X::Mtrx, d::RngElt) -> Mtrx
{Return the matrix derived by dividing all entries of X by d}

    R := BaseRing(X);
    l, d := IsCoercible(R, d);
    require l: "Scalar not in base ring of matrix";
    require d ne 0: "Division by zero";

    if Type(R) eq RngInt then
	return X div d; // Internal version
    end if;

    try
	return Matrix(R, Nrows(X), Ncols(X), [x div d: x in Eltseq(X)]);
    catch E
        require false: "Division failed:", E`Object;
    end try;
end intrinsic;

intrinsic IntegralMatrix(X::Mtrx) -> Mtrx, RngIntElt
{Return integral Y and common denominator d of X such that X = 1/d*Y};

    t := Type(BaseRing(X));
    if t eq RngInt then
        return X, 1;
    end if;
    require t eq FldRat: "Matrix is not rational";
    d := Denominator(X);
    return Matrix(IntegerRing(), d*X), d;
end intrinsic;

intrinsic IntegralMatrixByRows(X::Mtrx) -> Mtrx, SeqEnum
{Return integral Y and denominator sequence D such that row i of Y equals
D[i] * row i of X};

    r := Nrows(X);
    t := Type(BaseRing(X));
    if t eq RngInt then
        return X, [1: i in [1 .. r]];
    end if;

    require t eq FldRat: "Matrix is not rational";
    D := [LCM({Denominator(x): x in Eltseq(X)}): i in [1 .. r]];
    V := RSpace(IntegerRing(), Ncols(X));
    return Matrix([V | D[i]*X[i]: i in [1 .. r]]), D;
end intrinsic;

////////////

intrinsic Denominator(X::Mtrx) -> RngElt
{Common denominator of matrix/vector X}

    R := IntegerRing(BaseRing(X));
    m := Nrows(X);
    n := Ncols(X);
    return LCM({R | Denominator(x): x in Eltseq(X)});
end intrinsic;

intrinsic ClearDenominator(X::Mtrx) -> Mtrx
{Clear common denominator of matrix X}

    K := BaseRing(X);
    R := IntegerRing(K);
    d := Denominator(X);
    return Matrix(R, d*X), d;
end intrinsic;

intrinsic ClearRowDenominators(X::Mtrx) -> Mtrx
{Clear common row denominators of matrix X}

    K := BaseRing(X);
    R := IntegerRing(K);
    m := Nrows(X);
    n := Ncols(X);
    Y := Matrix(
	R, Nrows(X), Ncols(X),
	[Denominator(v)*v where v := X[i]: i in [1 .. m]]
    );
    return Y;
end intrinsic;

intrinsic EDMS(X::.) -> {**}
{The elementary divisors of X as a multi-set}
    return SequenceToMultiset(ElementaryDivisors(X));
end intrinsic;
