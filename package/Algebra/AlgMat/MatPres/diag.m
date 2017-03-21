freeze;

declare type MtrxDiag;

declare attributes MtrxDiag: T;

/*******************************************************************************
			Base operations
*******************************************************************************/

intrinsic Print(D::MtrxDiag, level::MonStgElt)
{}
    printf "Diagonal block matrix %o", [Nrows(x): x in D`T];
end intrinsic;

/*******************************************************************************
			    Creation
*******************************************************************************/

intrinsic BlockDiagMat(T::Tup) -> MtrxDiag
{The diagonal block matrix given by T}

    D := New(MtrxDiag);
    D`T := T;
    return D;

end intrinsic;

intrinsic BlockDiagScalarMat(B::[RngIntElt], x::RngElt) -> MtrxDiag
{Scalar matrix for x, using block structure B}

    return BlockDiagMat(<ScalarMatrix(b, x): b in B>);
end intrinsic;

intrinsic HasBlockDiagMat(X::Mtrx, B::[RngIntElt]) -> BoolElt, MtrxDiag
{}
    // Quick hack

    b := 1;
    T := <>;
    for n in B do
	Y := Submatrix(X, b, b, n, n);
	Append(~T, Y);
	b +:= n;
    end for;

    if DiagonalJoin(T) eq X then
	return true, BlockDiagMat(T);
    else
	return false, _;
    end if;
end intrinsic;

intrinsic BlockDiagMat(X::Mtrx, B::[RngIntElt]) -> MtrxDiag
{}
    l, D := HasBlockDiagMat(X, B);
    assert l;
    return D;
end intrinsic;

/*******************************************************************************
			    Access
*******************************************************************************/

intrinsic Matrix(A::MtrxDiag) -> Mtrx
{Dense matrix equal to A}
    return DiagonalJoin(A`T);
end intrinsic;

intrinsic CoefficientRing(A::MtrxDiag) -> MtrxDiag
{Coefficient ring of A}
    return CoefficientRing(A`T[1]);
end intrinsic;

/*******************************************************************************
			    Arithmetic
*******************************************************************************/

compat := func<A, B |
    #AT eq #BT and forall{i: i in [1..#AT] | Ncols(AT[i]) eq Ncols(BT[i])}
	where AT := A`T where BT := B`T>;

function binary_op(A, B, op)
    AT := A`T;
    BT := B`T;
    return BlockDiagMat(<op(AT[i], BT[i]): i in [1 .. #AT]>);
end function;

intrinsic '+'(A::MtrxDiag, B::MtrxDiag) -> MtrxDiag
{A + B}
    require compat(A, B): "Arguments are not compatible";
    return binary_op(A, B, '+');
end intrinsic;

intrinsic '-'(A::MtrxDiag, B::MtrxDiag) -> MtrxDiag
{A - B}
    require compat(A, B): "Arguments are not compatible";
    return binary_op(A, B, '-');
end intrinsic;

intrinsic '*'(A::MtrxDiag, B::MtrxDiag) -> MtrxDiag
{A*B}
    require compat(A, B): "Arguments are not compatible";
    return binary_op(A, B, '*');
end intrinsic;

intrinsic '^'(A::MtrxDiag, n::RngIntElt) -> MtrxDiag
{A^n}
    return BlockDiagMat(<X^n: X in A`T>);
end intrinsic;

/*******************************************************************************
				Mutation
*******************************************************************************/

procedure binary_op_mutate(~A, ~B, op)
    AT := A`T;
    BT := B`T;
    for i := 1 to #A`T do
	op(~A`T[i], ~B`T[i]);
    end for;
end procedure;

intrinsic '+:='(~A::MtrxDiag, ~B::MtrxDiag)
{A +:= B}
    require compat(A, B): "Arguments are not compatible";
    binary_op_mutate(~A, ~B, '+:=');
end intrinsic;

intrinsic '-:='(~A::MtrxDiag, ~B::MtrxDiag)
{A -:= B}
    require compat(A, B): "Arguments are not compatible";
    binary_op_mutate(~A, ~B, '-:=');
end intrinsic;

intrinsic '^:='(~A::MtrxDiag, n::RngIntElt)
{A ^:= n}
    for i := 1 to #A`T do
	A`T[i] ^:= n;
    end for;
end intrinsic;

/*******************************************************************************
			    Predicates
*******************************************************************************/

intrinsic IsZero(A::MtrxDiag) -> MtrxDiag
{Return whether A is zero}
    return forall{X: X in A`T | IsZero(X)};
end intrinsic;

intrinsic IsIdempotent(A::MtrxDiag) -> MtrxDiag
{Return whether A is idempotent}
    return forall{X: X in A`T | IsIdempotent(X)};
end intrinsic;

intrinsic IsNilpotent(A::MtrxDiag) -> BoolElt, RngIntElt
{Return whether A is nilpotent}
    m := 0;
    for X in A`T do
	l, d := IsNilpotent(X);
	if not l then
	    return false, _;
	end if;
	m := Max(m, d);
    end for;
    return true, m;
end intrinsic;

intrinsic IsInvertible(A::MtrxDiag) -> BoolElt, MtrxDiag
{Return whether A is invertible and the inverse, if so}
    T := <>;
    for X in A`T do
	l, Y := IsInvertible(X);
	if not l then
	    return false, _;
	end if;
	Append(~T, Y);
    end for;
    return true, BlockDiagMat(T);
end intrinsic;

/*******************************************************************************
			    Other
*******************************************************************************/

intrinsic Evaluate(f::RngUPolElt, A::MtrxDiag) -> MtrxDiag
{Return f(A)}
    return BlockDiagMat(<Evaluate(f, X): X in A`T>);
end intrinsic;

intrinsic Evaluate(S::[RngUPolElt], A::MtrxDiag) -> []
{Return f(A)}
    if #S eq 0 then
	return [];
    end if;
    E := <Evaluate(S, X): X in A`T>;
    return [BlockDiagMat(<E[i, j]: i in [1 .. #E]>): j in [1 .. #E[1]]];
end intrinsic;

intrinsic Rank(A::MtrxDiag) -> ModTupRng
{Return the rank of A}
    return &+[Rank(X): X in A`T];
end intrinsic;

intrinsic RowSpace(A::MtrxDiag) -> ModTupRng
{Return the rowspace of A}
    return DirectSum([RowSpace(X): X in A`T]);
end intrinsic;

intrinsic '*'(v::ModTupRngElt, A::MtrxDiag) -> ModTupRngElt
{Return v*A};
    b := 1;
    Q := [];
    for X in A`T do
	n := Nrows(X);
	w := Submatrix(v, 1, b, 1, n) * X;
	Q cat:= Eltseq(w);
	b +:= n;
    end for;
    return Vector(Q);
end intrinsic;
