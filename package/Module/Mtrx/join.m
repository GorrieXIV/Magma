freeze;

/*******************************************************************************
			    Joining with padding
*******************************************************************************/

/*
AKS, Sep 2013.
*/

intrinsic RightVerticalJoin(Q::<>) -> Mtrx
{The vertical block joining of the elements of Q, aligned on the right
(the number of columns may be different; padding added as
necessary on the left for each block).}

    require #Q gt 0: "Tuple must be non-empty";

    R := 0;
    NR := [];
    NC := [];
    for i := 1 to #Q do
	X := Q[i];
	require ISA(Type(X), Mtrx): "Element", i, "is not a matrix";
	Ri := BaseRing(X);
	if i eq 1 then
	    R := Ri;
	else
	    require Ri cmpeq R: "Incompatible base rings";
	end if;
	Append(~NR, Nrows(X));
	Append(~NC, Ncols(X));
    end for;

    nc := Max(NC);

    b := 1;
    J := ZeroMatrix(R, &+NR, nc);
    for i := 1 to #Q do
	X := Q[i];
	InsertBlock(~J, X, b, nc - NC[i] + 1);
	b +:= NR[i];
    end for;

    return J;

end intrinsic;

intrinsic RightVerticalJoin(Q::[Mtrx]) -> Mtrx
{"} // "

    return RightVerticalJoin(<X: X in Q>);

end intrinsic;

intrinsic RightVerticalJoin(X::Mtrx, Y::Mtrx) -> Mtrx
{The vertical block joining of X and Y, aligned on the right
(the number of columns may be different; padding added as
necessary on the left for each block).}

    R := BaseRing(X);
    require BaseRing(Y) cmpeq R: "Incompatible base rings";

    return RightVerticalJoin(<X, Y>);

end intrinsic;
