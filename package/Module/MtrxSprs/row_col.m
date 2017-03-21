freeze;

/*******************************************************************************
				Add row
*******************************************************************************/

intrinsic AddRow(~X::MtrxSprs, c::RngIntElt, i::RngIntElt, j::RngIntElt)
{Add c times row i of X to row j of X in place};

    requirerange i, 1, Nrows(X);
    requirerange j, 1, Nrows(X);
    l, c := IsCoercible(BaseRing(X), c);
    require l: "Argument 2 not coercible into ring of matrix";
    if IsZero(c) then
	return;
    end if;
    for k in Support(X, i) do
	X[j, k] := X[j, k] + c*X[i, k];
    end for;
end intrinsic;

intrinsic AddRow(X::MtrxSprs, c::RngIntElt, i::RngIntElt, j::RngIntElt)
    -> MtrxSprs
{Return the matrix obtained from X by adding c times row i of X to row j of X}

    AddRow(~X, c, i, j);
    return X;
end intrinsic;

/*******************************************************************************
				Add column
*******************************************************************************/

intrinsic AddColumn(~X::MtrxSprs, c::RngIntElt, i::RngIntElt, j::RngIntElt)
{Add c times column i of X to column j of X in place};

    nc := Ncols(X);
    requirerange i, 1, nc;
    requirerange j, 1, nc;
    l, c := IsCoercible(BaseRing(X), c);
    require l: "Argument 2 not coercible into ring of matrix";
    if IsZero(c) then
	return;
    end if;
    for k := 1 to Nrows(X) do
	X[k, j] := X[k, j] + c*X[k, i];
    end for;
end intrinsic;

intrinsic AddColumn(X::MtrxSprs, c::RngIntElt, i::RngIntElt, j::RngIntElt)
    -> MtrxSprs
{Return the matrix obtained from X by adding c times column i of X to
column j of X}

    AddColumn(~X, c, i, j);
    return X;
end intrinsic;

/*******************************************************************************
				Multiply row
*******************************************************************************/

intrinsic MultiplyRow(~X::MtrxSprs, c::RngIntElt, i::RngIntElt)
{Multiply row i of X by the scalar c in place}

    requirerange i, 1, Nrows(X);
    l, c := IsCoercible(BaseRing(X), c);
    require l: "Argument 2 not coercible into ring of matrix";
    if IsOne(c) then
	return;
    end if;
    for k in Support(X, i) do
	X[i, k] := c*X[i, k];
    end for;
end intrinsic;

intrinsic MultiplyRow(X::MtrxSprs, c::RngIntElt, i::RngIntElt) -> MtrxSprs
{Return the matrix obtained from X by multiplying row i by the scalar c};

    MultiplyRow(~X, c, i);
    return X;
end intrinsic;

/*******************************************************************************
				Multiply column
*******************************************************************************/

intrinsic MultiplyColumn(~X::MtrxSprs, c::RngElt, i::RngIntElt)
{Multiply column i of X by the scalar c in place}

    requirerange i, 1, Nrows(X);
    l, c := IsCoercible(BaseRing(X), c);
    require l: "Argument 2 not coercible into ring of matrix";
    if IsOne(c) then
	return;
    end if;
    for k := 1 to Nrows(X) do
	X[k, i] := c*X[k, i];
    end for;
end intrinsic;

intrinsic MultiplyColumn(X::MtrxSprs, c::RngElt, i::RngIntElt) -> MtrxSprs
{Return the matrix obtained from X by multiplying column i by the scalar c};

    MultiplyColumn(~X, c, i);
    return X;
end intrinsic;
