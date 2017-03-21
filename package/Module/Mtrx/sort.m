freeze;

intrinsic SortRows(~X::Mtrx)
{Sort the rows of X (by pivots)}

    n := Ncols(X);

    cmp := function(V, W)
	for j := 1 to n do
	    Vz := IsZero(V[j]);
	    Wz := IsZero(W[j]);
	    if Vz and not Wz then
		return -1;
	    elif not Vz and Wz then
		return +1;
	    end if;
	end for;
	return 0;
    end function;

    V := Rows(X);
    Sort(~V, cmp);
    X := Matrix(V);

end intrinsic;
