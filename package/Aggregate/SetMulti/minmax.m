freeze;

intrinsic Minimum(S::SetMulti) -> .
{The minimum of the elements of S};
    require not IsEmpty(S): "Illegal empty set";
    first := true;
    for x in Set(S) do
	if first then
	    first := false;
	    min := x;
	else
	    min := Min(x, min);
	end if;
    end for;
    return min;
end intrinsic;

intrinsic Maximum(S::SetMulti) -> .
{The maximum of the elements of S};
    require not IsEmpty(S): "Illegal empty set";
    first := true;
    for x in Set(S) do
	if first then
	    first := false;
	    max := x;
	else
	    max := Max(x, max);
	end if;
    end for;
    return max;
end intrinsic;
