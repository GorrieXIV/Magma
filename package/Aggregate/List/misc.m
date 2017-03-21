freeze;

// Insert for Lists

intrinsic Insert(~L::List, i::RngIntElt, x::Any)
{Destructively insert x into position i in list L.}
  require i gt 0 and i le #L+1: "Index out of range";
  for j in [#L..i by -1] do
    L[j+1] := L[j];
  end for;
  L[i] := x;
end intrinsic;

intrinsic Insert(L::List, i::RngIntElt, x::Any) -> List
{The list built by inserting x into position i in list L.}
  require i gt 0 and i le #L+1: "Index out of range";
  M := L;
  Insert(~M, i, x);
  return M;
end intrinsic;

intrinsic Position(L::List, x::Any) -> RngIntElt
{The index of x in L (i.e. the smallest integer i such that L[i] equals x),
0 if x is not in L}
    for i in [1..#L] do
	if L[i] cmpeq x then
	    return i;
	end if;
    end for;
    return 0;
end intrinsic;

intrinsic Index(L::List, x::Any) -> RngIntElt
{The index of x in L (i.e. the smallest integer i such that L[i] equals x),
0 if x is not in L}
    for i in [1..#L] do
	if L[i] cmpeq x then
	    return i;
	end if;
    end for;
    return 0;
end intrinsic;
