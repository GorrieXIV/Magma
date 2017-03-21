freeze;
 
 
intrinsic RestrictPartitionLength(s::AlgSymElt,l::RngIntElt : Exact := true) -> AlgSymElt
{Return the portion of the symmetric function s whose labelling partitions are of length (<)= l}

    requirege l,0;
    P, C := Support(s);
    p:=Parent(s);
    res := Zero(p);
    for i in [1..#P] do
	if #P[i] eq l then
	    c:=C[i] * p.(P[i]);
	    res +:= c;
	elif not Exact and #P[i] lt l then
	    c:=C[i] * p.(P[i]);
	    res +:= c;
	end if;
    end for;
    return res;
end intrinsic;

intrinsic RestrictParts(s::AlgSymElt,l::RngIntElt : Exact := true) -> AlgSymElt
{Return the portion of the symmetric function s whose labelling partitions have maximal parts (<)= l}
    requirege l,0;
    P, C := Support(s);
    p:=Parent(s);
    res := Zero(p);
    for i in [1..#P] do
	if #P[i] eq 0 then
	    if not Exact or l eq 0 then
		c:=C[i] * p.(P[i]);
		res +:= c;
	    end if;
	elif P[i][1] eq l then
	    c:=C[i] * p.(P[i]);
	    res +:= c;
	elif not Exact and P[i][1] le l then
	    c:=C[i] * p.(P[i]);
	    res +:= c;
	end if;
    end for;
    return res;
end intrinsic;

intrinsic RestrictDegree(s::AlgSymElt,l::RngIntElt : Exact := true) -> AlgSymElt
{Return the portion of the symmetric function s whose degree is (<)= l}
    requirege l,0;
    P, C := Support(s);
    p:=Parent(s);
    res := Zero(p);
    for i in [1..#P] do
	if Weight(P[i]) eq l or (not Exact and Weight(P[i]) le l) then
	    c:=C[i] * p.(P[i]);
	    res +:= c;
	end if;
    end for;
    return res;
end intrinsic;

