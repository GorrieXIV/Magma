freeze;

Z := IntegerRing();
Lee := [0, 1, 2, 1];

intrinsic LeeWeight1(v::ModTupRngElt) -> RngIntElt
{Return the Lee weight of the vector v}
    p := #BaseRing(Parent(v));
    if p eq 4 then
	return &+[Lee[Z!v[i] + 1]: i in [1 .. Ncols(v)]];
    end if;

    require IsPrime(p): "Vector should be over Z_4 or a prime field";
    pm1o2 := (p-1) div 2; 
    w := 0;
    for i in [1 .. Degree(v)] do
	    ci := Abs(Z!v[i]);
	    if (ci le pm1o2) then
		    w +:= ci;
	    else
		    w +:= Abs(Z!(-ci));
	    end if;
    end for;
    return w;
end intrinsic;

intrinsic LeeDistance1(v::ModTupRngElt, w::ModTupRngElt) -> RngIntElt
{Return the Lee distance between the vectors v and w}
    p := #BaseRing(Parent(v));
    require p eq 4 or IsPrime(p): "Vector should be over Z_4 or a prime field";
    return LeeWeight1(v - w);
end intrinsic;
