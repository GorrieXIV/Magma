freeze;

// Handy function to test if a number is a power of another one...
//			Lancelot Pecquet, 1996
//
// Rewritten (NB: argument order changed) by Geoff, 2001-07-14

intrinsic IsPowerOf(y::RngIntElt, x::RngIntElt) -> BoolElt, RngIntElt
{Returns whether y = x^n for some integer n, and if so also returns n}

    if y eq 1 then
	return true, 0;
    end if;

    if x eq y then
	return true, 1;
    end if;

    ax := Abs(x);
    ay := Abs(y);
    if ax le 1 or ay le 1 then
	return false, _;
    end if;

    n := Round(Log(ax, ay));
    if ay ne ax^n then
	return false, _;
    end if;

    if (IsEven(n) and y lt 0) or (IsOdd(n) and Sign(x) ne Sign(y)) then
	return false, _;
    end if;

    return true, n;
end intrinsic;

/*
intrinsic IsPowerOf(q::RngIntElt,Q::RngIntElt) -> BoolElt,RngIntElt
{Test if Q is a power of q>0, then return true and the exponent or false and 0}
	requirege q,1;
	requirege Q,1;
	if (q eq 1) then
		if (Q eq q) then
			pow := 1;
			rep := true;
		else
			pow := 0;
			rep := false;
		end if;
	elif (q gt Q) then
		pow := 0;
		rep := false;
	else
		pow := Floor(Log(q,Q));
		if (q^(pow-1) eq Q) then
			rep := true;
			pow -:= 1;
		elif (q^pow eq Q) then
			rep := true;
		elif (q^(pow+1) eq Q) then
			rep := true;
			pow +:= 1;
		else
			rep := false;
			pow := 0;
		end if;
	end if;
	return rep,pow;	
end intrinsic;
*/

