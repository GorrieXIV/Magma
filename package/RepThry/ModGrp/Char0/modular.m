freeze;

Z := IntegerRing();
Q := RationalField();

START_p := Floor(2^23.5);

/*******************************************************************************
			    Next prime
*******************************************************************************/

function next_prime(p, f: Cyclo := 0)
    if p eq 0 then
	p := START_p;
    end if;

    if Cyclo gt 0 then
	k := p div Cyclo;
    end if;

    while true do

	if Cyclo gt 0 then
	    repeat
		k -:= 1;
		p := k*Cyclo + 1;
	    until IsPrime(p);
	else
	    p := PreviousPrime(p);
	end if;

	//"Try prime", p;
	F := GF(p);

	if Type(f) eq SeqEnum then
	    /*
	    R := try_roots(f, F);
	    R := [Roots(g, F): f in g];
	    if forall{i: i in [1 .. #f] | R[i] eq Degree(f[i])} then
		return p, [[t[1]: t in r]: r in R];
	    end if;
	    */
	else
	    R := Roots(f, F);
	    if #R eq Degree(f) then
		//"New prime", p;
		return p, [t[1]: t in R];
	    end if;
	end if;
    end while;
end function;

intrinsic NextANFPrime(p::RngIntElt, f::.: Cyclo := 0) -> RngIntElt, []
{Next prime below p for which f splits}
    return next_prime(p, f: Cyclo := Cyclo);
end intrinsic;
