freeze;
 
///////////////////////////////////////////////////////////////////////
//			Lists of singularities
///////////////////////////////////////////////////////////////////////

intrinsic IsolatedGorensteinSingularitiesOfIndex(r::RngIntElt) -> SeqEnum
{A sequence of isolated singularities of the form 1/r(a,b,c) with
a + b + c = 0 mod r}
    sings := [ PowerStructure(GRPtS) | ];
    if IsEven(r) then
	return sings;
    end if;
    for i in [1..r-1] do
	if GCD(r,i) ne 1 then
	    continue i;
	end if;
	for j in [i..r-1] do
	    if GCD(r,j) ne 1 then
		continue j;
	    end if;
	    if i+j lt r then
		if GCD(r,r-i-j) ne 1 or r-i-j lt j then
		    continue j;
		end if;
		Append(~sings,Point(r,[i,j,r-i-j]));
	    elif i+j gt r then
		if GCD(r,2*r-i-j) ne 1 or 2*r-i-j lt j then
		    continue j;
		end if;
		Append(~sings,Point(r,[i,j,2*r-i-j]));
	    else
		continue j;
	    end if;
	end for;
    end for;
    return sings;
end intrinsic;

