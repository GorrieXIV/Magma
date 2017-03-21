freeze;

intrinsic AllPartitions( S::SetEnum ) -> SetEnum
{Compute all partitions of the set S.}
    if IsEmpty(S) then return {}; end if;
    return {{S}} join {{P} join copart : copart in AllPartitions(S diff P),
	    P in Subsets(S,i), i in [1..#S-1] };
end intrinsic;

intrinsic RandomSubset(S::SetEnum, k::RngIntElt) -> SetEnum
{A random subset of S of cardinality k}
    require k ge 0 and k le #S: "k must be at least 0 and at most", #S;

    if k eq #S then
	return S;
    end if;

    T := { Universe(S) | };
    if k eq 0 then
	return T;
    end if;

    // The old approach was to shrink S as shown below; this turns out
    // to be undesirable because determining a random element requires
    // some precomputation each time the set changes, and that ends up
    // dominating the time.
    /*
	for i := 1 to k do
	    x := Random(S);
	    Exclude(~S, x);
	    Include(~T, x);
	end for;
    */

    // A hybrid approach is possible, where we find a random batch of
    // some size (square root of the target size?) and then remove it,
    // repeating as necessary.  Non-rigorous analysis suggests that this
    // is not worth it given that the target size is at most half of the
    // set size.
    //
    // The optimal split is not actually at the halfway point, as the
    // final diff also takes time.  It is not currently considered worth
    // the effort to investigate the optimal splitting point further,
    // however.

    tsize := k;
    if tsize gt #S - k then
	tsize := #S - k;
    end if;

    while #T lt tsize do
	Include(~T, Random(S));
    end while;

    if tsize ne k then
	T := S diff T;
    end if;

    return T;
end intrinsic;

