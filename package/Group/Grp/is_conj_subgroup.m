freeze;

isRefinedOrblen := function(O1, O2)
/* Test if the orbit lengths O1 are a refinement of O2.  */

    n1 := #O1;
    n2 := #O2;

    if n2 gt n1 then
	return false;
    end if;

    if n2 eq 1 then
	return true;
    end if;

    left1 := [];
    left2 := O2;
    for i := 1 to n1 do
	p := Position(left2, O1[i]);
	if p eq 0 then
	    Append(~left1, O1[i]);
	else
	    Remove(~left2, p);
	end if;
    end for;

    n1 := #left1;
    n2 := #left2;

    if 2 * n2 gt n1 then
	return false;
    end if;

    if n2 eq 1 then
	return true;
    end if;

    /* rest is harder ... */
    return true;
end function;

intrinsic IsConjugateSubgroup(G::Grp, M::Grp, N::Grp) -> BoolElt, GrpElt
{Whether a conjugate of N is a subgroup of M, and if so, a conjugating element}

    require Type(G) eq Type(M) and M subset G:
	"Argument 2 is not a subgroup of argument 1";
    require Type(G) eq Type(N) and N subset G:
	"Argument 3 is not a subgroup of argument 1";
    
    if IsTrivial(N) or G eq M then
	return true, Id(G);
    end if;

    if Order(M) mod Order(N) ne 0 then
	return false, _;
    end if;

    if Type(G) eq GrpPerm then
	OM := [#x: x in Orbits(M)];
	ON := [#x: x in Orbits(N)];
	if not isRefinedOrblen(ON, OM) then
	    return false, _;
	end if;
    end if;

    NM := Normalizer(G, M);
    NN := Normalizer(G, N);
    lenM := Index(G, NM);
    lenN := Index(G, NN);

    if lenN le lenM then
	if lenN eq 1 then
	    if N subset M then
		return true, Id(G);
	    end if;
	    return false, _;
	end if;
	if exists(t){t: t in Transversal(G, NN) | N^t subset M} then
	    return true, t;
	end if;
	return false, _;
    end if;

    if exists(t){t: t in Transversal(G, NM) | N subset M^t} then
	return true, t^-1;
    end if;
    return false, _;

end intrinsic;

intrinsic Conjugates(G::Grp, H::Grp: Limit := 10000000) -> {}
{The set of conjugates of H by elements of G}
    require Type(G) eq Type(H) and H subset G:
	"Argument 2 is not a subgroup of argument 1";
    N := Normalizer(G, H);
    require Index(G, N) le Limit:
	"Number of conjugates of H in G is more than " cat Sprint(Limit);
    if Type(G) eq GrpPC then
	return { PowerGroup(G) | H^t: t in Transversal(G, N) };
    end if;
    return {H^t: t in Transversal(G, N)};
end intrinsic;

intrinsic Class(G::Grp, H::Grp: Limit := 10000000) -> {}
{The set of conjugates of H by elements of G}
    return Conjugates(G, H: Limit := Limit);
end intrinsic;
