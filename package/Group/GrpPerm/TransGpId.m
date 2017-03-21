freeze;

intrinsic TransitiveGroupIdentification(G::GrpPerm:Raw := true) -> RngIntElt, RngIntElt
{The number (and degree) of the group in the transitive groups database isomorphic to G. If Raw is false then the conjugating element is returned as well}

    require IsTransitive(G): "Group must be transitive";
    max := TransitiveGroupDatabaseLimit();
    if Degree(G) gt max then
	str := "Identification only implemented for degrees up to " cat IntegerToString(max);
	require Degree(G) le max: str;
    end if;

    if Degree(G) eq 32 then
	t, p := Trans32Identify(G);
	b := t[1];
	if b eq 2 then
	    filename := GetLibraryRoot() cat "/data/TrnGps/Trn32IdData/t2dbK"
		cat IntegerToString(t[2]) cat "g" cat IntegerToString(t[3]);
	    t2db := eval Read(filename);
	    i := t[4];
	else
	    filename := GetLibraryRoot() cat "/data/TrnGps/Trn32IdData/t2db"
		cat IntegerToString(b);
	    t2db := eval Read(filename);
	    i := t[2];
	end if;
	if Raw then return t2db[i], 32, _;
	else return t2db[i], 32, p;
	end if;
    end if;

    if Degree(G) in [33..47] then
	i,p := Trans33to47Identify(G);
	d := Degree(G);
	if Raw then
	    return i,d,_;
	else
	    return i,d,p;
	end if;
    end if;

    if Raw then
	return InternalTransitiveGroupIdentification(G);
    end if;

    i,d := InternalTransitiveGroupIdentification(G);
    GG := TransitiveGroup(d, i);
    fl, p := MyIsConjugate(Sym(d), G, GG);
    assert fl;
    return i, d, p;
end intrinsic;
