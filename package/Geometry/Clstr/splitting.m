freeze;

intrinsic PointsOverSplittingField(Z::Sch) -> SetIndx, Fld
    {An indexed set of the points of the zero-dimensional scheme Z
    defined over a splitting field, with the splitting field returned
    as a second value.}
    // AKS explained the VarietySizeOverAlgebraicClosure intrinsic.
    K := BaseRing(Z);
    dim := Dimension(Z);
    if dim eq -1 then // scheme empty!
        return {@ @},K;
    end if;
    require dim eq 0: "Argument must be zero dimensional";
    if Type(K) cmpeq FldAC then
	return RationalPoints(Z),K;
    elif K cmpeq RationalField() then
        pts := RationalPoints(Z,AlgebraicClosure());
	return pts, Ring(Parent(Representative(pts)));
    elif Type(K) eq FldFin then
	if IsAffine(Z) then
	    r := RadicalDecomposition(DefiningIdeal(Z));
	    d := LCM([VarietySizeOverAlgebraicClosure(J): J in r]);
	    L := ext< K | d >;
	    return RationalPoints(Z,L),L;
	else
	    ext_degs := [];
	    for i in [1..NumberOfAffinePatches(Z)] do
		Zi := AffinePatch(Z,i);
		ri := RadicalDecomposition(DefiningIdeal(Zi));
                if #ri ne 0 then
		  di := LCM([VarietySizeOverAlgebraicClosure(J): J in ri]);
		  Append(~ext_degs,di);
                end if;
	    end for;
	    d := LCM(ext_degs);
	    L := ext<K | d>;
	    return RationalPoints(Z,L),L;
	end if;
    else
	require false: "Cannot compute over the given base field";
    end if;
end intrinsic;

