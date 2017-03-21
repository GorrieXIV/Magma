freeze;

import "../Root/RootDtm.m": basisChange;

intrinsic Collect( R::RootDtm, D::LieRepDec, ResMat ) -> LieRepDec
{ Attemps to perform the inverse operation of branch, namely to reconstruct a R-module from its restriction to a smaller group.
  We compute decomp(filter_dom(dom_char(p,h)*InvResMat, g), g). See also page 69 of the LiE manual.  

  Note that for this form you must supply the matrix used in branch. This is *different*
  from the way it is done in LiE.
}
    GrpH := RootDatum(D);
	DimH := Dimension(GrpH);
	SSRankG := Rank(R);

    require DimH eq Dimension(R) : "Dimensions of RootData must be equal";

	InvResMat := (ChangeRing(ResMat, Rationals())) ^-1;

	res := LieRepresentationDecomposition(R);

    dcw, dcm := Explode( (DominantCharacter(D))`WtsMps );

	for i in [1..#dcw] do
		wt := dcw[i]; mp := dcm[i];

		add_wt := wt*InvResMat;
		add_wt_in_wt_basis := basisChange(R, add_wt, "Standard", "Weight", false);
		if (exists{a : a in Eltseq(add_wt_in_wt_basis) | a lt 0}) then
			continue i;
		end if;
		//add_wt := basisChange(R, add_wt, "Weight", "Standard", false);

        AddRepresentation(~res, add_wt, mp);
	end for;

	return DecomposeCharacter(res);
end intrinsic;
