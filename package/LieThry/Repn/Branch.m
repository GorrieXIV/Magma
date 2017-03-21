freeze;

import "../Root/RootDtm.m": basisChange;
import "RootDatumDan.m" : myComponents;

/* ActiveVars for Branch
   1. ToRootDtm
   2. FromRootDatum
   3. RestrictionMatrix
   4. Multi
   5. DRes                 (Result)
*/
function Branch_Simple_Irreducible( FromSimpGrp, ToGrp, Lambda, ResMat : Virtual := false) //-> LieRepDec
/*
  Branch irreducible module `lambda' to group `ToGrp' from simple group `FromSimpGrp' via linear map `ResMat'
*/
	ToLieRank := Dimension(ToGrp);
	ToSemiSimpleRank := Rank(ToGrp);

    V := VectorSpace(Rationals(), Dimension(ToGrp));
    ToWtBasis := Matrix([ basisChange(ToGrp, v, "Standard", "Weight", false) : v in Basis(V)]);

    DFrom := LieRepresentationDecomposition(FromSimpGrp);
	ActiveVars := [* ToGrp, FromSimpGrp, ResMat, ToWtBasis, 0, LieRepresentationDecomposition(ToGrp) *];
	WeylloopInitResult := InternalWeylloopInit( DFrom );

	domchar, mps := DominantCharacter( FromSimpGrp, Eltseq(Lambda) );

	for i in [1..#domchar] do
		ActiveVars[5] := mps[i];
		InternalWeylloopMain_Branch(~DFrom, WeylloopInitResult, ~ActiveVars, ChangeRing(domchar[i],Rationals()) );
	end for;

    if (Rank(ToGrp) gt 0) then
		if not Virtual then
	        ret := DecomposeCharacter( ActiveVars[6] );
		else
			ret := VirtualDecomposition( ActiveVars[6] );
		end if;
    else
        ret := ActiveVars[6];
    end if;
	return ret;
end function;


intrinsic Branch( FromGrp::RootDtm, ToGrp::RootDtm, v::ModTupRngElt, ResMat : Virtual := false) -> LieRepDec
{ 
  Branch irreducible module `v' to group `ToGrp' from (composite) group `FromGrp' via linear map `ResMat'
}
	v := ChangeRing(v, Rationals());
    ResMat := ChangeRing(ResMat, Rationals());
    require Dimension(FromGrp) eq NumberOfRows(ResMat) : "Dimension of source must be equal to the number of rows of the restriction matrix.";
    require Dimension(ToGrp) eq NumberOfColumns(ResMat) : "Dimension of target must be equal to the number of columns of the restriction matrix.";

	if (IsIrreducible(FromGrp)) then
		return Branch_Simple_Irreducible( FromGrp, ToGrp, v, ResMat : Virtual := Virtual );
	end if;

	FromTRank := Dimension(FromGrp) - Rank(FromGrp);
	FromSSRank := Rank(FromGrp);
	FromDim := Dimension(FromGrp);
	ToRank := Dimension(ToGrp);

	Comps, pi := myComponents(FromGrp);

	LambdaPi := PermuteSequence(Eltseq(v), pi);
	ResMatPi := PermuteSequence([ ResMat[row] : row in [1..NumberOfRows(ResMat)] ], pi);

	if (FromTRank eq 0) then
		tmpwt := Vector([ 0 : i in [1..FromDim] ]);
	else
		LambdaPi_ToralPart := Matrix([ LambdaPi[[FromSSRank+1..FromDim]] ]);
		ResMatPi_ToralPart := Matrix(ResMatPi[[FromSSRank+1..FromDim]]);
		tmpwt := (LambdaPi_ToralPart*ResMatPi_ToralPart);
	end if;

	pos := FromSSRank + 1;
	wtsmps := AlternatingDominant( LieRepresentationDecomposition(ToGrp, tmpwt) );

	for i in [#Comps..1 by -1] do
		dsd := Comps[i][1];
		d := Rank(dsd); pos -:= d;
		Lambda2 := ChangeRing(Vector([ LambdaPi[i] : i in [pos..(pos+d-1)] ]), Rationals());
		ResMat2 := ChangeRing(Matrix(ResMatPi[[pos..(pos+d-1)]]), Rationals());
		wtsmpsnew := Branch_Simple_Irreducible( dsd, ToGrp, Lambda2, ResMat2 : Virtual := Virtual);

		/* tensor in togrp */
		wtsmps := Tensor( wtsmpsnew, wtsmps );
	end for;

	if (not(IsIdentity(pi))) then
		wtsmps := PermuteWeights(wtsmps, pi^-1, ToGrp);
	end if;

	return wtsmps;
end intrinsic;

intrinsic Branch( FromGrp::RootDtm, ToGrp::RootDtm, v::SeqEnum, ResMat : Virtual := false ) -> LieRepDec
{ Branch irreducible module `v' to group `ToGrp' from (composite) group `FromGrp' via linear map `ResMat' }
    return Branch(FromGrp, ToGrp, ChangeRing(Vector(v), Rationals()), ResMat : Virtual := Virtual);
end intrinsic;

intrinsic Branch( ToGrp::RootDtm, D::LieRepDec, ResMat  : Virtual := false) -> LieRepDec
{ 
  branch module `D' to group `ToGrp' from group `RootDatum(D)' via linear map `ResMat'
}
    FromGrp := RootDatum(D);
    require Dimension(FromGrp) eq NumberOfRows(ResMat) : "Dimension of source must be equal to the number of rows of the restriction matrix.";
    require Dimension(ToGrp) eq NumberOfColumns(ResMat) : "Dimension of target must be equal to the number of columns of the restriction matrix.";

    Wts, Mps := Explode(D`WtsMps);
	if (#Wts eq 0) then return D; end if;

    res := LieRepresentationDecomposition(ToGrp);
	for i in [1..#(Wts)] do
	    AddRepresentation(~res, Branch(FromGrp, ToGrp, Wts[i], ResMat : Virtual := Virtual), Mps[i]);
	end for;
	return res;
end intrinsic;
