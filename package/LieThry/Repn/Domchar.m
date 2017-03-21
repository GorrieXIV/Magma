freeze;

import "../Root/RootDtm.m": basisChange;
import "RootDatumDan.m": myComponents;

function Dim_Simple_Irreducible( G, lambda ) //->RngIntElt
/* The Dimension of the irreducible representation lambda */
	LieRank := Rank(G);
	denom := 1; numer := 1;
	rootnorms := RootNorms(G);
	for alpha in PositiveRoots(G : Basis := "Root") do
		den := 0; num := 0;
		for j in [1..LieRank] do
			den +:= alpha[j]*rootnorms[j];
			num +:= alpha[j]*rootnorms[j]*(lambda[j]+1);
		end for;
		denom *:= den; numer *:= num;
	end for;
	return numer/denom;
end function;


function RepDim(R, Wts, Mps) 
	res := 0;
	comps, pi := myComponents(R);

	for i in [1..#Wts] do
		v := Wts[i];
		Wtpi := PermuteSequence(Eltseq(v), pi);
		pos := 1;
		compres := 1;

		for comp in comps do
			if (Type(comp[1]) eq MonStgElt and comp[1] eq "T") then continue; end if;
			ssp := comp[1];
			rnk := #(comp[2]);
			compres *:= Dim_Simple_Irreducible( ssp, Vector( Wtpi[[pos..(pos+rnk-1)]]) );
			pos +:= rnk;
		end for;

		res +:= Mps[i]*compres;
	end for;

	return res;
end function;


intrinsic RepresentationDimension( R::RootDtm, v::SeqEnum ) -> RngIntElt
{ Dimension of the representation V_v }
	return RepDim(R, [ Vector(v) ], [1]);
end intrinsic;

intrinsic RepresentationDimension( R::RootDtm, v::ModTupRngElt ) -> RngIntElt
{ " }
	return RepDim(R, [ ChangeRing(Vector(v),Rationals()) ], [1]);
end intrinsic;


intrinsic RepresentationDimension( D::LieRepDec ) -> RngIntElt
{ Dimension of the representation with decomposition D }
    R := RootDatum(D); Wts, Mps := Explode(D`WtsMps);
	return RepDim(R, Wts, Mps);
end intrinsic;


intrinsic DominantCharacter( D::LieRepDec : InBasis := "Standard") -> LieRepDec
{ Dominant character on more than one element.

  OutBasis is always "Standard".
 }
    R := RootDatum(D);
	rnkR := Rank(R); dimR := Dimension(R); 
	wtsp := RSpace(Rationals(), dimR);

    out := LieRepresentationDecomposition(R);
    Wts, Mps := Explode(D`WtsMps);
	for i in [1..#Wts] do
		wt := Eltseq(Wts[i]); c := Mps[i];
		wt_in_wt_basis := basisChange(R, wt, InBasis, "Weight", false);
			
		if (InBasis eq "Standard") then
			wt_in_std_basis := basisChange(R, wt_in_wt_basis, "Weight", "Standard", false);
			toral_part_of_wt := wtsp!wt - wt_in_std_basis;
		else
			toral_part_of_wt := ChangeRing(Vector([0 : i in [1..dimR] ]), Rationals());
		end if;

		tmpwts, tmpmps := DominantCharacter(R, wt_in_wt_basis);
		
		for j in [1..#tmpwts] do
			wt := basisChange(R, tmpwts[j], "Weight", "Standard", false);
			AddRepresentation(~out, wt + toral_part_of_wt, c*tmpmps[j]);
		end for;
	end for;

	return out;
end intrinsic;


/* 

//Original function:
> DominantCharacter(LiERootDatum("A2T1"), [1,1,-4]);

>> DominantCharacter(LiERootDatum("A2T1"), [1,1,-4]);
                    ^
Runtime error in 'DominantCharacter': The weight is not of the correct length

//New function:
> DominantCharacter(LiERootDatum("A2T1"),<[[1,1,-4]],[1]>);
<[
    ( 1  1 -4),
    ( 0  0 -4)
], [ 1, 2 ]>

cf LiE:

> dom_char([1,1,-4], A2T1)
     2X[0,0,-4] +1X[1,1,-4]

*/
