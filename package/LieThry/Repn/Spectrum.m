freeze;

import "RootDatumDan.m" : myComponents;

/* ActiveVars for Spectrum
   1. SemiSimpleElement (being analyzed, vector)
   2. SemiSimpleOrder   (integer)
   3. SpectrumCoeffs    (result, integer sequence)
   4. Multi             (integer)
*/
procedure Spectrum_AddWeight( ~ActiveVars, v )
	i := InnerProduct(v, ActiveVars[1]) mod ActiveVars[2];
	ActiveVars[3][i+1] +:= ActiveVars[4];
end procedure;

function Spectrum_Simple_Irreducible( Grp, Lambda, ToralElt, Ord, PR ) //->RngUPolElt
/*  note: the LiE notation of toral elements is used! */
	X := PR.1;
	SpectrumCoeffs := [ Integers() | 0 : i in [1..Ord] ];

	D := LieRepresentationDecomposition(Grp);	
	ActiveVars := [* ToralElt, Ord, SpectrumCoeffs, 0 *];
    WeylloopInitResult := InternalWeylloopInit(D);
	
	domchar, mps := DominantCharacter(Grp, Eltseq(Lambda));
	
	for i in [1..#domchar] do
		ActiveVars[4] := mps[i];
		InternalWeylloopMain_Spectrum( ~D, WeylloopInitResult, ~ActiveVars, domchar[i] );
	end for;
	
	return &+[ ActiveVars[3][i]*X^(i-1) : i in [1..Ord] ];
end function;

function Spectrum_Irreducible( Grp, Lambda, ToralElt, Ord, PR ) //->RngUPolElt
/*  note: the LiE notation of toral elements is used! */
	SSRank := Rank(Grp);
	TotRank := Dimension(Grp);
	TRank := TotRank-SSRank;
	X := PR.1;

	if (TRank eq 0) then 
		exp := 0; 
	else 
		exp := Integers()!(&+[ Lambda[i]*ToralElt[i] : i in [(SSRank+1)..TotRank] ]) mod Integers()!Ord; 
	end if;
	res := X^exp;

	Comps, pi := myComponents(Grp);
	LambdaPi := PermuteSequence(Eltseq(Lambda), pi);
	ToralEltPi := PermuteSequence(Eltseq(ToralElt), pi);

	pos := SSRank + 1;
	for i in [#Comps..1 by -1] do
		if Comps[i][1] cmpeq "T" then continue; end if;
		dsd := Comps[i][1];
		d := Rank(dsd); pos -:= d;
		Lambda2 := ChangeRing(Vector([ LambdaPi[i] : i in [pos..(pos+d-1)] ]), Rationals());
		ToralElt2 := ChangeRing(Vector([ ToralEltPi[i] : i in [pos..(pos+d-1)] ]), Rationals());
		res *:= Spectrum_Simple_Irreducible( dsd, Lambda2, ToralElt2, Ord, PR );
		res := &+[ trm / X^(Ord*(Degree(trm) div Ord)) : trm in Terms(PR!res) ]; 
	end for;

	return res;
end function;

intrinsic Spectrum( R::RootDtm, v::ModTupRngElt, ToralElt::SeqEnum ) -> SeqEnum
{ Spectrum.  }
	return Spectrum( LieRepresentationDecomposition(R, v), ToralElt );
end intrinsic;
intrinsic Spectrum( R::RootDtm, v::SeqEnum, ToralElt::SeqEnum ) -> SeqEnum
{ " }
	return Spectrum( LieRepresentationDecomposition(R, v), ToralElt );
end intrinsic;


intrinsic Spectrum( D::LieRepDec, ToralElt::SeqEnum ) -> SeqEnum
{ Spectrum.  }
    R := RootDatum(D);
	DimR := Dimension(R);

	Ord := ToralElt[DimR+1];
	ToralElt := Vector(ToralElt[[1..DimR]]);
	
	PR := PolynomialRing(Integers());
	res := PR!0;

    Wts, Mps := Explode(D`WtsMps); N := #Wts;
	for i in [1..N] do
		res +:= Mps[i]*Spectrum_Irreducible( R, Wts[i], ToralElt, Ord, PR );
	end for;  

	return [ Coefficient(PR!res, i) : i in [0..(Ord-1)] ];
end intrinsic;
