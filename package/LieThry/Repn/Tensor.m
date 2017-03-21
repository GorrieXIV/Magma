freeze;

import "../Root/RootDtm.m": basisChange;
import "Domchar.m": Dim_Simple_Irreducible;
import "RootDatumDan.m": myComponents;

function Tensor_SimpleIrreducible( R, lambda, mu : Goal := false ) //->LieRepDec
	for v in {lambda, mu} do
		v0 := basisChange(R, v, "Standard", "Weight", false);
		if (not(forall{ i : i in Eltseq(v0) | i ge 0})) then
			error v, " is not a dominant weight in", R;
		end if;
	end for;

	/* Initialization */
	lambda := ChangeRing(lambda, Rationals());
	mu := ChangeRing(mu, Rationals());
	if (Type(Goal) ne BoolElt) then
		nu := Vector(Goal); nu := ChangeRing(nu, Rationals());
		Goal := true;
	end if;
	LieType := (CartanName(R))[1];
	LieRank := Rank(R);
	
	zero := ChangeRing(Vector([ 0 : i in [1..LieRank] ]), Rationals());

								    /* LiE Equivalent: */
	ActiveVars := [* zero,			/* lamrho */
			"NOT USED",				/* cur_expon */
			0,					    /* cur_mult */
			zero,					/* goal */
			0,					    /* totmul, stores result in Goal case */
			LieRepresentationDecomposition(R), /* wt_init result, stores result in normal case */
			LieType,				/* lietype */
			LieRank,				/* lierank */
			R *];					/* the_g */

	if (Goal) then
		ActiveVars[4] := nu;
		for i in [1..LieRank] do ActiveVars[4][i] +:= 1; end for;
		weylloop_fn := InternalWeylloopMain_TensorGoal;
	else
		weylloop_fn := InternalWeylloopMain_TensorNormal;
	end if;

	/* Test if lambda > mu, or else fix it */
	deg_lam := Dim_Simple_Irreducible(R, lambda);
	deg_mu := Dim_Simple_Irreducible(R, mu);
	if (deg_lam lt deg_mu) then
		t := mu; mu := lambda; lambda := t;
	end if;

	ActiveVars[1] := lambda;
	for i in [1..LieRank] do ActiveVars[1][i] +:= 1; end for;  

	/* Actual loop */
	chars, mps := DominantCharacter(R, Eltseq(mu));
	InitResult := InternalWeylloopInit( ActiveVars[6] );

	for i in [1..#chars] do
		ActiveVars[3] := mps[i];
		weylloop_fn( ~(ActiveVars[6]), InitResult, ~ActiveVars, chars[i] );
	end for;

	/* Return result */
	if (Goal) then
		return ActiveVars[5];
	else
		return ActiveVars[6];
	end if;
end function;


function Tensor_Irreducible( R, lambda, mu : Goal := false ) //->Tup
	/* Init */
	if (IsIrreducible(R)) then 
		return Tensor_SimpleIrreducible( R, lambda, mu : Goal :=  Goal );
	end if;
	if (Type(Goal) ne BoolElt) then
		nu := Vector(Goal); nu := ChangeRing(nu, Rationals());
		Goal := true;
	end if;
	ssr := Rank(R); dim := Dimension(R); tr := dim-ssr;

	comps, pi := myComponents(R : IncludeToralPart := true);
	lambdapi := PermuteSequence(Eltseq(lambda), pi);
	mupi := PermuteSequence(Eltseq(mu), pi);
	if (Goal) then nupi := PermuteSequence(Eltseq(nu), pi); end if;
	
	/* Toral part */
	if (tr gt 0) then
		if (not(Goal)) then
		    wtsmps := LieRepresentationDecomposition(ToralRootDatum(tr), [ lambdapi[i] + mupi[i] : i in [(ssr+1)..dim] ]);
		else
			correct_weight := forall{i : i in [ssr+1..dim] | (lambdapi[i] + mupi[i] eq nupi[i]) };
			if (correct_weight) then
				goalres := 1;
			else
				return 0;
			end if;
		end if;
	else
	    if (not(Goal)) then
		    wtsmps := LieRepresentationDecomposition(ToralRootDatum(0));
		else
		    goalres := 0;
		end if;
	end if;

	/* Semi simple part(s) */
	pos := ssr;
	for i in [#comps..1 by -1] do
		ssp := comps[i][1];
		if (ssp cmpeq "T") then continue; end if;

		rnk := Rank(ssp); 
		lambda2 := Vector(lambdapi[[(pos-rnk+1)..pos]]);
		mu2 := Vector(mupi[[(pos-rnk+1)..pos]]);
	
		if (Goal) then
			nu2 := Vector(nupi[[(pos-rnk+1)..pos]]);
			goalres *:= Tensor_SimpleIrreducible(ssp, lambda2, mu2 : Goal := nu2);
		else
		    wtsmps := ProductRepresentation(Tensor_SimpleIrreducible(ssp, lambda2, mu2), wtsmps);
		end if;

		pos -:= rnk;
	end for;
	
	/* Return */
	if (Goal) then
		return goalres;
	else
		if (not(IsIdentity(pi))) then
			wtsmps := PermuteWeights(wtsmps, pi^-1, R);
		end if;

		//This is a bit evil, but it's all right. There will only be a very small
		//difference (e.g., in the extraspecial signs) between wtsmps`R and R.
		wtsmps`R := R;	

		return wtsmps;
	end if;
end function;


intrinsic Tensor( D::LieRepDec, E::LieRepDec : Goal := false ) -> .
{ The Tensor product of Lie representation decompositions D and E.
  If Goal is set, only the multiplicity of the module with highest weight
  Goal (i.e. an integer) is returned, otherwise a Lie representation
  decomposition.
}

    require RootDatum(D) eq RootDatum(E) : "RootData must be equal";

    R := RootDatum(D);

	reslt := LieRepresentationDecomposition(R);

	cnt := 0;
	if (Type(Goal) ne BoolElt) then
		nu := ChangeRing(Vector(Goal), Rationals());
		Goal := true;
	end if;

    wtsD, mpsD := Explode(D`WtsMps);
    wtsE, mpsE := Explode(E`WtsMps);
    N1 := #wtsD; N2 := #wtsE;

	for i in [1..N1] do
	    wtD := wtsD[i]; mpD := mpsD[i];
		for j in [1..N2] do
			if (Goal) then
				cnt +:= mpD*mpsE[j]*Tensor( R, wtD, wtsE[j] : Goal := nu);
			else
				wtsmpstmp := Tensor( R, wtD, wtsE[j] );
				AddRepresentation(~reslt, wtsmpstmp, mpD*(mpsE[j]));
			end if;
		end for;
	end for;

	if (Goal) then
		return cnt;
	else
		return reslt;
	end if;
end intrinsic;


intrinsic Tensor( R::RootDtm, v::SeqEnum, w::SeqEnum : Goal := false ) -> LieRepDec
{ Tensor the irreducible modules of R with highest weights v and w. }
	if (Type(Goal) ne BoolElt) then
		require (Type(Goal) eq SeqEnum) : "Goal must be of the same type as lambda and mu";
		return Tensor_Irreducible( R, Vector(v), Vector(w) : Goal := Vector(Goal) );
	else
		return Tensor_Irreducible( R, Vector(v), Vector(w) );
	end if;
end intrinsic;

intrinsic Tensor( R::RootDtm, v::ModTupFldElt, w::ModTupFldElt : Goal := false) -> LieRepDec
{ Tensor the irreducible modules of R with highest weights v and w. }
	return Tensor_Irreducible( R, v, w : Goal := Goal );
end intrinsic;
intrinsic Tensor( R::RootDtm, v::ModTupRngElt, w::ModTupRngElt : Goal := false) -> LieRepDec
{ Tensor the irreducible modules of R with highest weights v and w. }
	v := ChangeRing(v, Rationals());
	w := ChangeRing(w, Rationals());
	if (Type(Goal) eq ModTupRngElt) then Goal := ChangeRing(Goal, Rationals()); end if;
	return Tensor_Irreducible( R, v, w : Goal := Goal );
end intrinsic;



intrinsic TensorPower( D::LieRepDec, n::RngIntElt ) -> LieRepDec
{ The n-th tensor power of the module with decomposition D }
    R := RootDatum(D);
	if (n eq 0) then return LieRepresentationDecomposition(R, [ 0 : i in [1..Dimension(R)] ]); end if;
	if (n eq 1) then return D; end if;

	x := D;
	for i in [2..n] do
		x := Tensor(x, D);
	end for;
	return x;
end intrinsic;

intrinsic TensorPower( R::RootDtm, n::RngIntElt, v::SeqEnum ) -> LieRepDec
{ The n-th tensor power of the R-module with highest weight v }
	return TensorPower( LieRepresentationDecomposition(R, v), n );
end intrinsic;
intrinsic TensorPower( R::RootDtm, n::RngIntElt, v::ModTupRngElt ) -> LieRepDec
{ The n-th tensor power of the R-module with highest weight v }
	return TensorPower( LieRepresentationDecomposition(R, v), n );
end intrinsic;



