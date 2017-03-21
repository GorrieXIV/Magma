freeze;

/* By Dan */
import "RootDatumDan.m": myComponents;

/*********
 ********* Virtual Decomposition
 *********/

/* ActiveVars for VirtualDecomposition
    1. Rho
*/

function VirtualDecomposition_Simple_Irreducible( R, lambda ) //->LieRepDec
    D := LieRepresentationDecomposition(R);
	ActiveVars := [* ChangeRing(Vector([1 : i in [1..Rank(R)] ]), Rationals()) *];

	InitResult := InternalWeylloopInit(D);
	InternalWeylloopMain_Decomp( ~D, InitResult, ~ActiveVars, lambda );

	return D;
end function;

function VirtualDecomposition_Irreducible( R, lambda ) //-> LieRepDec
	ssr := Rank(R); r := Dimension(R); tr := r-ssr;

	comps, pi := myComponents(R);
	lambdapi := PermuteSequence(Eltseq(lambda), pi);

	/* Toral Part */
	if (tr gt 0) then
		wtsmps := LieRepresentationDecomposition(ToralRootDatum(tr), lambdapi[[(ssr+1)..r]]);
	else
		wtsmps := LieRepresentationDecomposition(ToralRootDatum(0));
	end if;

	/* Semi simple part(s) */
	pos := ssr;
	for i in [#comps..1 by -1] do
		if (Type(comps[i][1]) eq MonStgElt and comps[i][1] eq "T") then continue; end if;
		rnk := #(comps[i][2]);
		lambda2 := Vector([ lambdapi[i] : i in [(pos-rnk+1)..pos] ]);

		t := VirtualDecomposition_Simple_Irreducible(comps[i][1], lambda2);
		wtsmps := t*wtsmps;

		pos -:= rnk;
	end for;
  
	if (not(IsIdentity(pi))) then
	    wtsmps := PermuteWeights(wtsmps, pi^-1, R);
	end if;

	//This is a bit evil, but it's all right. There will only be a very small
	//difference (e.g., in the extraspecial signs) between wtsmps`R and R.
	wtsmps`R := R;

	return wtsmps;
end function;

intrinsic VirtualDecomposition( R::RootDtm, v ) -> LieRepDec
{ Decompose Character for virtual modules, i.e. no error is raised if
  v is a non-virtual module. }
	return VirtualDecomposition_Irreducible( R, ChangeRing(Vector(v), Rationals())  );
end intrinsic;

intrinsic VirtualDecomposition( D::LieRepDec ) -> LieRepDec
{ Decompose Character for virtual modules, i.e. no error is raised if
  D is a non-virtual module. }
    R := RootDatum(D);
	res := LieRepresentationDecomposition(R);
	Wts, Mps := Explode(D`WtsMps); N := #Wts;
	
	for i in [1..N] do
		wtsmpstmp := VirtualDecomposition_Irreducible( R, Wts[i] );
		AddRepresentation(~res, wtsmpstmp, Mps[i]);
	end for;

	return res;
end intrinsic;


/*********
 ********* Decomposition
 *********/
intrinsic DecomposeCharacter( D::LieRepDec ) -> LieRepDec
{ The decomposition polynomial of the module with dominant character polynomial D. 
  An error is raised if $D$ is non-virtual, i.e. if dominant weights occur with negative multiplicities.
  This is the inverse of DominantCharacter.
 }

    R := RootDatum(D);
	LieRank := Dimension(R);
	Ssrank := Rank(R);
	reslt := LieRepresentationDecomposition(R);
	
	cnt := 0;
	while (#D gt 0) do
		/* find index of maximum weight among wts*/
	    mxm, c := Explode(InternalMaximalWeightDHO(D));

        cnt +:= 1;

		/* Check if we're still non-virtual */
		if (c lt 0) then
    	    error "Non-virtual decomposition failed.";
		end if;

		/* insert weight into result */
		AddRepresentation(~reslt, mxm, c);

		/* update wtsmps (i.e. what is todo) */
		todo := DominantCharacter(LieRepresentationDecomposition(R, mxm));
        AddRepresentation(~D, todo, -c);
	end while;
	
	return reslt;
end intrinsic;

		