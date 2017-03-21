freeze;

/* 
 * Dan Roozemond, 2010. 
 */

/* Identification of the simple type of a Lie algebra L, 
   given only L and a splitting Cartan subalgebra H.
   (and the assumption that L is the Lie algebra of
   a simple algebraic group)
*/

import "chevbasdata.m":NewChevBasData;
import "identify.m":nice_fullname_irred_rootdtm;

cands_bydim := function(dim, rnk)
	local r;
	r := [];

	if dim eq (rnk+1)^2-1 then Append(~r, "A"); end if;
	if rnk ge 2 and dim eq 2*rnk^2+rnk then Append(~r, "B"); end if;
	if rnk ge 3 and dim eq 2*rnk^2+rnk then Append(~r, "C"); end if;
	if rnk ge 4 and dim eq 2*rnk^2-rnk then Append(~r, "D"); end if;

	if rnk eq 6 and dim eq 78 then Append(~r, "E"); end if;
	if rnk eq 7 and dim eq 133 then Append(~r, "E"); end if;
	if rnk eq 8 and dim eq 248 then Append(~r, "E"); end if;
	if rnk eq 4 and dim eq 52 then Append(~r, "F"); end if;
	if rnk eq 2 and dim eq 14 then Append(~r, "G"); end if;

	return [ t cat IntegerToString(rnk) : t in r ];
end function;

test_by_rootdtms := function(L,H, candsR  : Select := "All")
	//First return value is appropriate sequence of records;
	//Second return value is time of first hit.
	local CBD, ok, ret, RF, tfirst;

	assert Select in {"All", "CartanType", "First"};
	RF := recformat< str : MonStgElt, R : RootDtm, ChevBasData: Rec >;
	ret := [];
	foundCTs := {};
	tfirst := false;

	for R in candsR do
	 	if Select eq "CartanType" and CartanName(R) in foundCTs then
			vprintf ChevBas, 2: "[ILSG] Skipping %o...\n", nice_fullname_irred_rootdtm(R);
			continue;
		end if;
		
		vprintf ChevBas, 2: "[ILSG] Guessing %o...\n", nice_fullname_irred_rootdtm(R);
		
		ok := false;
		try
			_,_,_,CBD := ChevalleyBasis(L, H, R);
			Append(~ret, rec<RF | 
				str := Sprintf("Lie algebra of type %o", nice_fullname_irred_rootdtm(R)),
				ChevBasData := CBD,
				R := R
			>);
			Include(~foundCTs, CartanName(R));
			if tfirst cmpeq false then tfirst := Cputime(); end if;
			ok := true;
		catch e
			if GetVerbose("ChevBas") ge 2 then
				"[ILSG] That failed because of an error"; IndentPush(); e; IndentPop();
			end if;
			ok := false;
		end try;
		
		if ok and Select eq "First" then break; end if;
	end for;

	return ret, tfirst;
end function;

all_isogs := function(tp : chrfield := false)
	local fg, r, dc, s, inj;

	dc := Determinant(CartanMatrix(tp));

	//The adjoint isogeny, always exists
	r := [ RootDatum(tp : Isogeny := "Ad") ];

	/* 
     * If the determinant of the cartan matrix is not
	 * equal to 1, the Simply Connected isogeny is
	 * different from the Adjoint isogeny, but only if
	 * chrfield does not divide dc.
     */
	if (dc ne 1) and ((chrfield cmpeq false) or GCD(dc, chrfield) ne 1) then
		Append(~r, RootDatum(tp : Isogeny := "SC"));
	end if;

	/*
     * If the determinant of the cartan matrix is not
     * prime, there are "intermediate" isogenies. These
     * can be obtained using the subgroups of the 
     * fundamental group of the root dtm.
     */
	fg := FundamentalGroup(tp);
	for s in Subgroups(fg) do
		//Subgroup of order 1 is the adjoint variant;
		//Subgroup of full order 1 is the simply connected variant;
		//We already constructed those above
		if s`order eq 1 or s`order eq dc then continue; end if;

		//If s`order is coprime with chrfield the Lie algebra from
		// s is isomorphic to that from the adjoint isogeny.
		if (chrfield cmpne false) and GCD(s`order, chrfield) eq 1 then continue; end if;

		_,inj := sub<fg | s`subgroup>;
		Append(~r, RootDatum(tp : Isogeny := inj));
	end for;

	return r;
end function;

identify_liealgebra_of_simple_group_LeqH := function(L)
	local i, R, CBD;

	i := Dimension(L);
	R := RootDatum("T" cat IntegerToString(i));
	CBD := NewChevBasData(R, L, L);
	CBD`BasisPos := [ L | ];
	CBD`BasisNeg := [ L | ];
	CBD`BasisCart := [ L | b : b in Basis(L) ];

	return CBD;
end function;

function identify_liealgebra_of_simple_group(L, H : Select := "All", hintR := false) //-> SeqEnum, FldReElt
/* Use chevbasis to identify the Lie algebra of a simple algebraic group.

Select can be "All" (returns all hits), "CartanType" (return only one hit for each Cartan type), 
  or "First" (return as soon as the first hit is found).

 Returns a sequence Q of hits, each element q of Q is a record:
 - q`R    : The corresponding root datum
 - q`str  : A string describing the hit
 - q`CBD  : The ChevBasData object that is the proof

Second return value is the Cputime() of the first hit.
*/
	local cands, ret, candsR, retCBD, tfirst;
	
	//If hintR is set and it is twisted, we ignore
	if (hintR cmpne false)  and IsTwisted(hintR) then 
		vprintf ChevBas, 2: "[ILSG] hintR is twisted. Returning.\n";
		return [], _; 
	end if;

	//Exclude toral case
	if L eq H then
		retCBD := identify_liealgebra_of_simple_group_LeqH(L);
		return [ rec< recformat< str : MonStgElt, R : RootDtm, ChevBasData: Rec > | 
			str := Sprintf("Abelian Lie algebra of dimension %o", Dimension(L)),
			ChevBasData := retCBD,
			R := retCBD`R
		>], Cputime();
	end if;
	
	//Get possible candidates by the dimension
	if hintR cmpeq false then
		cands := cands_bydim(Dimension(L), Dimension(H));
		vprintf ChevBas, 2: "[ILSG]: cands_bydim: %o\n", cands; 
		candsR := &cat[ all_isogs(c) : c in cands ];
	else
		assert ISA(Type(hintR), RootDtm);
		assert IsIrreducible(hintR);
		candsR := [ hintR ];
	end if;
	vprintf ChevBas, 2: "[ILSG]: candsR: %o\n", candsR; 

	//Just try.
	Q, tfirst := test_by_rootdtms(L,H,candsR : Select := Select);

	//Done.
	return Q, tfirst;
end function;

