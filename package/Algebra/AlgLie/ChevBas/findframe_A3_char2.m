freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../quo_with_pullback.m":quo_with_pullback;
import "../derlie.m":ExtendHInDerL;
import "../stsa.m":DR_IsSTSA;
import "chevbasmain.m":findeigenspcLH;
import "diag.m":simdiag;
import "findframemain.m":insert_found_frame, findframe_all_pairs, verify_straight;

find_A3_inside_LLC3 := function(LL, HinLL)
	local L21, HinL21, DSD, DSDdims, CS,
		S, L21_to_S, S_to_L21,
		MinL21, HinMinL21;

	//Works as well if LL = C3 + 1:
	if Dimension(LL) eq 21 then
		L21 := LL;
	elif Dimension(LL) eq 22 then
		DSD := DirectSumDecomposition(LL);
		DSDdims := [ Dimension(d) : d in DSD ];
		assert SequenceToSet(DSDdims) eq {1,21};
		L21 := DSD[ Position(DSDdims, 21) ];
	else
		error Sprintf("find_A3_inside_LLC3: Dim(LL) = %o. Cannot handle.", Dimension(LL));
	end if;
	HinL21 := L21 meet HinLL;
	
	CS := CompositionSeries(L21);
	assert [ Dimension(d) : d in CS ] eq [14..21];
	S, L21_to_S, _, S_to_L21 := quo_with_pullback(L21, CS[1]);
	assert Dimension(S) eq 7;

	while true do
		vprintf ChevBas, 4: ".";

		M := Centraliser(S, Random(S));
		if Dimension(M) ne 1 then continue; end if;

		MinL21 := S_to_L21(S!Basis(M)[1]);
		if Dimension(MinL21) ne 15 then continue; end if;

		HinMinL21 := MinL21 meet Centraliser(L21, HinL21);
		if Dimension(HinMinL21) ne 3 then continue; end if;

		if not DR_IsSTSA(MinL21, HinMinL21) then continue; end if;

		break;
	end while;

	return MinL21, HinMinL21;
end function;

compseries_complements := function(L, CSL)
	local i, vswb1, vswb2, r;
	
	r := [* *];
	for i in [2..#CSL] do
		vswb1 := VectorSpaceWithBasis([ Vector(L!b) : b in Basis(CSL[i-1]) ]);
		vswb2 := VectorSpaceWithBasis([ Vector(L!b) : b in Basis(CSL[i]) ]);
		Append(~r, Basis(Complement(vswb2, vswb1)));
	end for;

	return r;
end function;

find_goodL15_nonAdnonSC := function(L, H)
	local LL, LLmaps, HinLL, LL15, LL15H, es, ev, backtoL;

	LL, LLmaps := ExtendHInDerL(L,H);
	HinLL := sub<LL | [ (LLmaps`mp_L_to_LL)(L!b) : b in Basis(H) ]>;

	while true do
		vprintf ChevBas, 4: "+";

		LL15, LL15H := find_A3_inside_LLC3(LL, HinLL);

		es, ev := findeigenspcLH(LL15, LL15H);
		if #ev ne 15 then continue; end if;

		break;
	end while;

	backtoL := 	func<x | L!((LLmaps`mp_LL_to_L)(LL!(LL15!x)))>;
	return es, ev, backtoL;
end function;

find_goodL15_SC := function(L,H)
	local LL, LLmaps, HinLL, HH,
		es, ev, backtoL;

	LL, LLmaps := ExtendHInDerL(L,H);
	HinLL := sub<LL | [ LL!((LLmaps`mp_L_to_LL)(L!b)) : b in Basis(H) ]>;
	HH := Centraliser(LL,HinLL);

	assert Dimension(LL) eq 15 and Dimension(HH) eq 3;

	es,ev := findeigenspcLH(LL, HH);
	assert #es eq 15;

	backtoL := func<x | L!((LLmaps`mp_LL_to_L)(LL!x))>;

	return es, ev, backtoL;
end function;

pullback_A3Ad_to_orig := procedure(es, ev, backtoL, ~CBD)
	local zr, dubs, esvs, z, L;

	L := CBD`L;

	//Clean the returned vectors; make them into vectorspaces...
	zr := [ i : i in [1..#ev] | IsZero(ev[i]) ];
	es := [ es[i] : i in [1..#es] | i notin zr ];
	ev := [ ev[i] : i in [1..#ev] | i notin zr ];
	dubs := { { i : i in [1..#ev] | ev[i] eq ev[j] } : j in [1..#ev] };
	dubs := [ SetToSequence(d) : d in dubs ];
	esvs := [ VectorSpaceWithBasis([ Vector(e) : e in es[d] ]) : d in dubs] ;

	//Check
	if { Dimension(V) : V in esvs } ne {2} then
		error "A_3(2): Unexpected form of diagonal action in Der(A_3(2)) (1)";
	end if;

	//Pull back these spaces to A3, and insert them into the CBD
	//Note that on the pullback, we may inadvertedly add a bit of
	//  centre into the eigenspaces.
	z := L!(Basis(Centre(L))[1]);
	BasisH := [ h : h in CBD`SCSAVectors ];

	pullback := function(espc)
		local y, vswb, LHS, Ms, es, ev, dims, p;

		vswb := VectorSpaceWithBasis(
			[ Vector(backtoL(e)) : e in Basis(espc) ]
			cat [ Vector(z) ]);
		Ms := [ Matrix([ Coordinates(vswb, Vector(L!b*L!h)) : b in Basis(vswb) ])
			: h in BasisH ];
		es,ev := simdiag(Ms);

		dims := [ Dimension(e) : e in es ];
		if Seqset(dims) ne {1,2} then 
			error "Could not pullback from Der(A3) to A3.";
		end if;
		p := Position(dims,2);
		
		return [ Vector(b*Matrix(Basis(vswb))) : b in Basis(es[p]) ];
	end function;

	newspcs := [ pullback(e) : e in esvs ];
	insert_found_frame(~CBD, &cat(newspcs), false);
end procedure;

findframe_A3_nonAd_char2_usingDerL := procedure(~CBD)
	local F,L, H, es, ev, backtoL, ok;
	
	L := CBD`L;
	H := CBD`H;
	F := CBD`F;

	while true do
		if IsSimplyConnected(CBD`R) then
			es, ev, backtoL := find_goodL15_SC(L,H);
		elif not IsAdjoint(CBD`R) then
			es, ev, backtoL := find_goodL15_nonAdnonSC(L, H);
		else
			error "findframe_A3nonAd_usingDerL, on not SC, not int.";
		end if;

		//We may, accidentally, run into a CSA that LOOKS like a CSA 
		//  but not actually is one.
		//But, if we try sufficiently often, we run into the right one.
		pullback_A3Ad_to_orig(es, ev, backtoL, ~CBD);

		try
			findframe_all_pairs(~CBD);
			ok := verify_straight(CBD); 
			//^^ we need to do this because we might (have) run into a wrong torus.
		catch e
			ok := false;
		end try;

		if ok then break; end if;
	end while;

end procedure;

