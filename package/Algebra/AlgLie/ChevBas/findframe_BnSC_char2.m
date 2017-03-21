freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../derlie.m":ExtendHInDerL;
import "diag.m":simdiag;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":mult_dim_eigenspc, findeigenspc_notinH, ismultof;
import "findframemain.m":findframe_all_pairs, verify_straight;

//Obs: The fours are Lie algebras of type A1 A1. Should be able to use that.
split_four_by_dsd := procedure(~CBD, d, centralelt)
	local L, H, Lfour, VSfull, Vfour, Vfourplus, DSD, DSDvs, newes, i, z;

	L := CBD`L; H := CBD`H; 
	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	Vfour := sub<VSfull | [ Vector(CBD`EigenSpaces[i]) : i in d ]>;
	Vfourplus  := sub<VSfull | [ Vector(CBD`EigenSpaces[i]) : i in d ] cat [ Vector(centralelt) ]>;
	Lfour := sub<L | [ L!b : b in Basis(Vfour) ]>;
	DSD := DirectSumDecomposition(Lfour);
	assert [ Dimension(M) : M in DSD ] eq [3,3];

	DSDvs := [ sub<VSfull | [ Vector(L!b) : b in Basis(M) ]> : M in DSD ];

	assert [ Dimension(V meet Vfourplus) : V in DSDvs ] eq [ 2, 2 ];
	newes := &cat[ Basis(V meet Vfourplus) : V in DSDvs ];

	//Take out the center in the following manner:
	for i in [1..4] do
		M := sub<VSfull | [ Vector(L!(newes[i])*L!h) : h in Basis(H) ]>;
		assert Dimension(M) eq 1;
		(CBD`EigenSpaces)[d[i]] := Basis(M)[1];
	end for;
	Include(~(CBD`PosNegPairs), { d[1], d[2] });
	Include(~(CBD`PosNegPairs), { d[3], d[4] });
end procedure;

findframe_A1_by_straight_A1 := procedure(~CBD, d2, pivot)
	local A, L, M, pivotelts, LHS, ns, d2ok;

	pivotelts := [ CBD`EigenSpaces[p] : p in pivot ];

	d2ok := [];
	L := CBD`L;
	A := sub<VectorSpace(BaseRing(L), Dimension(L))
		 | [ Vector(CBD`EigenSpaces[i]) : i in d2 ]>;
	for i in [1..2] do
		LHS := VerticalJoin([ Vector(L!b*L!pivotelts[i]) : b in Basis(A) ]);
		ns := Nullspace(LHS);
		assert Dimension(ns) eq 1;
		Append(~d2ok, L!(&+[ (Basis(ns)[1])[j]*(Basis(A)[j]) : j in [1..2] ]));
	end for;

	CBD`EigenSpaces[d2[1]] := d2ok[1];
	CBD`EigenSpaces[d2[2]] := d2ok[2];
end procedure;

findframe_BnSC_char2 := procedure(~CBD)
	local L, H, F, LL, LLMaps, HH, HinLL, z, VSfull,
		mats, es, ev, nonz, dup, dup4, dup2, d2, pp, M, p; 

	/* Use the fact that Der(BnSC) = Bn Ad. */

	L := CBD`L;
	F := CBD`F;
	H := CBD`H;
	VSfull := VectorSpace(BaseRing(L), Dimension(L));

	LL, LLMaps := ExtendHInDerL(L, H);
	HH := sub<LL | [ (LLMaps`mp_L_to_LL)(L!b) : b in Basis(H) ]>;
	HinLL := Centraliser(LL,HH);
	mats := [ (LLMaps`mp_LL_to_mats)(LL!x) : x in Basis(HinLL) ];
	es, ev := simdiag(mats);

	nonz := [ i : i in [1..#ev] | not IsZero(Vector(ev[i])) ];
	CBD`EigenVectors := &cat[ [ Vector(ev[i]) : j in [1..Dimension(es[i])] ] : i in nonz ];
	CBD`EigenSpaces := &cat[ Basis(es[i]) : i in nonz ];
	ChangeUniverse(~(CBD`EigenSpaces), L);

	//The newly found pairs, i.e. the two-spaces, cannot be trusted because they 
	//  may multiply incorrectly into the centre...
	//So first split the 4s using DirectSumDecomposition, then straighten those,
	//  then use those straight pairs to straighten the newly found pairs.
	dup := mult_dim_eigenspc(CBD);
	dup4 := [ d : d in dup | #d eq 4 ];
	dup2 := [ d : d in dup | #d eq 2 ];

	//Split the fours
	CBD`PosNegPairs := {};
	z := L!(Basis(Centre(L))[1]);
	for d in dup4 do
		split_four_by_dsd(~CBD, d, z);
	end for;
	findframe_all_pairs(~CBD);

	//Use the split fours to split the A1s
	for d2 in dup2 do
		pp := false;
		for p in CBD`PosNegPairs do
			M := [ Vector(L!CBD`EigenSpaces[i1]*L!CBD`EigenSpaces[i2]) : i1 in d2, i2 in p ];

			if forall{k : k in M | IsZero(k)} then continue; end if;

			pp := p;
			break;
		end for;

		if pp cmpeq false then 
			error "[findframe_B3SC_char2] Could not find pivot pair.";
		end if;

		findframe_A1_by_straight_A1(~CBD, d2, pp);
	end for;

	CBD`PosNegPairs join:= { SequenceToSet(d) : d in dup2 };
end procedure;
