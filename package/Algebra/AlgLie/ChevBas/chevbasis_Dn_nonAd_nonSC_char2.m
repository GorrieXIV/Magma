freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../quo_with_pullback.m":quo_with_pullback;
import "../derlie.m":ExtendHInDerL;
import "../diagram_auts.m":dn_diagram_auts, extend_root_automorphism;
import "../stsa.m":DR_IsSTSA;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":findeigenspc_notinH, ismultof, compute_basis_by_simp_es, pullback, mult_dim_eigenspc, recompute_eigenvectors;
import "identify_roots.m":compute_idrts, check_indrts;
import "findframemain.m":verify_straight, insert_found_frame, findframe_all_pairs;
import "findframe.m":findframe;
import "diag.m":simdiag;

should_use_chevbasis_Dn_nonAd_nonSC_4s_char2 := function(CBD)
	assert CartanName(CBD`R)[1] eq "D";
	if IsAdjoint(CBD`R) then return false; end if;
	if IsSimplyConnected(CBD`R) then return false; end if;

	findeigenspc_notinH(~CBD);
	return SequenceToSet([ #d : d in mult_dim_eigenspc(CBD)]) eq {4};
end function;

should_use_chevbasis_Dn_nonAd_nonSC_2s_char2 := function(CBD)
	//For now, we use this only for even n.
	assert CartanName(CBD`R)[1] eq "D";
	if IsAdjoint(CBD`R) then return false; end if;
	if IsSimplyConnected(CBD`R) then return false; end if;

	if (Rank(CBD`R) lt 6) or (IsOdd(Rank(CBD`R))) then return false; end if;

	findeigenspc_notinH(~CBD);
	return SequenceToSet([ #d : d in mult_dim_eigenspc(CBD)]) eq {2};
end function;

find_H_for_Cn_DerDn_int := function(DerL, HinDerL, RnkR, CSDerL)
	local c, M, MinDerL, DerL15, DerL15H,
		S, CSdims, DerL_to_S, S_to_DerL,
		willfinddim, DerL16, DSD, BaseL, x, ns;

	CSdims := [ Dimension(d) : d in CSDerL ];
	if IsEven(RnkR) then
		assert CSdims eq [(2*(RnkR^2)-RnkR-2)..(2*(RnkR^2)+RnkR)];
		BaseL := CSDerL[2];
	else
		assert CSdims eq [(2*(RnkR^2)-RnkR-1)..(2*(RnkR^2)+RnkR)];
		BaseL := CSDerL[1];
	end if;

	S, DerL_to_S, _, S_to_DerL := quo_with_pullback(CSDerL[#CSDerL], BaseL);

	M := Centraliser(S, Random(S));
	if Dimension(M) ne 1 then return false,_; end if;

	MinDerL := S_to_DerL(S!Basis(M)[1]);
	DerL28 := sub<DerL | BaseL, HinDerL, MinDerL>;
	DerL28H := Centraliser(DerL28, HinDerL) meet MinDerL;
	assert Dimension(DerL28) eq 2*(RnkR^2)-RnkR;
	assert Dimension(DerL28H) eq RnkR;

	if not DR_IsSTSA(DerL28, DerL28H) then 
		return false,_; 
	end if;

	return DerL28, DerL28H;
end function;

pullback_Ad_to_int := procedure(~CBD, CBDAd, pi)
	local fromR, imgs_of_simple_rts, RtoR, indrtsorig;

	//On the pullback, we need to take into account the diagram auts. of D4.
	fromR := CBDAd`R;
	imgs_of_simple_rts := [1..Rank(fromR)];
	RtoR := function(k)
		local v, w;

		v := Eltseq(Root(fromR, k : Basis := "Root"));
		v := PermuteSequence(v, pi);
		w := &+[ Root(CBD`R,imgs_of_simple_rts[i])*v[i] : i in [1..Rank(fromR)] ];
		return RootPosition(CBD`R,w);
	end function;

	CBD`IndRts := [ CBDAd`IndRts[RtoR(i)] : i in [1..2*NumPosRoots(fromR)] ];

	try
		compute_basis_by_simp_es(~CBD);
		return;
	catch e
		CBD`IndRts := [];
	end try;
end procedure;

chevbasis_Dn_nonAd_nonSC_4s_char2 := procedure(~CBD)
	local R, L, H, LL, LLmaps, 
		VSfull, VEigenSpc, centrelt,
		LCnAd, CSLCnAd, HinLCnAd, pi, RnkR, DnAd, DnAdH;

	//we use Der(L), which is CnAd, therefore contains DnAd, to find the frame.
	// well, a little centre comes along, so we fix that.
	R := CBD`R;
	L := CBD`L;
	H := CBD`H;
	RnkR := Rank(R);
	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	centrelt := L!(Basis(Centre(L))[1]);

	LL,LLmaps := ExtendHInDerL(L, H);
	vprintf ChevBas, 2: "[chevbasis_Dn_nonAd_nonSC_char2] Computing DirectSumDecomposition(DerL)\n";
	DSD := DirectSumDecomposition(LL);
	DSDdims := [ Dimension(d) : d in DSD ];
	assert SequenceToSet(DSDdims) eq {2*(RnkR^2) + RnkR,1};

	LCnAd := DSD[ Position(DSDdims,2*(RnkR^2) + RnkR) ];
	HinLCnAd := LCnAd meet sub<LL | [ (LLmaps`mp_L_to_LL)(L!b) : b in Basis(H) ]>;

	CSLCnAd := CompositionSeries(LCnAd);
	while true do
		vprintf ChevBas, 4: ".";
		DnAd, DnAdH := find_H_for_Cn_DerDn_int(LCnAd, HinLCnAd, RnkR, CSLCnAd);

		if DnAd cmpeq false then continue; end if;

		RDnAd := RootDatum("D" cat IntegerToString(RnkR) : Isogeny := "Ad");
		CBDAd := NewChevBasData(RDnAd, DnAd, DnAdH);
		try
			findframe(~CBDAd);
			ok := verify_straight(CBDAd);
		catch e
			ok := false;
		end try;
		
		if ok then break; end if;
	end while;

	//Pull back.
	findeigenspc_notinH(~CBD);
	VEigenSpc := sub<VSfull | [ Vector(e) : e in CBD`EigenSpaces ]>;
	CBD`SCSAVectors := [ L!b : b in Basis(H) ];
	CBD`EigenSpaces := [];
	for e in CBDAd`EigenSpaces do
		V := sub<VSfull | [ Vector((LLmaps`mp_LL_to_L)(LL!e)), Vector(centrelt) ]>
			meet VEigenSpc;
		assert Dimension(V) eq 1;
		Append(~(CBD`EigenSpaces), L!(Basis(V)[1]));
	end for;
	recompute_eigenvectors(~CBD);
	CBD`PosNegPairs := CBDAd`PosNegPairs;
	compute_idrts(~CBDAd);

	//Pull back needs to take into account the diagram auts...
	for pi in dn_diagram_auts(RnkR) do
		pullback_Ad_to_int(~CBD, CBDAd, pi);
		if CBD`IndRts cmpne [] then
			//It worked out!
			return;
		end if;
	end for;

	error "Could not pull back from adjoint Dn to int. Dn";
end procedure;


chevbasis_Dn_nonAd_nonSC_2s_char2 := procedure(~CBD)
	local n, pi;

	findeigenspc_notinH(~CBD);
	findframe(~CBD);
	compute_idrts(~CBD);

	try
		compute_basis_by_simp_es(~CBD);
		ok := true;
	catch e
		vprintf ChevBas, 2: "[chevbasis_Dn_nonAd_nonSC_2s_char2] Failed, trying diagram automorphism...\n";
		ok := false;
	end try;

	if not ok then
		n := Rank(CBD`R);
		pi := extend_root_automorphism(CBD`R, Sym(n)!(n-1,n));
		CBD`IndRts := PermuteSequence(CBD`IndRts, pi);
		compute_basis_by_simp_es(~CBD);
	end if;		

end procedure;
