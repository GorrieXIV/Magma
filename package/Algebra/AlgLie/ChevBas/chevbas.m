freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":findeigenspc_notinH, compute_basis_by_simp_es, fix_chevbas_scalars;
import "identify_roots.m":compute_idrts, check_indrts;
import "distort.m":ChangeBasisLie_SparseWrtH, ChangeBasisLie_CBD;
import "../stsa.m":DR_IsSTSA;

//Special char. 3 procedures
import "chevbasis_A2SC_char3.m":chevbasis_A2SC_char3;
import "chevbasis_G2_char3.m":chevbasis_G2_char3;

//Special char. 2 procedures
import "findframe.m":findframe;
import "chevbasis_A1_char2.m":chevbasis_A1_char2;
import "chevbasis_B2SC_char2.m":chevbasis_B2SC_char2;
import "chevbasis_Bn_char2.m":chevbasis_Bn_char2;
import "chevbasis_Cn_char2.m":chevbasis_Cn_char2;
import "chevbasis_Dn_nonAd_nonSC_char2.m":chevbasis_Dn_nonAd_nonSC_4s_char2, should_use_chevbasis_Dn_nonAd_nonSC_4s_char2, chevbasis_Dn_nonAd_nonSC_2s_char2, should_use_chevbasis_Dn_nonAd_nonSC_2s_char2;
import "chevbasis_F4_char2.m":chevbasis_F4_char2;
import "chevbasis_G2_char2.m":chevbasis_G2_char2;

/*
Is it a good idea to precompute a new Lie algebra to multiply in?
The trade-off here is the time it would take to compute the new Lie
multiplication table VS the speedup you get by multiplying in this
more suitable Lie algebra instead of in the "old" L. The function 
below (based on heuristics) could say something about this trade off.
*/
function should_change_basis(F)
	return (Characteristic(F) in {2,3});
end function;

//The real stuff below...
intrinsic ChevalleyBasis(L::AlgLie, H::AlgLie, R::RootDtm :
		CheckSTSA := true,
		CheckResult := true,
		ExtraspecialSigns := false,
		PermuteRoots := false,
		ChangeToSparserBasis := "Auto"		
) -> SeqEnum, SeqEnum, SeqEnum, Rec
{Compute Chevalley basis for L wrt root datum R and Cartan subalgebra H}

	local ok, tp, rnk, char, CBD, Lnw, Hnw, TrMat, changed_basis;
	
	
	/* Cached? (i.e., sometimes it works for non-irreducible root data, too!)*/
	if assigned L`ChevalleyBasis then
		cc := L`ChevalleyBasis;
		if sub<L | cc[3]> eq H then
			ok, p,n,c, CBD := fix_chevbas_scalars(L, R, cc[1], cc[2], cc[3]);
			if ok then return p,n,c,CBD; end if;
		end if;
	end if;

	/* Do things! */
	if not IsIrreducible(R) then
		error "ChevalleyBasis(L,H,R) only works for irreducible root data";
	end if;
	if CheckSTSA and not DR_IsSTSA(L,H) then
		error "H is not a split toral subalgebra of L";
	end if;
	
	if (ChangeToSparserBasis cmpeq true) or
		((ChangeToSparserBasis cmpeq "Auto") and should_change_basis(BaseRing(L))) 
	then
		L2, H2, TrMat := ChangeBasisLie_SparseWrtH(L,H);
		changed_basis := not IsIdentity(TrMat);
	else
		changed_basis := false;
	end if;

	if changed_basis then CBD := NewChevBasData(R,L2,H2);
	else                  CBD := NewChevBasData(R,L,H);
	end if;
	if ExtraspecialSigns cmpne false then
		CBD`ExtraspecialSigns := ExtraspecialSigns;
	end if;

	tp := CartanName(R)[1];
	rnk := Rank(R);
	char := Characteristic(BaseRing(CBD`L));

	/* EXCEPTIONS: CHARACTERISTIC 2 */
 	if char eq 2 then
		if tp in {"A","D"} and rnk eq 1 then
			chevbasis_A1_char2(~CBD);
		elif tp eq "B" and rnk eq 2 and IsSimplyConnected(R) then
			chevbasis_B2SC_char2(~CBD);
		elif tp eq "B" then
			chevbasis_Bn_char2(~CBD);
		elif tp eq "C" then
			chevbasis_Cn_char2(~CBD);
		elif tp eq "D" and should_use_chevbasis_Dn_nonAd_nonSC_4s_char2(CBD) then
			chevbasis_Dn_nonAd_nonSC_4s_char2(~CBD);
		elif tp eq "D" and should_use_chevbasis_Dn_nonAd_nonSC_2s_char2(CBD) then
			chevbasis_Dn_nonAd_nonSC_2s_char2(~CBD);
		elif tp eq "F" then
			chevbasis_F4_char2(~CBD);
		elif tp eq "G" then
			chevbasis_G2_char2(~CBD);
		else
			findeigenspc_notinH(~CBD);
			findframe(~CBD);
		end if;
	end if;

	/* EXCEPTIONS: CHARACTERISTIC 3 */
	if char eq 3 then
		if tp eq "G" and rnk eq 2 then
			chevbasis_G2_char3(~CBD);
		elif tp eq "A" and rnk eq 2 and IsSimplyConnected(R) then
			chevbasis_A2SC_char3(~CBD);
		else
			findeigenspc_notinH(~CBD);
		end if;
	end if;

	/* NORMAL CASE */
	//Some of the exceptions above solve the CB completely; otherwise:
	if not assigned CBD`BasisPos then
		if char notin {2,3} then
			findeigenspc_notinH(~CBD);
		end if;

		compute_idrts(~CBD : PermuteRoots := PermuteRoots);
		compute_basis_by_simp_es(~CBD);
	end if;

	//If we changed the basis earlier, we should change back:
	if changed_basis then
		ChangeBasisLie_CBD(~CBD, TrMat^(-1) : RefOldL := L, RefOldH := H);
	end if;
	
	//Sometimes it looks like a Chevalley basis, but it didn't end up being one,
	//e.g. sometimes if the isogeny type is wrong.
	if CheckResult and not IsChevalleyBasis(CBD) then 
		error "Could not construct Chevalley basis: Verification failed. (Wrong isogeny type?)";
	end if;
	
	L`RootDatum := R;
	
	if not assigned L`ChevalleyBasis then
		L`ChevalleyBasis := [* CBD`BasisPos, CBD`BasisNeg, CBD`BasisCart *];
	end if;

	return CBD`BasisPos, CBD`BasisNeg, CBD`BasisCart, CBD;
end intrinsic;






