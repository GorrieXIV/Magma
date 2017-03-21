freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../derlie.m":ExtendHInDerL;
import "../stsa.m":DR_IsSTSA;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":findeigenspc_notinH, mult_dim_eigenspc;
import "findframemain.m":findframe_all_pairs, insert_found_frame, verify_straight;
import "diag.m":simdiag;

findframe_Dn_SC_char2 := procedure(~CBD)
	//We use the fact that Der(Dn_SC) = Dn_Ad.
	
	local L, H, rnk, LL, LLmaps, S, HH,
		mats, es, ev, nonz;

	L := CBD`L;
	H := CBD`H;
	rnk := Rank(CBD`R);

	//Construct Der(L), which is supposed to be adjoint Dn, and
	//   construct a splitting cartan subalgebra for that
	LL, LLmaps := ExtendHInDerL(L,H);

	S := sub<LL | [ (LLmaps`mp_L_to_LL)(L!h) : h in Basis(H) ]>;
	HH := Centraliser(LL,S);

	if Dimension(HH) ne rnk or not DR_IsSTSA(LL,HH) then
		error "DnSC (char2): Expected Centraliser(DerL, S) to be a STSA of DerL";
	end if;

	mats := [ (LLmaps`mp_LL_to_mats)(LL!h) : h in Basis(HH) ];
	es,ev := simdiag(mats);
	ev := [ Vector(t) : t in ev ];
	nonz := [ i : i in [1..#ev] | not IsZero(ev[i]) ];

	if  { Dimension(es[i]) : i in nonz } ne {2} then
		error "DnSC (char2): Expected Dn(Ad) to have 2^^.. as eigenspace mults.";
	end if;
	CBD`EigenVectors := &cat[ [ Vector(ev[i]) : j in [1..Dimension(es[i])] ] : i in nonz ];
	CBD`EigenSpaces := &cat[ Basis(es[i]) : i in nonz ];
	ChangeUniverse(~(CBD`EigenSpaces), L);

	//Simply straighten the pairs now.
	CBD`PosNegPairs := {{2*i-1,2*i} : i in [1..Floor(#nonz)] };
	findframe_all_pairs(~CBD);
end procedure;

