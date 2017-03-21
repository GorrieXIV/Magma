freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../derlie.m":ExtendHInDerL;
import "chevbasdata.m":NewChevBasData;
import "diag.m":simdiag;
import "chevbasmain.m":findeigenspc_notinH, compute_basis_by_simp_es, recompute_eigenvectors;
import "identify_roots.m":compute_idrts, check_indrts;
import "findframemain.m":verify_straight;

chevbasis_A2SC_char3 := procedure(~CBD)
	local L, H, LL, HH, CBDLL, LLmaps, mats, es, ev, nonz;

	findeigenspc_notinH(~CBD);
	L := CBD`L; H := CBD`H;

	//We may use the Derivation algebra for straightening :)
	LL, LLmaps := ExtendHInDerL(CBD`L, CBD`H);
	HH := Centraliser(LL, sub<LL | [ (LLmaps`mp_L_to_LL)(L!x) : x in Basis(H) ]> );
	mats := [ (LLmaps`mp_LL_to_mats)(LL!x) : x in Basis(HH) ];
	es, ev := simdiag(mats);

	assert {* Dimension(e) : e in es *} eq {*1^^6,2*};
	nonz := [ i : i in [1..#ev] | not IsZero(Vector(ev[i])) ];

	CBD`EigenVectors := &cat[ [ Vector(ev[i]) : j in [1..Dimension(es[i])] ] : i in nonz ];
	CBD`EigenSpaces := &cat[ Basis(es[i]) : i in nonz ];
	ChangeUniverse(~(CBD`EigenSpaces), L);

	compute_idrts(~CBD);
	assert check_indrts(CBD);

	compute_basis_by_simp_es(~CBD);
end procedure;


