freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../derlie.m":ExtendHInDerL;
import "findframe_A3_char2.m":find_A3_inside_LLC3;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":findeigenspcLH, ismultof, mult_dim_eigenspc, compute_basis_by_simp_es;
import "identify_roots.m":check_indrts;
import "findframemain.m":findframe_all_pairs, verify_straight;

chevbasis_G2_char2 := procedure(~CBD)
	local L, H, R, fld,
		LL, LLmaps, 
		HinLL,
		triesneeded, LL15, LL15H;

	L := CBD`L; H := CBD`H; fld := CBD`F; R := CBD`R;

	LL, LLmaps := ExtendHInDerL(L,H);
	HinLL := sub<LL | [ (LLmaps`mp_L_to_LL)(L!b) : b in Basis(H) ]>;

	//Find an A3 inside Der(G2); we know it is there.
	use_A3_to_findframe := function(DerL15, DerL15H)
		local es1, ev1, dup, esG2, evG2, CBD, CBDA3, rtsmap;

		es1, ev1 := findeigenspcLH(DerL15, DerL15H);
		dup := { { i : i in [1..#ev1] | ev1[i] eq ev1[j] } : j in [1..#ev1] };
		assert {* #d : d in dup *} eq {* 3, 2^^6 *};

		try
			_,_,_,CBDA3 := ChevalleyBasis(DerL15, DerL15H, RootDatum("A3" : Isogeny := "Ad"));
		catch e
			return false;
		end try;

		//Correspondence between A3 and G2, 
		//e.g. \alpha_2 in G2 corresponds to -(\alpha_1+\alpha_2) in A3.
		rtsmap := [ 1, 10, 8,  5,  6, 3,  7, 4,  2, 11, 12, 9 ];

		esG2 := [ L | (LLmaps`mp_LL_to_L)(LL!x) : 
			x in CBDA3`EigenSpaces[CBDA3`IndRts[rtsmap]] ];
		evG2 := [ Vector([ ismultof(L!e, L!e*L!h) : h in Basis(H) ]) : e in esG2 ];

		CBD := NewChevBasData(R,L,H);
		CBD`EigenSpaces := esG2;
		CBD`EigenVectors := evG2;
		CBD`PosNegPairs := { {i, i+6} : i in [1..6] };
		CBD`SCSAVectors := [ L!b : b in Basis(H) ];
		CBD`IndRts := [ 1..12 ];

		assert verify_straight(CBD);
		assert check_indrts(CBD);

		return CBD;
	end function;


	//Repeat:
	//1. Find an A3 with SCSA inside there;
	//2. Try to straighten eigenspaces without enlarging the field;
	triesneeded := [0,0];
	while true do
		vprintf ChevBas, 4: "+";
		triesneeded[1] +:= 1;

		LL15, LL15H := find_A3_inside_LLC3(LL, HinLL);
		if LL15 cmpeq false then continue; end if;

		triesneeded[2] +:= 1;
		CBD := use_A3_to_findframe(LL15, LL15H);
		if CBD cmpeq false then continue; end if;

		break;
	end while;

	if not verify_straight(CBD) then
		error "Hmz; not straight? Should be!";
	end if;

	compute_basis_by_simp_es(~CBD);
end procedure;
