freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../diagram_auts.m":dn_diagram_auts;
import "findframemain.m":findframe_all_pairs;
import "findframe_F4_char2.m":findframe_F4_char2;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":pullback, findeigenspc_notinH, mult_dim_eigenspc, compute_basis_by_simp_es;
import "identify_roots.m":compute_idrts, check_indrts;

/* define the pullback maps (long is never used, actually) */
pullback_DtoFlong := procedure(fromCBD, ~toCBD : pi := false)
	local R, imgs_of_simp;

	R := toCBD`R;
	imgs_of_simp := [RootPosition(R,[0,1,0,0] : Basis := "Root"),
					 RootPosition(R,[1,0,0,0] : Basis := "Root"),
					 RootPosition(R,[0,1,2,0] : Basis := "Root"),
					 RootPosition(R,[0,1,2,2] : Basis := "Root") ];

	pullback(fromCBD, ~toCBD, imgs_of_simp : pi := pi);
end procedure;

pullback_DtoFshort := procedure(fromCBD, ~toCBD : pi := false)
	local R, imgs_of_simp;

	R := toCBD`R;
	imgs_of_simp := [RootPosition(R,[0,0,1,0] : Basis := "Root"),
					 RootPosition(R,[0,0,0,1] : Basis := "Root"),
					 RootPosition(R,[0,1,1,0] : Basis := "Root"),
					 RootPosition(R,[1,1,1,0] : Basis := "Root") ];

	pullback(fromCBD, ~toCBD, imgs_of_simp : pi := pi);
end procedure;


/* F4 is two D4's */

D4part := function(CBD, Q)
	local RD, LD, HD, CBDD, dup;

	RD := RootDatum("D4");
	LD := sub<CBD`L | (CBD`EigenSpaces)[Q] cat CBD`SCSAVectors>;
	HD := sub<LD | CBD`SCSAVectors>;
	CBDD := NewChevBasData(RD, LD, HD);

	findeigenspc_notinH(~CBDD);
	dup := mult_dim_eigenspc(CBDD);
	if {* #d : d in dup *} ne {* 2^^12 *} then 
		error "Unexpected D4 in F4. Expecting adjoint. This isn't, I think";
	end if;
	CBDD`PosNegPairs := { SequenceToSet(d) : d in dup };
	
	/* Experiments show that in very rare cases we have an unfortunate
	   result of findframe_all_pairs resulting in failed identification
	   of the roots -- so we have a couple of goes */
	cnt := 0; ok := false;
	while ((cnt lt 10) and (not ok)) do
		cnt +:= 1;
		try
			findframe_all_pairs(~CBDD);
			compute_idrts(~CBDD);
			ok := true;
		catch problem
			ok := false;
		end try;
	end while;

	/* Check; return */
	if (not ok) or (not check_indrts(CBDD)) then
		error "Could not identify roots in D4.";
	end if;

	return CBDD;
end function;

chevbasis_F4_char2 := procedure(~CBD)
	local L, R, es, ev, cart, dims, short, long,
		CBD_D1, CBDorig, indrts, shortroots, I, 
		ok, i, xi, y, p, j, k;

	L := CBD`L;
	R := CBD`R;
	
	findeigenspc_notinH(~CBD);
	findframe_F4_char2(~CBD);

	es := CBD`EigenSpaces;
	ev := CBD`EigenVectors;
	cart := CBD`SCSAVectors;
	dims := [ Dimension(ideal<L | es[i]>) : i in [1..48] ]; 

	short := [ i : i in [1..CBD`NRoots] | dims[i] eq 26 ];
	long :=  [ i : i in [1..CBD`NRoots] | dims[i] ne 26 ];


	CBD_D1 := D4part(CBD, short);
	CBDorig := CBD;

	for pi in dn_diagram_auts(4) do
		CBD := CBDorig;
		
		pullback_DtoFshort(CBD_D1, ~CBD : pi := pi);

		//the short ones generate a nontrivial ideal of type D4, we use that :)
		indrts := CBD`IndRts;
		es := CBD`EigenSpaces;
		shortroots := [ i : i in [1..2*NumPosRoots(R)] | IsShortRoot(R,i) ];
		I := ideal<L|[ es[indrts[i]] : i in [1..CBD`NRoots] | IsDefined(indrts,i)]>;

		ok := true;
		for i in shortroots do
			for xi in long do
				y := es[indrts[i]]*es[xi];
				if IsZero(y) then continue; end if;

				p := [ j : j in [1..CBD`NRoots] | 
					Rank(Matrix([ Vector(y),Vector(es[j]) ])) lt 2 ];
				if #p ne 1 then "hmz, overlapping eigenspaces ?!"; end if;
				j := Position(indrts,p[1]);

				//so i*xi = j, so xi must correspond to root j - i =: k
				k := RootPosition(R, Root(R,j) - Root(R,i));

				if not IsShortRoot(R,i) then error "!! i is not short"; end if;
				if not IsShortRoot(R,j) then error "!! j is not short"; end if;
				if not IsLongRoot(R,k) then error "!! k is not long"; end if;

				if k eq 0 then 
					ok := false;
					break i;
				end if;

				if IsDefined(indrts, k) and indrts[k] ne xi then
					ok := false;
					break i;
				end if;
				indrts[k] := xi;
			end for;
		end for;

		CBD`IndRts := indrts;
		ok := ok and check_indrts(CBD);

		if ok then
			break;
		end if;
		indrts := false;
	end for;

	if indrts cmpeq false then error "Stop."; end if;

	CBD`IndRts := indrts;
	if not check_indrts(CBD) then
		error "check_indrts failed in F4.";
	end if;

	compute_basis_by_simp_es(~CBD);
end procedure;

