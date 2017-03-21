freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":findeigenspc_notinH, compute_basis_by_simp_es, mult_dim_eigenspc, ismultof;
import "identify_roots.m":compute_idrts, check_indrts;

findframe_G2_char3 := procedure(~CBD)

	dup := mult_dim_eigenspc(CBD);

	if [ #d : d in dup ] ne [3,3] then
		error "Straightening G2(3): Unexpected eigenspace dims.";
	end if;

	//Many of them are not in dup
	notdup := [ i : i in [1..12] | i notin &cat(dup) ];

	es := CBD`EigenSpaces;
	ev := CBD`EigenVectors;

	L := CBD`L;
	F := CBD`F;
	Vfull := VectorSpace(F, Dimension(L));
	Vdups := [*
		sub<Vfull | [ Vector(e) : e in es[d] ]>
		: d in dup
	*];
	Vdupsnw := [*
		sub<Vfull | []>
		: d in dup
	*];
	esnw := [* [] : d in dup *];


	/* Computing i*j for i in notdup does not give us
		additional information. So we try to solve 
		equations instead. It does not work immediately,
		but it does if we use the nullspace of [x,-x] for
		x a short root.
	*/
	
	for i in notdup do
		x := L!es[i];
		j := [ j : j in notdup | ev[j] eq -ev[i] ];
		if #j ne 1 then 
			error "Expected to be able to identify minus of short roots in G2 over characteristic 3.";
		end if;
		y := L!es[j[1]];

		for k in [1..#Vdups] do
			B := Basis(Vdups[k]);
			NS := Nullspace(HorizontalJoin(
				Matrix([ Vector(L!b*L!x) : b in B ]),
				Matrix([ Vector(L!b*L!y) : b in B ])));
			if Dimension(NS) ne 1 then
				continue;
			end if;

			z := Basis(NS)[1]*Matrix(B);
	
			//Add, if that helps.
			Vtmp := sub<Vfull | Vdupsnw[k], z>;
			if Dimension(Vtmp) gt Dimension(Vdupsnw[k]) then
				Vdupsnw[k] := Vtmp;
				Append(~(esnw[k]), z);
			end if;
		end for;
	end for;

	if [ #t : t in esnw ] ne [3,3] then	
		printf "esnw = \n";	IndentPush(); esnw; IndentPop();
		error "Could not find correct eigenspaces in G2 over characteristic 3";
	end if;

	for i in [1..#dup] do
		for k in [1..#dup[i]] do
			CBD`EigenSpaces[dup[i][k]] := esnw[i][k];
		end for;
	end for;
end procedure;


chevbasis_G2_char3 := procedure(~CBD)

	local L, H, R, dupl, shortrts;

	L := CBD`L;
	H := CBD`H;
	R := CBD`R;

	findeigenspc_notinH(~CBD);
	findframe_G2_char3(~CBD);

	ev := CBD`EigenVectors; 
	es := CBD`EigenSpaces;

	dupl := [ i : i in [1..CBD`NRoots] | #[ p : p in ev | p eq ev[i] ] gt 1 ];
	dims := [ Dimension(ideal<L|es[i]>) : i in [1..CBD`NRoots] ];
	shortrts := [ i : i in [1..CBD`NRoots] | dims[i] eq 7 ];

	vprintf ChevBas, 2 : "  Dimensions: %o\n", dims;
	vprintf ChevBas, 2 : "  Short roots: %o\n", shortrts;

	/***
	 *** Use the A2 stuff to sort this out 
	 ***/
	Ltmp := sub<L | es[shortrts] cat CBD`SCSAVectors >;
	Htmp := H;
	Rtmp := RootDatum("A2");
	CBDA2 := NewChevBasData(Rtmp, Ltmp, Htmp);
	CBDA2`EigenVectors := ev[shortrts];
	CBDA2`EigenSpaces := [ Ltmp | e : e in es[shortrts] ];

	compute_idrts(~CBDA2);
	vprintf ChevBas, 2 : "  A2 identified: %o\n", CBDA2`IndRts;
	if not check_indrts(CBDA2) then error "Ho"; end if;

	//We identified the A2 bit.
	//There are a two possible pullbacks:
	//  a and -(2a+b) may be switched in G2;
	//  so a and (-a+b) whend pulling back.
	pullbacks := { PermuteSequence([1..6],w) : w in CoxeterGroup("A2")};

	found_indrts_G2 := false;
	for pb in pullbacks do
		Q := CBDA2`IndRts;
		alpha := shortrts[Q[pb[1]]];
		alpha_plus_beta := shortrts[Q[pb[2]]];
		twoalpha_plus_beta := shortrts[Q[pb[3]]];
		min_alpha := shortrts[Q[pb[4]]];
		min_alpha_plus_beta := shortrts[Q[pb[5]]];
		min_twoalpha_plus_beta := shortrts[Q[pb[6]]];

		/***
		 *** Find beta
		 ***/
		betas := [ i : i in [1..#ev] | ev[alpha_plus_beta] + ev[min_alpha] eq ev[i] ];
	
		/* find beta*/
		mklhsrhs := function(poss, lhsind, rhsind)
			local lhs, rhs;
			lhs := VerticalJoin([ Vector((L!(poss[i]))*(L!(es[lhsind])))
			: i in [1..#poss] ]);
			rhs := rhsind eq 0 select Matrix(Vector(L!0)) else Matrix(Vector(L!es[rhsind]));
			return lhs, rhs;
		end function;

		poss := es[betas];
		/* using that (beta) + -(alpha+beta) = -alpha */
		lhs1, rhs1 := mklhsrhs(poss, min_alpha_plus_beta, min_alpha);
		/* using that (beta) + -(2alpha+beta) is no root */
		lhs2, rhs2 := mklhsrhs(poss, min_twoalpha_plus_beta, 0);
		/* using that (beta) + (alpha+beta) is no root */
		lhs3, rhs3 := mklhsrhs(poss, alpha_plus_beta, 0);

		c,v,n := IsConsistent(
			HorizontalJoin([lhs1,lhs2,lhs3]), 
			HorizontalJoin([rhs1, rhs2,rhs3])
		);

		if not c or Dimension(n) gt 0 then 
			print "not consistent or still freedom (beta)";
			continue;
		end if;
		esbeta := L!Eltseq(Vector(v)*Matrix(poss));
		beta := [ j : j in betas | ismultof(es[j], esbeta) cmpne false ][1];
	

		/***
		 *** Find -beta
		 ***/
		minbetas := [ i : i in [1..#ev] | ev[min_alpha_plus_beta] + ev[alpha] eq ev[i] ];
		poss := es[minbetas];
		/* using that (-beta) + (alpha+beta) = alpha */
		lhs1, rhs1 := mklhsrhs(poss, alpha_plus_beta, alpha);
		/* using that (-beta) + (2alpha+beta) is no root */
		lhs2, rhs2 := mklhsrhs(poss, twoalpha_plus_beta, 0);
		/* using that (-beta) + -(alpha+beta) is no root */
		lhs3, rhs3 := mklhsrhs(poss, min_alpha_plus_beta, 0);

		c,v,n := IsConsistent(HorizontalJoin([lhs1,lhs2,lhs3]), HorizontalJoin([rhs1, rhs2,rhs3]));
		if not c or Dimension(n) gt 0 then 
			print "not consistent or still freedom (-beta)"; 
			continue;
		end if;

		esminbeta := L!Eltseq(Vector(v)*Matrix(poss));
		minbeta := [ j : j in minbetas | ismultof(es[j], esminbeta) cmpne false ][1];
	
		/* see what spaces are left*/
		therest_plus := [ <i,es[i]> : i in betas | i ne beta ];
		therest_minus := [ <i,es[i]> : i in minbetas | i ne minbeta ];
	
		if #therest_plus ne 2 or #therest_minus ne 2 then
			error "Unexpected error in chevbasis_G2(3) (TRP/TRM)";
		end if;

		/* there's some choice here */
		threealpha_plus_beta := therest_plus[1][1];
		min_threealpha_plus_twobeta := therest_plus[2][1];
	
		/* and then the last two are fixed */
		//es_threealpha_plus_twobeta := (L!esbeta)*(L!therest_plus[1]);
		//es_min_threealpha_plus_beta := (L!esbeta)*(L!therest_plus[2]);
	
		o := L!es[threealpha_plus_beta]*L!esbeta;
		t := [ j : j in therest_minus | 
			ismultof(o, j[2]) cmpne false and ismultof(o,j[2]) cmpne 0 ];
		if #t ne 1 then 
			error "Unexpected error in chevbasis_G2(3) (3a+2b)";
		end if;
		threealpha_plus_twobeta := t[1][1];

		o := L!es[min_threealpha_plus_twobeta]*L!esbeta;
		t := [ j : j in therest_minus | 
			ismultof(o, j[2]) cmpne false and ismultof(o,j[2]) cmpne 0 ];
		if #t ne 1 then 
			error "Unexpected error in chevbasis_G2(3) (3a+b)";
		end if;
		min_threealpha_plus_beta := t[1][1];

	

		/* done :) */
		indrts := [ Integers() | ];
		indrts[1] := alpha;
		indrts[2] := beta;
		indrts[3] := alpha_plus_beta;
		indrts[4] := twoalpha_plus_beta;
		indrts[5] := threealpha_plus_beta;
		indrts[6] := threealpha_plus_twobeta;
		indrts[7] := min_alpha;
		indrts[8] := minbetas[1];
		indrts[9] := min_alpha_plus_beta;
		indrts[10] := min_twoalpha_plus_beta;
		indrts[11] := min_threealpha_plus_beta;
		indrts[12] := min_threealpha_plus_twobeta;

		CBD`IndRts := indrts;

		vprintf ChevBas, 2: "  Roots of G2 identified: %o\n", indrts; 

		if check_indrts(CBD) then
			found_indrts_G2 := true;
			break;
		end if;
	end for; //try a few pullbacks from A2 (not necessary, really, any should work)

	if not found_indrts_G2 then 
		error "Ho"; 
	end if;


	compute_basis_by_simp_es(~CBD);
end procedure;
