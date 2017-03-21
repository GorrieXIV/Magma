freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../diagram_auts.m":dn_diagram_auts;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":pullback, findeigenspc_notinH, compute_basis_by_simp_es, ismultof, recompute_eigenvectors;
import "identify_roots.m":compute_idrts, check_indrts;
import "findframemain.m":verify_straight;
import "findframe.m":findframe;
import "chevbasis_A1_char2.m":chevbasis_A1_char2;
import "chevbasis_Bn_char2.m":idrts_Bn_using_Dn;

pullback_DtoC := procedure(fromCBD, ~toCBD : pi := false)
	local rnk, rtn, toR;

	toR := toCBD`R;
	rnk := Rank(toR);
	rtn := RootPosition(toR, Root(toR,rnk-1) + Root(toR,rnk) );
	if rnk lt 3 then
		error "pullback_DtoC: rnk < 3";
	elif rnk eq 3 then
		//D3 uses A3 and stuff and blwech.
		imgs_of_simp := [2,1,rtn];
	else
		imgs_of_simp := [1..(rnk-1)] cat [rtn];
	end if;

	pullback(fromCBD, ~toCBD, imgs_of_simp : pi := pi);
end procedure;



find_longrts_Cn := function(CBD)
	local L, R, NPR, rnk, indrts, es, ev, 
		rt00112211, rt0011221, rt00221, rt12221, 
		i, t, v, p, longest, poslong, neglong;

	L := CBD`L;
	R := CBD`R;
	NPR := NumPosRoots(R);
	rnk := Rank(R);
	indrts := CBD`IndRts;
	es := CBD`EigenSpaces; ev := CBD`EigenVectors;

	rt00112211 := function(numzeroes,numones1,numtwos,numones2 : minus := false)
		local s, Q;

		s := minus select -1 else 1;

		Q := [ 0: i in [1..numzeroes]] 
					cat [1 : i in [1..numones1] ] 
					cat [2 : i in [1..numtwos] ] 
					cat [1 : i in [1..numones2] ];
		
		if #Q ne Rank(R) then 
			error Sprintf("Q = %o\nrt001221: Wrong length of root.", Q);
		end if;

		return RootPosition(R, s*Vector(Q) : Basis := "Root");
	end function;
	rt001221 := function(numzeroes, numtwos : minus := false)
		return rt00112211(numzeroes,1,numtwos,1 : minus := minus);
	end function;
	rt00221 := function(numzeroes,numtwos : minus := false)
		return rt00112211(numzeroes,0,numtwos,1 : minus := minus);
	end function;

	/*
		Find (longest) root 222..21 using 222..21*-10000 = 122221
	*/
	rt12221 := rt001221(0,rnk-2);
	
	p := [ i : i in CBD`IndLong | not IsZero((L!es[i])*(L!es[indrts[1+NPR]])) 
			and (ismultof( L!es[indrts[rt12221]], (L!es[i])*(L!es[indrts[1+NPR]])) cmpne false )];
	if #p ne 1 then 
		//Could be the cause of a wrong diagram automorphism. (esp. D4 case)
		return false; 
	end if;
	
	longest := rt00221(0,rnk-1);
	indrts[longest] := p[1];

	/*
		Descend, using e.g. 002221*010000=012221
	*/
	for i in [1..rnk-1] do
		t := rt00221(i,rnk-i-1); //This is the root we're trying to find
		v := rt001221(i-1,rnk-i-1);
		
		//Some debug info
		p := [ j : j in CBD`IndLong | 
			not IsZero((L!es[j])*(L!es[indrts[i]])) 
			and ( ismultof( (L!es[j])*(L!es[indrts[i]]), L!es[indrts[v]] ) cmpne false ) ];

		if #p ne 1 then print "hmz (2)"; return false; end if;
		indrts[t] := p[1];
	end for;

	/*
		Now find the minuses of these roots
	*/
	poslong := [ i : i in CBD`IndLong | i in indrts ];
	neglong := [ i : i in CBD`IndLong | i notin indrts ];
	for i in neglong do
		p := [ j : j in poslong | not IsZero(es[j]*es[i]) ];
		if #p ne 1 then print "hmz (3)"; return false; end if;
		indrts[ Position(indrts,p[1])+NPR ] := i;
	end for;

	return indrts;
end function;


idrts_Cn_using_Dn := procedure(~CBD)
	local rnk, LD, HD, RD, CBDDn, pi, indrtsC, L, H;

	/* 
		Assumption: LonShort roots generate a Lie algebra of type D_n
	*/
	L := CBD`L; H := CBD`H;
	rnk := Rank(CBD`R);
	if rnk eq 3 then
		RD := RootDatum("A3" : Isogeny := (IsAdjoint(CBD`R) select "Ad" else "SC"));
	else
		RD := RootDatum("D" cat IntegerToString(rnk));
	end if;
	k := Dimension(LieAlgebra(RD, Rationals()));
	LD := sub<L | [ CBD`EigenSpaces[i] : i in CBD`IndShort] 
			cat [ L | b : b in Basis(H) ]>;
	HD := sub<LD | [ LD | b : b in Basis(H) ]>;
	
	if (Dimension(LD) ne k) then	
		error "Could not find subalgebra of type D_n of C_n";
	end if;

	CBDDn := NewChevBasData(RD,LD,HD);
	CBDDn`EigenSpaces := [ LD!(L!(CBD`EigenSpaces[i])) : i in CBD`IndShort ];
	recompute_eigenvectors(~CBDDn);
	CBDDn`PosNegPairs := { 
		{ Position(CBDDn`EigenSpaces, LD!(CBD`EigenSpaces[i])) : i in pr }
		: pr in CBD`PosNegPairs | #(pr meet CBD`IndShort) ne 0 };

	compute_idrts(~CBDDn);

	/* Now we may have to test some automorphisms of the diagram D_n,
       because otherwise pulling back to B_n might go wrong just a bit */
	for pi in dn_diagram_auts(rnk) do
		pullback_DtoC(CBDDn, ~CBD : pi := pi);
		indrtsC := find_longrts_Cn(CBD);

		if indrtsC cmpne false then
			vprintf ChevBas, 2: "[Found long roots]\n";
			break;
		end if;
		vprintf ChevBas, 2: "[Failed to find long roots]";
	end for;

	if indrtsC cmpeq false then
		error "Helaas.";
	end if;

	CBD`IndRts := indrtsC;
end procedure;

chevbasis_C2_char2 := procedure(~CBD)
	local RB, CBDB;

	//Use B2.

	RB := RootDatum("B2" : Isogeny := ( IsAdjoint(CBD`R) select "Ad" else "SC") );
	_,_,_,CBDB := ChevalleyBasis(CBD`L,CBD`H, RB);

	CBD`SCSAVectors := CBDB`SCSAVectors;
	CBD`EigenSpaces := CBDB`EigenSpaces;
	CBD`EigenVectors := CBDB`EigenVectors;
	CBD`PosNegPairs := CBDB`PosNegPairs;
	CBD`IndRts := (CBDB`IndRts)[[2,1,3,4,6,5,7,8]];
	assert verify_straight(CBD);
	assert check_indrts(CBD);
	compute_basis_by_simp_es(~CBD);

	assert IsChevalleyBasis(CBD);
end procedure;

chevbasis_Cn_char2 := procedure(~CBD)
	local L, H, R,
		ok, rnk, 
		founddims, totry, the_ideals, 
		i, I, d;

	R := CBD`R;
	L := CBD`L;
	H := CBD`H;
	rnk := Rank(R);

	//Silly exceptions
	if rnk eq 1 then 
		chevbasis_A1_char2(~CBD);
		return;
	elif rnk eq 2 then
		chevbasis_C2_char2(~CBD);
		return;
	end if;

	findframe(~CBD);

	if (CBD`NRoots ne Dimension(L) - rnk) then
		error Sprintf("Dimensions not OK (%o should be %o)\n", CBD`NRoots, Dimension(L) - rnk);
	end if;

	//The short roots generate a smaller dimension ideal than the long roots.
	founddims := {}; the_ideals := []; totry := {1..CBD`NRoots};
	while (#founddims lt 2) and (#totry gt 0) do
		i := Random(totry); Exclude(~totry, i);
		I := ideal<L | CBD`EigenSpaces[i]>;
		if Dimension(I) notin founddims then
			Include(~founddims, Dimension(I));
			the_ideals[Dimension(I)] := I;
		end if;
	end while;
	if #founddims lt 2 then
		error "Could not find two different ideals in chevbasis_Cn_char2";
	end if;

	I := the_ideals[Minimum(founddims)];
	CBD`IndLong := { i  : i in [1..CBD`NRoots] | L!(CBD`EigenSpaces[i]) notin I };
	CBD`IndShort := { i : i in [1..CBD`NRoots] | L!(CBD`EigenSpaces[i]) in I };

	//Use Dn to identify the roots (using the above)
	idrts_Cn_using_Dn(~CBD);

	if CBD`IndRts cmpeq false or not check_indrts(CBD) then
		error "Errors made in identification of roots in C_n";
	end if;

	compute_basis_by_simp_es(~CBD);
end procedure;
