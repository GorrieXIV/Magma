freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "../diagram_auts.m":dn_diagram_auts;
import "chevbasdata.m":NewChevBasData;
import "chevbasmain.m":pullback, findeigenspc_notinH, compute_basis_by_simp_es, ismultof, recompute_eigenvectors;
import "identify_roots.m":compute_idrts, check_indrts;
import "findframe.m":findframe;
import "cartints.m":findminofroot;
import "chevbasis_A1_char2.m":chevbasis_A1_char2;

pullback_DtoB := procedure(fromCBD, ~toCBD : pi := false)
	local rnk, rtn, toR;

	toR := toCBD`R;
	rnk := Rank(toR);
	rtn := RootPosition(toR, Root(toR,rnk-1) + 2*Root(toR,rnk) );
	imgs_of_simp := [1..(rnk-1)] cat [rtn];

	pullback(fromCBD, ~toCBD, imgs_of_simp : pi := pi);
end procedure;

/* Identify A_1 pairs */
findpairs := function(idx, f)
	local ret, todo, i, j, p;
	ret := {};

	todo := idx;
	while #todo gt 0 do
		i := Representative(todo);
		p := [ j : j in todo | f(i,j) ];
		if #p ne 1 then 
			return false;
		end if;
		j := p[1];
		Include(~ret, {i,j});
		todo diff:= {i,j};
	end while;

	return ret;
end function;

compute_posnegpairs_BCn := procedure(~CBD)
	local es, ev;
	/* Find pairs */
	es := CBD`EigenSpaces;
	ev := CBD`EigenVectors;
	if (IsAdjoint(CBD`R)) then
		CBD`PosNegPairsShort := findpairs(CBD`IndShort, func<i,j | i ne j and ev[j] eq ev[i]>);
	else
		CBD`PosNegPairsShort := findpairs(CBD`IndShort, func<i,j | not IsZero(es[j]*es[i])>);
	end if;
	CBD`PosNegPairsLong := findpairs(CBD`IndLong, func<i,j | not IsZero(es[j]*es[i])
		and ev[i] eq ev[j] >);

	if CBD`PosNegPairsShort cmpeq false then 
		error "Could not find A_1 pairs corresponding to short rts.";
	elif CBD`PosNegPairsLong cmpeq false then 
		error "Could not find A_1 pairs corresponding to long rts.";
	end if;

	CBD`PosNegPairs := CBD`PosNegPairsShort join CBD`PosNegPairsLong;
end procedure;



find_shortrts := function(CBD)
	local R, N, rnk, indrts,
		hri, p, i, x, fnd, y, pp, v, rp;

	R := CBD`R;
	N := NumPosRoots(R);
	rnk := Rank(R);
	indrts := CBD`IndRts;

	/* We use:
		Highest root of B_n is (12....2) (which is long), 
		so that if you multiply the element corresponding
		to thisone by -(11...1) (which is short), you
		get another short root. (namely 01....1). 

		This puts us into business as you can now "descend"
		by using (0,1,...,1)*(0,-1,0...,0) = (0,0,1,..1)
		etc.
	*/

	hri := indrts[RootPosition(R, HighestRoot(R))];
	p := [ i : i in CBD`IndShort | not IsZero(CBD`EigenSpaces[hri]*CBD`EigenSpaces[i]) ];


	/* maybe change -- see notes */
	for i in [1..#p] do
		x := findminofroot(CBD,p[i]);

		fnd := [x];
		y := CBD`EigenSpaces[x];

		repeat
			y := y*(CBD`EigenSpaces[indrts[#fnd+N]]);

			pp := [ i : i in [1..CBD`NRoots] | y in sub<CBD`L|CBD`EigenSpaces[i]> ];
			if #pp ne 1 then	x := 0;
			else			x := pp[1];
			end if;

			Append(~fnd, x);
		until IsZero(x) or #fnd eq rnk;

		if #fnd eq rnk then 
			break;
		end if;
	end for;

	if #fnd ne rnk or fnd[#fnd] eq 0 then
		return false;
	end if;

	v := Vector([1 : i in [1..rnk]]);
	for i in [1..rnk] do
		rp := RootPosition(R, v : Basis := "Root");
		indrts[rp] := fnd[i];
		indrts[rp+N] := fnd[i] eq 0 select 0 else findminofroot(CBD,fnd[i]);
		v[i] := 0;
	end for;

	return indrts;
end function;


idrts_Bn_using_Dn := procedure(~CBD)
	local rnk, mpinds, esnw, LD, HD, RD, CBDDn, pi, indrtsB,
		V, VSfull;

	/* 
		Long roots generate a Lie algebra of type D_n
	*/
	rnk := Rank(CBD`R);
	
	mpinds := SetToSequence(CBD`IndLong);
	LD := sub<CBD`L | [ CBD`EigenSpaces[i] : i in CBD`IndLong] 
			cat [ CBD`L | b : b in Basis(CBD`H) ]>;
	HD := CBD`L meet CBD`H;
	RD := RootDatum("D" cat IntegerToString(rnk) : Isogeny := "SC");

	//We have to "catch" the centre when going to this subalgebra of type Dn, annoyingly,
	// since it is simply connected Dn.
	CBDDn := NewChevBasData(RD,LD,HD);

	esnw := []; VSfull := VectorSpace(BaseRing(LD), Dimension(LD));
	for i in mpinds do
		V := sub<VSfull | [ Vector(LD!(CBD`EigenSpaces[i])*LD!h) : h in Basis(HD) ]>;
		assert Dimension(V) eq 1;
		Append(~esnw, V);
	end for;
	assert { Dimension(e) : e in esnw} eq {1};
	CBDDn`EigenSpaces := [ LD!(Basis(e)[1]) : e in esnw ];
	recompute_eigenvectors(~(CBDDn));

	CBDDn`PosNegPairs := { 
		{ Position(mpinds, i) : i in pr }
		: pr in CBD`PosNegPairs | #(pr meet CBD`IndLong) ne 0 };
	compute_idrts(~CBDDn);

	/* Now we may have to test some automorphisms of the diagram D_n,
       because otherwise pulling back to B_n might go wrong just a bit */
	for pi in dn_diagram_auts(rnk) do
		pullback_DtoB(CBDDn, ~CBD : pi := pi);
		indrtsB := find_shortrts(CBD);

		if indrtsB cmpne false then
			break;
		end if;
		vprintf ChevBas, 2: "[Failed to find short roots]";
	end for;

	if indrtsB cmpeq false then
		error "Helaas.";
	end if;

	CBD`IndRts := indrtsB;
end procedure;

idrts_B2 := procedure(~CBD)
	local pairsshort, pairslong, gl, indrtsB,
		i, j, t, es, ev;

	es := CBD`EigenSpaces;
	ev := CBD`EigenVectors;

	assert IsAdjoint(CBD`R);

	pairslong := [ <Min(j), Max(j)> : j in CBD`PosNegPairsLong ];
	pairsshort := [ <Min(j), Max(j)> : j in CBD`PosNegPairsShort ];
	short := &cat[ [ Min(j), Max(j) ] : j in CBD`PosNegPairsShort ];

	//Positive roots 1 and 4 are long; 2 and 3 are short
	for gl in Sym(2) do for hl in Sym(2) do 
		//init
		indrtsB := [];		

		//long
		indrtsB[1] := pairslong[1^gl][1]; //(1,0)
		indrtsB[5] := pairslong[1^gl][2]; //-(1,0)
		indrtsB[4] := pairslong[2^gl][1^hl]; //(1,2)
		indrtsB[8] := pairslong[2^gl][2^hl]; //-(1,2)

		//short follow, as (1,2)*(0,-1) = (1,1)
		//                 long   short   short
		if not exists(ind){ i :  i in short | not IsZero(es[i]*es[indrtsB[4]]) } then
			continue;
		end if;

		_ := exists(t){ <i,j> : i in [1..2], j in [1..2] | pairsshort[i][j] eq ind };

		indrtsB[6] := ind; 						//-(0,1)
		indrtsB[2] := pairsshort[t[1]][3-t[2]]; //(0,1)
		
		i := 3-t[1];
		pr := pairsshort[i];
		if not IsZero(es[pr[1]]*es[indrtsB[4]]) then
			indrtsB[7] := pr[1];
			indrtsB[3] := pr[2];
		elif not IsZero(es[pr[2]]*es[indrtsB[4]]) then
			indrtsB[7] := pr[2];
			indrtsB[3] := pr[1];
		else
			continue;
		end if;
		
		CBD`IndRts := indrtsB;

		b := check_indrts(CBD);
		if b then 
			return;
		end if;
	end for; end for;

	error "Could not identify roots of type B2.";
end procedure;

chevbasis_Bn_char2 := procedure(~CBD)
	local L, rnk, founddims, the_ideals, totry, i, I;

	L := CBD`L;
	rnk := Rank(CBD`R);

	//Silly exception
	if rnk eq 1 then
		chevbasis_A1_char2(~CBD);
		return;
	end if;

	findeigenspc_notinH(~CBD);
	findframe(~CBD);

	//Use the fact that the long roots generate an ideal of type Dn, 
	//  whereas the short roots generate (sort of) an ideal of A_1^n
	//[The Dn-ideal does contain the short roots, but not the other way around]
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
		error "Could not find two different ideals in chevbasis_Bn_char2";
	end if;

	I := the_ideals[Minimum(founddims)];
	CBD`IndLong := { i  : i in [1..CBD`NRoots] | L!(CBD`EigenSpaces[i]) notin I };
	CBD`IndShort := { i : i in [1..CBD`NRoots] | L!(CBD`EigenSpaces[i]) in I };

	compute_posnegpairs_BCn(~CBD);

	if rnk eq 2 then idrts_B2(~CBD);
	else			 idrts_Bn_using_Dn(~CBD);
	end if;

	if CBD`IndRts cmpeq false then
		error "Could not identify roots.";
	end if;

	if not check_indrts(CBD) then error "ho :("; end if;

	compute_basis_by_simp_es(~CBD);
end procedure;


