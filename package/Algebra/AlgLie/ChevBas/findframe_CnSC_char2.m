freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspc, mult_dim_eigenspc;
import "chevbasis_B2SC_char2.m":findframe_fourspace_by_two_A1s, findframe_fourspace_by_straight_A1s;
import "findframemain.m":findframe_all_pairs;

//We compute the A1s by using the nullspaces of the fourspaces,
//  (otherwise we'll mess up later), the C3SC case
find_A1s_with_Z_C3SC := function(L, L0, fours)
	//Get the A1s from the nullspaces of the fourspaces.
	// These A1s also include the centre of the Lie algebra, unfortunately.
	local A1s, ret, i, M, h, VL0, VL, W;

	VL0 := sub< VectorSpace(BaseRing(L), Dimension(L0)) |
		   [ Vector(b) : b in Basis(L0) ]>;
	VL := VectorSpace(BaseRing(L), Dimension(L));
	assert #fours eq 3;

	//At first, the A1s are 4-dim because each contains the centre as well.
	A1s := [];
	for i in [1..#fours] do
		   M := VerticalJoin([ HorizontalJoin([ Vector(L!b*L!c) : b in Basis(fours[i]) ]) : c in Basis(L0) ]);

		   Append(~A1s, Nullspace(M));
	end for;

	//Now convert back to L
	ret := [ sub<VL | [ Vector(L!(L0!b)) : b in Basis(W) ]> : W in A1s ];
	ret := [ [* ret[i], {1,2,3} diff {i}, {i} *] : i in [1..3] ];

	//Done!
	return ret;
end function;

//The CnSC, n >= 3
graph_of_fourspcs := function(L, fourspcs)
	local i, j, n, neighbrs, S;

	n := #fourspcs;
	neighbrs := [ {Integers()|} : i in [1..n] ];
	for i in [1..n] do for j in [(i+1)..n] do
		S := sub<L | [ L!x*L!y : x in Basis(fourspcs[i]), y in Basis(fourspcs[j]) ]>;
		if Dimension(S) eq 0 then 
			Include(~(neighbrs[i]), j);
			Include(~(neighbrs[j]), i);
		end if;
	end for; end for;

	return Graph<n | neighbrs>;
end function;

find_A1s_with_Z_CnSC := function(L, L0, fours)
	local G, CompG, Clqs, MaxClqs, fourspacesfound,
		Q, QQ, Qbar, Qelts, mat, MatBasR0, ns, n,
		VSfull;

	G := graph_of_fourspcs(L, fours);
	
	//Find a maximum coclique Q, i.e. n-1 V4's that don't commute.
	//Then, find the complement Q\bar of Q,
	//and take the Centraliser of Q\bar inside Vbig 
	CompG := Complement(G);
	Clqs := AllCliques(CompG);
	MaxClqs := { c : c in Clqs | #c eq Maximum({ #d : d in Clqs }) };

	//This list will contain tuples: space, Q, Qbar
	//such that fourspcs[Q] does not commute with the space,
	//and fourspcs[Qbar] does.
	fourspacesfound := [* *];
	MatBasL0 := Matrix([ Vector(L!b) : b in Basis(L0) ]);
	n := #fours;
	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	
	for Q in MaxClqs do
		QQ := { i : i in [1..n] | i in Q };
		Qbar := { i : i in [1..n] | i notin Q };
		Qelts := &cat[ Basis(fours[q]) : q in Qbar ];

		mat := VerticalJoin([
			HorizontalJoin([ Vector(L!x*L!y) : y in Qelts ]) 
			: x in Basis(L0) ]);
		ns := sub<VSfull | [ b*MatBasL0 : b in Basis(Nullspace(mat)) ]>;

		Append(~fourspacesfound, [*ns, QQ, Qbar*]);
	end for;

	return fourspacesfound;
end function;


split_A1_with_Z := function(L, VA1)
	local M, DSD, ds;
	M := sub<L | [ L!b : b in Basis(VA1) ]>;
	DSD := DirectSumDecomposition(M);
	ds := [ Dimension(t) : t in DSD ];
	assert SequenceToMultiset(ds) eq {* 3,1 *};
	return DSD[Position(ds,3)], DSD[Position(ds,1)];
end function;


findframe_Cn_SC_char2 := procedure(~CBD)
	local es, dup, dupsz, VSfull, fourspcs, L0, A1_with_Zs, LA1s, 
		B22, B23, B21, B41, B42, B43, RnkR, fld, L,
		pr, i, j, fouri;

	L := CBD`L;
	RnkR := Rank(CBD`R);
	fld := BaseRing(L);

	findeigenspc(~CBD);
	es := CBD`EigenSpaces;
	dup := mult_dim_eigenspc(CBD);
	dupsz := [ #d : d in dup ];
	assert SequenceToMultiset(dupsz) eq {* 3*RnkR, 4^^Floor((RnkR^2-RnkR)/2) *};

	VSfull := VectorSpace(fld, Dimension(L));
	fourspcs := [ sub< VSfull | [ Vector(b) : b in es[d] ]> : d in dup | #d eq 4 ];

	i := dup[ Position(dupsz, 3*RnkR) ];
	L0 := sub<L | [ L!b : b in es[i] ]>;

	//Get the A1s
	if RnkR lt 3 then
		error "findframe_Cn_SC_char2: Was not expecting Cn, n<3";
	elif RnkR eq 3 then
		A1_with_Zs := find_A1s_with_Z_C3SC(L, L0, fourspcs);
	else
		A1_with_Zs := find_A1s_with_Z_CnSC(L, L0, fourspcs);
		A1_with_Zs := [ A : A in A1_with_Zs | Dimension(A[1]) eq 4 ];
	end if;
	assert #A1_with_Zs eq RnkR;

	A1s := [ <split_A1_with_Z(L, A[1]), A[2], A[3]> : A in A1_with_Zs ];

	//Straighten all of the two-spaces first; we do this in pairs, so we must
	//  be a bit careful if RnkR is odd.
	BasA1s := [];
	for pr in [1..Ceiling(RnkR/2)] do
		i := 2*pr-1; j := 2*pr;
		if j gt RnkR then j := RnkR-1; end if;

		fouri := A1s[i][2] meet A1s[j][2];
		vprintf ChevBas, 3: "[findframe_CnSC, two] i = %o, j = %o => fouri = %o\n", i, j, fouri;
		assert #fouri eq 1;

		B2a, B2b := findframe_fourspace_by_two_A1s(L, 
			A1s[i][1], A1s[j][1], fourspcs[Representative(fouri)]);
		Append(~BasA1s, B2a);
		if not (j lt i) then Append(~BasA1s, B2b); end if;
	end for;
	assert #BasA1s eq RnkR;

	//And then the four spaces
	Bas4s := [];
	for i in [1..#fourspcs] do
		twoind := [ j : j in [1..#A1s] | i in A1s[j][2] ];
		vprintf ChevBas, 3: "[findframe_CnSC, four] i = %o, twoind = %o\n", i, twoind;
		assert #twoind eq 2;

		x1 := BasA1s[twoind[1]][1]; x2 := BasA1s[twoind[1]][2];
		x3 := BasA1s[twoind[2]][1];	x4 := BasA1s[twoind[2]][2];
		
		B4 := findframe_fourspace_by_straight_A1s(L, fourspcs[i], x1,x2,x3,x4);
		Append(~Bas4s, B4);
	end for;

	CBD`EigenSpaces := &cat(BasA1s) cat &cat(Bas4s);
	CBD`EigenVectors := [];
	CBD`PosNegPairs := { {2*i-1,2*i} : i in [1..NumPosRoots(CBD`R)] };

	findframe_all_pairs(~CBD);
end procedure;
