freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspc, mult_dim_eigenspc, compute_basis_by_simp_es;
import "identify_roots.m":check_indrts;

matxV := function(L, x, V)
	return Matrix([ Coordinates(V, Vector(L!x*L!b)) : b in Basis(V) ]);
end function;	

split_A1_by_action_on_short := function(L, A1, Lshort)
	local LHS, RHS, i, r, modl, b, T, xa, xma,
		mats, MA, A, M, IDS, fld;

	assert Dimension(A1) eq 3;

	mats := [ matxV(L, b, Lshort) : b in Basis(A1) ];
	fld := BaseRing(L);

	MA := MatrixAlgebra(fld,4);
	A := sub<MA | mats>;
	modl := RModule(A);
	IDS := IndecomposableSummands(modl);

	B1 := [ &+[ Vector(modl!m)[i]*Lshort.i : i in [1..4] ] : m in Basis(IDS[1]) ];
	repeat
		//TODO: IMPROVE THIS
		LHS := [];
		RHS := [];
		for i in [1..10] do
			r := Random(A1);
			M := matxV(L, r, VectorSpaceWithBasis(B1));
			assert M[1][1] eq M[2][2];

			Append(~LHS, Vector([M[1][2], M[2][1], M[1][1]]));
			Append(~RHS, Vector(r));
		end for;

		LHS := Matrix(LHS);
		RHS := Matrix(RHS);
	until Rank(LHS) eq 3 and Rank(RHS) eq 3;

	b,T := IsConsistent(Transpose(LHS), Transpose(RHS));
	assert b;
	T := Transpose(T);
	xa := L!(A1!(&+[ T[1][j]*(Basis(A1)[j]) :j in [1..3] ]));
	xma := L!(A1!(&+[ T[2][j]*(Basis(A1)[j]) :j in [1..3] ]));

	return xa, xma;
end function;

findframe_fourspace_by_straight_A1s := function(L, four, xp1, xm1, xp2, xm2)
	local Bfour, M, ns, xab, xb, xmab, xmb;

	Bfour := Basis(four);
	M := VerticalJoin([ HorizontalJoin([ Vector(L!b*L!c) : c in [xp1,xp2] ]) 
		: b in Bfour ]);
	ns := Nullspace(M);
	assert Dimension(ns) eq 1;
	ns := Basis(ns)[1];
	xab := L!(&+[ ns[i]*Bfour[i] : i in [1..4] ]);

	xb := L!xm1*L!xab;
	assert not IsZero(xb);

	xmab := L!xb*L!xm2;
	assert not IsZero(xmab);

	xmb := L!xmab*L!xp1;
	assert not IsZero(xmb);

	return [xb, xmb, xab, xmab];
end function;

findframe_fourspace_by_two_A1s := function(L, A11, A12, four :
	BasA11 := false, BasA12 := false)

	//if BasA11 or BasA12 is not given, they are computed
	//  using split_A1_by_action_on_short above.

	local xa,xma,xa2b,xma2b, h1, hz,
		NBfour, M, ns, xab, xb, xmab, xmb;

	if BasA11 cmpeq false then
		xa, xma := split_A1_by_action_on_short(L, A11, four);
	else
		xa, xma := Explode(BasA11);
	end if;
	if BasA12 cmpeq false then
		xa2b, xma2b := split_A1_by_action_on_short(L, A12, four);
	else
		xa2b, xma2b := Explode(BasA12);
	end if;

	NBfour := findframe_fourspace_by_straight_A1s(L, four, xa, xma, xa2b, xma2b);

	return [xa,xma], [xa2b,xma2b], NBfour;
end function;

chevbasis_B2SC_char2 := procedure(~CBD)
	local L, H, fld,
		VSfull, dup, dupsz, es,
		L0, L1, DSD;

	L := CBD`L;
	H := CBD`H;
	fld := CBD`F;
	VSfull := VectorSpace(fld, 10);

	findeigenspc(~CBD);
	dup := mult_dim_eigenspc(CBD);
	dupsz := [ #d : d in dup ];

	assert SequenceToMultiset(dupsz) eq {* 4,6 *};

	es := CBD`EigenSpaces;
	L0 := sub<VSfull | [ Vector(b) : b in es[ dup[Position(dupsz,6)] ] ]>;
	L1 := sub<VSfull | [ Vector(b) : b in es[ dup[Position(dupsz,4)] ] ]>;
	DSD := DirectSumDecomposition(sub<L | [ L!b : b in Basis(L0) ]>);
	if #DSD ne 2 then
		print DSD;
		error "Unexpected DirectSumDecomposition in chevbasis_B2SC_char2";
	end if;

	BasDSD1, BasDSD2, BasL1 := 
		findframe_fourspace_by_two_A1s(L, DSD[1], DSD[2], L1);

	CBD`SCSAVectors := [ L!b : b in Basis(H) ];
	CBD`EigenSpaces := [ 
		BasDSD1[1], BasL1[1], BasL1[3], BasDSD2[1],
		BasDSD1[2], BasL1[2], BasL1[4], BasDSD2[2]
	];

	CBD`IndRts := [1..8];
	CBD`PosNegPairs := {{i,i+4} : i in [1..4]};
	assert check_indrts(CBD);
	compute_basis_by_simp_es(~CBD);
end procedure;
