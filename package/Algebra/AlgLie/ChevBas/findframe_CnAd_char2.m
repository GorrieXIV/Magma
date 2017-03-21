freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspc_notinH, mult_dim_eigenspc;
import "findframemain.m":findframe_all_pairs, insert_found_frame, verify_straight;
import "findframe_BnSC_char2.m":findframe_A1_by_straight_A1;

pivot_repeated_nullspace := function(L, VSfull, Vbig, Qpivots)
	local foundnew, Vfoundnew, V, rndorder,
		B, M, NS, somethinghappens;

	foundnew := [VSfull|];
	Vfoundnew := VectorSpaceWithBasis(foundnew);

	while Dimension(Vfoundnew) lt Dimension(Vbig) do
		//Repeatedly take nullspaces under twospaces, 
		//until only a two-dim space is left.

		V := Vbig;
		rndorder := PermuteSequence([1..#Qpivots], Random(Sym(#Qpivots)));
		somethinghappens := false;
		for i in rndorder do
			B := Basis(V);
			M := VerticalJoin([	
					HorizontalJoin([ Matrix(L!x*L!b) : x in Qpivots[i]])
				: b in B ]);

			NS := Nullspace(M);
			if Dimension(NS) eq 0 then continue; end if;
			if Dimension(NS) eq Dimension(V) then continue; end if;

			somethinghappens := true;

			//Good, continue with only the nullspace
			V := sub<V | [ Vector(n*Matrix(B)) : n in Basis(NS) ]>;
			vprintf ChevBas, 3: "%o-", Dimension(V);

			if Dimension(V) eq 2 then
				if Dimension(V meet Vfoundnew) eq 0 then
					//Good, found a new pair!
					vprintf ChevBas, 3: "pair found";
					foundnew cat:= Basis(V);
					Vfoundnew := VectorSpaceWithBasis(foundnew);
					break i;
				end if;
			end if;
		end for;

		vprintf ChevBas, 3: "/";

		if not somethinghappens then
			error "pivot_repeated_nullspace: Does not work in this case.";
		end if;
	end while;

	return [ L!b : b in foundnew ];
end function;


//The code below for the adjoint case works just fine :)
findframe_Cn_Ad_char2 := procedure(~CBD)
	local dup, duptwo, dupbig, es, VSfull, Vbig, p, q, M,
		foundnew, L;

	L := CBD`L;
	
	findeigenspc_notinH(~CBD);
	dup := mult_dim_eigenspc(CBD);
	duptwo := { SequenceToSet(d) : d in dup | #d eq 2 };
	dupbig := [ d : d in dup | #d ne 2 ];
	if #dupbig ne 1 then error "Unexpected eigenspace dimensions in C_n (Ad)"; end if;
	dupbig := dupbig[1];

	CBD`PosNegPairs := duptwo;
	findframe_all_pairs(~CBD);

	es := CBD`EigenSpaces;

	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	Vbig := sub<VSfull | [ Vector(es[i]) : i in dupbig ]>;

	//Use pivot_repeated_nullspace to break up the big space
	twospcs := [ [ L!(es[i]) : i in d ] : d in dup | #d eq 2 ];
	foundnew := pivot_repeated_nullspace(L, VSfull, Vbig, twospcs);
	insert_found_frame(~CBD, foundnew, false);

	//Straighten the newly found spaces using the ones we already have.
	es := CBD`EigenSpaces;
	for p in CBD`PosNegPairs do
		if p in duptwo then continue; end if;

		for q in duptwo do
			//See if the pair p and q commute...
			M := [ es[i]*es[j] : i in p, j in q ];
			if forall{k : k in M | IsZero(k)} then continue; end if;

			//If not, straighten!
			findframe_A1_by_straight_A1(~CBD, SetToSequence(p), SetToSequence(q));
			break q;
		end for;
	end for;

	assert verify_straight(CBD);
end procedure;
