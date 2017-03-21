freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspc_notinH, mult_dim_eigenspc;
import "findframemain.m":findframe_all_pairs;

findframe_F4_char2 := procedure(~CBD)
	local dup, L, VSfull, spcs, spcs2;
	
	findeigenspc_notinH(~CBD);
	dup := mult_dim_eigenspc(CBD);
	L := CBD`L;
	VSfull := VectorSpace(BaseRing(L), Dimension(L));
	spcs := [ sub<VSfull | [ Vector(b) : b in CBD`EigenSpaces[d] ]> : d in dup ];
	spcs2 := [ s : s in spcs | Dimension(s) eq 2 ];

	//We have three 8-spaces.
	findframe_eight_using_pairs := function(V)
		local p, LHS, ns, nss, i, j, twospaces, tmpV, VS8;

		//Construct all nullspaces of V wrt the pairs;
		// these are all four-dimensional.
		nss := [];
		for p in spcs2 do
			LHS := VerticalJoin([ HorizontalJoin([ 
				Vector(L!b*L!c) : b in Basis(p) ])
			: c in Basis(V) ]);
			Append(~nss, Nullspace(LHS));
		end for;

		//Intersections of these fourspaces are sometimes
		//  two dimensional, which is useful!
		VS8 := VectorSpace(BaseRing(L), 8);
		twospaces := [];
		tmpV := sub<VS8 | >;
		for i in [1..#nss] do for j in [(i+1)..#nss] do
			ns := nss[i] meet nss[j];
			if Dimension(ns) ne 2 then continue; end if;
			if Dimension(ns meet tmpV) ne 0 then continue; end if;

			//Found new :)
			Append(~twospaces, ns);
			tmpV := sub<VS8 | &cat([ Basis(s) : s in twospaces ])>;

			//Done?
			if Dimension(tmpV) eq 8 then break i; end if;
		end for; end for;

		//Make the spaces found into basisvectors
		twospaces := [ [ Vector(b)*Matrix(Basis(V)) : b in Basis(s) ] : s in twospaces ];

		//Done!
		return twospaces;
	end function;

	//Find frames in the 8-spaces by calls to the above procedure.
	CBD`PosNegPairs := { SequenceToSet(d) : d in dup | #d eq 2 };
	findframe_all_pairs(~CBD);

	for i in [1..#dup] do
		if #dup[i] ne 8 then continue; end if;

		twospaces := findframe_eight_using_pairs(spcs[i]);

		for j in [1..4] do
			CBD`EigenSpaces[dup[i][2*j-1]] := twospaces[j][1];
			CBD`EigenSpaces[dup[i][2*j]] := twospaces[j][2];
			Include(~(CBD`PosNegPairs), { dup[i][2*j-1], dup[i][2*j] });
		end for;
	end for;

	//Finish by straightening the pairs again...	
	findframe_all_pairs(~CBD);
end procedure;
