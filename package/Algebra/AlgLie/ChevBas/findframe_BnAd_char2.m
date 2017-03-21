freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "chevbasmain.m":findeigenspc_notinH, mult_dim_eigenspc;
import "findframemain.m":findframe_comm_quad_pair_pair, findframe_all_pairs;

findframe_Bn_2s_and_4s := procedure(~CBD)
	local dup, dup4, dup2, comm, d, pp, L;

	L := CBD`L;

	dup := mult_dim_eigenspc(CBD);
	dup4 := [ d : d in dup | #d eq 4 ];
	dup2 := [ d : d in dup | #d eq 2 ];

	comm := function(d,e)
		return forall{ <i,j> : i in d, j in e | IsZero(L!(CBD`EigenSpaces[i])*L!(CBD`EigenSpaces[j])) };
	end function;

	CBD`PosNegPairs := { SequenceToSet(d) : d in dup2 };
	for d in dup4 do
		pp := [ e : e in dup2 | not comm(d,e) ];
		if #pp lt 2 then error "Not enough pivot pairs for 4-space."; end if;
		findframe_comm_quad_pair_pair(~CBD, d, pp[1], pp[2]);
	end for;
	findframe_all_pairs(~CBD);
end procedure;

