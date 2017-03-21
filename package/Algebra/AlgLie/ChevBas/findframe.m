freeze;

/* 
 * Dan Roozemond, 2010. 
 */

import "findframemain.m":verify_straight, findframe_all_pairs;
import "chevbasmain.m":findeigenspc_notinH, mult_dim_eigenspc;
import "findframe_A3_char2.m":findframe_A3_nonAd_char2_usingDerL;
import "findframe_BnAd_char2.m":findframe_Bn_2s_and_4s;
import "findframe_BnSC_char2.m":findframe_BnSC_char2;
import "findframe_CnAd_char2.m":findframe_Cn_Ad_char2;
import "findframe_CnSC_char2.m":findframe_Cn_SC_char2;
import "findframe_DnSC_char2.m":findframe_Dn_SC_char2;

/* Note that some of the findframe procedures do exist, 
   but are used directly from the special chevalley basis
   procedures, as they are special cases anyway.

   These are, in particular: F4, G2, B2, C2, D4

	CnSC and B2 (char. 2)  are the only cases where there are root spaces with 
	eigenvalue 0, hence root spaces indistinguishable from H, so we avoid
    calling findeigenspc_notinH there, which normally _is_ useful.
*/

findframe := procedure(~CBD)
	local i, j, tp, rnk, 
		dup, dup_set, dup_multiset, dup_pr;

	//If, for some reason, everything is OK, we don't do anything.
	if verify_straight(CBD) then
		return;
	end if;
	tp := CartanName(CBD`R)[1]; rnk := Rank(CBD`R);

	if (tp eq "C" and IsSimplyConnected(CBD`R))  then
		findframe_Cn_SC_char2(~CBD);
		assert verify_straight(CBD);
		return;
	end if;

	if not assigned CBD`EigenVectors then
		findeigenspc_notinH(~CBD);
	end if;
	dup := mult_dim_eigenspc(CBD);
	dup_set := { #d : d in dup };
	dup_multiset := {* #d : d in dup *};
	dup_pr := [ d : d in dup | #d eq 2 ];

	CBD`PosNegPairs := { Seqset(i) : i in dup_pr };

	//Check what to do
	if dup_set eq {2} then 
		//Do the pairs
		findframe_all_pairs(~CBD);
	elif tp in {"A","D"} and rnk eq 3 and dup_multiset eq {* 4^^3 *} then
		findframe_A3_nonAd_char2_usingDerL(~CBD);
	elif tp eq "B" and dup_set eq {2,4} and IsAdjoint(CBD`R) then
		findframe_Bn_2s_and_4s(~CBD);
	elif tp eq "B" and IsSimplyConnected(CBD`R) then
		findframe_BnSC_char2(~CBD);
	elif tp eq "C" and IsAdjoint(CBD`R) then
		findframe_Cn_Ad_char2(~CBD);
	elif tp eq "D" and IsSimplyConnected(CBD`R) then
		findframe_Dn_SC_char2(~CBD);
	else
		//Not caught. Should do something about that.
		error "Cannot handle these multidimensional eigenspaces of type " cat Sprintf("%o", {* #d : d in dup *});
	end if;

	assert verify_straight(CBD);
end procedure;

