freeze;

/*
====================================================

Filename: grppermdata.m

Date: 11/03/2009

Description: 

Comments: 

====================================================
*/


// load "grputils.m";
// load "recfrmtdef.m";
//

import "attributes.m": PDF;


forward SVWordInv, SVPermutationInv, StrongGenWord, WordPermutation;


GrpPermData := function(G, B, S, sv, bo)
    /*

    Arguments:

	    G: Permutation group, Type(s): GrpPerm
    
	    B: Base of G, Type(s): SeqEnum

	    S: Strong generating set of G, Type(s): SetIndx

	    sv: Seqeunce of Schreier vectors relative to (B, S), Type(s): SeqEnum

	    bo: Sequence of basic orbits relative to B, Type(s): SeqEnum
    
    Parameters:
    

    Return Type(s):

	    Rec

    Description:
    
	    Returns a record holding BSGS data for G.

    */
    /* for 1 <= i <= #B, 1 <= j <= #bo[i], let g be the permutation defined by sv[i] which takes B[i] to bo[i][j]. For 1 <= k <= #sgindexlist[i], let h_1, h_2 be the permutations defined by sv[i] which take B[i] to the image of B[i] under g * S[sgindexlist[i][k]] and g * (S[sgindexlist[i][k]])^-1 respectively. Then g * S[sgindexlist[i][k]] = t_1 * h_1 and g * (S[sgindexlist[i][k]])^-1 = t_2 * h_2 for some t_1, t_2 in G[i + 1]. The elements tail[i][j][k] and tailinv[i][j][k] are lists of integers defining words over S, which represent t_1 and t_2 respectively. If G is a quotient group E/N of some larger group  E, then g * S[sgindexlist[i][k]] = t_1 * h_1 * n_1 and g * (S[sgindexlist[i][k]])^-1 = t_2 * h_2 * n_2 for some n_1, n_2 in N. The entries utail[i][j][k] and utailinv[i][j][k] act as pointers to the elements n_1 and n_2, a 0 value indicating that the normal subgroup element is trivial. */
    GR := rec<PDF | >;
    GR`G := G;
    GR`natset := GSet(G);
    GR`B := B;
    l := #GR`B;
    GR`S := S;
    GR`Sinv := {@ x^-1: x in S @};
    m := #S;
    GR`bo := bo;
    GR`sv := sv;
    bs := [Stabiliser(G, B[1 .. i - 1]) : i in [1 .. l]];
    sgindexlist:=[[1..m]];
    for i in [2..l] do
	sgindexlist[i] := [k : k in [1 .. m] | S[k] in bs[i]];
    end for;
    GR`sgindexlist := sgindexlist;
    sgindexmap := [[0:k in [1..m]]:i in [1..l]];
    for i := 1 to l do
	for k := 1 to #sgindexlist[i] do
	    sgindexmap[i, sgindexlist[i,k]] := k;
	end for;
    end for;
    GR`sgindexmap := sgindexmap;
    tail := [];
    tailinv := [];
    utail := [];
    utailinv := [];
    gct := 0;
    gctinv := 0;
    for i in [1 .. l] do
	tail[i]:=[];
	tailinv[i] := [];
	utail[i]:= [];
	utailinv[i] := [];
	orb := GR`bo[i];
	v := sv[i];
	sg := sgindexlist[i];
	orbsize := #orb;
	for j in [1 .. orbsize] do
	    tail[i][j]:= [];
	    tailinv[i][j] := [];
	    utail[i][j]:= [];
	    utailinv[i][j] := [];
	    pt := orb[j];
	    nsg := #sg;
	    for k in [1 .. nsg] do
		ipt := pt^S[sg[k]];
		pos := Position(orb, ipt);
		if v[pos] eq sg[k] or v[j] eq -sg[k] then
		    // This image is a definition
		    tail[i][j][k] := [Integers()|];
		    utail[i][j][k] := 0;
		else
		    tail[i][j][k] := StrongGenWord(GR, SVPermutationInv(G, S, v, orb, pt)*S[sg[k]]*SVPermutationInv(G, S, v, orb, ipt)^-1);
		    gct +:= 1;
		    utail[i][j][k] := gct;
		end if;
		ipt := pt^(S[sg[k]]^-1);
		pos := Position(orb, ipt);
		if v[pos] eq -sg[k] or v[j] eq sg[k] then
		    // This image is a definition
		    tailinv[i][j][k] := [Integers()|];
		    utailinv[i][j][k] := 0;
		else
		    tailinv[i][j][k] := StrongGenWord(GR, SVPermutationInv(G, S, v, orb, pt)*(S[sg[k]]^-1)*SVPermutationInv(G, S, v, orb, ipt)^-1);
		    gctinv +:= 1;
		    utailinv[i][j][k] := gctinv;
		end if;
	    end for;
	end for;
    end for;
    GR`tail := tail;
    GR`utail := utail;
    GR`tailinv := tailinv;
    GR`utailinv := utailinv;
    return GR;
end function;


WordInverse := func < x | [ -y : y in Reverse(x) ] >;


SVWordInv := function(G, S, v, orb, pt)
	/*

	Arguments:

		G: Permutation group, Type(s): GrpPerm
	
		S: Strong generating set for G, Type(s): SetIndx

		v: Schreier vector corresponding to orbit orb (with indexing relative to S), Type(s): SeqEnum
	
		orb: Sequence containing exactly the orbit of orb[1] under S, Type(s): SeqEnum

		pt: Element of the set upon which G acts, Type(s): Elt
	
	Parameters:
	

	Return Type(s):

		SeqEnum

	Description:
	
		Returns inverse of what SVWord should return, as an integer sequence i.e. a word in strong generators taking base point to pt as defined by the Schreier vector v.

	*/
	pos := Position(orb, pt);
	r := v[pos];
	w := [];
	while r ne 0 do
		Append(~w, r);
		pt := r gt 0 select pt^(S[r]^-1) else pt^(S[-r]);
		pos := Position(orb, pt);
		r := v[pos];
	end while;
	return Reverse(w);
end function;

SVWordInvProc := procedure(~GR, i, pt, ~w)
    /*
	Procedural version of the above - Bill Unger's code
    */
    G := GR`G;
    S := GR`S;
    Si := GR`Sinv;
    v := GR`sv[i];
    orb := GR`bo[i];
    pos := Position(orb, pt);
    r := v[pos];
    w := [];
    while r ne 0 do
	Append(~w, r);
	pt := r gt 0 select pt^(Si[r]) else pt^(S[-r]);
	pos := Position(orb, pt);
	r := v[pos];
    end while;
    w := Reverse(w);
end procedure;


SVPermutationInv := function(G, S, v, orb, pt)
	/*

	Arguments:

		G: Permutation group, Type(s): GrpPerm
	
		S: Strong generating set for G, Type(s): SetIndx

		v: Schreier vector corresponding to orbit orb (with indexing relative to S), Type(s): SeqEnum
	
		orb: Sequence containing exactly the orbit of orb[1] under S, Type(s): SeqEnum

		pt: Element of the set upon which G acts, Type(s): Elt
	
	Parameters:
	

	Return Type(s):

		GrpPermElt

	Description:
	
		Returns inverse of what SVPermutation should return.  i.e. a permutation (or matrix) at level of basic orbit orb taking base point to pt.

	*/
	pos := Position(orb, pt);
	r := v[pos];
	u := Id(G);
	y := Id(G);
	while r ne 0 do
		y := r gt 0 select S[r]^-1 else S[-r];
		u *:= y;
		pt := pt^y;
		pos := Position(orb, pt);
		r := v[pos];
	end while;
	return u^-1;
end function;


StrongGenWord := function(GR, g)
    /*

    Arguments:

	    GR: Record of type PDF, Type(s): Rec
    
	    g: Element of GR`G, Type(s): GrpPermElt
    
    Parameters:
    

    Return Type(s):

	    SeqEnum

    Description:
    
	    Returns an integer sequence representing a word in the strong generators for g.

    */
    w := [];
    B := GR`B;
    G := GR`G;
    S := GR`S;
    sv := GR`sv;
    bo := GR`bo;
    l := #B;
    for i in [1 .. l] do
	ipt := B[i]^g;
	w := SVWordInv(G, S ,sv[i], bo[i], ipt) cat w;
	g *:= SVPermutationInv(G, S, sv[i], bo[i], ipt)^-1;
    end for;
    return w;
end function;


StrongGenNormalForm := function(GR, g)
	/*

	Arguments:

		GR: Record of type PDF, Type(s): Rec
	
		g: Element of GR`G, Type(s): GrpPermElt
	
	Parameters:
	

	Return Type(s):

		SeqEnum

	Description:
	
		Returns a 2-D integer sequence representing the normal form of g relative to the base and strong generating set held in GR.

	*/
	B := GR`B;
	G := GR`G;
	S := GR`S;
	sv := GR`sv;
	bo := GR`bo;
	nf := [];
	l := #GR`B;
	for i in [1 .. l] do
		ipt := B[i]^g;
		nf[i] := SVWordInv(G, S ,sv[i], bo[i], ipt);
		g *:= WordPermutation(GR, nf[i])^-1;
	end for;
	return nf;
end function;


WordPermutation := function(GR, w)
	/*

	Arguments:

		GR: Record of type PDF, Type(s): Rec
	
		w: Integer sequence representing word over the strong generating set held in GR, Type(s): SeqEnum
	
	Parameters:
	

	Return Type(s):

		GrpPermElt

	Description:
	
		Returns the permutation of GR`G represented by the integer sequence w.

	*/
	g := Id(GR`G);
	if IsEmpty(GR`S) then return g; end if;
	wordlength := #w;
	for i in [1 .. wordlength] do
		g *:= w[i] gt 0 select GR`S[w[i]] else (GR`S[-w[i]])^-1;
	end for;
	return g;
end function;
