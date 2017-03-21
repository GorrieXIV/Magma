freeze;

/*
====================================================

Filename: pcbfarithmetic.m

Date: 24/02/2009

Description: 

Comments: 

====================================================
*/


import "grppermdata.m": SVPermutationInv, SVWordInv, WordPermutation, 
    StrongGenWordi, SVWordInvProc;
import "construct.m": make_pcbf_elt;

PCBFNSEConjugateByWord := function(EG, a, w)
    /*

    Arguments:

	    EG: PCBF-group, Type(s): Rec
    
	    a: Element of EG`N, Type(s): GrpPCElt or GrpGPCElt

	    w: Sequence of integers representing a word in the preimages of the strong generators of the quotient group EG`Q, Type(s): SeqEnum
    
    Parameters:
    

    Return Type(s):

	    GrpPCElt or GrpGPCElt

    Description:
    
	    Returns the conjugate of the element a by the element of EG represented by w.

    */
    N := EG`N;
    if a eq Id(N) or #w eq 0 then return a; end if;
    y := a;
    for i in [1 .. #w] do
	yseq := Eltseq(y);
	y := Identity(N);
	for j in [1 .. #yseq] do
	    y *:= w[i] gt 0
		select
		    EG`PCGC[w[i]][j]^yseq[j]
		else
		    EG`PCGCI[-w[i]][j]^yseq[j];
	end for;
    end for;
    return y;
end function;

intrinsic PCBFMult(EG::GrpPCBF, ele1::GrpPCBFElt, ele2::GrpPCBFElt) -> GrpPCBFElt
{}
    /*

    Arguments:

	    EG: PCBF-group, Type(s): Rec
    
	    ele1: Element of EG, Type(s): Tup

	    ele2: Element of EG, Type(s): Tup
    
    Parameters:
    

    Return Type(s):

	    Tup

    Description:
    
	    Computes the product ele1 * ele2.

    */
    GR := EG`GR;
    N := EG`N;
    tailelts := EG`tailelts;
    taileltsinv := EG`taileltsinv;

    B := GR`B;
    S := GR`S;
    Sinv := GR`Sinv;
    bo := GR`bo;
    tail := GR`tail;
    tailinv := GR`tailinv;
    utail := GR`utail;
    utailinv := GR`utailinv;
    sgindexmap := GR`sgindexmap;

    l := #B;
    u := [[Integers()|]:i in [1..l]];
    rightword := &cat Reverse(ele2`u);
// #rightword;
    leftword := [];
    n_arr := [];
    n := ele1`n;
    e1u := ele1`u;
    for i in [1 .. l] do
	pt := B[i];
	for let in e1u[i] do
	    pt := pt ^ (let gt 0 select S[let] else Sinv[-let]);
	end for;
	boi := bo[i];
	taili := tail[i];
	tailinvi := tailinv[i];
	utaili := utail[i];
	utailinvi := utailinv[i];
	sgindexmapi := sgindexmap[i];
	for let in rightword do
	    n := PCBFConjByWord(EG, n, let);
	    j := Position(boi, pt);
	    if let lt 0 then
		pt := pt^(Sinv[-let]);
		k := sgindexmapi[-let];
		leftword cat:= tailinvi[j,k];
		utijk := utailinvi[j,k];
		if utijk ne 0 then
		    n := taileltsinv[utijk] * n;
		end if;	
	    else
		pt := pt^(S[let]);
		k := sgindexmapi[let];
		leftword cat:= taili[j,k];
		utijk := utaili[j,k];
		if utijk ne 0 then
		    n := tailelts[utijk] * n;
		end if;
	    end if;
	end for;
	n_arr[i] := n;
	n := Id(N);
	SVWordInvProc(~GR, i, pt, ~u[i]);
	rightword := leftword;
// #rightword;
	leftword := [];
    end for;
    n := n_arr[l];
    for i :=  l-1 to 1 by -1 do
	n := PCBFConjByWord(EG, n, u[i]) * n_arr[i];
    end for;
    res := PCBFEltNew(EG);
    res`u := u;
    res`n := n * ele2`n;
    return res;
end intrinsic;

/*
intrinsic '*'(x::GrpPCBFElt, y::GrpPCBFElt) -> GrpPCBFElt
{The product of x and y}
    // require Parent(x) eq Parent(y): "not compatible";
    return PCBFMult(Parent(x), x, y);
end intrinsic;
*/

intrinsic Inverse(ele::GrpPCBFElt) -> GrpPCBFElt
{The inverse of ele}
    G := Parent(ele);
    x := CreateElement(G, Rho(ele)^-1, Id(G`N));
    m := PCBFMult(G, ele, x)`n;
    return make_pcbf_elt(G, x`u, m^-1); 
end intrinsic;

/*
intrinsic '^'(x::GrpPCBFElt, n::RngIntElt) -> GrpPCBFElt
{x to the n-th power}
    if n eq 0 then return Identity(Parent(x)); end if;
    if n lt 0 then
	x := Inverse(x); n := -n;
    end if;
    if n eq 1 then return x; end if;
    a := Identity(Parent(x));
    repeat
	n, r := Quotrem(n, 2);
	if r eq 1 then a := a*x; end if;
	x := x*x;
    until n eq 1;
    return a*x;
end intrinsic;
*/
