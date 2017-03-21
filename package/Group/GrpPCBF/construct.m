freeze;

/*
====================================================

Filename: pcbfconstruct.m

Date: 24/02/2009

Description: 

Comments: 

====================================================
*/

import "grppermdata.m": GrpPermData, StrongGenNormalForm, SVWordInv,
	WordInverse, SVPermutationInv, StrongGenWord,
	WordPermutation;

import "grputils.m": WordMultiply;

make_pcbf_elt := function(G, u, n)
    e := PCBFEltNew(G);
    e`u := u;
    e`n := n;
    return e;
end function;

PCBFMasterConstruct := function(E, L, Q, rho)
    /*

    Arguments:

	    E: Polycyclic-by-finite group, Type(s): Grp
    
	    L: Polycyclic normal subgroup of E, Type(s): GrpPerm, GrpMat

	    Q: Quotient E/L (finite), Type(s): GrpPerm

	    rho: Natural map E -> Q, Type(s): Map
    
    Parameters:
    

    Return Type(s):

	    Rec

    Description:
    
	    Returns a record representing a PCBF-group isomorphic to E, with normal polycyclic subgroup and quotient ismorphic to L and Q respectively.

    */
    EG := PCBFNew();
    EG`E := E;
    EG`L := L;
    EG`Q := Q;
    B := Base(Q);
    S := StrongGenerators(Q);
    bo := BasicOrbits(Q);
    sv := SchreierVectors(Q);
    GR := GrpPermData(Q, B, S, sv, bo);
    EG`GR := GR;
    assert assigned EG`GR;
    EG`rho := rho;
    strgenpreimgs := (GR`S)@@rho;
    EG`strgenpreimgs := strgenpreimgs;
    // the following only works if L is of the type GrpPerm, GrpMat,
    // GrpAb or GrpGPC, phi : L -> N is an isomorphism onto the
    // polycyclically presented group N
    if IsFinite(L) then
	N, phi := PCGroup(L);
    else
	N, phi := GPCGroup(L);
    end if;
    pcgens := PCGenerators(N);
    r := #pcgens;
    m := #strgenpreimgs;
    PCGC := [];
    PCGCI := [];
    for i in [1 .. m] do
	PCGC[i] := [N | ];
	PCGCI[i] := [N | ];
	xim := strgenpreimgs[i];
	for j in [1 .. r] do
	    // computing conjugates of the jth polycyclic generator with
	    // the ith preimage of the strong generating set of Q and its inverse
	    yim := (pcgens[j])@@phi;
	    PCGC[i][j] := phi(yim^xim); // stored as an element of N
	    PCGCI[i][j] := phi(yim^(xim^-1)); // stored as an element of N
	end for;
    end for;
    l := #GR`B; // number of elements in the stored base of the quotient group
    tail := GR`tail;
    tailinv := GR`tailinv;
    utail := GR`utail;
    utailinv := GR`utailinv;
    h := [];
    g := [];
    w := [];
    tailelts := [N | ];
    taileltsinv := [N | ];
    for i in [1..l] do
	orb := GR`bo[i];
	v := GR`sv[i];
	sg := GR`sgindexlist[i];
	for j in [1..#orb] do
	    pt := orb[j];
	    for k in [1..#sg] do
		g := SVWordInv(Q, S, v, orb, pt);
		if utail[i][j][k] ne 0 then
		    ipt := pt^S[sg[k]];
		    h := SVWordInv(Q, S, v, orb, ipt);
		    w := WordInverse(h) cat
			WordInverse(tail[i][j][k]) cat g cat [sg[k]];
		    tailelts[utail[i][j][k]] := phi(WordMultiply(strgenpreimgs, w));
		end if;
		if utailinv[i][j][k] ne 0 then
		    ipt := pt^(S[sg[k]]^-1);
		    h := SVWordInv(Q, S, v, orb, ipt);
		    w := WordInverse(h) cat
			WordInverse(tailinv[i][j][k]) cat g cat [-sg[k]];
		    taileltsinv[utailinv[i][j][k]] :=
			    phi(WordMultiply(strgenpreimgs, w));
		end if;
	    end for;
	end for;
    end for;
    EG`pcgens := pcgens;
    EG`PCGC := PCGC;
    EG`PCGCI := PCGCI;
    EG`tailelts := tailelts;
    EG`taileltsinv := taileltsinv;
    EG`N := N;
    EG`phi := phi;
    assert assigned EG`GR;
    e := CreateElement(EG, Id(GR`G), Id(N));
    assert assigned EG`GR;
    EG`e := e;
    EG`ismaster := true;
    EG`strgenpreimgsnf := [];
    EG`strgenpreimgsnfinv := [];
    for i in [1 .. #GR`S] do
	EG`strgenpreimgsnf[i] := CreateElement(EG, S[i], Id(N));
	EG`strgenpreimgsnfinv[i] := CreateElement(EG, S[i]^-1, Id(N));
    end for;
    EG`pcgensnf := [];
    for i in [1 .. #pcgens] do
	EG`pcgensnf[i] := make_pcbf_elt(EG, e`u, pcgens[i]);
    end for;
    EG`grpgens := EG`strgenpreimgsnf cat EG`pcgensnf;
    return EG;
end function;

intrinsic PolycyclicByFiniteGroup(E::GrpPerm, L::GrpPerm, Q::GrpPerm, rho::Map) -> GrpPCBF
    { Constructs a group of type GrpPCBF isomorphic to E }
    require IsNormal(E, L): "L is not a normal subgroup of E";
    require IsSoluble(L): "L is not soluble";
    return PCBFMasterConstruct(E, L, Q, rho);
end intrinsic;

PCBFrho := function(EG, ele)
/*
 *         Arguments:
 *                EG: PCBF-group
 *                ele: Element of EG
 *
 *         Return Type(s):
 *                GrpPermElt
 *
 *         Description:
 *                Returns the image of the element ele of EG under the
 *                natural map onto the quotient EG`Q.
 *
 * 
 */ 
        word := [];
        for i in [#ele`u .. 1 by -1] do
                word cat:= ele`u[i]; // u field specifies a word in the strong generators of the quotient group
        end for;
	return WordPermutation(EG`GR, word);
end function;

intrinsic Rho(x::GrpPCBFElt) -> GrpElt
{The image of x in the defining quotient group}
    return PCBFrho(Parent(x), x);
end intrinsic;


intrinsic GeneratorsSequence(EG::GrpPCBF) -> SeqEnum
{The generators of EG as a sequence}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):

		SeqEnum

	Description:
	
		Returns a sequence containing a full generating set for EG.

	*/
	return EG`grpgens;
end intrinsic;

intrinsic Ngens(EG::GrpPCBF) -> RngIntElt
{The number of defining generators for EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):

		RngIntElt

	Description:
	
		Returns the number of defining generators for EG.

	*/
	return #EG`grpgens;
end intrinsic;


/* Not necessary to define NumberOfGenerators, since it's
   defined to be identical to Ngens in bind/n.b */



intrinsic QuotientGroup(EG::GrpPCBF) -> Grp
{The defining finite quotient of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):

		GrpPerm

	Description:
	
		Returns a permutation group isomorphic to the quotient group used to construct EG.

	*/
	return EG`Q;
end intrinsic;


intrinsic NormalSubgroup(EG::GrpPCBF) -> Grp
{The defining polycyclic normal subgroup of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		GrpPC or GrpGPC

	Description:
	
		Returns a polycyclically presented group isomorphic to the normal subgroup group used to construct EG.

	*/
	return EG`N;
end intrinsic;


intrinsic SuperGroup(EG::GrpPCBF) -> GrpPCBF
{}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		Rec

	Description:
	
		Returns the PCBF-group from which EG was primarily derived.

	*/
	return EG`ismaster select EG else EG`supergrp;
end intrinsic;


intrinsic Order(EG::GrpPCBF) -> RngIntElt
{The order of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		RngIntElt

	Description:
	
		Returns the order of the PCBF-group EG.

	*/
	return Order(QuotientGroup(EG)) * Order(NormalSubgroup(EG));
end intrinsic;


intrinsic IsFinite(EG::GrpPCBF) -> BoolElt
{Return true if and only if EG is finite}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if EG is a finite group.

	*/
	return IsFinite(EG`N);
end intrinsic;


intrinsic IsTrivial(EG::GrpPCBF) -> BoolElt
{Returns true if and only if EG is a trivial group}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if EG is trivial.

	*/
	return IsTrivial(QuotientGroup(EG)) and IsTrivial(NormalSubgroup(EG));
end intrinsic;


intrinsic IsSoluble(EG::GrpPCBF) -> BoolElt
{Returns true if and only if EG is soluble}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if EG is soluble.

	*/
	return IsSoluble(QuotientGroup(EG));
end intrinsic;

intrinsic CreateElement(EG::GrpPCBF, g::GrpElt, n::GrpElt) -> GrpPCBFElt
{The element of EG representing the pair (g,n), g in defining quotient
of EG, n in defining normal subgroup of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
		g: Element of EG`Q, Type(s): GrpPermElt

		n: Element of EG`N, Type(s): GrpPCElt or GrpGPCElt
	
	Parameters:
	

	Return Type(s):

		Tup

	Description:
	
		Returns an ordered pair representing the element (g, n) of EG.

	*/
	require g in EG`Q: "2nd argument not in defining quotient";
	require n in EG`N: "3rd argument not in defining normal subgroup";
	x := PCBFEltNew(EG);
	x`u := StrongGenNormalForm(EG`GR, g);
	x`n := n;
	return x;
end intrinsic;


intrinsic Identity(EG::GrpPCBF) -> GrpPCBFElt
{The identity element of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
	

	Return Type(s):
	
		Tup

	Description:
	
		Returns the identity element of EG.

	*/
	return EG`e;
end intrinsic;

intrinsic Phi(ele::GrpPCBFElt) -> GrpElt
{The second component of ele}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec

		ele: Element of EG, Type(s): Tup
	
	Parameters:
	

	Return Type(s):
	
		GrpPCElt or GrpGPCElt

	Description:
	
		Returns the second component of the ordered pair ele. This is NOT a homomorphism as no check is made to determine whether ele represents an element of the normal subgroup used in the construction of EG.

	*/
	return ele`n;
end intrinsic;


intrinsic PhiInverse(EG::GrpPCBF, n::GrpPCElt) -> GrpPCBFElt
{The embedding of n in EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec

		ele: Element of EG`N, Type(s): GrpPCElt or GrpGPCElt
	
	Parameters:
	

	Return Type(s):
	
		Tup

	Description:
	
		Returns image in EG of the element n of EG`N.

	*/
	fl, x := IsCoercible(EG`N, n);
	require fl: "Unable to coerce into defining normal subgroup";
	return make_pcbf_elt(EG, (EG`e)`u, x);
end intrinsic;


intrinsic PCBFElteq(ele1::GrpPCBFElt, ele2::GrpPCBFElt) -> BoolElt
{true if and only if ele1 and ele2 are equal}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec

		ele1: Element of EG, Type(s): Tup

		ele2: Element of EG, Type(s): Tup
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if ele1 and ele2 are equal in EG.

	*/
	EG := Parent(ele1);
	if EG ne Parent(ele2) then return false; end if;
	return Rho(ele1) eq Rho(ele2) and Phi(ele1) eq Phi(ele2);
end intrinsic;


intrinsic PCBFEltne(ele1::GrpPCBFElt, ele2::GrpPCBFElt) -> BoolElt
{}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec

		ele1: Element of EG, Type(s): Tup

		ele2: Element of EG, Type(s): Tup
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if ele1 and ele2 are not equal in EG.

	*/
	return not PCBFElteq(ele1, ele2);
end intrinsic;


intrinsic IsIdentity(ele::GrpPCBFElt) -> BoolElt
{True if and only if ele is the identity element}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec

		ele: Element of EG, Type(s): Tup
	
	Parameters:
	

	Return Type(s):
	
		BoolElt

	Description:
	
		Returns true if and only if ele is the identity element of EG.

	*/
	return PCBFElteq(ele, Identity(Parent(ele)));
end intrinsic;

intrinsic Random(EG::GrpPCBF) -> GrpPCBFElt
{A random element of EG}

	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
		

	Return Type(s):

		Tup

	Description:
	
		Generates a pseudo-random element of EG.

	*/
	g := Random(EG`Q);
	n := Random(EG`N);
	return CreateElement(EG, g, n);
end intrinsic;


intrinsic RandomSequence(EG::GrpPCBF, l::RngIntElt) -> SeqEnum
{A sequence of length l of random elements of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
		

	Return Type(s):

		SeqEnum

	Description:
	
		Generates a sequence (of length l) of pseudo-random elements of EG.

	*/
	require l ge 0: "length cannot be negative";
	return [Random(EG):i in [1..l]];
end intrinsic;


intrinsic Representative(EG::GrpPCBF) -> GrpPCBFElt
{An element of EG}
	/*

	Arguments:

		EG: PCBF-group, Type(s): Rec
	
	Parameters:
		

	Return Type(s):

		Tup

	Description:
	
		Returns a representative element of EG.

	*/
	return Identity(EG);
end intrinsic;

intrinsic PCBFNormalForm(EG::GrpPCBF, y::GrpElt)-> GrpPCBFElt
{}
        /*
	 *
	 *         Arguments:
	 *
	 *            EG: PCBF-group, Type(s): Rec
	 *                                 
	 *            y: element of original polycyclic-by-finite group, Type(s): -
	 *
	 *         Parameters:
	 *                                                                 
	 *
	 *         Return Type(s):
	 *
	 * 	        GrpPermElt
	 */

    GR := EG`GR;
    strgenpreimgs := EG`strgenpreimgs;
    rho := EG`rho;
    phi := EG`phi;
    cr := StrongGenNormalForm(GR, rho(y));
    ele := y;
    l := #cr;
    for i in [l .. 1 by -1] do
	u := cr[i];
	for j in [1 .. #u] do
	    ele := (u[j] lt 0 select
	       	strgenpreimgs[-u[j]]
	    else (strgenpreimgs[u[j]]^-1)) * ele;
	end for;
    end for;
    return make_pcbf_elt(EG, cr, phi(ele));
end intrinsic;

intrinsic PCBFRevert(EG::GrpPCBF, ele::GrpPCBFElt) -> GrpElt
{Dummy}
        /*
	 *
	 *  Arguments:
	 *
	 *     EG: PCBF-group, Type(s): Rec
	 *                                 
	 *     ele: ordered pair representing an element of the PCBF-group EG,
	 *     Type(s): Tup
	 *                                                  
	 *  Parameters:
	 *                                                                  
	 *
	 *  Return Type(s):
	 *
	 *     -
	 *
	 *  Description:
	 *                                                         
	 *     Returns the element of the original master group represented
	 *     by ele. USED FOR TESTING ONLY.
	 */

    assert EG`ismaster;
    //if not EG`ismaster then
	// recurse if the given group is not a master group
	//return PCBFRevert(EG`supergrp, PCBFiota(EG, ele));
    //end if;
    E := EG`E;
    strgenpreimgs := EG`strgenpreimgs;
    phi := EG`phi;
    ans := Id(E);
    l := #ele`u;
    for i in [l .. 1 by -1] do
	u := ele`u[i];
        for j in [1 .. #u] do
            if u[j] lt 0 then
                ans *:= strgenpreimgs[-u[j]]^-1;
            else
                ans *:= strgenpreimgs[u[j]];
            end if;
        end for;
    end for;
    ans *:= ele`n@@phi;
    return ans;
end intrinsic;

