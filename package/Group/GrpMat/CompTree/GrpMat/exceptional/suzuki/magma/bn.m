/******************************************************************************
 *
 *    bn.m      BN-pair code for Suzuki groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2007-11-26
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: bn.m 1605 2008-12-15 09:05:48Z jbaa004                         $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiBN, 10;

declare attributes GrpMat : SuzukiBNData;

// Information about Suzuki maximal subgroups
SuzukiBNInfo := recformat<
    BNGroups : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function SuzukiStandardBNpair(G)

    F := CoefficientRing(G);
    m := (Degree(F) - 1) div 2;
    _, gens := SuzukiStandardGeneratorsNaturalRep(m);
    q := #F;
    
    // Borel
    B := sub<Generic(G) | gens[2], gens[3]>;
    B`Order := q^2 * (q - 1);
    
    // Torus
    T := sub<Generic(G) | gens[2]>;
    T`Order := q - 1;
    
    // Monomial (torus-normaliser)
    N := sub<Generic(G) | gens[1], gens[2]>;
    N`Order := 2 * (q - 1);
    
    // Weyl 
    W := sub<Generic(G) | gens[1]>;
    W`Order := 2;
    
    // Unipotent
    U := sub<Generic(G) | [gens[3]^(gens[2]^i) : i in [1 .. Degree(F)]]>;
    U`Order := q^2;
    
    assert assigned G`RandomProcess;
    groups := [B, N, U, T, W];
    slps := [[slp where _, slp is
	SuzukiStandardConstructiveMembership(G, g : CheckInput := false,
	Randomiser := G`RandomProcess) :
	g in UserGenerators(H)] : H in groups];

    return groups, slps;
end function;

intrinsic SuzukiBNpair(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Suzuki group,
    return B,N,U,T,W of G.

    Also returns lists of SLPs of the generators of the subgroups, in
    the generators of G. }
    local maximals, slps;
    
    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    if assigned G`SuzukiBNData then
	return G`SuzukiBNData`BNGroups, G`SuzukiBNData`slps;
    end if;

    assert assigned G`SuzukiReductionData`stdCopy;
    if not assigned G`SuzukiReductionData`stdCopy`SuzukiBNData then
	vprint SuzukiBN, 1:
	    "Construct BN groups of standard copy";
	
	bnGroups, slps :=
	    SuzukiStandardBNpair(G`SuzukiReductionData`stdCopy);
	G`SuzukiReductionData`stdCopy`SuzukiBNData :=
	    rec<SuzukiBNInfo |
	    BNGroups := bnGroups, slps := slps>;
    end if;

    // Use explicit isomorphism to obtain maximals in input copy
    bnGroups := [sub<Generic(G) | G`SuzukiReductionData`slpHomo(slps)> :
	slps in G`SuzukiReductionData`stdCopy`SuzukiBNData`slps];

    // Take orders from standard copies
    for i in [1 .. #bnGroups] do
	bnGroups[i]`Order :=
	    G`SuzukiReductionData`stdCopy`SuzukiBNData`BNGroups[i]`Order;
    end for;
    
    G`SuzukiBNData := rec<SuzukiBNInfo |
	BNGroups := bnGroups,
	slps := G`SuzukiReductionData`stdCopy`SuzukiBNData`slps>;

    return G`SuzukiBNData`BNGroups, G`SuzukiBNData`slps;
end intrinsic;
