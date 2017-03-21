/******************************************************************************
 *
 *    bn.m      BN-pair code for Ree groups
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

declare verbose ReeBN, 10;

declare attributes GrpMat : ReeBNData;

import "standard.m" : standardGeneratorsNaturalRep;

// Information about Suzuki maximal subgroups
ReeBNInfo := recformat<
    BNGroups : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function ReeStandardBNpair(G)

    F := CoefficientRing(G);
    m := (Degree(F) - 1) div 2;
    gens := standardGeneratorsNaturalRep(F);
    q := #F;
    
    // Borel
    B := sub<Generic(G) | gens[2], gens[3]>;
    B`Order := q^3 * (q - 1);
    
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
    U`Order := q^3;
    
    assert assigned G`RandomProcess;
    groups := [B, N, U, T, W];
    slps := [[slp where _, slp is
	ReeStandardConstructiveMembership(G, g : CheckInput := false,
	Randomiser := G`RandomProcess) :
	g in UserGenerators(H)] : H in groups];

    return groups, slps;
end function;

intrinsic ReeBNpair(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Ree group,
    return B,N,U,T,W of G.

    Also returns lists of SLPs of the generators of the subgroups, in
    the generators of G. }
    local maximals, slps;
    
    if not assigned G`ReeReductionData then
	error "G must be a recognised Ree group";
    end if;

    if assigned G`ReeBNData then
	return G`ReeBNData`BNGroups, G`ReeBNData`slps;
    end if;

    assert assigned G`ReeReductionData`stdCopy;
    if not assigned G`ReeReductionData`stdCopy`ReeBNData then
	vprint ReeBN, 1:
	    "Construct BN groups of standard copy";
	
	bnGroups, slps :=
	    ReeStandardBNpair(G`ReeReductionData`stdCopy);
	G`ReeReductionData`stdCopy`ReeBNData :=
	    rec<ReeBNInfo |
	    BNGroups := bnGroups, slps := slps>;
    end if;

    // Use explicit isomorphism to obtain maximals in input copy
    bnGroups := [sub<Generic(G) | G`ReeReductionData`slpHomo(slps)> :
	slps in G`ReeReductionData`stdCopy`ReeBNData`slps];

    // Take orders from standard copies
    for i in [1 .. #bnGroups] do
	bnGroups[i]`Order :=
	    G`ReeReductionData`stdCopy`ReeBNData`BNGroups[i]`Order;
    end for;
    
    G`ReeBNData := rec<ReeBNInfo |
	BNGroups := bnGroups,
	slps := G`ReeReductionData`stdCopy`ReeBNData`slps>;

    return G`ReeBNData`BNGroups, G`ReeBNData`slps;
end intrinsic;
