/******************************************************************************
 *
 *    bn.m      BN-pair code for large Ree groups
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

declare verbose LargeReeBN, 10;

declare attributes GrpMat : LargeReeBNData;

import "standard.m" : getLargeReeRobStandardGenerators;

// Information about Large Ree BN groups
LargeReeBNInfo := recformat<
    BNGroups : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/
    
function LargeReeStandardBNpair(G, wordGroup)

    F := CoefficientRing(G);
    m := (Degree(F) - 1) div 2;
    q := #F;

    gens := getLargeReeRobStandardGenerators(F);
    assert #gens eq 7;
    
    // Use Rob's notation
    x := gens[7];
    sigma := gens[4];
    z := gens[5];
    rho := gens[3];
    t := gens[6];
            
    // Torus
    T := sub<Generic(G) | gens[1], gens[2]>;
    T`Order := (q - 1)^2;

    // Unipotent
    U_base := [x, x^sigma, x^(sigma * rho), x^(sigma * rho * sigma),
	t, t^rho, t^(rho * sigma), t^(rho * sigma * rho)];
    U := sub<Generic(G) | [U_base[j]^(T.2^i) : i in [1 .. Degree(F)],
	j in [1 .. #U_base]]>;
    U`Order := q^12;
    
    // Borel
    B := sub<Generic(G) | U_base, T>;
    B`Order := #U * #T;
    
    // Weyl 
    W := sub<Generic(G) | rho, sigma>;
    W`Order := 16;

    // Monomial (torus-normaliser)
    N := sub<Generic(G) | T, W>;
    N`Order := #W * #T;
            
    assert assigned G`RandomProcess;
    groups := [B, N, T, W];
    slps := [[slp where _, slp is
	LargeReeStandardConstructiveMembership(G, g : CheckInput := false,
	Randomiser := G`RandomProcess, wordGroup := wordGroup) :
	g in UserGenerators(H)] : H in groups];
    
    U_slps := [slps[1][j]^(slps[3][2]^i) : i in [1 .. Degree(F)],
	j in [1 .. NumberOfGenerators(B)]];

    Insert(~groups, 3, U);
    Insert(~slps, 3, U_slps);
    
    return groups, slps;
end function;

intrinsic LargeReeBNpair(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Large Ree group,
    return B,N,U,T,W of G.

    Also returns lists of SLPs of the generators of the subgroups, in
    the generators of G. }
    local maximals, slps;
    
    if not assigned G`LargeReeReductionData then
	error "G must be a recognised Large Ree group";
    end if;

    if assigned G`LargeReeBNData then
	return G`LargeReeBNData`BNGroups, G`LargeReeBNData`slps;
    end if;

    assert assigned G`LargeReeReductionData`stdCopy;
    if not assigned G`LargeReeReductionData`stdCopy`LargeReeBNData then
	vprint LargeReeBN, 1:
	    "Construct BN groups of standard copy";
	
	bnGroups, slps :=
	    LargeReeStandardBNpair(G`LargeReeReductionData`stdCopy,
	    WordGroup(G));
	G`LargeReeReductionData`stdCopy`LargeReeBNData :=
	    rec<LargeReeBNInfo |
	    BNGroups := bnGroups, slps := slps>;
    end if;

    // Use explicit isomorphism to obtain maximals in input copy
    bnGroups := [sub<Generic(G) | G`LargeReeReductionData`slpHomo(slps)> :
	slps in G`LargeReeReductionData`stdCopy`LargeReeBNData`slps];

    // Take orders from standard copies
    for i in [1 .. #bnGroups] do
	bnGroups[i]`Order :=
	    G`LargeReeReductionData`stdCopy`LargeReeBNData`BNGroups[i]`Order;
    end for;
    
    G`LargeReeBNData := rec<LargeReeBNInfo |
	BNGroups := bnGroups,
	slps := G`LargeReeReductionData`stdCopy`LargeReeBNData`slps>;

    return G`LargeReeBNData`BNGroups, G`LargeReeBNData`slps;
end intrinsic;
