/******************************************************************************
 *
 *    sylow.m   Big Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-07-30
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: sylow.m 1605 2008-12-15 09:05:48Z jbaa004                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "standard.m" : getLargeReeRobStandardGenerators, getLargeReeOrder;
import "maximals.m" : findSzWreath2, findSzParabolic;
import "../../../util/basics.m" : MatSLP;

declare verbose LargeReeSylow, 10;

// Stores information about Sylow p-subgroups that are built up from Suzuki
// Sylows
LargeReeSylowInfo := recformat<
    prime : RngIntElt,    // The prime p
    small1 : GrpMat,      // 4-dim Suzuki Sylow
    small2 : GrpMat,      // 4-dim Suzuki Sylow
    small1SLPs : SeqEnum, // SLPs of Suzuki Sylow, in Big Ree gens
    small2SLPs : SeqEnum, // SLPs of Suzuki Sylow, in Big Ree gens
    slps : SeqEnum,       // SLPs of Big Ree Sylow
    szWr2 : Rec,          // LargeReeSzWreath2Data that was used 
    parabolic : Rec,      // LargeReeSzParabolicData that was used 
    ree : GrpMat          // Big Ree group that Sylow comes from
    >;

declare attributes GrpMat : LargeReeSylowData;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/
	    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeSylow(G :: GrpMat, p :: RngIntElt) -> GrpMat, SeqEnum
    { G is isomorphic to LargeRee(q), RecogniseLargeRee(G) has returned true,
    p is a prime. Returns a random Sylow p-subgroup S of G.

    Also returns list of SLPs of the generators of S, in generators of G.
    If p does not divide |G|, then the trivial subgroup is returned.

    This is not implemented if p divides q + 1. }
    
    if not (assigned G`LargeReeReductionData and IsPrime(p)) then
	error "Large Ree Sylow: G must be a recognised Ree and p a prime";
    end if;

    assert assigned G`RandomProcess;
        
    F := CoefficientRing(G);
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    q := #F;
    S := G`LargeReeReductionData`stdCopy;
    
    if not IsDivisibleBy(#S, p) then
	return sub<G | >;
    end if;

    // 2-Sylows consist of centre of an involution centraliser, together with
    // the Sylow of the Sz in the centraliser
    if p eq 2 then
	if not assigned G`LargeReeSzParabolicData then
	    // This should only happen if G is the standard copy
	    assert LargeReeStandardRecogniser(G);
	    findSzParabolic(G, WordGroup(G));
	end if;

	H := G;
	assert assigned H`LargeReeSzParabolicData;
	
	// Find a q-1 element in the parabolic that can be used to obtain
	// the O_2 generators
	repeat
	    flag, g, slp :=
		RandomElementOfOrder(H`LargeReeSzParabolicData`szCyclic,
		q - 1);
	    assert flag;
	    
	until forall{h : h in Generators(H`LargeReeSzParabolicData`sz) |
	    g^h eq g};
	slp := Evaluate(slp, H`LargeReeSzParabolicData`szCyclicSLPs);

	// Obtain all O_2 generators
	if not assigned H`LargeReeSzParabolicData`o2SLPs then
	    o2gens := &cat[[h`mat^(g^i) : i in [1 .. Degree(F)]] :
		h in H`LargeReeSzParabolicData`o2Base] ;
	    o2slps := &cat[[h`slp^(slp^i) : i in [1 .. Degree(F)]] :
		h in H`LargeReeSzParabolicData`o2Base] ;
	    
	    H`LargeReeSzParabolicData`o2 := sub<Generic(H) | o2gens>;
	    H`LargeReeSzParabolicData`o2SLPs := o2slps;
	end if;

	// Find Sz Sylow
	S, S_slps := SuzukiSylow(H`LargeReeSzParabolicData`smallSZ, p);
	slps := H`LargeReeSzParabolicData`slpCoercion(S_slps);

	// Obtain SLPs of all Sylow generators
	slpList := [G`LargeReeReductionData`slpGroup ! g :
	    g in slps cat H`LargeReeSzParabolicData`o2SLPs];
	
	// Obtain matrices in input copy
	gens := G`LargeReeReductionData`slpHomo(slpList);
	
	// Return Sylow subgroup
	GS := sub<Generic(G) | gens>;
	GS`Order := q^12;

	GS`LargeReeSylowData := rec<LargeReeSylowInfo |
	    prime := p, small1 := S, small1SLPs := slps,
	    slps := slpList, ree := G,
	    parabolic := H`LargeReeSzParabolicData>;
	
	return GS, slpList;
    elif exists(o){o : o in [q - 1, q + t + 1, q - t + 1] |
	IsDivisibleBy(o, p)} then

	if not assigned G`LargeReeSzWreath2Data then
	    assert LargeReeStandardRecogniser(G);
	    findSzWreath2(G, WordGroup(G));
	end if;
	H := G;
	
	// Take one Sylow from each Sz in the Sz \wr 2
	S1, l1 := SuzukiSylow(H`LargeReeSzWreath2Data`sz1small, p);
	S2, l2 := SuzukiSylow(H`LargeReeSzWreath2Data`sz2small, p);

	// Obtain Sylow SLPs in the Big Ree generators
	slps1 := H`LargeReeSzWreath2Data`slpCoercion1(l1);
	slps2 := H`LargeReeSzWreath2Data`slpCoercion2(l2);
	slpList := [G`LargeReeReductionData`slpGroup ! g :
	    g in slps1 cat slps2];

	// Obtain matrices in input copy
	gens := G`LargeReeReductionData`slpHomo(slpList);
		
	// Return Sylow subgroup
	GS := sub<Generic(G) | gens>;
	GS`Order := o^2;

	GS`LargeReeSylowData := rec<LargeReeSylowInfo |
	    prime := p, small1 := S1, small2 := S2,
	    small1SLPs := slps1, small2SLPs := slps2,
	    slps := slpList, ree := G,
	    szWr2 := H`LargeReeSzWreath2Data>;
	
	return GS, slpList;
    elif IsDivisibleBy(q + 1, p) then
	// What to do here?
    else
	
	// Other Sylow subgroups are cyclic
	multiple := rep{n : n in [q^2 - q + 1, q^2 + t * q + q + t + 1,
	    q^2 - t * q + q - t + 1] | IsDivisibleBy(n, p)};

	// Find order of cyclic Sylow subgroup
	k, divisor := Valuation(multiple, p);
	order := p^k;
	
	// Find cyclic Sylow subgroup generator
	flag, g, slp := RandomElementOfOrder(S, order :
	    Randomiser := S`RandomProcess, MaxTries := q^2);
	assert flag;
	
	// Return Sylow subgroup
	GS := sub<Generic(G) | G`LargeReeReductionData`slpHomo(slp)>;
	assert Order(GS.1 : Proof := false) eq order;
	
	GS`Order := order;
	return GS, [G`LargeReeReductionData`slpGroup ! slp];
    end if;
end intrinsic;
