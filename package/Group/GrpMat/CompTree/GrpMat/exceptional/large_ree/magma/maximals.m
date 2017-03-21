/******************************************************************************
 *
 *    maximals.m Big Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-07-28
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: maximals.m 1605 2008-12-15 09:05:48Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "standard.m" : getLargeReeRobStandardGenerators, getLargeReeOrder;
import "ree.m" : LargeReeSzWreath2Info, LargeReeSzParabolicInfo;
import "involution.m" : checkCentraliserCompletion;
import "conjugate.m" : findSzInParabolic;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/basics.m" : MatSLP;

forward findSzWreath2, findSzParabolic;

declare verbose LargeReeMaximals, 10;

// Information about Big Ree maximals
LargeReeMaximalsInfo := recformat<
    maximals : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/
	
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeMaximalSubgroups(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Large Ree group,
    find a list of representatives of the maximal subgroups of G. }
    local slp, isStdCopy;
    
    if not assigned G`LargeReeReductionData then
	error "G must be a recognised Large Ree group";
    end if;

    if assigned G`LargeReeMaximals then
	return G`LargeReeMaximals`maximals, G`LargeReeMaximals`slps;
    end if;

    // If G is not the standard copy, we already have some maximals
    isStdCopy := LargeReeStandardRecogniser(G);

    assert assigned G`LargeReeReductionData`stdCopy;
    if not assigned G`LargeReeReductionData`stdCopy`LargeReeMaximals then

	vprint LargeReeGeneral, 1:
	    "Construct maximals subgroups of standard copy";
	maximals, slps :=
	    LargeReeStandardMaximalSubgroups(G`LargeReeReductionData`stdCopy :
	    wordGroup := WordGroup(G),
	    isStdCopy := isStdCopy);

	// Save maximals to avoid recomputation
	G`LargeReeReductionData`stdCopy`LargeReeMaximals :=
	    rec<LargeReeMaximalsInfo |
	    maximals := maximals,
	    slps := slps>;
    end if;

    // Use explicit isomorphism to obtain maximals in input copy
    maximals := [sub<Generic(G) | G`LargeReeReductionData`slpHomo(gens)> :
	gens in G`LargeReeReductionData`stdCopy`LargeReeMaximals`slps];

    // Add already computed maximals
    if not isStdCopy then
	assert assigned G`LargeReeSzParabolicData;
	assert assigned G`LargeReeSzWreath2Data;

	maximals cat:= [G`LargeReeSzParabolicData`parabolic,
	    G`LargeReeSzWreath2Data`group];
	slps cat:= [G`LargeReeSzParabolicData`parabolicSLPs,
	    G`LargeReeSzWreath2Data`slps];
    end if;
    
    // Save maximals to avoid recomputation
    G`LargeReeMaximals := rec<LargeReeMaximalsInfo |
	maximals := maximals,
	slps := slps>;

    return maximals, slps;
end intrinsic;

intrinsic LargeReeStandardMaximalSubgroups(G :: GrpMat :
    wordGroup := WordGroup(G), isStdCopy := false) -> [], []
    { G must be the standard Ree copy. Find a list of representatives of some
    of the maximal subgroups of G, as well as SLPs of their generators. }

    if not assigned G`LargeReeMembershipData then
	error "G must be a recognised standard Large Ree copy";
    end if;

    F := CoefficientRing(G);
    q := #F;
    p := Characteristic(F);
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    assert assigned G`RandomProcess;
    
    maximals := [];
    slps := [];

    // Find Rob's standard generators
    gens := getLargeReeRobStandardGenerators(F);

    // Torus
    T := sub<Generic(G) | gens[1], gens[2]>;

    // Use Rob's notation
    x := gens[7];
    sigma := gens[4];
    z := gens[5];
    rho := gens[3];
    t := gens[6];
    
    vprint LargeReeMaximals, 2 : "Find smaller Ree";
    
    // Add Ree's over subfields
    for deg in {x : x in Divisors(Degree(F)) | x gt 1 and x lt Degree(F)} do
	assert IsDivisibleBy(q - 1, p^deg - 1);
	power := (q - 1) div (p^deg - 1);

	maximal := sub<Generic(G) | gens[2]^power, rho * sigma * x>;
	maximal`Order := getLargeReeOrder(p^deg);
	Append(~maximals, maximal);
    end for;
        
    // Unipotent part of L2 parabolic
    L2_unipotent := sub<Generic(G) | x, x^sigma, x^(sigma * rho),
	x^(sigma * rho * sigma), t, t^rho, t^(rho * sigma),
	t^(rho * sigma * rho)>;

    // L2 parabolic
    maximal := sub<Generic(G) | T, sigma, t, L2_unipotent>;
    maximal`Order := q^11 * #SL(2, q) * (q - 1);
    Append(~maximals, maximal);
    
    // Sp_4 : 2 
    maximal := sub<Generic(G) | T, sigma, t, rho, rho * sigma * rho>;
    maximal`Order := 2 * #Sp(4, q);
    Append(~maximals, maximal);
    
    vprint LargeReeMaximals, 2 : "Get SLPs of maximal subgroup gens";

    // Get SLPs for maximal subgroup generators
    for maximal in maximals do
	Append(~slps, [slp where _, slp is
	    LargeReeStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := wordGroup) :
	    g in UserGenerators(maximal)]);
    end for;

    if isStdCopy then
	// The original group is the standard copy, so we need to find
	// a parabolic and Sz \wr 2
	
	vprint LargeReeMaximals, 2 : "Find Sz \wr 2";
	
	// Sz \wr 2
	if not assigned G`LargeReeSzWreath2Data then
	    findSzWreath2(G, wordGroup);
	end if;
	
	Append(~maximals, G`LargeReeSzWreath2Data`group);
	Append(~slps, [G`LargeReeReductionData`slpGroup ! g :
	    g in G`LargeReeSzWreath2Data`slps]);
	
	vprint LargeReeMaximals, 2 : "Find Sz parabolic";
	
	// Sz parabolic
	if not assigned G`LargeReeSzParabolicData then
	    findSzParabolic(G, wordGroup);
	end if;
	
	Append(~maximals, G`LargeReeSzParabolicData`group);
	Append(~slps, [G`LargeReeReductionData`slpGroup ! g :
	    g in G`LargeReeSzParabolicData`slps]);
    end if;
    
    return maximals, slps;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Split up modules for given Sz, recognise Sz, return structure for Sz \wr 2
function recogniseSzWreath2(G, SZ, slps, SZ1, slps1, SZ2, slps2,
    conj, wordGroup, q)
    
    szSmall := [];
    slpMaps := [* *];
    
    for S in [SZ1, SZ2] do
	// Split up Sz to get 4-dim natural
	M := GModule(S);
	M4 := rep{f[1] : f in ConstituentsWithMultiplicities(M) |
	    Dimension(f[1]) eq 4 and f[2] eq 4};
	SZ4 := ActionGroup(M4);
	
	vprint LargeReeMaximals, 5 : "Recognise Sz";
	flag := RecogniseSz(SZ4 : Verify := false, FieldSize := q);
	assert flag;
	
	Append(~szSmall, SZ4);
	Append(~slpMaps, hom<WordGroup(SZ4) -> S | UserGenerators(S)>);
    end for;

    // Set order
    SZ`Order := (#Sz(q))^2 * 2;

    // Store information
    return rec<LargeReeSzWreath2Info |
	group := SZ, sz1 := SZ1, sz2 := SZ2, conj := conj,
	slps := slps, sz1slps := slps1, sz2slps := slps2,
	slpMap1 := slpMaps[1], slpMap2 := slpMaps[2],
	sz1small := szSmall[1], sz2small := szSmall[2],
	slpCoercion1 := hom<WordGroup(szSmall[1]) -> wordGroup | slps1>,
    slpCoercion2 := hom<WordGroup(szSmall[2]) -> wordGroup | slps2>>;
end function;

// Construct Sz \wr 2 from Rob's generators
// If G already has a stored Sz \wr 2, nothing is done, unless RandomConjugate
// is true, in which case a random conjugate is returned.
procedure findSzWreath2(G, wordGroup : RandomConjugate := false)
    local z, sigma, rho, T, SZ, SZ_commute, SZ_2, slp, conj, slps1, slps2;

    F := CoefficientRing(G);
    q := #F;

    if not assigned G`LargeReeSzWreath2Data then
	gens := getLargeReeRobStandardGenerators(CoefficientRing(G));
	rho := gens[3];
	sigma := gens[4];
	z := gens[5];
	
	// Sz
	SZ := sub<Generic(G) | z^(sigma * rho * sigma), rho, gens[2]>;
	SZ_commute := SZ^(sigma * rho * sigma);
	assert forall{<g, h> : g in Generators(SZ),
	    h in Generators(SZ_commute) | g^h eq g};
	
	// Sz \wr 2, two possibilites
	SZ_2 := sub<Generic(G) | z^(sigma * rho * sigma), rho,
	    sigma * rho * sigma, gens[1], gens[2]>;

	// Obtain the wreathing 2, ie the conjugator of the two Sz in Sz \wr 2
	flag, slp := LargeReeStandardConstructiveMembership(G,
	    sigma * rho * sigma : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := wordGroup);
	assert flag;
	conj := rec<MatSLP | mat := sigma * rho * sigma, slp := slp>;

	// Obtain SLPs of first Sz
	slps1 := [slp where _, slp is
	    LargeReeStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := wordGroup) :
	    g in UserGenerators(SZ)];

	// Obtain SLPs of second Sz
	slps2 := [w^conj`slp : w in slps1];

	// Obtain SLPs of Sz \wr 2
	slps := [slp where _, slp is
	    LargeReeStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := wordGroup) :
	    g in UserGenerators(SZ_2)];

	// Recognise Sz's and store structure
	G`LargeReeSzWreath2Data := recogniseSzWreath2(G, SZ_2, slps, SZ, slps1,
	    SZ_commute, slps2, conj, wordGroup, q);
    else
	if RandomConjugate then
	    // Take a random conjugate of Sz \wr 2
	    assert assigned G`RandomProcess;
	    g, w := Random(G`RandomProcess);

	    // Conjugate groups
	    SZ := G`LargeReeSzWreath2Data`group^g;
	    SZ1 := G`LargeReeSzWreath2Data`sz1^g;
	    SZ2 := G`LargeReeSzWreath2Data`sz2^g;

	    // Conjugate SLPs
	    slps := G`LargeReeSzWreath2Data`slps^w;
	    slps1 := G`LargeReeSzWreath2Data`sz1slps^w;
	    slps2 := G`LargeReeSzWreath2Data`sz2slps^w;
	    conj := rec<MatSLP | mat := G`LargeReeSzWreath2Data`conj`mat^g,
		slp := G`LargeReeSzWreath2Data`conj`slp^w>;

	    // Recognise new Sz's and store structure
	    G`LargeReeSzWreath2Data :=
		recogniseSzWreath2(G, SZ, slps, SZ1, slps1,
		SZ2, slps2, conj, wordGroup, q);
	end if;
    end if;    
end procedure;

// Recognise Sz parabolic P
// HG should be the contained involution centraliser
// centSLPs are SLPs of HG generators
// invol is the centralised involution
// wordGroup is the 
function recogniseSzParabolic(G, P, HG, centSLPs, invol, q, wordGroup)

    // Construct kernel gens etc
    repeat
	flag := checkCentraliserCompletion(HG, G, invol`mat, centSLPs);
    until flag;

    // Set order and recognise Sz in parabolic
    P`Order := q^10 * #Sz(q) * (q - 1);
    return findSzInParabolic(HG, wordGroup, q);
end function;

// Construct an Sz parabolic from Rob's generators
// If G already has a stored Sz parabolic, nothing is done,
// unless RandomConjugate is true, in which case a random
// conjugate is returned.
procedure findSzParabolic(G, wordGroup : RandomConjugate := false)
    
    F := CoefficientRing(G);
    q := #F;

    if not assigned G`LargeReeSzParabolicData then
	// This should only happen if we are in the standard copy already
	assert LargeReeStandardRecogniser(G);
	
	gens := getLargeReeRobStandardGenerators(CoefficientRing(G));
	rho := gens[3];
	sigma := gens[4];
	z := gens[5];
	x := gens[7];
	t := gens[6];
	
	// Parabolic of Sz type, two possibilities
	P_SZ := sub<Generic(G) | t, rho, x, z^(sigma * rho * sigma),
	    gens[2], gens[1]>;

	// We also want involution centraliser
	H, H_slps := DerivedGroupMonteCarlo(P_SZ);
	
	// Obtain SLPs of parabolic
	slps := [slp where _, slp is
	    LargeReeStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess, wordGroup := wordGroup) :
	    g in UserGenerators(P_SZ)];
	
	// A random involution should be central and of Sz type 
	R := RandomProcessWithWords(H : Scramble := 1,
	    WordGroup := WordGroup(H));
	repeat
	    j, w := RandomInvolution(H : Randomiser := R);
	until LargeReeInvolutionClass(j) eq "2A" and
	    forall{g : g in Generators(H) | j^g eq j};
	invol := rec<MatSLP | mat := j, slp :=
	    Evaluate(Evaluate(w, H_slps), slps)>;
	
	// Put involution as the first generator, as required by the code
	HG := sub<Generic(G) | invol`mat, H>;
	centSLPs := [invol`slp] cat Evaluate(H_slps, slps);

	// Recognise Sz in parabolic and store data
	G`LargeReeSzParabolicData := recogniseSzParabolic(G, P_SZ, HG,
	    centSLPs, invol, q, wordGroup);
	G`LargeReeSzParabolicData`parabolic := P_SZ;
	G`LargeReeSzParabolicData`parabolicSLPs := slps;
    else
	if RandomConjugate then
	    // Take a random conjugate of the parabolic
	    assert assigned G`RandomProcess;
	    g, w := Random(G`RandomProcess);
	    
	    C := G`LargeReeSzParabolicData`group^g;
	    slps := G`LargeReeSzParabolicData`slps^w;
	    invol := rec<MatSLP | mat := C.1, slp := slps[1]>;
	    
	    // Recognise new parabolic
	    G`LargeReeSzParabolicData :=
		recogniseSzParabolic(G, C, slps, invol, q, wordGroup);
	end if;
    end if;    
end procedure;
