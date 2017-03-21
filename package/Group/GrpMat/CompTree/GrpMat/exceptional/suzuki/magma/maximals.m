/******************************************************************************
 *
 *    maximals.m   Suzuki group package maximal subgroups code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-07-18
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

declare verbose SuzukiMaximals, 10;

import "standard.m" : getSuzukiSylowGen, getSuzukiOrder;
import "sylow.m" : sylow2Conjugation, cyclicSylowConjugation,
    hardSylowConjugation;

forward findHardMaximals, smallerSzConjugation, determineMaximalClass;

MAXIMAL_PARABOLIC   := 1;
MAXIMAL_CYCLIC_EASY := 2;
MAXIMAL_CYCLIC_HARD := 3;
MAXIMAL_SMALLER_SZ  := 4;

// Information about Suzuki maximal subgroups
SuzukiMaximalsInfo := recformat<
    maximals : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiMaximalSubgroups(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Suzuki group,
    find a list of representatives of the maximal subgroups of G.

    Also returns lists of SLPs of the generators of the subgroups, in
    the generators of G. }
    local maximals, slps;
    
    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    if assigned G`SuzukiMaximals then
	return G`SuzukiMaximals`maximals, G`SuzukiMaximals`slps;
    end if;

    assert assigned G`SuzukiReductionData`stdCopy;
    if not assigned G`SuzukiReductionData`stdCopy`SuzukiMaximals then
	vprint SuzukiMaximals, 1:
	    "Construct maximals subgroups of standard copy";
	
	maximals, slps :=
	    SuzukiStandardMaximalSubgroups(G`SuzukiReductionData`stdCopy);
	G`SuzukiReductionData`stdCopy`SuzukiMaximals :=
	    rec<SuzukiMaximalsInfo |
	    maximals := maximals,
	    slps := slps>;
    end if;

    // Use explicit isomorphism to obtain maximals in input copy
    maximals := [sub<Generic(G) | G`SuzukiReductionData`slpHomo(gens)> :
	gens in G`SuzukiReductionData`stdCopy`SuzukiMaximals`slps];

    // Take orders from standard copies
    for i in [1 .. #maximals] do
	maximals[i]`Order :=
	    G`SuzukiReductionData`stdCopy`SuzukiMaximals`maximals[i]`Order;
    end for;
    
    G`SuzukiMaximals := rec<SuzukiMaximalsInfo |
	maximals := maximals,
	slps := G`SuzukiReductionData`stdCopy`SuzukiMaximals`slps>;

    return maximals, G`SuzukiReductionData`stdCopy`SuzukiMaximals`slps;
end intrinsic;

intrinsic SuzukiStandardMaximalSubgroups(G :: GrpMat) -> [], []
    { G is Sz(q), RecogniseSz(G) has returned true.
    Returns a sequence of representatives of conjugacy classes of maximal
    subgroups of G.

    Also returns sequence of sequences of SLPs of the generators of the
    subgroups. }

    if not (assigned G`SuzukiRecognitionData and
	SuzukiStandardRecogniser(G)) then
	error "Sz maximal subgroups: G must be a recognised standard Sz copy";
    end if;

    F := CoefficientRing(G);
    q := #F;
    p := Characteristic(F);
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    assert assigned G`RandomProcess;
    
    maximals := [];
    slps := [];

    // Construct easy maximals
    gens, gens2 := SuzukiStandardGeneratorsNaturalRep(m);
    pointStab := sub<Generic(G) | gens[2], gens2[3]>;
    pointStab`Order := q^2 * (q - 1);
    
    torusNormaliser := sub<Generic(G) | gens[1], gens[2]>;
    torusNormaliser`Order := 2 * (q - 1);
    
    maximals := [pointStab, torusNormaliser];
        
    // Construct hard maximals (ie normalisers of other cyclic groups)
    maximals cat:= findHardMaximals(F, gens);

    // Add Sz's over subfields
    for deg in {x : x in Divisors(Degree(F)) | x gt 1 and x lt Degree(F)} do
	assert IsDivisibleBy(q - 1, p^deg - 1);
	power := (q - 1) div (p^deg - 1);
	
	sz := sub<Generic(G) | gens[1], gens[2]^power, gens2[3]>;
	sz`Order := getSuzukiOrder(p^deg);
	
	Append(~maximals, sz);
    end for;
    
    // Get SLPs for maximal subgroup generators
    for maximal in maximals do
	Append(~slps, [slp where _, slp is
	    SuzukiStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess) : g in UserGenerators(maximal)]);
    end for;
    
    return maximals, slps;
end intrinsic;

intrinsic SuzukiMaximalSubgroupsConjugacy(G :: GrpMat, R :: GrpMat,
    S :: GrpMat) -> GrpMatElt, GrpSLPElt
    { G is Sz(q), RecogniseSz(G) has returned true, R and S are maximal
    subgroup of the same class. Find g in G such that R^g eq S. }
    local F, q;

    if not (assigned G`SuzukiReductionData) then
	error "Sz maximal subgroup conjugation: G must be a recognised Sz";
    end if;
    
    assert assigned G`RandomProcess;

    // Work in standard copy
    vprint SuzukiMaximals, 3 : "Get standard copy";
    H := G`SuzukiReductionData`stdCopy;
    assert assigned H`SuzukiRecognitionData;
    
    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    q := #field;
    
    vprint SuzukiMaximals, 3 : "Get image of first maximal";
    RH := sub<Generic(H) | [Function(G`SuzukiReductionData`iso)(g) :
	g in UserGenerators(R)]>;
    
    vprint SuzukiMaximals, 3 : "Get image of second maximals";
    SH := sub<Generic(H) | [Function(G`SuzukiReductionData`iso)(g) :
	g in UserGenerators(S)]>;

    typeR := determineMaximalClass(RH);
    typeS := determineMaximalClass(SH);
    if typeR ne typeS then
	error "Sz maximal subgroup conjugation:",
	    "maximals must be of same class";
    end if;
    
    if typeR ne MAXIMAL_SMALLER_SZ then
	MR := DerivedGroupMonteCarlo(RH);
	MS := DerivedGroupMonteCarlo(SH);

	if typeR eq MAXIMAL_PARABOLIC then
	    conjugator, slp := sylow2Conjugation(H, MR, MS);
	elif typeR eq MAXIMAL_CYCLIC_EASY then
	    conjugator, slp := cyclicSylowConjugation(H, MR, MS);
	else
	    conjugator, slp := hardSylowConjugation(H, MR, MS);	    
	end if;
    else
	// Must be smaller Sz
	conjugator, slp := smallerSzConjugation(H, RH, SH);
    end if;

    assert SuzukiStandardMembership(conjugator);
    vprint SuzukiMaximals, 3 : "Move back to input copy";
    
    // Map back to input copy
    assert IsCoercible(Domain(G`SuzukiReductionData`slpHomo), slp);
    conjugator := G`SuzukiReductionData`slpHomo(slp);
    
    return conjugator, slp;
end intrinsic;
    
/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function determineMaximalClass(H)
    F := CoefficientRing(H);
    q := #F;

    n := #Constituents(GModule(H));

    // Constituents differ in natural representation
    if n eq 4 then
	return MAXIMAL_PARABOLIC;
    elif n eq 2 then
	return MAXIMAL_CYCLIC_EASY;
    else
	// When q=8, Sz(2) is picked up as "real" Sz
	if q eq 8 then
	    return MAXIMAL_CYCLIC_HARD;
	end if;
	
	// Use heavier weapons for irreducible subgroups
	if IsOverSmallerField(H) then
	    return MAXIMAL_SMALLER_SZ;
	else
	    return MAXIMAL_CYCLIC_HARD;
	end if;
    end if;    
end function;

function smallerSzConjugation(H, MR, MS)

    flag, R1 := IsOverSmallerField(MR);
    assert flag;

    flag, R2 := IsOverSmallerField(MS);
    assert flag;

    // Assume we are given same type of smaller Sz
    assert SmallerField(MR) eq SmallerField(MS);
    
    cbm1 := SmallerFieldBasis(MR);
    cbm2 := SmallerFieldBasis(MS);
    
    _, conj1 := SuzukiConjugacy(R1 : CheckInput := false);
    assert flag;

    _, conj2 := SuzukiConjugacy(R2 : CheckInput := false);
    assert flag;

    assert SuzukiStandardRecogniser(R1^conj1);
    assert SuzukiStandardRecogniser(R2^conj2);
    
    // Remove scalars from conjugating matrix, so that it lies in Sz
    flag, conjugator := ScaleMatrix(cbm1 * Generic(H) ! (conj1 *
	conj2^(-1)) * cbm2^(-1));
    assert flag;
    assert Determinant(conjugator) eq 1;
    assert SuzukiStandardMembership(conjugator);
    
    flag, slp := SuzukiStandardConstructiveMembership(H, conjugator :
	Randomiser := H`RandomProcess, CheckInput := false);
    assert flag;
    
    return conjugator, slp;
end function;

// Find meta-cyclic maximal subgroups of orders 4(q \pm t + 1)
// Use generators x,y s.t. x has order 2, (xy) has order 4 and
// (xy^2) has order q \pm t + 1.
// x is the anti-diag involution and y is in the standard Borel of order 4
function findHardMaximals(F, gens)
    local q, m, t, maximals, orders, P, a, poly, xi, gamma, g, h, o1, o2;
    
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    maximals := [];

    // Orders of cyclic subgroups
    orders := {q + t + 1, q - t + 1};
    P<x> := PolynomialAlgebra(F);
    
    repeat
	// Solve this equation to find generators
	// Equation derived from the fact that xy should have trace 0
	a := Random(F);
	poly := x^2 + a^(t + 1) * x + (a^t + a^(t + 2))^t +
	    a^t * (a^t + a^(t + 2));

	// The generator x, ie anti-diag involution
	xi := gens[1];
	
	for b in  {r[1] : r in Roots(poly)} do
	    // Try an element of order 4 as y
	    gamma := getSuzukiSylowGen(F, a, b);
	    g := xi * gamma;
	    h := xi * gamma^2;

	    // g is xy and should have trace 0, h is xy^2 and should have the
	    // specified trace
	    if IsZero(Trace(g)) and Trace(h) eq a^(t + 2) then
		o1 := Order(g);
		o2 := Order(h);

		// Check that orders are also correct
		// We need precise orders!
		if o1 eq 4 and o2 in orders then
		    maximal := sub<GL(4, F) | xi, gamma>;
		    maximal`Order := o1 * o2;
		    
		    Append(~maximals, maximal);
		    Exclude(~orders, o2);
		end if;
	    end if;
	end for;
    until IsEmpty(orders);

    return maximals;
end function;
