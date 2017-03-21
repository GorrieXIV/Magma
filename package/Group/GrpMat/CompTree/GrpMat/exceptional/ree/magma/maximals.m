/******************************************************************************
 *
 *    maximals.m Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-07-20
 *
 *    Version   : $Revision:: 2448                                           $:
 *    Date      : $Date:: 2013-12-30 06:29:55 +1100 (Mon, 30 Dec 2013)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: maximals.m 2448 2013-12-29 19:29:55Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

forward findHardMaximals, solveEquations, smallerReeConjugation,
    involutionCentraliserConjugation, determineMaximalClass;

import "standard.m" : standardGeneratorsNaturalRep, getReeInfSylowGenMatrix,
    getRobReeCopy, getReeOrder;
import "sylow.m" : hardSylowConjugation, sylow3Conjugation;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/basics.m" : MatSLP;

declare verbose ReeMaximals, 10;

MAXIMAL_PARABOLIC   := 1;
MAXIMAL_INVOL_CENT  := 2;
MAXIMAL_FROBENIUS   := 3;
MAXIMAL_SMALLER_REE := 4;

// Store information about maximal subgroups
ReeMaximalsInfo := recformat<
    maximals : SeqEnum,
    slps : SeqEnum>;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*
intrinsic testReeMaximals(m :: RngIntElt) -> BoolElt
    { }

SetVerbose("ReeMaximals", 3);
F := GF(3, 2 * m + 1);
G := Ree(F);
flag := RecogniseRee(G);
maximals := ReeMaximalSubgroups(G);
for H in maximals[4 .. 6] do
    M := GModule(H);
    print IndecomposableSummands(M);
end for;

return true;
end intrinsic;
*/
	
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeMaximalSubgroups(G :: GrpMat) -> [], []
    { If G has been constructively recognised as a Ree group,
    find a list of representatives of the maximal subgroups of G.
    
    Also returns lists of SLPs of the generators of the subgroups, in
    the generators of G. }

    local slp;
    
    if not assigned G`ReeReductionData then
	error "G must be a recognised Ree group";
    end if;

    if assigned G`ReeMaximals then
	return G`ReeMaximals`maximals, G`ReeMaximals`slps;
    end if;

    assert assigned G`ReeReductionData`stdCopy;
    if not assigned G`ReeReductionData`stdCopy`ReeMaximals then
	vprint ReeGeneral, 1: "Construct maximals subgroups of standard copy";
	maximals, slps :=
	    ReeStandardMaximalSubgroups(G`ReeReductionData`stdCopy :
	    wordGroup := WordGroup(G));
	G`ReeReductionData`stdCopy`ReeMaximals := rec<ReeMaximalsInfo |
	    maximals := maximals,
	    slps := slps>;
    end if;
    
    // Use explicit isomorphism to obtain maximals in input copy
    maximals := [sub<Generic(G) | G`ReeReductionData`slpHomo(gens)> :
	gens in G`ReeReductionData`stdCopy`ReeMaximals`slps];

    // Set orders from standard copies
    for i in [1 .. #maximals] do
	maximals[i]`Order :=
	    G`ReeReductionData`stdCopy`ReeMaximals`maximals[i]`Order;
    end for;
    
    G`ReeMaximals := rec<ReeMaximalsInfo |
	maximals := maximals,
	slps := slps>;

    return maximals, slps;
end intrinsic;

intrinsic ReeStandardMaximalSubgroups(G :: GrpMat :
    wordGroup := WordGroup(G)) -> [], []
    { G is Ree(q), RecogniseRee(G) has returned true.
    Returns a sequence of representatives of conjugacy classes of maximal
    subgroups of G.

    Also returns sequence of sequences of SLPs of the generators of the
    subgroups. }

    if not (assigned G`ReeRecognitionData and ReeStandardRecogniser(G)) then
	error "G must be a recognised standard Ree copy";
    end if;

    F := CoefficientRing(G);
    q := #F;
    p := Characteristic(F);
    m := (Degree(F) - 1) div 2;
    t := 3^m;
    assert assigned G`RandomProcess;
    
    maximals := [];
    slps := [];

    // Construct easy maximals
    gens := standardGeneratorsNaturalRep(F);
    pointStab := sub<Generic(G) | gens[2], gens[3]>;
    pointStab`Order := q^3 * (q - 1);

    involCentraliser := sub<Generic(G) | gens[1], gens[2],
	getReeInfSylowGenMatrix(F, 0, 1, 0)>;
    involCentraliser`Order := q * (q^2 - 1);
    
    maximals := [pointStab, involCentraliser];
        
    vprint ReeMaximals, 2 : "Find smaller Ree";
    
    // Add Ree's over subfields, even over GF(3)
    for deg in {x : x in Divisors(Degree(F)) | x ge 1 and x lt Degree(F)} do
	assert IsDivisibleBy(q - 1, p^deg - 1);
	power := (q - 1) div (p^deg - 1);

	ree := sub<Generic(G) | gens[1], gens[2]^power, gens[3]>;
	ree`Order := getReeOrder(p^deg);
	
	Append(~maximals, ree);
    end for;
    
    vprint ReeMaximals, 2 : "Find hard maximals";

    // Construct hard maximals (ie normalisers of other cyclic groups)
    maximals cat:= findHardMaximals(G, gens, wordGroup);

    vprint ReeMaximals, 2 : "Get SLPs of maximal subgroup gens";

    // Get SLPs for maximal subgroup generators
    for maximal in maximals do
	Append(~slps, [slp where _, slp is
	    ReeStandardConstructiveMembership(G, g : CheckInput := false,
	    Randomiser := G`RandomProcess) : g in UserGenerators(maximal)]);
    end for;
    
    return maximals, slps;
end intrinsic;

intrinsic ReeMaximalSubgroupsConjugacy(G :: GrpMat, R :: GrpMat,
    S :: GrpMat) -> GrpMatElt, GrpSLPElt
    { G is isomorphic to Ree(q), RecogniseRee(G) has returned true,
    R and S are maximal subgroup of the same class.
    Find g in G such that R^g eq S. }
    local F, q;

    if not (assigned G`ReeReductionData) then
	error "Ree maximal subgroup conjugation: G must be a recognised Ree";
    end if;

    assert assigned G`RandomProcess;

    // Work in standard copy
    vprint ReeMaximals, 3 : "Get standard copy";
    H := G`ReeReductionData`stdCopy;
    assert assigned H`ReeRecognitionData;
    
    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 3^(m + 1);
    q := #field;
    
    vprint ReeMaximals, 3 : "Get image of first maximal";
    RH := sub<Generic(H) | [Function(G`ReeReductionData`iso)(g) :
	g in UserGenerators(R)]>;
    
    vprint ReeMaximals, 3 : "Get image of second maximals";
    SH := sub<Generic(H) | [Function(G`ReeReductionData`iso)(g) :
	g in UserGenerators(S)]>;

    typeR := determineMaximalClass(RH);
    typeS := determineMaximalClass(SH);
    if typeR ne typeS then
	error "Ree maximal subgroup conjugation:",
	    "maximals must be of same class";
    end if;

    // Separate cases by testing orders 
    if typeR notin {MAXIMAL_SMALLER_REE, MAXIMAL_INVOL_CENT} then
	MR := DerivedGroupMonteCarlo(RH);
	MS := DerivedGroupMonteCarlo(SH);

	if typeR eq MAXIMAL_PARABOLIC then
	    conjugator, slp := sylow3Conjugation(H, MR, MS);
	else
	    error "Ree maximal subgroup conjugation:",
		"conjugation not implemented for Frobenius groups";
	end if;

	assert ReeStandardMembership(conjugator);
    elif typeR eq MAXIMAL_INVOL_CENT then
	conjugator, slp := involutionCentraliserConjugation(H, RH, SH,
	    WordGroup(G));
    else
	// Must be smaller Ree groups
	conjugator, slp := smallerReeConjugation(H, RH, SH);
    end if;

    vprint ReeMaximals, 3 : "Move back to input copy";
    
    // Map back to input copy
    assert IsCoercible(Domain(G`ReeReductionData`slpHomo), slp);
    conjugator := G`ReeReductionData`slpHomo(slp);
    
    return conjugator, slp;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function determineMaximalClass(H)
    F := CoefficientRing(H);
    q := #F;

    M := GModule(H);
    n := #Constituents(M);
    maxDim := Max([Dimension(N) : N in Constituents(M)]);
    
    // Constituents differ in natural representation
    if n eq 7 then
	return MAXIMAL_PARABOLIC;
    elif n eq 2 then
	if maxDim eq 4 then
	    return MAXIMAL_INVOL_CENT;
	else
	    return MAXIMAL_FROBENIUS;
	end if;
    else
	return MAXIMAL_SMALLER_REE;
    end if;    
end function;

function smallerReeConjugation(H, MR, MS)

    flag, R1 := IsOverSmallerField(MR);
    assert flag;

    flag, R2 := IsOverSmallerField(MS);
    assert flag;

    // Assume we are given same type of smaller Ree
    assert SmallerField(MR) eq SmallerField(MS);

    cbm1 := SmallerFieldBasis(MR);
    cbm2 := SmallerFieldBasis(MS);

    
    if #SmallerField(MR) gt 3 then
	_, conj1 := ReeConjugacy(R1 : CheckInput := false);
	_, conj2 := ReeConjugacy(R2 : CheckInput := false);
    else
	repeat
	    flag, iso1, inv1 := RecogniseSL(R1, 2, 8);
	until flag;
	repeat
	    flag, iso2, inv2 := RecogniseSL(R2, 2, 8);
	until flag;

	repeat
	    gens1 := [inv1(x) : x in UserGenerators(SL(2, 8))];
	    gens2 := [inv2(x) : x in UserGenerators(SL(2, 8))];
	    RR := sub<Generic(R1) | gens1>;
	    
	    M1 := GModule(RR);
	    M2 := GModule(RR, gens2);
	    flag, conj := IsIsomorphic(M1, M2);
	until flag;

	conj1 := Generic(R1) ! conj;
	conj2 := Identity(R2);

	assert R1^conj1 eq R2;
    end if;
    
    // Scale conjugator so that it lies in the Ree group
    flag, conjugator := ScaleMatrix(cbm1 * (Generic(H) ! (conj1 *
	conj2^(-1))) * cbm2^(-1));
    assert flag;
    
    assert Determinant(conjugator) eq 1;
    assert ReeStandardMembership(conjugator);
	
    flag, slp := ReeStandardConstructiveMembership(H, conjugator :
	Randomiser := H`RandomProcess, CheckInput := false);
    assert flag;
    
    return conjugator, slp;
end function;

function findCentralisedInvolution(C)
    local centerElements, derivedGens, C_prim, g, mostCommon;
    
    if not assigned C`RandomProcess then
	C`RandomProcess :=
	    RandomProcessWithWords(C : WordGroup := WordGroup(C));
    end if;

    // We are likely to hit the centralised involution, and we can determine if
    // we have since it is the unique element in the center
    repeat
	g := RandomInvolution(C : Randomiser := C`RandomProcess);
	
	if forall{h : h in Generators(C) | g^h eq g} then
	    return g;
	end if;
    until false;
end function;

function involutionCentraliserConjugation(H, MR, MS, W)
    local j1, j2, conj, slp;

    // Try to find centralised involutions
    j1 := findCentralisedInvolution(MR);
    j2 := findCentralisedInvolution(MS);

    assert assigned H`RandomProcess;

    // Sufficient to conjugate the involutions
    conj := DihedralTrick(rec<MatSLP | mat := j1, slp := Identity(W)>,
	rec<MatSLP | mat := j2, slp := Identity(W)>, H`RandomProcess);

    assert ReeStandardMembership(conj`mat);	
    flag, slp := ReeStandardConstructiveMembership(H, conj`mat :
	Randomiser := H`RandomProcess, CheckInput := false);
    assert flag;
    
    return conj`mat, slp;
end function;

// Tr(x * y) = -1, where x is one of two possible anti-diagonal involutions
// and y is an element in standard Borel, leads to the following two systems
// of equations.
function hardMaximalEqns(F, a)

    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 3^m;
    
    flag, x := IsSquare((1 - a)^(3 * t - 1));
    if flag then
	flag, y := IsSquare(a - 1 - x^2);
	if flag then
	    sols1 := [<x, y>, <-x, -y>, <x, -y>, <-x, y>];
	else
	    sols1 := [];
	end if;
    else
	sols1 := [];
    end if;

    flag, x := IsSquare((a - 1)^(3 * t - 1));
    if flag then
	flag, y := IsSquare(1 - a + x^2);
	if flag then
	    sols2 := [<x, y>, <-x, y>, <x, -y>, <-x, -y>];
	else
	    sols2 := [];
	end if;
    else
	sols2 := [];
    end if;

    return [sols1, sols2];
end function;

function findHardMaximals(G, gens, wordGroup)
    local x, y, g, F, q, n, t, P, R, o, MA, maximals, found;
    
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 3^m;

    maximals := [];
    invols := [gens[1], gens[2]^((q - 1) div 2) * gens[1]];
    
    assert forall{x : x in invols | IsIdentity(x^2) and
	ReeStandardMembership(x)};
    orders := [q + 3 * t + 1, q - 3 * t + 1, (q + 1) div 2];

    // Try generate maximals with elements x, y
    // x one of two possible anti-diagonal involutions,
    // y an element of standard Borel
    
    // x * y should have order 6, and hence trace -1
    // (x, y) should have order o in orders, unknown trace

    // Want one maximal of each order
    for o in orders do
	repeat
	    found := false;

	    // Find an element of correct order
	    // Now (x,y) should have the same trace
	    flag, g := RandomElementOfOrder(G, o :
		Randomiser := G`RandomProcess, MaxTries := q^2);
	    assert flag;
	    
	    vprint ReeMaximals, 3 : "Got element with trace", Trace(g), o;

	    // Find field elements determining Borel elements
	    allsols := hardMaximalEqns(F, Trace(g));

	    // Try each involution
	    for i in [1 .. #invols] do
		
		w := invols[i];
		sols := allsols[i];

		// Try each possible Borel element
		for sol in sols do
		    z := Generic(G) !
			getReeInfSylowGenMatrix(F, 0, sol[1], sol[2]);
		    
		    vprint ReeMaximals, 3 : "Got orders",  Order(w * z),
			Order((w, z)), o;
		    
		    // Want product of order 6 and commutator of given order
		    // This should never fail, in fact!
		    if Order(w * z) eq 6 and Order((w, z)) eq o then
			vprint ReeMaximals, 3 : "Found maximal";
			maximal := sub<Generic(G) | w, z>;
			
			if o eq (q + 1) div 2 then
			    maximal`Order := 12 * o;
			else
			    maximal`Order := 6 * o;
			end if;
			
			Append(~maximals, maximal);
			found := true;
			break;
		    end if;
		end for;
		if found then
		    break;
		end if;
	    end for;
	until found;
    end for;
    
    return maximals;
end function;
