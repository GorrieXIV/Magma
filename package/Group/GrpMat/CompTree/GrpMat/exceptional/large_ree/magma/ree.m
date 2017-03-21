/******************************************************************************
 *
 *    ree.m    Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-06-15
 *
 *    Version   : $Revision:: 2354                                           $:
 *    Date      : $Date:: 2012-10-22 07:38:54 +1100 (Mon, 22 Oct 2012)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: ree.m 2354 2012-10-21 20:38:54Z jbaa004                        $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose LargeReeGeneral, 10;

// Store isomorphisms to standard copy
LargeReeReductionMaps := recformat<
    conjugation : Map>; // Conjugation to standard copy

// Store information for constructive recognition
LargeReeReductionFormat := recformat<
    maps : Rec,             // LargeReeReductionMaps
    conjugator : GrpMatElt, // Conjugating element to standard copy
    stdCopy : GrpMat,       // The standard copy
    iso : Map,              // Isomorphism to standard copy
    inv : Map,              // Isomorphism from standard copy
    slpHomo : Map,          // Evaluate SLPs in given copy
    slpHomoInv : Map,       // Express elements as SLPs
    slpGroup : GrpSLP,      // Parent of SLPs returned
    slpCoercion : Map>;     // Convert from SLP group to WordGroup

// Generators of Sz \wr 2 and its two Sz subgroups, as SLPs in Big Ree gens
// Also the 2 as SLP in Big Ree gens
LargeReeSzWreath2Info := recformat<
    group : GrpMat,      // 26-dim Sz \wr 2
    slps : SeqEnum,      // SLPs of generators, in Big Ree generators
    sz1 : GrpMat,        // 26-dim first Sz factor
    sz1slps : SeqEnum,   // SLPs of first Sz generators
    sz2 : GrpMat,        // 26-dim second Sz factor
    sz2slps : SeqEnum,   // SLPs of second Sz generators
    sz1small : GrpMat,   // 4-dim first Sz 
    sz2small : GrpMat,   // 4-dim second Sz
    slpMap1 : Map,       // Evaluate 4-dim SLPs on 26-dim Sz
    slpMap2 : Map,       // Evaluate 4-dim SLPs on 26-dim Sz
    slpCoercion1 : Map,  // Evaluate 4-dim SLPs on sz1slps
    slpCoercion2 : Map,  // Evaluate 4-dim SLPs on sz2slps
    conj : Rec           // Conjugate first to second Sz inside Sz \wr 2
    >; 

// Sz parabolic has shape q.q^4.q.q^4 : (Sz(q) x (q-1))
// So the O_2 part is q.q^4.q.q^4
LargeReeSzParabolicInfo := recformat<
    group : GrpMat,          // The recognised centraliser it includes
    slps : SeqEnum,          // SLPs of centraliser, in Big Ree generators
    parabolic : GrpMat,      // The whole parabolic
    parabolicSLPs : SeqEnum, // SLPs of whole parabolic
    szCyclic : GrpMat,       // Sz x (q-1) inside parabolic
    szCyclicSLPs : SeqEnum,  // SLPs of Sz x (q-1)
    sz : GrpMat,             // 26-dim Sz inside Sz x (q-1)
    szSLPs : SeqEnum,        // SLPs of 26-dim Sz
    smallSZ : GrpMat,        // 4-dim Sz
    slpMap : Map,            // Evaluate 4-dim SLPs on 26-dim Sz
    slpCoercion : Map,       // Evaluate 4-dim SLPs on szSLPs
    o2Base : SeqEnum,        // Generators of O_2, as module for centraliser
    o2 : GrpMat,             // All group generators for O_2 part
    o2SLPs : SeqEnum         // SLPs of O_2 part
    >;
    
declare attributes GrpMat : LargeReeReductionData, LargeReeMaximals,
    LargeReeSzWreath2Data, LargeReeSzParabolicData;

forward LargeReeTrivialRecognitionChecks;

import "../../../util/basics.m" : getMapFunction, MatSLP;

import "conjugate.m" : findSzWreath2;
import "standard.m" : getLargeReeCorrectForm,
    getLargeReeRobStandardGenerators, getLargeReeDiagonalAlt, getLargeReeOrder;
import "ryba.m" : RybaInitialisation;
import "involution.m" : initialiseCentraliser,
    getCentraliserEvenOrderElement;
import "trick.m" : initialiseTrick, TrickInCoset;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAGMA STANDARD INTERFACE INTRINSICS                                       */
/*****************************************************************************/

// Provide intrinsics similar to the ones for SL2

intrinsic RecogniseLargeRee(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimise := false) ->
    BoolElt, Map, Map, Map, Map
    { Constructively recognise G as a Large Ree group. If G is isomorphic to
    LargeRee(q) where q is the size of the defining field of G, then return:
    1. Isomorphism from G to LargeRee(q).
    2. Isomorphism from LargeRee(q) to G.
    3. Map from G to the word group of G.
    4. Map from the word group of G to G.

    The isomorphisms are composed of maps that are defined by rules,
    so Function can be used on each component.
    The word group is the GrpSLP which is the parent of the elements returned
    from LargeReeElementToWord. In general this is not the same as
    WordGroup(G), but is created from it using AddRedundantGenerators.
    
    If Verify is true, then it is checked that G really is isomorphic to
    LargeRee(q), otherwise this is not checked. In that case, the FieldSize
    must be set to the correct value of q. }
    local flag, iso, inv, q;
    
    if Verify then
	flag, q := LargeReeRecognition(G);
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Field size must be greater than 2";
	end if;
	flag, degree := IsPowerOf(FieldSize, 2);
	if not (flag and IsOdd(degree)) then
	    error "Field size must be an odd power of 2";
	else
	    q := FieldSize;
	end if;
	flag := true;
    end if;

    if not flag then
	return false, _, _, _, _;
    end if;
    
    iso, inv := LargeReeReduction(G : CheckInput := false, FieldSize := q,
	Optimise := Optimise);
    assert assigned G`LargeReeReductionData`slpHomo;
    assert assigned G`LargeReeReductionData`slpHomoInv;
    
    return true, iso, inv, G`LargeReeReductionData`slpHomoInv,
	G`LargeReeReductionData`slpHomo;
end intrinsic;

intrinsic LargeReeResetRandomProcess(G :: GrpMat) -> BoolElt
    { G is isomorphic to LargeRee(q) and RecogniseLargeRee(G) has returned
    true. Resets the random process used in the constructive membership,
    so that the SLPs are again short. }
    
    if not assigned G`LargeReeReductionData then
	return false;
    end if;

    assert assigned G`LargeReeReductionData`stdCopy;
    G`LargeReeReductionData`stdCopy`RandomProcess :=
	RandomProcessWithWords(G`LargeReeReductionData`stdCopy :
	WordGroup := WordGroup(G));
    vprint LargeReeGeneral, 5 : "Random process reset";
    
    return true;
end intrinsic;

intrinsic RecognizeLargeRee(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimise := false) ->
    BoolElt, Map, Map, Map, Map
    { See RecogniseRee }
    
    return RecogniseLargeRee(G : Verify := Verify, FieldSize := FieldSize,
	Optimise := Optimise);
end intrinsic;

intrinsic LargeReeElementToWord(G :: GrpMat, g :: GrpMatElt) ->
    BoolElt, GrpSLPElt
    { If G has been constructively recognised as a Large Ree group,
    and if g is an element of G, then return GrpSLPElt from word group of G
    which evaluates to g, else false.
    This facilitates membership testing in G. }
    local q;

    flag, slps := LargeReeElementToWord(G, [g]);
    if flag then
	return true, slps[1];
    else
	return false, _;
    end if;
end intrinsic;

intrinsic LargeReeElementToWord(G :: GrpMat, batch :: SeqEnum[GrpMatElt]) ->
    BoolElt, SeqEnum[GrpSLPElt]
    { If G has been constructively recognised as a Large Ree group,
    and if g is an element of G, then return GrpSLPElt from word group of G
    which evaluates to g, else false.
    This facilitates membership testing in G.

    When SLPs of many elements are to be found, this intrinsic should be used
    rather than the single element version, since it will be more efficient. }
    local q;
    
    if not assigned G`LargeReeReductionData then
	return false, _;
    end if;

    q := #CoefficientRing(G`LargeReeReductionData`stdCopy);
    assert assigned G`RandomProcess;

    // Find reduction to standard Ree group
    iso, _, ree := LargeReeReduction(G : CheckInput := false,
    Randomiser := G`RandomProcess, FieldSize := q);

    // Compute image in standard copy
    assert assigned ree`RandomProcess;
    elements := Function(iso)(batch);

    // Solve constructive membership in standard copy
    return LargeReeStandardConstructiveMembership(ree, elements :
	CheckInput := false, Randomiser := ree`RandomProcess,
	wordGroup := G`LargeReeReductionData`slpGroup);
end intrinsic;

intrinsic LargeReeSLPCoercion(G :: GrpMat) -> Map
    { Return the SLP coercion map, which is a homomorphism from the word group
    of G to WordGroup(G). }

    if not assigned G`LargeReeReductionData then
	error "G must be a recognised Large Ree group";
    end if;

    assert assigned G`LargeReeReductionData`slpCoercion;
    return G`LargeReeReductionData`slpCoercion;
end intrinsic;

intrinsic LargeReeRedundantSLPGenerators(G :: GrpMat) -> []
    { If G has been constructively recognised as a Ree group, return the
    extra generators in the word group of G. }
    local W, nGens;
    
    if not assigned G`LargeReeReductionData then
	error "G must be a recognised Large Ree group";
    end if;
    
    assert assigned G`LargeReeReductionData`slpCoercion;
    W := Domain(G`LargeReeReductionData`slpCoercion);
    nGens := NumberOfGenerators(G);
    
    return [G`LargeReeReductionData`slpCoercion(W.i) :
	i in [nGens + 1 .. NumberOfGenerators(W)]];
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeGeneralRecogniser(G :: GrpMat) -> BoolElt, RngIntElt
    { Monte-Carlo check if G is isomorphic to LargeRee(q). Also returns q.}
    local recognition, lieType;

    if not IsAbsolutelyIrreducible(G) or IsOverSmallerField(G) then
	return false, 0;
    end if;

    vprint LargeReeGeneral, 5 : "Executing IdentifyLieType";
    recognition, lieType := LieType(G, 2);
    vprint LargeReeGeneral, 5 : "IdentifyLieType done", recognition;

    if recognition then
	vprint LargeReeGeneral, 5 : "Got answer", lieType;
    end if;
    
    if not recognition then
	return false, 0;
    end if;
    if not (lieType[1] eq "2F" and lieType[2] eq 4) then
	return false, 0;
    end if;
    
    return true, lieType[3];
end intrinsic;

intrinsic IsLargeReeGroup(G :: GrpMat) -> BoolElt, RngIntElt
    { G \leq GL(d, q). Determine (non-constructively) if G is isomorphic to
    LargeRee(q). The corresponding q is also returned. }

    return LargeReeRecognition(G);
end intrinsic;

intrinsic LargeReeRecognition(G :: GrpMat) -> BoolElt, RngIntElt
    { G \leq GL(d, q). Determine (non-constructively) if G is isomorphic to
    LargeRee(q). The corresponding q is also returned. }

    if Degree(G) gt 26 or Characteristic(CoefficientRing(G)) gt 2 then
	return LargeReeGeneralRecogniser(G);
    else
	if LargeReeStandardRecogniser(G) then
	    return true, #CoefficientRing(G);
	else
	    return LargeReeGeneralRecogniser(G);
	end if;
    end if;
end intrinsic;

intrinsic LargeReeReduction(G :: GrpMat : CheckInput := true,
    Optimise := false, FieldSize := 0,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> Map, Map
    { G \leq GL(d, q) is isomorphic to LargeRee(q). Compute explicit inverse
    isomorphisms to LargeRee(q). This is the Large Ree constructive
    recognition engine.

    Currently only d = 26 is implemented.
    }
    local q, recognition, flag, ree, tensorHomo, symSquareHomo,
	homo, inv, slpHomo;
    
    if CheckInput then
	recognition, q := LargeReeRecognition(G);
	if not recognition then
	    error "Large Ree reduction: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Large Ree reduction: Field size must be > 2";
	end if;
	flag, degree := IsPowerOf(FieldSize, 2);
	if not (flag and IsOdd(degree)) then
	    error "Large Ree reduction: Field size must be an odd power of 2";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    // Don't run constructive recognition twice
    if assigned G`LargeReeReductionData then
	assert assigned G`LargeReeReductionData`iso and
	    assigned G`LargeReeReductionData`inv;

	vprint LargeReeGeneral, 1: "Using precomputed reduction data";
	return G`LargeReeReductionData`iso, G`LargeReeReductionData`inv,
	    G`LargeReeReductionData`stdCopy;
    end if;

    // Setup data structure
    G`LargeReeReductionData := rec<LargeReeReductionFormat | maps :=
	rec<LargeReeReductionMaps | >>;

    // Use cross char method if necessary
    flag, power := IsPowerOf(#CoefficientRing(G), 2);
    if not (flag and power ge 3) then
	error "Large Ree Reduction: Cross characteristic case not implemented";
    else
	// Check if we need to decompose
	if Degree(G) gt 26 then
	    error "Large Ree Reduction:",
		"Only natural representation implemented";
	end if;
    end if;
    
    assert Degree(G) eq 26;
    W, slpHomo := WordGroup(G);

    // Check if we need to conjugate to standard copy
    if not LargeReeStandardRecogniser(G) then	
	vprint LargeReeGeneral, 1: "Conjugating to standard Ree copy";
	conjHomo, conjugator :=
	    LargeReeConjugacy(G : Randomiser := G`RandomProcess,
	    CheckInput := false); 
	
	G`LargeReeReductionData`conjugator := conjugator;
	G`LargeReeReductionData`maps`conjugation := conjHomo;
	ree := Codomain(conjHomo);
    else
	// No conjugation needed
	ree := G;
	G`LargeReeReductionData`conjugator := Identity(ree);
	G`LargeReeReductionData`maps`conjugation := hom<ree -> ree | x :-> x>;
    end if;

    vprint LargeReeGeneral, 1: "Precompute constructive membership data";

    if not assigned ree`RandomProcess then
	ree`RandomProcess :=
	    RandomProcessWithWords(ree : WordGroup := W);
    else
	assert LargeReeStandardRecogniser(G);
    end if;

    // Set order on standard copy
    ree`Order := getLargeReeOrder(q);

    if not assigned ree`LargeReeMembershipData then
	   if assigned G`LargeReeSzParabolicData then
	   invol := rec<MatSLP | mat :=
	   	G`LargeReeSzParabolicData`group.1^conjugator,
	   	slp := G`LargeReeSzParabolicData`slps[1]>;
	   else
	    invol := rec<MatSLP | mat := Identity(ree), slp := Identity(W)>;
end if;
	
	// Precompute centralisers
	vprint LargeReeGeneral, 1 : "Initialise membership testing";
        RybaInitialisation(ree, W : invol := invol);
	assert assigned ree`LargeReeMembershipData;
    end if;
        
/*
    vprint LargeReeGeneral, 1: "Construct SLP homomorphism";
    assert Parent(ree`LargeReeMembershipData`centraliserSz`
	LargeReeInvolCentraliserData`genSLPs[1]) cmpeq
	Parent(ree`LargeReeMembershipData`centraliserSL2`
	LargeReeInvolCentraliserData`genSLPs[1]);
    newSLPs :=
	ree`LargeReeMembershipData`centraliserSz`
	LargeReeInvolCentraliserData`genSLPs cat
	ree`LargeReeMembershipData`centraliserSL2`
	LargeReeInvolCentraliserData`genSLPs;

    W_opt := AddRedundantGenerators(W, newSLPs);
    slpCoercion := hom<W_opt -> W | [W.i : i in [1 .. NumberOfGenerators(W)]]
    cat newSLPs>;
*/
    
    vprint LargeReeGeneral, 1: "Construct SLP homomorphism";
    
    // Construct homomorphisms that evaluate SLPs in input Ree group
    //if Optimise then
	// Optimized SLP homo
//	slpHomoOpt := hom<W_opt -> G | slpHomo>;
//	G`LargeReeReductionData`slpHomo := slpHomoOpt;
//    else
	G`LargeReeReductionData`slpHomo := slpHomo;
//    end if;
    
    slpMap := hom<G -> W | x :-> 
    flag eq true select slp else flag
	where flag, slp is LargeReeElementToWord(G, x)>;

    G`LargeReeReductionData`slpHomoInv := slpMap;
    G`LargeReeReductionData`slpCoercion := IdentityHomomorphism(W);
    G`LargeReeReductionData`slpGroup := W;
    
    vprint LargeReeGeneral, 1: "Construct isomorphism to standard Ree copy";
    
    // Construct homomorphism from given group to standard copy, by
    // composing the various computed homos
    homo := hom<G -> ree | x :->
    getMapFunction(G`LargeReeReductionData`maps`conjugation)(x)>;
    
    // Construct inverse isomorphism by solving constructive
    // membership in standard copy
    inv := hom<ree -> G | x :-> 
    flag eq true select G`LargeReeReductionData`slpHomo(slp) else flag
	where flag, slp is LargeReeStandardConstructiveMembership(ree, x :
	CheckInput := false, Randomiser := ree`RandomProcess,
	wordGroup := W)>;
    
    G`LargeReeReductionData`iso := homo;
    G`LargeReeReductionData`inv := inv;
    G`LargeReeReductionData`stdCopy := ree;

    vprint LargeReeGeneral, 1: "Ree reduction successful";
    return homo, inv, ree;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function LargeReeTrivialRecognitionChecks(field)
    local flag, p, k, q;

    if Category(field) ne FldFin then
	return false;
    end if;

    if Characteristic(field) eq 2 and IsOdd(Degree(field)) and
	Degree(field) gt 1 then
	return true;
    else
	return false;
    end if;
end function;
