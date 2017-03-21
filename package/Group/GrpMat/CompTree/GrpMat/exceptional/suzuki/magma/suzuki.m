/******************************************************************************
 *
 *    suzuki.m  Suzuki group package for the matrix recognition project
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B??rnhielm
 *    Dev start : 2004-11-06
 *
 *    Version   : $Revision:: 2239                                           $:
 *    Date      : $Date:: 2011-03-24 09:18:15 +1300 (Thu, 24 Mar 2011)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: suzuki.m 2239 2011-03-23 20:18:15Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;

/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "standard.m" : diagramAutomorphism, getSuzukiOrder;
import "membership.m" : getSuzukiRecognitionData, getInfMappingMatrix;
import "solve.m" : findMappingElements, elementFormat,
    findMappingElementsAlt;
import "trick.m" : getStabiliser;

import "../../../util/basics.m" : getMapFunction, MatSLP;

declare attributes GrpMat : RandomProcess, SuzukiRecognitionData,
    SuzukiReductionData, SuzukiStandardGenerators, SuzukiMaximals;
declare verbose SuzukiGeneral, 10;

forward checkSuzukiProperSubgroups, is2Sz8, Recognise2Sz8,
    BraySzRelations;

// Store isomorphisms to standard copy
SuzukiReductionMaps := recformat<
    tensor : Map,      // Tensor decomposition map
    conjugation : Map, // Conjugation to standard copy
    crossChar : Map>;  // Map from cross char rep to standard copy

// Store information about a tensor decomposition
SuzukiTensorData := recformat<
    tensorCBM : GrpMatElt, // Tensor decomposition change of basis
    maps : SeqEnum>;       // Maps to each tensor factor

// Store information for constructive recognition
SuzukiReductionFormat := recformat<
    maps : Rec,             // SuzukiReductionMaps
    conjugator : GrpMatElt, // Conjugating element to standard copy
    tensorCBM : GrpMatElt,  // Tensor decomposition change of basis
    tensorData : Rec,       // SuzukiTenorData
    stdCopy : GrpMat,       // The standard copy
    iso : Map,              // Isomorphism to standard copy
    inv : Map,              // Isomorphism from standard copy
    slpHomo : Map,          // Evaluate SLPs in given copy
    slpHomoInv : Map,       // Express elements as SLPs
    slpGroup : GrpSLP,      // Parent of SLPs returned
    slpCoercion : Map>;     // Convert from SLP group to WordGroup

// Store information about standard generators
SuzukiStandardGensFormat := recformat<x : Rec, h : Rec, z : Rec>;

recognitionErrors := [
    "Given group is Sz",
    "Given group has wrong field or degree",
    "Given group is not subgroup of Sz",
    "Given group is a proper subgroup of Sz",
    "Given group is a conjugate of Sz",
    "Given group has wrong field or degree",
    "Given group is not a subgroup of Sp",
    "Given group is not a proper subgroup of Sp",
    "Given group is not an almost simple subgroup",
    "Given group is the wrong C9 class group"];

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAGMA STANDARD INTERFACE INTRINSICS                                       */
/*****************************************************************************/

// Provide intrinsics similar to the ones for SL2

intrinsic RecogniseSz(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimise := false) ->
    BoolElt, Map, Map, Map, Map
    { G is absolutely irreducible and defined over minimal field.
    Constructively recognise G as a Suzuki group. If G is isomorphic to Sz(q)
    where q is the size of the defining field of G, then return:
    1. Isomorphism from G to Sz(q).
    2. Isomorphism from Sz(q) to G.
    3. Map from G to the word group of G.
    4. Map from the word group of G to G.

    The isomorphisms are composed of maps that are defined by rules,
    so Function can be used on each component.
    The word group is the GrpSLP which is the parent of the elements returned
    from SzElementToWord. In general this is not the same as WordGroup(G), but
    is created from it using AddRedundantGenerators.

    If Verify is true, then it is checked that G really is isomorphic to
    Sz(q), otherwise this is not checked. In that case, the FieldSize must be
    set to the correct value of q.

    Constructive recognition of 2.Sz(8) is also handled.
    }
    local flag, isos, slpHomo, q;

    if Verify then
	flag, q := SuzukiRecognition(G);
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

    // Special treatment of 2.Sz(8)
    if is2Sz8(G, q) then
	iso, inv := Recognise2Sz8(G);
    else
	iso, inv := SuzukiReduction(G : CheckInput := false, FieldSize := q,
	    Optimise := false);
    end if;

    assert assigned G`SuzukiReductionData;
    assert assigned G`SuzukiReductionData`slpHomo;
    assert assigned G`SuzukiReductionData`slpHomoInv;

    return true, iso, inv, G`SuzukiReductionData`slpHomoInv,
	G`SuzukiReductionData`slpHomo;
end intrinsic;

intrinsic SuzukiResetRandomProcess(G :: GrpMat) -> BoolElt
    { G is isomorphic to Sz(q) and RecogniseSz(G) has returned true.
    Resets the random process used in the constructive membership,
    so that the SLPs are again short. }

    if not assigned G`SuzukiReductionData then
	return false;
    end if;

    assert assigned G`SuzukiReductionData`stdCopy;
    G`SuzukiReductionData`stdCopy`RandomProcess :=
	RandomProcessWithWords(G`SuzukiReductionData`stdCopy :
	WordGroup := WordGroup(G));
    vprint SuzukiGeneral, 5 : "Random process reset";

    return true;
end intrinsic;

intrinsic RecognizeSz(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimise := false) ->
    BoolElt, Map, Map, Map, Map
    { See RecogniseSz. }

    return RecogniseSz(G : Verify := Verify, FieldSize := FieldSize,
	Optimise := Optimise);
end intrinsic;

intrinsic SzElementToWord(G :: GrpMat, g :: GrpMatElt) -> BoolElt, GrpSLPElt
    { If G has been constructively recognised as a Suzuki group,
    and if g is an element of G, then return GrpSLPElt from word group of G
    which evaluates to g, else false.
    This facilitates membership testing in G. }
    local slp;

    if not assigned G`SuzukiReductionData then
	return false, _;
    end if;

    q := #CoefficientRing(G`SuzukiReductionData`stdCopy);

    // Special treatment of 2.Sz(8)
    if is2Sz8(G, q) then
	slp := G`SuzukiReductionData`slpHomoInv(g);
	if slp cmpeq false then
	    return false, _;
	else
	    return true, slp;
	end if;
    end if;

    assert assigned G`RandomProcess;
    return SuzukiConstructiveMembership(G, g : CheckInput := false,
	Randomiser := G`RandomProcess, FieldSize := q);
end intrinsic;

intrinsic SzSLPCoercion(G :: GrpMat) -> Map
    { Return the SLP coercion map, which is a homomorphism from the word group
    of G to WordGroup(G). }

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    assert assigned G`SuzukiReductionData`slpCoercion;
    return G`SuzukiReductionData`slpCoercion;
end intrinsic;

intrinsic SzRedundantSLPGenerators(G :: GrpMat) -> []
    { If G has been constructively recognised as a Suzuki group, return the
    extra generators in the word group of G. }
    local W, nGens;

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    assert assigned G`SuzukiReductionData`slpCoercion;
    W := Domain(G`SuzukiReductionData`slpCoercion);
    nGens := NumberOfGenerators(G);
    return [G`SuzukiReductionData`slpCoercion(W.i) :
	i in [nGens + 1 .. NumberOfGenerators(W)]];
end intrinsic;

intrinsic SzPresentation(q :: RngIntElt) -> GrpFP, HomGrp
    { q = 2^(2m + 1) with m > 0. Return a presentation of Sz(q) on the
    Magma standard generators. }
    local stabiliserRels, G, m, F, field, minPoly, power, flag, H, homo;

    flag, power := IsPowerOf(q, 2);
    if not (flag and power gt 1 and IsOdd(power)) then
	error "q must be an odd power of 2";
    end if;

    return SzPresentation(GF(2, power));
end intrinsic;

intrinsic SzPresentation(F :: FldFin) -> SeqEnum
    { #F = 2^(2m + 1) with m > 0. Return relations of Sz(F) on the
    standard generators. }
    local flag, power;

    if not (Characteristic(F) eq 2 and IsOdd(Degree(F)) and
	Degree(F) gt 1) then
	error "q must be an odd power of 2";
    end if;

    m := (Degree(F) - 1) div 2;
    q := #F;
    t := 2^(m + 1);
    relations := BraySzRelations(F);
    FG<x, y, z> := Parent(relations[1]);

    // Move to Magma standard generators
    WH<r, h, s> := SLPGroup(3);
    l := -(2 + t) * (q div 2);

    //freeMap := hom<FG -> WH | [<x, (s^(-1))^(h^l)>, <y, h^(t + q)>, <z, r>]>;
    freeMap := hom<FG -> WH | (s^(-1))^(h^l), h^(t + q), r>;
    return freeMap(relations);
end intrinsic;

intrinsic SatisfiesSzPresentation(G :: GrpMat, q :: RngIntElt) -> BoolElt
    { G is constructively recognised as Sz(q). Verify that it satisfies a
    presentation for this group. }
    local presentation, gens, F;

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    F := CoefficientRing(G`SuzukiReductionData`stdCopy);
    if q ne #F then
	return false;
    end if;

    return SatisfiesSzPresentation(G);
end intrinsic;

intrinsic SatisfiesSzPresentation(G :: GrpMat) -> BoolElt
    { G is constructively recognised as Sz(q) for some q.
    Verify that it satisfies a presentation for this group. }
    local gens, presentation, F;

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    F := CoefficientRing(G`SuzukiReductionData`stdCopy);

    // Get standard Suzuki generators in given group
    gens := [Function(G`SuzukiReductionData`inv)(g) :
	g in UserGenerators(Sz(F))];

    // Get relations on S-gens
    presentation := SzPresentation(F);
    return SequenceToSet(Evaluate(presentation, gens)) eq {Identity(G)};
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiReduction(G :: GrpMat : CheckInput := true, FieldSize := 0,
    Optimise := false, Randomiser := RandomProcessWithWords(G : WordGroup :=
    WordGroup(G))) -> Map, Map
    { G \leq GL(d, q) is isomorphic to Sz(q). Compute explicit inverse
    isomorphisms to Sz(q). This is the Sz constructive recognition engine. }
    local q, flag, sz, tensorHomo, homo, inv, slpHomo;

    if CheckInput then
	flag, q := SuzukiRecognition(G);
	if not flag then
	    error "Sz reduction: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz reduction: Field size must be > 2";
	end if;
	flag, degree := IsPowerOf(FieldSize, 2);
	if not (flag and IsOdd(degree)) then
	    error "Sz reduction: Field size must be an odd prime power";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // Don't run constructive recognition twice
    if assigned G`SuzukiReductionData then
	assert assigned G`SuzukiReductionData`iso and
	    assigned G`SuzukiReductionData`inv;

	vprint SuzukiGeneral, 1: "Using precomputed reduction data";
	return G`SuzukiReductionData`iso, G`SuzukiReductionData`inv,
	    G`SuzukiReductionData`stdCopy;
    end if;

    // Setup data structure
    G`SuzukiReductionData := rec<SuzukiReductionFormat | maps :=
	rec<SuzukiReductionMaps | >>;
    sz := G;

    isTensorProd, degreePower := IsPowerOf(Degree(G), 4);
    flag, power := IsPowerOf(#CoefficientRing(sz), 2);

    // Use cross char method if necessary
    if not (flag and power ge 3) or not isTensorProd then
	vprint SuzukiGeneral, 1: "Running odd char reduction";
	crossCharHomo :=
	    SuzukiOddCharacteristicReduction(sz : CheckInput := false,
	    FieldSize := q, Randomiser := Randomiser);
	sz := Codomain(crossCharHomo);
    else
	// Check if we need to decompose
	if Degree(sz) gt 4 then

	    vprint SuzukiGeneral, 1: "Running tensor decomposition";

	    // Get homomorphism to tensor factor of dim 4
	    tensorHomo, tensorCBM, tensorData :=
		SuzukiTensorDecompose(sz : Randomiser := Randomiser,
		CheckInput := false, FieldSize := q);

	    G`SuzukiReductionData`tensorCBM := tensorCBM;
	    G`SuzukiReductionData`tensorData := tensorData;
	    G`SuzukiReductionData`maps`tensor := tensorHomo;
	    sz := Codomain(tensorHomo);
	else
	    // No tensor decomposition needed
	    G`SuzukiReductionData`tensorCBM := Identity(sz);
	    G`SuzukiReductionData`maps`tensor := hom<sz -> sz | x :-> x>;
	end if;
    end if;

    assert Degree(sz) eq 4;
    assert SuzukiConjugateRecogniser(sz);

    W, slpHomo := WordGroup(G);
    assert NumberOfGenerators(sz) eq NumberOfGenerators(G);

    // Should be assigned only if no decomposition needed
    if not assigned sz`RandomProcess then
	sz`RandomProcess :=
	    RandomProcessWithWords(sz : WordGroup := W);
    end if;

    vprint SuzukiGeneral, 1: "Conjugating to standard copy";
    conjHomo, conjugator :=
	SuzukiConjugacy(sz : Randomiser := sz`RandomProcess,
	CheckInput := false, W := W);

    G`SuzukiReductionData`conjugator := conjugator;
    G`SuzukiReductionData`maps`conjugation := conjHomo;
    sz := Codomain(conjHomo);

    vprint SuzukiGeneral, 1: "Precompute constructive membership data";

    assert SuzukiStandardRecogniser(sz);
    if not assigned sz`RandomProcess then
	sz`RandomProcess :=
	    RandomProcessWithWords(sz : WordGroup := W);
    else
	assert SuzukiStandardRecogniser(G);
    end if;

    assert assigned Domain(conjHomo)`SuzukiRecognitionData;
    sz`SuzukiRecognitionData := Domain(conjHomo)`SuzukiRecognitionData;

    // Set order on standard copy
    AssertAttribute(sz, "Order", getSuzukiOrder(q));

    vprint SuzukiGeneral, 1: "Construct SLP homomorphism";

    // Construct homomorphisms that evaluate SLPs in input Suzuki group

    if Optimise then
	// Optimized SLP homo
	slpHomoOpt := hom<sz`SuzukiRecognitionData`slpGroup -> G | slpHomo>;
	G`SuzukiReductionData`slpHomo := slpHomoOpt;
    else
	G`SuzukiReductionData`slpHomo := slpHomo;
    end if;

    slpMap := hom<G -> sz`SuzukiRecognitionData`slpGroup | x :->
    flag eq true select slp else flag
	where flag, slp is SuzukiConstructiveMembership(G, x :
	CheckInput := false, Randomiser := G`RandomProcess, FieldSize := q)>;

    G`SuzukiReductionData`slpHomoInv := slpMap;
    G`SuzukiReductionData`slpCoercion := sz`SuzukiRecognitionData`slpHomo;
    G`SuzukiReductionData`slpGroup := sz`SuzukiRecognitionData`slpGroup;

    vprint SuzukiGeneral, 1: "Construct isomorphism to standard copy";

    // Construct homomorphism from given group to standard copy, by
    // composing the various computed homos
    // Cross-char homo does all in one step
    if assigned G`SuzukiReductionData`maps`crossChar then
	homo := hom<G -> sz | x :->
	getMapFunction(G`SuzukiReductionData`maps`crossChar *
	    G`SuzukiReductionData`maps`conjugation)(x)>;
    else
	homo := hom<G -> sz | x :->
	getMapFunction(G`SuzukiReductionData`maps`tensor *
	    G`SuzukiReductionData`maps`conjugation)(x)>;
    end if;

    // Construct inverse isomorphism by solving constructive
    // membership in standard copy
    inv := hom<sz -> G | x :->
    flag eq true select G`SuzukiReductionData`slpHomo(slp) else flag
	where flag, slp is SuzukiStandardConstructiveMembership(sz, x :
	CheckInput := false, Randomiser := sz`RandomProcess)>;

    G`SuzukiReductionData`iso := homo;
    G`SuzukiReductionData`inv := inv;
    G`SuzukiReductionData`stdCopy := sz;

    vprint SuzukiGeneral, 1: "Suzuki reduction successful";
    return homo, inv, sz;
end intrinsic;

intrinsic SuzukiConstructiveMembership(G :: GrpMat, g :: GrpMatElt :
    CheckInput := true, FieldSize := 0,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> BoolElt, GrpSLPElt
    { G \leq GL(d, q) is isomorphic to Sz(q) and g \in GL(d, q).
    Determine if g \in G and express g as SLP in generators of G.
    }
    local q, flag, iso, sz, element;

    if CheckInput then
	flag, q := SuzukiRecognition(G);
	if not flag then
	    error "Sz constructive membership: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz constructive membership: Field size must be > 2";
	end if;

	flag, degree := IsPowerOf(FieldSize, 2);
	if not (flag and IsOdd(degree)) then
	    error "Sz constructive membershipreduction:",
		"Field size must be an odd prime power";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // Find reduction to standard Suzuki group
    iso, _, sz := SuzukiReduction(G : CheckInput := false,
	Randomiser := Randomiser, FieldSize := q);

    // Compute image in standard copy
    assert assigned sz`RandomProcess;
    element := Function(iso)(g);

    // Solve constructive membership in standard copy
    return SuzukiStandardConstructiveMembership(sz, element :
	CheckInput := false, Randomiser := sz`RandomProcess);
end intrinsic;

intrinsic IsSuzukiGroup(G :: GrpMat) -> BoolElt, RngIntElt
    { See SuzukiRecognition }

    return SuzukiRecognition(G);
end intrinsic;

intrinsic SuzukiRecognition(G :: GrpMat) -> BoolElt, RngIntElt
    { Determine (non-constructively) if G is isomorphic to
    Sz(q) for some q. The corresponding q is also returned.

    If G is in odd characteristic or has degree greater than 4, the
    Monte Carlo algorithm of LieType is used.
    If G has degree 4 and has characteristic 2, then a fast Las Vegas
    algorithm is used. }
    local recognition;

    if Degree(G) gt 4 or IsOdd(Characteristic(CoefficientRing(G))) then
	return SuzukiGeneralRecogniser(G);
    else
	recognition :=
	    SuzukiStandardRecogniser(G);
	if recognition then
	    return recognition, #CoefficientRing(G);
	else
	    recognition :=
		SuzukiConjugateRecogniser(G);
	    return recognition, #CoefficientRing(G);
	end if;
    end if;
end intrinsic;

intrinsic SuzukiGeneralRecogniser(G :: GrpMat) -> BoolElt, RngIntElt
    { Monte-Carlo check if G is isomorphic to Sz(q). Also returns q.}
    local recognition, lieType, type;

    if not IsAbsolutelyIrreducible(G) or IsOverSmallerField(G) then
	return false, 0;
    end if;

    vprint SuzukiGeneral, 5 : "Executing IdentifyLieType";
    recognition, lieType := LieType(G, 2);
    vprint SuzukiGeneral, 5 : "IdentifyLieType done", recognition;
    if recognition then
	vprint SuzukiGeneral, 5 : "Got answer", lieType;
    end if;

    if not recognition then
	return false, 0;
    end if;
    if not (lieType[1] eq "2B" and lieType[2] eq 2) then
	return false, 0;
    end if;

    return true, lieType[3];
end intrinsic;

intrinsic SuzukiStabiliser(G :: GrpMat, P :: ModTupFldElt  :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, UseDiscreteLog := true) -> [], RngIntElt
    { G \leq GL(4, q) and G is a conjugate of Sz(q). P is in the ovoid w.r.t G.
    Returns list of generators for stabiliser of <P> in G. Each list entry is
    a tuple with two elements: an SLP for the generator and then the generator.

    Also returns the time spent in discrete logarithm computations. }
    local stabiliser, elements, m, q, x, y, field, g, w, Q, bool, status,
	logTime, totalLogTime;

    if CheckInput then
	bool, status := SuzukiConjugateRecogniser(G);
	if not bool then
	    error "Sz stabiliser: G is not a conjugate of Sz",
		recognitionErrors[status];
	end if;
    end if;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    q := #field;
    stabiliser := {};
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if assigned G`SuzukiReductionData and
	assigned G`SuzukiReductionData`stdCopy then
	// Work in standard copy
	S := G`SuzukiReductionData`stdCopy;

	conjugator := getInfMappingMatrix(S, P);

	// Get generators of stabiliser by conjugating stabiliser of zero
	stab := [<g[1]^(conjugator[1]^(-1)),
	    g[2]^(conjugator[2]^(-1))>,
	    <h[1]^(conjugator[1]^(-1)), h[2]^(conjugator[2]^(-1))>]
	    where g is
	    Rep(S`SuzukiRecognitionData`upperGens`subDiagonal`generators)
	    where h is S`SuzukiRecognitionData`upperGens`diagonal;

	conjugator := G`SuzukiReductionData`conjugator^(-1);
	return [<stab[1][1], stab[1][2]^conjugator>,
	    <stab[2][1], stab[2][2]^conjugator>], 0;
    end if;

    // Find a random point different from P
    repeat
	g, w := Random(G`RandomProcess);
	Q := P * g;
	if Q eq P then
	    Include(~stabiliser, <w, g>);
	end if;
    until Q ne P;

    // Compute initial commutators
    stabiliser join:= {<(e[1], f[1]), (e[2], f[2])> :
	e in stabiliser, f in stabiliser};

    totalLogTime := 0;
    while not (exists(x){element : element in stabiliser |
	Order(element[2] : Proof := false) eq q - 1} and
	    exists(y){element :  element in stabiliser |
	    Order(element[2]) eq 4}) do

	    repeat
	    // Find an element mapping P to Q
	    elements, status, logTime :=
		findMappingElements(G`RandomProcess, P, Q, m :
		UseDiscreteLog := UseDiscreteLog);
	    totalLogTime +:= logTime;
	until not IsEmpty(elements);

	// Compute stabiliser elements and take commutators to get elements
	// of even order
	elements := {<w * e[1]^(-1), g * e[2]^(-1)> : e in elements};
	stabiliser join:= elements;

	stabiliser join:= {<(e[1], f[1]), (e[2], f[2])> :
	    e in stabiliser, f in elements};
    end while;

    return [y, x], totalLogTime;
end intrinsic;

intrinsic SuzukiPointStabiliser(G :: GrpMat : CheckInput := true,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    FieldSize := 0) -> GrpMat, [], ModTupFld
    { G \leq GL(d, q) and G is isomorphic to Sz(q).
    Returns generating set of a stabiliser of some point in the ovoid
    corresponding to G, SLPs of the generators in the generators of G, and
    the point that is stabilised.

    Only feasible for small q. Does not work for odd q. }
    local element1, element2, q, point, field, w1, w2, w, stabElts,
	inc, N, M, series;

    if CheckInput then
	recognition, q := SuzukiRecognition(G);
	if not recognition then
	    error "Sz stabiliser: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz stabiliser: Field size must be > 2";
	end if;
	if not (bool and prime eq 2 and IsOdd(degree))
	    where bool, prime, degree is IsPrimePower(FieldSize) then
	    error "Sz stabiliser: Field size must be an odd prime power";
	end if;

	q := FieldSize;
    end if;

    field := CoefficientRing(G);
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if #field ne q then
	error "Sz stabiliser: Cross char not possible";
    end if;

    // Find stabiliser
    stabElts := getStabiliser(G : UseDiscreteLog := true, FieldSize := q);
    element1 := stabElts[1][2];
    w1 := stabElts[1][1];
    element2 := stabElts[2][2];
    w2 := stabElts[2][1];

    assert Evaluate([w1, w2], UserGenerators(G)) eq [element1, element2];

    stab := sub<Generic(G) | element2, element1>;
    M := GModule(stab);

    series := CompositionSeries(M);
    assert exists(N){f : f in series | Dimension(f) eq 1};
    N := rep{f : f in series | Dimension(f) eq 1};

    // Find stabilised point
    inc := Morphism(N, M);
    point := sub<V | [V ! ElementToSequence(inc(gen)) :
	gen in Basis(N)]> where V is VectorSpace(G);

    return stab, [w2, w1], point;
end intrinsic;

intrinsic SuzukiPermutationRepresentation(G :: GrpMat : CheckInput := true,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    FieldSize := 0) -> Map, GrpPerm, GrpPerm
    { G \leq GL(d, q) and G is isomorphic to Sz(q).
    Returns an isomorphism to a permutation group on q^2 + 1 points as well as
    the permutation group itself. Also returns a stabiliser of a point.

    Only feasible for small q. Does not work for odd q. }
    local q, flag, H, point, orbit, homo, permGroup, kernel;

    if CheckInput then
	flag, q := SuzukiRecognition(G);
	if not flag then
	    error "Sz perm rep: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz perm rep: Field size must be > 2";
	end if;
	if not (bool and prime eq 2 and IsOdd(degree))
	    where bool, prime, degree is IsPrimePower(FieldSize) then
	    error "Sz perm rep: Field size must be an odd prime power";
	end if;

	q := FieldSize;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if SuzukiStandardRecogniser(G) then
	V := VectorSpace(G);
	homo, permGroup, kernel := OrbitAction(G,
	    sub<V | elt<V | 1, 0, 0, 0>>);

	W := WordGroup(G);
	F := CoefficientRing(G);
	m := (Degree(F) - 1) div 2;

	_, _, gens := SuzukiStandardGeneratorsNaturalRep(m);
	HH := sub<Generic(G) | gens>;
	assert SuzukiStandardRecogniser(HH);

	flag, _, _, slp2g := RecogniseSz(G);
	assert flag;
	H_w := [W ! Function(slp2g)(x) : x in [HH.2, HH.1]];

    else
	repeat
	    vprint SuzukiGeneral, 5: "Finding stabiliser";
	    _, H_w, point := SuzukiPointStabiliser(G : CheckInput := false,
		Randomiser := Randomiser, FieldSize := q);

	    if Category(point) ne ModTupFld then
		flag := false;
		continue;
	    end if;

	    vprint SuzukiGeneral, 5: "Checking orbit size";
	    flag, orbit := OrbitBounded(G, point, q^2 + 1);
	until flag and #orbit eq q^2 + 1;

	vprint SuzukiGeneral, 5: "Found orbit";

	homo, permGroup, kernel := OrbitAction(G, orbit);
    end if;

    assert NumberOfGenerators(G) eq NumberOfGenerators(permGroup);
    //print NumberOfGenerators(Parent(H_w[1])), NumberOfGenerators(permGroup);
    stab := sub<permGroup | Evaluate(H_w, UserGenerators(permGroup))>;
    assert IsTrivial(kernel);
    return homo, permGroup, stab, H_w;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function SzStabPresentation(field, lambda, freeGroup, gens)

    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    x := freeGroup.1;
    y := freeGroup.2;

    // lambda is a primitive element of field
    minPoly1 := MinimalPolynomial(lambda^(1 + t));
    assert not IsZero(Coefficient(minPoly1, 0)) and
	not IsZero(Coefficient(minPoly1, Degree(field)));

    minPoly2 := MinimalPolynomial(lambda);
    assert not IsZero(Coefficient(minPoly2, 0)) and
	not IsZero(Coefficient(minPoly2, Degree(field)));

    prod := &*[gens[1]^(gens[2]^i) : i in Reverse([0 .. Degree(field)]) |
	not IsZero(Coefficient(minPoly2, i))];
    basis := [((gens[1]^2)^(gens[2]^i))[4, 2] :
	i in [0 .. Degree(field) - 1]];

    V, inc := VectorSpace(field, PrimeField(field), basis);
    e := Coordinates(V, inc(prod[4, 2]));
    assert #e eq Degree(field);

    if IsIdentity(prod) then
	rhs := Identity(freeGroup);
    else
	rhs := &*[(x^(y^i))^2 : i in Reverse([0 .. Degree(field) - 1]) |
	    not IsZero(e[i + 1])];
    end if;

    // Relations for Frobenius group, the point stabiliser
    stabiliserRels := [x^4, y^(q - 1),
	&*[(x^(y^i))^2 : i in Reverse([0 .. Degree(field)]) |
	not IsZero(Coefficient(minPoly1, i))],
	&*[(x^(y^i)) : i in Reverse([0 .. Degree(field)]) |
	not IsZero(Coefficient(minPoly2, i))] * rhs^(-1)] cat
	&cat[[(x^2, x^(y^i)),
	(x, x^(y^i)) * ((x^(y^(i * (t - 1))))^2 *
	(x^(y^(i * (2 - t))))^2)^(-1)] :
	i in [1 .. Degree(field) - 1]];

    return stabiliserRels;
end function;

function checkSuzukiProperSubgroups(G)
    local c;

    // Check that all generators do not fix a point, ie check that they act
    // irreducibly on the full vector space, using MeatAxe
    if not IsAbsolutelyIrreducible(G) then
	return false;
    end if;

    // Check that the generators cannot be written over a smaller field, use
    // code in Magma, ie SmallerField
    if IsOverSmallerField(G) then
	return false;
    end if;

    for i in [1 .. NumberOfGenerators(G) - 1] do
	for j in [i + 1 .. NumberOfGenerators(G)] do
	    c := (G.i, G.j);
	    if not IsIdentity(c) then
		if exists{x : x in Generators(G) | not IsIdentity(x) and
		    not IsIdentity((c, c^x))} then
		    return true;
		else
		    return false;
		end if;
	    end if;
	end for;
    end for;

    return false;
end function;

// Check if G is 2.Sz(8) or 2^2.Sz(q) rather than Sz(8)
function is2Sz8(G, q)

    // The center of 2.Sz(8) is non-trivial, which we can easily check
    // when q = 8, and center is the same as the soluble radical in this case
    if q eq 8 then
	vprint SuzukiGeneral, 2 : "Check for center";
	if not IsTrivial(SolubleRadical(G)) then
	    return true;
	end if;
    end if;

    return false;
end function;

function Recognise2Sz8(G)

    RandomSchreier(G);

    W, slpHomo := WordGroup(G);
    phi := InverseWordMap(G);
    assert W cmpeq Codomain(phi);

    // Standard copy is the group itself
    slpMap := hom<G -> W | x :-> x notin G select false else phi(x)>;
    slpCoercion := IdentityHomomorphism(W);
    S := sub<Generic(Sz(8)) | UserGenerators(Sz(8))>;
    q := 8;
    AssertAttribute(S, "Order", getSuzukiOrder(q));
    // Remove scalars at the bottom
    // Obtain Sz regular perm rep
    vprint SuzukiGeneral, 2 : "Quotient out by center";
    H := SolubleRadical(G);
    GG, f1 := quo<G | H>;

    vprint SuzukiGeneral, 2 : "Find standard gens";

    // Obtain standard generators
    gensGG := SzBlackBoxGenerators(GG, GF(8));
    gensS := SzBlackBoxGenerators(S, GF(8));

    // Isomorphism induced from standard generators
    GS := sub<GG | gensGG>;

    W := WordGroup(GS);
    GS`SzCrossCharData := GG`SzCrossCharData;
    GS`SzCrossCharData`stdSLPs := UserGenerators(W);
    GS`RandomProcess :=
	RandomProcessWithWords(GS : WordGroup := W, Scramble := 1);

    W := WordGroup(S);
    S`SzCrossCharData`stdSLPs := UserGenerators(W);
    S`RandomProcess :=
	RandomProcessWithWords(S : WordGroup := W, Scramble := 1);

    iso := hom<GS -> S | g :-> Evaluate(w, gensS)
    where _, w is SzBlackBoxMembership(GS, g)>;
    inv := hom<S -> GS | g :-> Evaluate(w, gensGG)
    where _, w is SzBlackBoxMembership(S, g)>;

    vprint SuzukiGeneral, 2 : "2Sz8 perm rep iso found";

    // iso * inv is the identity modulo scalars
    iso := f1 * iso;
    inv := inv * Inverse(f1);

    ruleIso := hom<G -> S | x :-> iso(x)>;
    ruleInv := hom<S -> G | x :-> inv(x)>;

    G`SuzukiReductionData := rec<SuzukiReductionFormat |
	maps := rec<SuzukiReductionMaps | crossChar := iso>,
	slpHomoInv := slpMap,
	slpCoercion := slpCoercion,
	slpHomo := slpHomo,
	stdCopy := S,
	iso := ruleIso,
	inv := ruleInv>;

    //G`RandomProcess := RandomProcessWithWords(G : Generators := UserGenerators(GS), WordGroup := WordGroup(GS));
    G`RandomProcess := RandomProcessWithWords(GS : WordGroup := WordGroup(GS));
    S`RandomProcess := RandomProcessWithWords(S : WordGroup := W);
    return ruleIso, ruleInv, S;
end function;

function BraySzRelations(F)

    m := (Degree(F) - 1) div 2;

    // Bray's ordering of generators: put stabiliser generators first, to get
    // stabiliser relations easily
    // x is element of order 4
    // y is diagonal matrix of order q-1
    // z is anti-diagonal
    WG<x, y, z> := SLPGroup(3);

    WS<xs, ys> := SLPGroup(2);
    //stabToFull := hom<WS -> WG | [<xs, x>, <ys, y>]>;
    stabToFull := hom<WS -> WG | x, y>;

    lambda := PrimitiveElement(F);
    assert MinimalPolynomial(lambda) eq DefiningPolynomial(F);

    // Bray's Suzuki standard generators
    _, _, bgens := SuzukiStandardGeneratorsNaturalRep(m);

    // Relations for Frobenius group, the point stabiliser
    stabiliserRels := SzStabPresentation(F, lambda, WS, bgens[1 .. 2]);

    // Complete Sz relations on Bray generators
    relations := stabToFull(stabiliserRels) cat [z^2, (y * z)^2,
	x * z * x^2 * z * x^(-1) * z];

    return relations, stabiliserRels;
end function;
