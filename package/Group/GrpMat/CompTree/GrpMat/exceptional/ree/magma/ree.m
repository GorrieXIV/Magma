/******************************************************************************
 *
 *    ree.m    Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-04-30
 *
 *    Version   : $Revision:: 2060                                           $:
 *    Date      : $Date:: 2010-11-18 21:46:13 +1100 (Thu, 18 Nov 2010)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: ree.m 2060 2010-11-18 10:46:13Z eobr007                        $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare attributes GrpMat: ReeRecognitionData, ReeReductionData, ReeMaximals;

declare verbose ReeGeneral, 10;

import "standard.m": getReeMagmaCBM, getReeSylowGen, getReeDiagonalElt,
    isOrbitPoint, checkTwistedMiddleAlgebra, getReeInfSylowGenMatrix,
    getReeDiagonal, getOrbitPoint, getReeOrder;

import "membership.m": getReeRecognitionData;

import "../../../util/basics.m" : getMapFunction, MatSLP;

// Store isomorphisms to standard copy
ReeReductionMaps := recformat<
    tensor : Map,      // Tensor decomposition map
    symSquare : Map,   // 27-dim decomposition map
    conjugation : Map, // Conjugation to standard copy
    crosschar : Map>;  // Map from cross char rep to standard copy

// Store information for constructive recognition
ReeReductionFormat := recformat<
    maps : Rec,             // ReeReductionMaps
    conjugator : GrpMatElt, // Conjugating element to standard copy
    tensorCBM : GrpMatElt,  // Tensor decomposition change of basis
    stdCopy : GrpMat,       // The standard copy
    iso : Map,              // Isomorphism to standard copy
    inv : Map,              // Isomorphism from standard copy
    slpHomo : Map,          // Evaluate SLPs in given copy
    slpHomoInv : Map,       // Express elements as SLPs
    slpGroup : GrpSLP,      // Parent of SLPs returned
    slpCoercion : Map>;     // Convert from SLP group to WordGroup

forward ReeTrivialRecognitionChecks;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAGMA STANDARD INTERFACE INTRINSICS                                       */
/*****************************************************************************/

// Provide intrinsics similar to the ones for SL2 and Sz

intrinsic RecogniseRee(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimise := false) ->
    BoolElt, Map, Map, Map, Map
    { Constructively recognise G as a Ree group. If G is isomorphic to Ree(q)
    where q is the size of the defining field of G, then return:
    1. Isomorphism from G to Ree(q).
    2. Isomorphism from Ree(q) to G.
    3. Map from G to the word group of G.
    4. Map from the word group of G to G.

    The isomorphisms are composed of maps that are defined by rules,
    so Function can be used on each component.
    The word group is the GrpSLP which is the parent of the elements returned
    from ReeElementToWord. In general this is not the same as WordGroup(G), but
    is created from it using AddRedundantGenerators.
    
    If Verify is true, then it is checked that G really is isomorphic to
    Ree(q), otherwise this is not checked. In that case, the FieldSize must be
    set to the correct value of q. }
    local flag, iso, inv, q;
    
    if Verify then
	flag, q := ReeRecognition(G);
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Field size must be greater than 3";
	end if;
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Field size must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
	flag := true;
    end if;

    if not flag then
	return false, _, _, _, _;
    end if;
    
    iso, inv := ReeReduction(G : CheckInput := false, FieldSize := q,
	Optimise := Optimise);
    assert assigned G`ReeReductionData`slpHomo;
    assert assigned G`ReeReductionData`slpHomoInv;
    
    return true, iso, inv, G`ReeReductionData`slpHomoInv,
	G`ReeReductionData`slpHomo;
end intrinsic;


intrinsic ReeResetRandomProcess(G :: GrpMat) -> BoolElt
    { G is isomorphic to Ree(q) and RecogniseRee(G) has returned true.
    Resets the random process used in the constructive membership,
    so that the SLPs are again short. }
    
    if not assigned G`ReeReductionData then
	return false;
    end if;

    assert assigned G`ReeReductionData`stdCopy;
    G`ReeReductionData`stdCopy`RandomProcess :=
	RandomProcessWithWords(G`ReeReductionData`stdCopy :
	WordGroup := WordGroup(G));
    vprint ReeGeneral, 5 : "Random process reset";
    
    return true;
end intrinsic;

intrinsic RecognizeRee(G :: GrpMat : Verify := true, FieldSize := 0,
    Optimize := false) ->
    BoolElt, Map, Map, Map, Map
    { See RecogniseRee }
    
    return RecogniseRee(G : Verify := Verify, FieldSize := FieldSize,
	Optimise := Optimize);
end intrinsic;

intrinsic ReeElementToWord(G :: GrpMat, g :: GrpMatElt) -> BoolElt, GrpSLPElt
    { If G has been constructively recognised as a Ree group,
    and if g is an element of G, then return GrpSLPElt from word group of G
    which evaluates to g, else false.
    This facilitates membership testing in G. }
    local q;
    
    if not assigned G`ReeReductionData then
	return false, _;
    end if;

    q := #CoefficientRing(G`ReeReductionData`stdCopy);
    assert assigned G`RandomProcess;
    return ReeConstructiveMembership(G, g : CheckInput := false,
	Randomiser := G`RandomProcess, FieldSize := q);
end intrinsic;

intrinsic ReeSLPCoercion(G :: GrpMat) -> Map
    { Return the SLP coercion map, which is a homomorphism from the word group
    of G to WordGroup(G). }

    if not assigned G`ReeReductionData then
	error "G must be a recognised Ree group";
    end if;

    assert assigned G`ReeReductionData`slpCoercion;
    return G`ReeReductionData`slpCoercion;
end intrinsic;

intrinsic ReeRedundantSLPGenerators(G :: GrpMat) -> []
    { If G has been constructively recognised as a Ree group, return the
    extra generators in the word group of G. }
    local W, nGens;
    
    if not assigned G`ReeReductionData then
	error "G must be a recognised Ree group";
    end if;
    
    assert assigned G`ReeReductionData`slpCoercion;
    W := Domain(G`ReeReductionData`slpCoercion);
    nGens := NumberOfGenerators(G);
    return [G`ReeReductionData`slpCoercion(W.i) :
	i in [nGens + 1 .. NumberOfGenerators(W)]];
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

// overwritten by later redefinition of Ree (q)  
/* 

intrinsic Ree(m :: RngIntElt) -> GrpMat
    { m is a positive integer. Return Ree(3^(2m + 1)) on its
    standard generators. }
    local field;

    require m gt 0 : "m must be positive";
    
    field := GF(3, 2 * m + 1);
    return ReeStandardCopy(field);
end intrinsic;

*/

intrinsic Ree(F :: FldFin) -> GrpMat
    { |F| = 3^(2m + 1) with m > 0. Return Ree(F) on its standard generators. }

    if not ReeTrivialRecognitionChecks(F) then
	error "#F must be an odd power of 3";
    end if;
    return ReeStandardCopy(F);
end intrinsic;

intrinsic ReeGroup(F :: FldFin) -> GrpMat
    { |F| = 3^(2m + 1) with m > 0. Return Ree(F) on its standard generators. }

    return Ree(F);
end intrinsic;

intrinsic Ree(q :: RngIntElt) -> GrpMat
    { q = 3^(2m + 1) with m > 0. Return Ree(q) on its standard generators. }
    local field;

    field := GF(q);
    if not ReeTrivialRecognitionChecks(field) then
	error "q must be an odd power of 3";
    end if;
    
    return ReeStandardCopy(field);
end intrinsic;

intrinsic ReeGroup(q :: RngIntElt) -> GrpMat
    { q = 3^(2m + 1) with m > 0. Return Ree(q) on its standard generators. }

    return Ree(q);
end intrinsic;

intrinsic Ree(V :: ModTupRng) -> GrpMat
    { Given a 7-dimensional vector space V over the finite field GF(q), where
    q = 3^(2m + 1) with m > 0, return Ree(V) on its standard generators. }
    local field;

    field := CoefficientRing(V);
    if not (Degree(V) eq 7 and Dimension(V) eq 7 and
	ReeTrivialRecognitionChecks(field)) then
	error "q must be an odd power of 3 and V of dimension 7";
    end if;
    
    return ReeStandardCopy(field);
end intrinsic;

intrinsic ReeGroup(V :: ModTupRng) -> GrpMat
    { Given a 7-dimensional vector space V over the finite field GF(q), where
    q = 3^(2m + 1) with m > 0, return Ree(V) on its standard generators. }

    return Ree(V);
end intrinsic;

intrinsic ReeGeneralRecogniser(G :: GrpMat) -> BoolElt, RngIntElt
    { Monte-Carlo check if G is isomorphic to Ree(q). Also returns q.}
    local recognition, lieType;

    if not IsAbsolutelyIrreducible(G) or IsOverSmallerField(G) then
	return false, 0;
    end if;

    vprint ReeGeneral, 5 : "Executing IdentifyLieType";
    recognition, lieType := LieType(G, 3);
    vprint ReeGeneral, 5 : "IdentifyLieType done", recognition;

    if recognition then
	vprint ReeGeneral, 5 : "Got answer", lieType;
    end if;
    
    if not recognition then
	return false, 0;
    end if;
    if not (lieType[1] eq "2G" and lieType[2] eq 2) then
	return false, 0;
    end if;
    
    return true, lieType[3];
end intrinsic;

intrinsic IsReeGroup(G :: GrpMat) -> BoolElt, RngIntElt
    { See ReeRecognition }

    return ReeRecognition(G);
end intrinsic;

intrinsic ReeRecognition(G :: GrpMat) -> BoolElt, RngIntElt
    { G \leq GL(d, q). Determine (non-constructively) if G is isomorphic to
    Ree(q). The corresponding q is also returned.
    
    If G is in characteristic not 3 or has degree greater than 7, the
    Monte Carlo algorithm of LieType is used.
    If G has degree 7 and has characteristic 3, then a fast Las Vegas
    algorithm is used. }
    local recognition, status;

    if Characteristic(CoefficientRing(G)) ne 3 or Degree(G) ne 7 then
	return ReeGeneralRecogniser(G);
    else
	recognition := ReeStandardRecogniser(G);
	if not recognition then
	    recognition := ReeGeneralRecogniser(G);
	end if;
	return recognition, #CoefficientRing(G);
    end if;
end intrinsic;

intrinsic ReeReduction(G :: GrpMat : CheckInput := true, FieldSize := 0,
    Optimise := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> Map, Map
    { G \leq GL(d, q) is isomorphic to Ree(q). Compute explicit inverse
    isomorphisms to Ree(q). This is the Ree constructive recognition engine. }
    local q, recognition, flag, ree, tensorHomo, symSquareHomo,
	homo, inv, slpHomo;
    
    if CheckInput then
	recognition, q := ReeRecognition(G);
	if not recognition then
	    error "Ree reduction: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Ree reduction: Field size must be > 3";
	end if;
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Ree reduction: Field size must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    // Don't run constructive recognition twice
    if assigned G`ReeReductionData then
	assert assigned G`ReeReductionData`iso and
	    assigned G`ReeReductionData`inv;

	vprint ReeGeneral, 1: "Using precomputed reduction data";
	return G`ReeReductionData`iso, G`ReeReductionData`inv,
	    G`ReeReductionData`stdCopy;
    end if;

    // Setup data structure
    G`ReeReductionData := rec<ReeReductionFormat | maps :=
	rec<ReeReductionMaps | >>;
    ree := G;
    W, slpHomo := WordGroup(G);

    // Use cross char method if necessary
    flag, power := IsPowerOf(#CoefficientRing(ree), 3);
    if not (flag and power ge 3) then
	crossCharHomo :=
	    ReeCrossCharacteristicReduction(ree : CheckInput := false,
	    FieldSize := q, Randomiser := Randomiser);
	ree := Codomain(crossCharHomo);
    else
	// Check if we need to decompose
	if Degree(ree) gt 7 then
	    
	    // Check if we need to tensor decompose
	    if Degree(ree) gt 27 then
		
		vprint ReeGeneral, 1: "Running tensor decomposition";
		
		// Get homomorphism to tensor factor of dim 7 or 27
		tensorHomo, tensorCBM :=
		    ReeTensorDecompose(ree : Randomiser := Randomiser,
		    CheckInput := false, FieldSize := q, wordGroup := W);
		
		G`ReeReductionData`tensorCBM := tensorCBM;
		G`ReeReductionData`maps`tensor := tensorHomo;
		ree := Codomain(tensorHomo);
	    else
		// No tensor decomposition needed
		G`ReeReductionData`tensorCBM := Identity(ree);
		G`ReeReductionData`maps`tensor := hom<ree -> ree | x :-> x>;
	    end if;
	    
	    // Check if we have to decompose the symmetric square
	    if Degree(ree) gt 7 then
		
		vprint ReeGeneral, 1: "Decomposing symmetric square factor";
		
		// Get 7-dim natural from 27-dim symmetric square
		symSquareHomo :=
		    ReeSymmetricSquareDecompose(ree : CheckInput := false);
			    
		G`ReeReductionData`maps`symSquare := symSquareHomo;
		ree := Codomain(symSquareHomo);
	    else
		// No symmetric square decomposition needed
		G`ReeReductionData`maps`symSquare := hom<ree -> ree | x :-> x>;
	    end if;
	else
	    // No decomposition needed
	    G`ReeReductionData`maps`symSquare := hom<ree -> ree | x :-> x>;
	    G`ReeReductionData`maps`tensor := hom<ree -> ree | x :-> x>;
	    G`ReeReductionData`tensorCBM := Identity(ree);
	end if;
    end if;
    
    assert Degree(ree) eq 7;

    // Check if we need to conjugate to standard copy
    if not ReeStandardRecogniser(ree) then
	// Should be assigned only if no decomposition needed
	if not assigned ree`RandomProcess then
	    ree`RandomProcess :=
		RandomProcessWithWords(ree : WordGroup := W);
	end if;
	
	vprint ReeGeneral, 1: "Conjugating to standard Ree copy";
	conjHomo, conjugator :=
	    ReeConjugacy(ree : Randomiser := ree`RandomProcess,
	    CheckInput := false, wordGroup := W);
		
	G`ReeReductionData`conjugator := conjugator;
	G`ReeReductionData`maps`conjugation := conjHomo;
	ree := Codomain(conjHomo);
    else
	// No conjugation needed
	G`ReeReductionData`conjugator := Identity(ree);
	G`ReeReductionData`maps`conjugation := hom<ree -> ree | x :-> x>;
    end if;

    vprint ReeGeneral, 1: "Precompute constructive membership data";

    assert ReeStandardRecogniser(ree); 
    if not assigned ree`RandomProcess then
	ree`RandomProcess :=
	    RandomProcessWithWords(ree : WordGroup := W);
    else
	assert ReeStandardRecogniser(G);
    end if;

    if not assigned ree`ReeRecognitionData then
	ree`ReeRecognitionData := getReeRecognitionData(ree, false, W);
    end if;

    // Set order on standard copy
    ree`Order := getReeOrder(q);
    
    vprint ReeGeneral, 1: "Construct SLP homomorphism";
    
    // Construct homomorphisms that evaluate SLPs in input Ree group

    // Optimized SLP homo
    if Optimise then
	slpHomoOpt := hom<ree`ReeRecognitionData`slpGroup -> G | slpHomo>;
	G`ReeReductionData`slpHomo := slpHomoOpt;
    else
	G`ReeReductionData`slpHomo := slpHomo;
    end if;
    
    slpMap := hom<G -> ree`ReeRecognitionData`slpGroup | x :-> 
    flag eq true select slp else flag
	where flag, slp is ReeConstructiveMembership(G, x :
	CheckInput := false, Randomiser := G`RandomProcess, FieldSize := q)>;

    G`ReeReductionData`slpHomoInv := slpMap;
    G`ReeReductionData`slpCoercion := ree`ReeRecognitionData`slpMap;
    G`ReeReductionData`slpGroup := ree`ReeRecognitionData`slpGroup;
    
    vprint ReeGeneral, 1: "Construct isomorphism to standard Ree copy";
    
    // Construct homomorphism from given group to standard copy, by
    // composing the various computed homos
    // Cross-char homo does all in one step
    if assigned G`ReeReductionData`maps`crosschar then
	homo := hom<G -> ree | x :-> G`ReeReductionData`maps`crosschar(x)>;
    else
	homo := hom<G -> ree | x :->
	getMapFunction(G`ReeReductionData`maps`tensor *
	    G`ReeReductionData`maps`symSquare *
	    G`ReeReductionData`maps`conjugation)(x)>;
    end if;
    
    // Construct inverse isomorphism by solving constructive
    // membership in standard copy
    inv := hom<ree -> G | x :-> 
    flag eq true select G`ReeReductionData`slpHomo(slp) else flag
	where flag, slp is ReeStandardConstructiveMembership(ree, x :
	CheckInput := false, Randomiser := ree`RandomProcess)>;
    
    G`ReeReductionData`iso := homo;
    G`ReeReductionData`inv := inv;
    G`ReeReductionData`stdCopy := ree;

    vprint ReeGeneral, 1: "Ree reduction successful";
    return homo, inv, ree;
end intrinsic;

intrinsic ReeConstructiveMembership(G :: GrpMat, g :: GrpMatElt :
    CheckInput := true, FieldSize := 0,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> BoolElt, GrpSLPElt
    { G \leq GL(d, q) is isomorphic to Ree(q) and g \in GL(d, q).
    Determine if g \in G and express g as SLP in generators of G. }    
    local q, recognition, iso, ree, element;
    
    if CheckInput then
	recognition, q := ReeRecognition(G);
	if not recognition then
	    error "Ree constructive membership: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Ree constructive membership:",
		"Field size must be > 3";
	end if;
	
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Ree constructive membership:",
		"Field size must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // Find reduction to standard Ree group
    iso, _, ree := ReeReduction(G : CheckInput := false,
	Randomiser := Randomiser, FieldSize := q);

    // Compute image in standard copy
    assert assigned ree`RandomProcess;
    element := Function(iso)(g);

    // Solve constructive membership in standard copy
    return ReeStandardConstructiveMembership(ree, element :
	CheckInput := false, Randomiser := ree`RandomProcess);
end intrinsic;

intrinsic ReePermutationRepresentation(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)), CheckInput := true,
    FieldSize := 0) -> Map, GrpPerm
    { G \leq GL(d, q) and G is isomorphic to Ree(q).
    Returns an isomorphism to a permutation group on q^3 + 1 points as well as
    the permutation group itself.
    
    Only feasible for small q. Works only when q is an odd power of 3. }
    local V, P, orbit, iso, H, K, field, q, flag, point;
    
    if CheckInput then
	recognition, q := ReeRecognition(G);
	if not recognition then
	    error "Ree perm rep: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Ree perm rep: Field size must be > 3";
	end if;
	
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Ree perm rep: Field size must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
    end if;
    
    field := CoefficientRing(G);
    V := VectorSpace(field, Degree(G));
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    // Find random point and its orbit
    if ReeStandardRecogniser(G) then
	V := VectorSpace(G);
	iso, H, K := OrbitAction(G,
	    sub<V | elt<V | 0, 0, 0, 0, 0, 0, 1>>);

	W := WordGroup(G);

	HH := Ree(field);
	flag, _, _, slp2g := RecogniseRee(G : Verify := false, FieldSize := q);
	assert flag;
	
	H_w := [W ! slp2g(x) : x in [HH.2, HH.3]];
   else
	repeat
	    _, P, H_w := ReePointStabiliser(G : Randomiser := Randomiser,
		CheckInput := false, FieldSize := q);
	    vprint ReeGeneral, 2 : "Found point stabiliser";

	    // Compute permutation representation
	    //iso, H, K := OrbitAction(G, P);
	    //flag := true;
	    flag, iso, H, K := OrbitActionBounded(G, P, q^3 + 1);
	    vprint ReeGeneral, 2 : "Orbit action calculated";
	until flag;
    end if;

    assert NumberOfGenerators(G) eq NumberOfGenerators(H);
    stab := sub<H | Evaluate(H_w, UserGenerators(H))>;
    assert IsTrivial(K);
    
    return iso, H, stab, H_w;
end intrinsic;

intrinsic ReePointStabiliser(G :: GrpMat : CheckInput := true,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    FieldSize := 0) -> GrpMat, ModTupFld
    { G \leq GL(d, q) and G is isomorphic to Ree(q).
    Returns generating set of a stabiliser of some point in the ovoid
    corresponding to G, SLPs of the generators in the generators of G, and
    the point that is stabilised.
    
    Only feasible for small q. Works only when q is an odd power of 3. }
    local element1, element2, q, point, field, module, w1, w2, w, g, i;
    
    if CheckInput then
	recognition, q := ReeRecognition(G);
	if not recognition then
	    error "Ree stabiliser: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Ree perm rep: Field size must be > 3";
	end if;
	
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Ree perm rep: Field size must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
    end if;
    
    field := CoefficientRing(G);
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if #field ne q then
	error "Ree perm rep: Cannot find stabiliser in cross characteristic";
    end if;
    
    // Find element of order q - 1
    repeat
	element1, w1 := Random(G`RandomProcess);
    until Order(element1 : Proof := false) eq q - 1;
    
    // Take random pairs of elements of order q - 1
    repeat
	// Take random conjugate, hope that they stabilise a common point
	g, w := Random(G`RandomProcess);
	element2 := element1^g;
	w2 := w1^w;
	
	stab := sub<G | element1, element2>;
	M := GModule(stab);
	series, factors := CompositionSeries(M);
    until exists(N){f : f in series | Dimension(f) eq 1};

    // Find a stabilised point 
    inc := Morphism(N, M);
    point := sub<V | [V ! ElementToSequence(inc(gen)) : 
	gen in Basis(N)]> where V is VectorSpace(G);
    
    return stab, point, [w1, w2];
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Easy checks on the field, to see if it is the ground field of a Ree group
function ReeTrivialRecognitionChecks(field)
    local flag, p, k, q;

    if Category(field) ne FldFin then
	return false;
    end if;
    
    if Characteristic(field) eq 3 and IsOdd(Degree(field)) and
	Degree(field) gt 1 then
	return true;
    else
	return false;
    end if;
end function;
