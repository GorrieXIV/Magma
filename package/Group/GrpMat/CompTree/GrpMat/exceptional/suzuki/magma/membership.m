/******************************************************************************
 *
 *    membership.m Suzuki constructive membership testing code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-03-31
 *
 *    Version   : $Revision:: 3160                                           $:
 *    Date      : $Date:: 2015-11-02 09:56:37 +1100 (Mon, 02 Nov 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: membership.m 3160 2015-11-01 22:56:37Z jbaa004                 $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiMembership, 10;

forward performRightRowOperations, findFixedPoint, ovoidPoint,
    getDiagonalMatrix, getSuzukiStandardGenerators, constructDiagonalMatrix,
    getInfMappingMatrix, getZeroMappingMatrix, getSuzukiDiagonalGenerators,
    getSuzukiSylowGen, getSuzukiRecognitionData,
    SuzukiConstructiveMembershipEngine;

// Information stored with standard Sz copy, containing data used in
// membership testing
SuzukiRecognitionFormat := recformat<
    upperStab : GrpMat,  // Upper triangular stabiliser
    upperSLPs : SeqEnum, // SLPs of upper triangular generators
    lowerStab : GrpMat,  // Lower triangular stabiliser
    lowerSLPs : SeqEnum, // SLPs of lower triangular generators
    lowerGens : Rec,     // Generators of lower triangular Sylow 2-subgroup
    upperGens : Rec,     // Generators of upper triangular Sylow 2-subgroup
    slpGroup : GrpSLP,   // SLP group with redundant generators
    slpHomo : Map,       // Coercion from slpGroup to WordGroup
    slpHomoInv : Map>;   // Coercion from WordGroup to slpGroup

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiStandardConstructiveMembership(G :: GrpMat, g :: GrpMatElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true) -> BoolElt, GrpSLPElt
    { G is Sz(q), the standard copy, and g \in GL(4, q).
    
    Return true and straight line program of g in generators of G, if g \in G.
    Otherwise return false. }
    local bool, slp;

    if CheckInput then
	if not SuzukiStandardRecogniser(G) then
	    error "G is not the standard Suzuki group";
	end if;
    end if;

    vprint SuzukiMembership, 2 : "Non-explicit membership";
    
    // Non-constructive membership is easy
    if not SuzukiStandardMembership(g) then
	return false, _;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    vprint SuzukiMembership, 2 : "Get recognition data";
    assert assigned G`SuzukiRecognitionData;
    vprint SuzukiMembership, 2 : "Get SLP for given element";

    // Perform constructive membership
    bool, slp := SuzukiConstructiveMembershipEngine(G, g);
    if not bool then
	return false, _;
    end if;

    return bool, slp;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Core of the constructive membership routine
function SuzukiConstructiveMembershipEngine(G, g)
    local field, m, t, element, fixingElement, diagonal, diag, SLP, fixedPoint,
	h, word;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);

    assert assigned G`RandomProcess;
    assert assigned G`SuzukiRecognitionData;

    vprint SuzukiMembership, 1: "Entering Suzuki constructive membership";

    // Convert to an element that fixes at least one point
    fixedPoint, h, word := findFixedPoint(g, G`RandomProcess,
	Identity(G`SuzukiRecognitionData`slpGroup));

    // fixedPoint is in the ovoid and is fixed by h
    // Find an element in the stabiliser of infinity that maps fixedPoint
    // to zero. We contruct it using row operations
    element := getInfMappingMatrix(G, fixedPoint);

    // fixingElement is in the stabiliser of zero => upper triangular
    // Write it in terms of upperGens by using row operations
    fixingElement := <Identity(G`SuzukiRecognitionData`slpGroup),
	(g * h)^element[2]>;

    // Transform element into a diagonal matrix
    diagonal := getDiagonalMatrix(fixingElement, G`SuzukiRecognitionData);

    // Construct diagonal matrix as a word
    if not IsIdentity(diagonal[2]) then
	diag := constructDiagonalMatrix(G, diagonal);
	assert diag[2] eq diagonal[2];
	
	diagonal[1] *:= diag[1]^(-1);
	diagonal[2] *:= diag[2]^(-1);
    end if;

    // Create word of g in generators
    SLP := (diagonal[1]^(-1))^(element[1]^(-1)) *
	(G`SuzukiRecognitionData`slpGroup ! (word^(-1)));

    vprint SuzukiMembership, 1: "Leaving Suzuki constructive membership";
    return true, SLP;
end function;

function getSuzukiRecognitionDataCore(G, lowerStabiliser, upperStabiliser,
    inputWordGroup)       
    field := CoefficientRing(G);

    U := sub<Generic(G) | lowerStabiliser[1][2], lowerStabiliser[2][2]>;
    U`RandomProcess := RandomProcessWithWords(U : WordGroup := WordGroup(U));

    L := sub<Generic(G) | upperStabiliser[1][2], upperStabiliser[2][2]>;
    L`RandomProcess := RandomProcessWithWords(L : WordGroup := WordGroup(L));
    
    // Add these SLPs to our word group, for optimisation
    extraSLPs := [lowerStabiliser[1][1], lowerStabiliser[2][1],
	upperStabiliser[1][1], upperStabiliser[2][1]];
    vprint SuzukiMembership, 5: "Extending SLP group";
    wordGroup := AddRedundantGenerators(inputWordGroup, extraSLPs);
    
    // Map from extended word group to standard word group
    slpMap := hom<wordGroup -> inputWordGroup | [H.i : i in
    [1 .. NumberOfGenerators(H)]] cat extraSLPs where H is inputWordGroup>;

    // Coercion from standard word group to extended word group
    slpMapInv := hom<inputWordGroup -> wordGroup |
    [wordGroup.i : i in [1 .. NumberOfGenerators(G)]]>;
    
    // Construct standard generators for Gauss-Jordan elimination
    recognitionData := rec<SuzukiRecognitionFormat |
	lowerStab := L, lowerSLPs := [lowerStabiliser[1][1],
	lowerStabiliser[2][1]],
	upperStab := U, upperSLPs := [upperStabiliser[1][1],
	upperStabiliser[2][1]],
	lowerGens :=
	getSuzukiStandardGenerators(field, lowerStabiliser, wordGroup),
	upperGens :=
	getSuzukiStandardGenerators(field, upperStabiliser, wordGroup),
	slpGroup := wordGroup, slpHomo := slpMap, slpHomoInv := slpMapInv>;
    
    return recognitionData;
end function;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Returns a point in the ovoid of standard Sz
function ovoidPoint(x, y, m : UseInfinity := false)
    local V, pi, t, q;

    q := 2^(2 * m + 1);
    t := 2^(m + 1);
    pi := func<x | x^t>;
    V := VectorSpace(GF(q), 4);

    return UseInfinity select elt<V | 1, 0, 0, 0> else
	elt<V | x * y + pi(x) * x^2 + pi(y), y, x, 1>;
end function;

procedure performRightRowOperations(~element, generators, lookup)
    local fieldBasis, fieldSpace, fieldIso, coordinates, field;

    field := CoefficientRing(element[2]);
    
    if not IsZero(lookup) then
	// Construct base of finite field over its prime subfield
	fieldBasis := SetToSequence(generators`basis);
	fieldSpace, fieldIso :=
	    VectorSpace(field, PrimeField(field), fieldBasis);
	
	// Adjust first super/sub diagonal of element
	coordinates := Coordinates(fieldSpace, fieldIso(lookup));
	element[1] *:= &*[generators`generators[index][1] :
	    i in [1 .. #coordinates] | not IsZero(coordinates[i])
	    where index is Index(generators`basis, fieldBasis[i])];	
	element[2] *:= &*[generators`generators[index][2] :
	    i in [1 .. #coordinates] | not IsZero(coordinates[i])
	    where index is Index(generators`basis, fieldBasis[i])];
    end if;
end procedure;

procedure performLeftRowOperations(~element, generators, lookup)
    local fieldBasis, fieldSpace, fieldIso, coordinates, field;

    field := CoefficientRing(element[2]);
    if not IsZero(lookup) then
	// Construct base of finite field over its prime subfield
	fieldBasis := SetToSequence(generators`basis);
	fieldSpace, fieldIso :=
	    VectorSpace(field, PrimeField(field), fieldBasis);
	
	// Adjust first super/sub diagonal of element
	coordinates := Coordinates(fieldSpace, fieldIso(lookup));
	element[1] := &*[generators`generators[index][1] :
	    i in [1 .. #coordinates] | not IsZero(coordinates[i])
	    where index is Index(generators`basis, fieldBasis[i])]
	    * element[1];
	element[2] := &*[generators`generators[index][2] :
	    i in [1 .. #coordinates] | not IsZero(coordinates[i]) 
	    where index is Index(generators`basis, fieldBasis[i])]
	    * element[2];
    end if;
end procedure;

// Express a diagonal matrix in terms of our standard generators
function constructDiagonalMatrix(G, diagonal)
    local element, trace, field, q, a, b, upperElt, lowerElt, conjugator, m, t;

    field := CoefficientRing(diagonal[2]);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    trace := Trace(diagonal[2]);
    identity := <Identity(G`SuzukiRecognitionData`slpGroup), Identity(Generic(G))>;

    // Construct element in the generators with correct trace
    upperElt := identity;
    performLeftRowOperations(~upperElt,
	G`SuzukiRecognitionData`upperGens`subsubDiagonal, One(field));
    lowerElt := identity;
    performLeftRowOperations(~lowerElt,
	G`SuzukiRecognitionData`lowerGens`subsubDiagonal, Root(trace^t, 4));
    element := <(lowerElt[1], upperElt[1]), (lowerElt[2], upperElt[2])>;

    // Check that we got correct order
    assert Trace(element[2]) eq trace;
    assert IsDivisibleBy(q - 1, Order(element[2] : Proof := false));
    assert Order(element[2] : Proof := false) eq
	Order(diagonal[2] : Proof := false);
    
    // Get element that conjugates us to a diagonal matrix
    _, points := SuzukiCyclicEigenvalues(element[2]);   
    a := getInfMappingMatrix(G, points[1]);
    b := getZeroMappingMatrix(G, points[4] * a[2]);
    conjugator := <a[1] * b[1], a[2] * b[2]>;

    // Hope that we got correct diagonal (there are 2 possibilities)
    element := <element[1]^conjugator[1], element[2]^conjugator[2]>;

    // Take the element or its inverse
    assert element[2] in {diagonal[2], diagonal[2]^(-1)};
    if element[2] eq diagonal[2] then
	return element;
    else
	return <element[1]^(-1), element[2]^(-1)>;
    end if;
end function;

function findFixedPoint(element, randomiser, identityWord)
    local g, residue, word, m, t;

    m := (Degree(CoefficientRing(element)) - 1) div 2;
    t := 2^(m + 1);
    word := identityWord;
    
    // Transform element into another element that fixes a point
    repeat
	repeat
	    residue, word := Random(randomiser);
	    g := element * residue;
	until not IsEmpty(Eigenvalues(g));

	fixedPoint := rep{Rep(Basis(Eigenspace(g, f))) :
	    f in eigenvalues}
	    where eigenvalues is {e[1] : e in Eigenvalues(g)};
    until not IsZero(fixedPoint[4]) and
	(IsZero(point[1] + point[2] * point[3] + point[2]^t + point[3]^(t + 2))
	where point is fixedPoint * fixedPoint[4]^(-1));

    assert Normalise(fixedPoint * g) eq Normalise(fixedPoint);
    
    return fixedPoint, residue, word;
end function;

// Find matrix as word in our generators that takes the given point to the
// infinity point
function getInfMappingMatrix(G, point)
    local lookup, element;
    
    assert assigned G`SuzukiRecognitionData;
    
    element := <Identity(G`SuzukiRecognitionData`slpGroup), Identity(Generic(G))>;

    if not IsZero(point[4]) then
	point *:= point[4]^(-1);
	
	// Construct first subdiagonal
	lookup := point[3];
  	performRightRowOperations(~element,
	    G`SuzukiRecognitionData`lowerGens`subDiagonal, lookup);

	// Construct second subdiagonal
	lookup := point[2] + element[2][3, 1];
	performRightRowOperations(~element,
	    G`SuzukiRecognitionData`lowerGens`subsubDiagonal, lookup);

    end if;
    vprint SuzukiMembership, 5: Normalise(point * element[2]);
    
    return element;
end function;

// Find matrix as word in our generators that takes the given point to the
// zero point
function getZeroMappingMatrix(G, point)
    local lookup, element, t, m;
    
    assert assigned G`SuzukiRecognitionData;

    m := (Degree(CoefficientRing(G)) - 1) div 2;
    t := 2^(m + 1);
    element := <Identity(G`SuzukiRecognitionData`slpGroup), Identity(Generic(G))>;

    if not IsZero(point[1]) then
	point *:= point[1]^(-1);
	
	// Construct first subdiagonal
	lookup := point[2];
	performRightRowOperations(~element,
	    G`SuzukiRecognitionData`upperGens`subDiagonal, lookup);
	
	// Construct second subdiagonal
	lookup := point[3] + point[2]^(t + 1) + element[2][1, 3];
	performRightRowOperations(~element,
	    G`SuzukiRecognitionData`upperGens`subsubDiagonal, lookup);
    end if;
    vprint SuzukiMembership, 5: Normalise(point * element[2]);
    
    return element;
end function;

// Get "standard" generators for the stabiliser of a point in Sz
function getSuzukiStandardGenerators(field, stabiliser, slpGroup)
    local conjugator, conjugatee, gens, elements, generator,
	normaliser, standardGenerators, value, diagonal, generatorFormat,
	coordinates, power;

    // The element of order 4
    conjugatee := <slpGroup ! stabiliser[1][1], stabiliser[1][2]>;

    // The element of order q - 1
    conjugator := <slpGroup ! stabiliser[2][1], stabiliser[2][2]>;
    assert Order(conjugator[2] : Proof := false) eq #field - 1 and
	Order(conjugatee[2]) eq 4;

    // Store generators in a proper structure
    generatorFormat := recformat<basis : SetIndx, generators : SetIndx>;
    allGensFormat := recformat<subDiagonal : Rec, subsubDiagonal :
	Rec, diagonal : Tup>;
    
    standardGenerators := rec<allGensFormat | diagonal := conjugator>;
    gens := {@ @};
    elements := {@ @};
    power := conjugator;
    
    // Create first set of standard generators, which all have order 4
    for i in [1 .. Degree(field)] do
	generator := <conjugatee[1]^power[1], conjugatee[2]^power[2]>;

	// element is either lower or upper triangular
	if IsUpperTriangular(generator[2]) then
	    value := generator[2][1, 2];
	else
	    value := generator[2][2, 1];
	end if;

	// Store element and its defining field element
	Include(~elements, value);
	Include(~gens, generator);
	power := <power[1] * conjugator[1], power[2] * conjugator[2]>;
    end for;
    assert #elements eq Degree(field);

    standardGenerators`subDiagonal :=
	rec<generatorFormat | basis := elements, generators := gens>;

    // Create second set of standard generators, which all have order 2
    gens := {@ @};
    elements := {@ @};
    conjugatee[1] *:= conjugatee[1];
    conjugatee[2] *:= conjugatee[2];
    power := conjugator;

    for i in [1 .. Degree(field)] do
	generator := <conjugatee[1]^power[1], conjugatee[2]^power[2]>;
	
	// element is either lower or upper triangular
	if IsUpperTriangular(generator[2]) then
	    value := generator[2][1, 3];
	else
	    value := generator[2][3, 1];
	end if;

	// Store element and its defining field element
	Include(~elements, value);
	Include(~gens, generator);
	power := <power[1] * conjugator[1], power[2] * conjugator[2]>;
    end for;
    assert #elements eq Degree(field);
    
    standardGenerators`subsubDiagonal :=
	rec<generatorFormat | basis := elements, generators := gens>;
    
    return standardGenerators;
end function;

// Construct a diagonal matrix from the given triangular matrix
function getDiagonalMatrix(element, generators)
    local value;
    
    // Use row operations to eradicate super/sub diagonals    
    if IsUpperTriangular(element[2]) then
	value := element[2][1, 2] * element[2][1, 1]^(-1);
	performRightRowOperations(~element, generators`upperGens`subDiagonal,
	    value);
    else
	value := element[2][2, 1] * element[2][2, 2]^(-1);
	performRightRowOperations(~element, generators`lowerGens`subDiagonal,
	    value);
    end if;
   
    if IsUpperTriangular(element[2]) then
	value := element[2][1, 3] * element[2][1, 1]^(-1);
	performRightRowOperations(~element,
	    generators`upperGens`subsubDiagonal, value);
    else
	value := element[2][3, 1] * element[2][3, 3]^(-1);
	performRightRowOperations(~element,
	    generators`lowerGens`subsubDiagonal, value);
    end if;

    assert IsDiagonal(element[2]);
    return element;
end function;
