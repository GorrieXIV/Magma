/******************************************************************************
 *
 *    membership.m    Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-05-31
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: membership.m 1605 2008-12-15 09:05:48Z jbaa004                 $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeMembership, 10;

import "standard.m": getReeInfSylowGen, getReeZeroSylowGen, isOrbitPoint,
    getOrbitPoint;
import "../../../util/basics.m" : MatSLP;

forward getReeStandardGenerators, performRightRowOperations,
    getReeRecognitionData, findFixedPoint, getInfMapping, getDiagonalMatrix,
    constructDiagonalMatrix, getZeroMapping;

// Structure for storing precomputed standard generators
ReeRecognitionFormat := recformat<
    upperStab : GrpMat,  // Upper triangular stabiliser
    upperSLPs : SeqEnum, // SLPs of upper triangular generators
    lowerStab : GrpMat,  // Lower triangular stabiliser
    lowerSLPs : SeqEnum, // SLPs of lower triangular generators
    lowerGens : Rec, // Standard generators for lower triangular stabiliser 
    upperGens : Rec, // Standard generators for upper triangular stabiliser 
    slpGroup : GrpSLP, // Parent of returned SLPs 
    slpMap : Map, // Map from slpGroup to standard WordGroup
    slpMapInv : Map // Map from standard WordGroup to slpGroup
    >;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeStandardConstructiveMembership(G :: GrpMat, g :: GrpMatElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> BoolElt, GrpSLPElt
    { G is Ree(q), the standard copy, and g \in GL(7, q).
    
    Return true and straight line program of g in generators of G, if g \in G.
    Otherwise return false. }
    local field, t, h, index, lookup, m, word, element,
	fixedPoint, SLP, fixingElement, fixingWord, diagonal;

    if CheckInput then
	if  not ReeStandardRecogniser(G) then
	    error "G is not the standard Ree group";
	end if;
    end if;
    
    field := CoefficientRing(G);
    q := #field;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    t := 3^m;

    // Non-constructive membership is easy
    if not ReeStandardMembership(g) then
	return false, _;
    end if;
    
    if not assigned G`ReeRecognitionData then
	G`ReeRecognitionData := getReeRecognitionData(G, false, wordGroup);
    end if;

    vprint ReeMembership, 1: "Entering Ree constructive membership";

    vprint ReeMembership, 2: "Find fixed point";

    repeat
	// Convert to an element that fixes at least one point
	fixedPoint, h, word := findFixedPoint(g, G`RandomProcess,
	    Identity(G`ReeRecognitionData`slpGroup));
	
	vprint ReeMembership, 2: "Compute cbm to zero point";
	
	// fixedPoint is in the ovoid and is fixed by h
	// Find an element in the stabiliser of infinity that maps fixedPoint
	// to zero. We contruct it using row operations
	element := getInfMapping(G, fixedPoint);
	
	// fixingElement is in the stabiliser of zero => lower triangular
	// Write it in terms of upperGens by using row operations
	fixingElement := rec<MatSLP | mat := (g * h)^element`mat, slp :=
	    Identity(G`ReeRecognitionData`slpGroup)>;
	
	vprint ReeMembership, 2: "Get diagonal matrix";
	
	diagonal := getDiagonalMatrix(fixingElement,
	    G`ReeRecognitionData`lowerGens, G`ReeRecognitionData`slpGroup);
	
	// Construct diagonal matrix as a word
	if not IsIdentity(diagonal`mat) then
	    vprint ReeMembership, 2: "Construct diagonal matrix";
	    
	    flag, diag := constructDiagonalMatrix(G, diagonal);
	    if flag then
		vprint ReeMembership, 2:
		    "Succeded in constructing diagonal matrix";
		diagonal`slp *:= diag`slp^(-1);
		diagonal`mat *:= diag`mat^(-1);
	    end if;
	end if;
    until IsIdentity(diagonal`mat);
    
    // Create word of g in generators
    SLP := (diagonal`slp^(-1))^(element`slp^(-1)) *
	(G`ReeRecognitionData`slpGroup ! word^(-1));
    
    vprint ReeMembership, 2: "Length of SLPs:", #SLP, #word,
	#diagonal`slp, #element`slp;
    vprint ReeMembership, 1: "Leaving Ree constructive membership";
    return true, SLP;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// transform element into an element that fixes a point
function findFixedPoint(element, randomiser, identityWord)
    local g, residue, word, m, t;

    m := (Degree(CoefficientRing(element)) - 1) div 2;
    t := 3^m;
    word := identityWord;
    
    // Transform element into another element that fixes a point
    repeat
	repeat
	    residue, word := Random(randomiser);
	    g := element * residue;
	until not IsEmpty(Eigenvalues(g));
	fixedPoint := rep{Rep(Basis(Eigenspace(g, f))) : f in eigenvalues}
	    where eigenvalues is {e[1] : e in Eigenvalues(g)};
    until isOrbitPoint(fixedPoint);
    
     assert Normalise(fixedPoint * g) eq Normalise(fixedPoint);
    
    return fixedPoint, residue, word;
end function;

function getReeRecognitionData(G, checkInput, inputWordGroup)
    local recognitionData, lowerStabiliser, upperStabiliser,
	field, zero, infinity, identity, lowerGens, upperGens,
	lowerSLPs, upperSLPs, slpMap, wordGroup, slpMapInv;
    
    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    infinity := getOrbitPoint(field, 0, 0, 0 : Infinity := true);
    zero := getOrbitPoint(field, 0, 0, 0);
    
    // Find stabiliser generators for 2 points
    vprint ReeMembership, 5: "Get stabilisers";
    lowerStabiliser := ReeStabiliser(G, zero :
	Randomiser := G`RandomProcess, CheckInput := checkInput,
	wordGroup := inputWordGroup);
    upperStabiliser := ReeStabiliser(G, infinity : Randomiser :=
	G`RandomProcess, CheckInput := checkInput,
	wordGroup := inputWordGroup);
   
    U := sub<Generic(G) | lowerStabiliser[1]`mat, lowerStabiliser[2]`mat>;
    U`RandomProcess := RandomProcessWithWords(U : WordGroup := WordGroup(U));

    L := sub<Generic(G) | upperStabiliser[1]`mat, upperStabiliser[2]`mat>;
    L`RandomProcess := RandomProcessWithWords(L : WordGroup := WordGroup(L));

    // Add these SLPs to our word group, for optimisation
    vprint ReeMembership, 5: "Extending SLP group";
    wordGroup := AddRedundantGenerators(inputWordGroup,
	[lowerStabiliser[1]`slp, lowerStabiliser[2]`slp,
	upperStabiliser[1]`slp, upperStabiliser[2]`slp]);
    
    // Map from extended word group to standard word group
    slpMap := hom<wordGroup -> inputWordGroup | [H.i : i in
    [1 .. NumberOfGenerators(H)]] cat [lowerStabiliser[1]`slp,
	lowerStabiliser[2]`slp, upperStabiliser[1]`slp,
	upperStabiliser[2]`slp] where H is inputWordGroup>;
    
    // Coercion from standard word group to extended word group
    slpMapInv := hom<inputWordGroup -> wordGroup |
    [wordGroup.i : i in [1 .. NumberOfGenerators(G)]]>;
    
    // Construct standard generators for Gauss-Jordan elimination
    vprint ReeMembership, 5: "Get standard generators";
    lowerGens, lowerSLPs := getReeStandardGenerators(field,
	lowerStabiliser, wordGroup);
    upperGens, upperSLPs := getReeStandardGenerators(field,
	upperStabiliser, wordGroup);

    recognitionData := rec<ReeRecognitionFormat |
	lowerStab := L, lowerSLPs := [lowerStabiliser[1]`slp,
	lowerStabiliser[2]`slp],
	upperStab := U, upperSLPs := [upperStabiliser[1]`slp,
	upperStabiliser[2]`slp],
	lowerGens := lowerGens,
	upperGens := upperGens, slpGroup := wordGroup, slpMap := slpMap,
	slpMapInv := slpMapInv>;
    
    return recognitionData;
end function;

function getReeStandardGenerators(field, stabiliser, slpGroup)
    local conjugator, conjugatee, gens, elements, generator,
	normaliser, standardGenerators, value, diagonal, generatorFormat,
	coordinates, power, SLPs;
    
    // The element of order 9
    conjugatee := rec<MatSLP | mat := stabiliser[1]`mat, slp :=
	slpGroup ! stabiliser[1]`slp>;

    // The element of order q - 1
    conjugator := rec<MatSLP | mat := stabiliser[2]`mat, slp :=
	slpGroup ! stabiliser[2]`slp>;

    vprint ReeMembership, 5: "SLP Lengths:", #stabiliser[1]`slp,
	#stabiliser[2]`slp, #conjugatee`slp, #conjugator`slp;
    
    assert Order(conjugator`mat : Proof := false) eq #field - 1 and
	Order(conjugatee`mat) eq 9;

    // Store generators in a proper structure
    generatorFormat := recformat<basis : SetIndx, generators : List>;
    allGensFormat := recformat<subDiagonals : List>;

    SLPs := {};
    standardGenerators := rec<allGensFormat | subDiagonals := [* 0, 0, 0 *]>;

    // Third layer comes from first by taking power 3
    for i in [1, 3] do
	gens := [* *];
	elements := {@ @};
	power := conjugator;
	
	// Create set of standard generators
	for j in [1 .. Degree(field)] do
	    generator := rec<MatSLP | mat := conjugatee`mat^power`mat,
		slp := conjugatee`slp^power`slp>;

	    // element is either lower or upper triangular
	    idx := [i + 1, 1];
	    if IsUpperTriangular(generator`mat) then
		Reverse(~idx);
	    end if;
	    value := generator`mat[idx[1], idx[2]];
	    
	    // Store element and its defining field element
	    Include(~elements, value);
	    Append(~gens, generator);
	    power := rec<MatSLP | mat := power`mat * conjugator`mat,
		slp := power`slp * conjugator`slp>;
	    Include(~SLPs, generator`slp);
	end for;
	assert #elements eq Degree(field);

	standardGenerators`subDiagonals[i] := 
	    rec<generatorFormat | basis := elements, generators := gens>;
	
	conjugatee`mat ^:= 3;
	conjugatee`slp ^:= 3;
    end for;
    
    field := CoefficientRing(conjugator`mat);
    fieldSpace, fieldIso := VectorSpace(field, PrimeField(field));

    // Second layer are the commutators
    element := standardGenerators`subDiagonals[1]`generators[1];
    gens := [* *];
    elements := {@ @};
    tuples := CartesianPower([1 .. Degree(field)], 2);
    for tuple in tuples do
	i := tuple[1];
	j := tuple[2];
	if i lt j then
	    generator := rec<MatSLP | mat :=
		(standardGenerators`subDiagonals[1]`generators[i]`mat,
		standardGenerators`subDiagonals[1]`generators[j]`mat),
		slp :=
		(standardGenerators`subDiagonals[1]`generators[i]`slp,
		standardGenerators`subDiagonals[1]`generators[j]`slp)>;
		
	    // element is either lower or upper triangular
	    idx := [3, 1];
	    if IsUpperTriangular(generator`mat) then
		Reverse(~idx);
	    end if;
	    value := generator`mat[idx[1], idx[2]];
	    
	    if IsIndependent(SetToSequence(Include(fieldIso(elements),
		fieldIso(value)))) then
		
		// Store element and its defining field element
		Include(~elements, value);
		Append(~gens, generator);
		Include(~SLPs, generator`slp);
	    end if;
	    if #elements eq Degree(field) then
		break;
	    end if;
	end if;
    end for;
    assert #elements eq Degree(field) and #gens eq Degree(field);
    
    standardGenerators`subDiagonals[2] := 
	rec<generatorFormat | basis := elements, generators := gens>;
    
    return standardGenerators, SLPs;
end function;

// Construct a diagonal matrix from the given triangular matrix
function getDiagonalMatrix(element, generators, wordGroup)
    local value, idx;
    
    // Use row operations to eradicate super/sub diagonals

    for i in [1 .. #generators`subDiagonals] do
	idx := [i + 1, 1];
	if IsUpperTriangular(element`mat) then
	    Reverse(~idx);
	end if;

	value := -element`mat[idx[1], idx[2]] *
	    element`mat[idx[1], idx[1]]^(-1);
	performRightRowOperations(~element,
	    generators`subDiagonals[i], value, wordGroup);
    end for;
    
    assert IsDiagonal(element`mat);
    return element;
end function;

procedure performRightRowOperations(~element, generators, lookup, wordGroup)
    local fieldBasis, fieldSpace, fieldIso, coordinates, field;

    field := CoefficientRing(element`mat);
    if not IsZero(lookup) then
	// Construct base of finite field over its prime subfield
	fieldBasis := SetToSequence(generators`basis);
	fieldSpace, fieldIso :=
	    VectorSpace(field, PrimeField(field), fieldBasis);

	lift := map<PrimeField(field) -> Integers() |
	[<0, 0>, <1, 1>, <-1, -1>]>;

	assert Dimension(sub<fieldSpace | [fieldIso(x) : x in fieldBasis]>) eq
	    Degree(field);

	// Adjust first super/sub diagonal of element
	coordinates := Coordinates(fieldSpace, fieldIso(lookup));

	element`mat *:= 
	    &*[generators`generators[index]`mat^lift(coordinates[i])
	    where index is Index(generators`basis, fieldBasis[i])
	    : i in [1 .. #coordinates] | not IsZero(coordinates[i])];

	element`slp *:= wordGroup !
	    &*[generators`generators[index]`slp^lift(coordinates[i])
	    where index is Index(generators`basis, fieldBasis[i]) :
	    i in [1 .. #coordinates] | not IsZero(coordinates[i])];
    end if;
end procedure;

// Find matrix as word in our generators that takes the given point to the
// zero point
function getZeroMapping(G, point)
    local m, t, element, field, gen;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    t := 3^m;

    // Get field elements that determines matrix
    if IsZero(point[7]) then
	alpha := 0;
	beta := 0;
	gamma := 0;
    else
	point *:= point[7]^(-1);
	
	alpha := (-point[6])^(3 * t);
	beta := (point[6] * alpha + point[5])^(3 * t);
	gamma := ((alpha * beta)^t + point[6] * (beta^t + alpha^(t + 1)) +
	    point[5] * alpha^t + point[4])^(3 * t);
    end if;

    // Get matrix
    gen := getReeZeroSylowGen(field, alpha, beta, gamma);
    element := rec<MatSLP | mat := gen, slp :=
	Identity(G`ReeRecognitionData`slpGroup)>;
    
    // Turn matrix into identity
    for i in [1 .. #G`ReeRecognitionData`lowerGens`subDiagonals] do
	performRightRowOperations(~element,
	    G`ReeRecognitionData`lowerGens`subDiagonals[i],
	    -element`mat[i + 1, 1], G`ReeRecognitionData`slpGroup);
    end for;

    assert IsIdentity(element`mat);
    element`mat := gen;
    element`slp ^:= -1;

    return element;
end function;

// Find matrix as word in our generators that takes the given point to the
// infinity point
function getInfMapping(G, point)
    local m, t, field, gen, element;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    t := 3^m;

    // Get field elements that determines matrix
    if IsZero(point[1]) then
	alpha := 0;
	beta := 0;
	gamma := 0;
    else
	point := Normalise(point);
	
	alpha := (-point[2])^(3 * t);
	beta := (point[2] * alpha + point[3])^(3 * t);
	gamma := ((alpha * beta)^t + point[2] * (alpha^(t + 1) + beta^t) +
	    point[3] * alpha^t + point[4])^(3 * t);
    end if;

    // Get matrix
    gen := getReeInfSylowGen(field, alpha, beta, gamma);
    element := rec<MatSLP | mat := gen, slp :=
	Identity(G`ReeRecognitionData`slpGroup)>;

    // Turn matrix into identity
    for i in [1 .. #G`ReeRecognitionData`upperGens`subDiagonals] do
	performRightRowOperations(~element,
	    G`ReeRecognitionData`upperGens`subDiagonals[i],
	    -element`mat[1, i + 1], G`ReeRecognitionData`slpGroup);
    end for;

    assert IsIdentity(element`mat);
    element`mat := gen;
    element`slp ^:= -1;

    return element;
end function;

// Express a diagonal matrix in terms of our standard generators
function constructDiagonalMatrix(G, diagonal)
    local element, trace, field, q, a, b, upperElt, lowerElt, conjugator, m,
	t, sqrt, elements;

    field := CoefficientRing(diagonal`mat);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    trace := Trace(diagonal`mat);
    identity := rec<MatSLP | slp := Identity(G`ReeRecognitionData`slpGroup),
	mat := Identity(G)>;

    // It only works if we get a square in the field, which happens with
    // probability 1/2
    if not IsSquare(trace - 1) then
	return false, _;
    end if;
    
    lookup := Sqrt(trace - 1);
        
    // Construct element in the generators with correct trace
    upperElt := identity;
    performRightRowOperations(~upperElt,
	G`ReeRecognitionData`upperGens`subDiagonals[3], lookup,
	G`ReeRecognitionData`slpGroup);
    
    lowerElt := identity;
    performRightRowOperations(~lowerElt,
	G`ReeRecognitionData`lowerGens`subDiagonals[2],
	One(field), G`ReeRecognitionData`slpGroup);
    performRightRowOperations(~lowerElt,
	G`ReeRecognitionData`lowerGens`subDiagonals[3],
	-lowerElt`mat[4, 1], G`ReeRecognitionData`slpGroup);
    
    element := rec<MatSLP | mat := upperElt`mat * lowerElt`mat,
	slp  := upperElt`slp * lowerElt`slp>;

    assert Trace(element`mat) eq trace;
    
    // Check that we got correct order
    assert Order(element`mat : Proof := false) eq
	Order(diagonal`mat : Proof := false);

    // Get element that conjugates us to a diagonal matrix
    P, Q := ReeFixedPoints(element`mat : CheckInput := false);   
    a := getInfMapping(G, P);
    b := getZeroMapping(G, Q * a`mat);
    conjugator := rec<MatSLP | mat := a`mat * b`mat,
	slp := a`slp * b`slp>;
    
    // Hope that we got correct diagonal (there are 2 possibilities)
    element := rec<MatSLP | mat := element`mat^conjugator`mat,
	slp := element`slp^conjugator`slp>;

    // Take the element or its inverse
    assert element`mat eq diagonal`mat or element`mat eq diagonal`mat^(-1);
    if element`mat ne diagonal`mat then
	element`mat ^:= -1;
	element`slp ^:= -1;
    end if;
    
    return true, element;
end function;
