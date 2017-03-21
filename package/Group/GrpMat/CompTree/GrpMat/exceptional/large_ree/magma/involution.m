/******************************************************************************
 *
 *    involution.m    Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-07-10
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: involution.m 1605 2008-12-15 09:05:48Z jbaa004                 $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

involCentraliserInfo := recformat<
    class : MonStgElt,       // Class 2A or 2B
    involution : GrpMatElt,  // The centralised involution
    genSLPs : SeqEnum,       // SLPs of centraliser gens in gens of Ree group
    diagonalBlocks : SeqEnum,// diagonalBlockFormat records
    ree : GrpMat,            // Big Ree group
    slpCoercion : Map,       // Evaluate SLPs centraliser to Big Ree 
    normaliser : Rec,        // Element that generates maximal subgroup 
    cbm : GrpMatElt,         // CBM from MeatAxe
    sections : SeqEnum,      // Sections of unitriangular subgroup
    smallInit : UserProgram, // Initialiser of small centraliser
    slpHomo : UserProgram,   // Used in 2B case, evaluate centraliser SLPs
    filtration : SeqEnum,    // Filtration of O2 part, from MeatAxeMaps
    meatAxeData : SeqEnum,   // Structure from MeatAxeMaps
    kernelGens : SeqEnum,    // Generates O2 part as module for centraliser
    compSeries : SeqEnum,    // Composition series of centraliser
    compFactors : SeqEnum>;  // Composition factors of centraliser

diagonalBlockFormat := recformat<
    group : GrpMat,          // Small centraliser, Sz or SL2 or trivial
    slpHomo : Map,           // Evaluate 4-sim SLPs on 26-dim centraliser
    slpEvalGens : SeqEnum,   // Generators that slpHomo evaluates on
    slpGroup : GrpSLP,       // Parent group of small SLPs
    iso : Map,               // Mapping from group to standard Sz
    invIso : Map,            // Mapping from standard Sz to group
    proj : Map,              // Projection to diagonal block
    genIndices : SeqEnum,    // Indices of large gens in small centraliser
    smallSLPHomo : Map,      // Homo from small SLP group to small centraliser
    smallSLPCoercion : Map>; // Homo from small SLP group to large SLP group

blocksFormat := recformat<
    space : ModMatFld,    // Block as vector space over GF(q)
    proj : Map,           // Projection from Ree group to block subspace
    basis : SeqEnum,      // Matrices whose projections form block basis
    scalars : SeqEnum,    // GF(q) elements that form basis over GF(2)
    multiples : SetIndx>; // Matrices and SLPs that acts as scalars on block

declare attributes GrpMat : LargeReeInvolCentraliserData;

import "ree.m": getLargeReeOrder;
import "centraliser.m": SolveWordReeCentraliser;
import "../../../util/centraliser.m" : BrayAlgorithm;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/section.m" : MeatAxeMaps;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/forms.m" : SubPerp;
import "../../../util/basics.m" : getMapFunction, MatSLP;

declare verbose LargeReeInvolution, 10;

forward checkCentraliserCompletion, check2ACentraliser,
    check2BCentraliser, centraliserMembership, getNormalisingElement,
    getSmallCentraliserSLP, reduceElementInBlock, initialiseCentraliser,
    removeSmallCentraliser, getKernelGens, removeSmallCentraliserBatch;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeInvolutionCentraliser(G :: GrpMat, g :: GrpMatElt,
    slp :: GrpSLPElt : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true) -> GrpMat
    { Compute an involution centraliser in G = Ree(q), using the Bray trick}
    local centraliser, slpMap, completion;

    if CheckInput then
	if not LargeReeStandardRecogniser(G) then
	    error "G must be the standard Big Ree group";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    vprint LargeReeInvolution, 2 : "Executing Bray Trick";
    
    centraliser, slpMap :=
	BrayAlgorithm(G, g, slp : Randomiser := G`RandomProcess,
	completionCheck := checkCentraliserCompletion);

    assert assigned centraliser`LargeReeInvolCentraliserData;
    centraliser`LargeReeInvolCentraliserData`involution := g;
    centraliser`LargeReeInvolCentraliserData`genSLPs := slpMap;
    
    vprint LargeReeInvolution, 2 : "Bray Trick done";

    return centraliser;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Find a composition series of the centraliser, ordered in a canonical way
function getOrderedCompSeries(M, S, V, topFactors, bottomFactors)
    local goodMods, submods, flag, series;
    
    // Base case
    if #topFactors gt 0 and #bottomFactors gt 0 and
	Dimension(topFactors[#topFactors]) eq
	Dimension(bottomFactors[#bottomFactors]) then
	series := {x : x in topFactors} join {x : x in bottomFactors};

	return true, Sort(SetToSequence(series),
	    func<x, y | Dimension(x) - Dimension(y)>);
    end if;

    // First put a 1-dim module at the top and bottom
    // One of them should be the orthogonal complement of the other
    
    factors := [f : f in CompositionFactors(M) | Dimension(f) eq 1];
    homos := [GHom(M, x) : x in factors];

    f := rep{x : x in homos | Dimension(x) gt 0};
    if Dimension(f) ne 1 then
	return false, _;
    end if;

    // Remove a 1-space and store the rest
    N1 := Kernel(f.1);
    assert Dimension(N1) eq Dimension(M) - 1;
    Append(~topFactors, N1);

    // Take the orthogonal complement of the preimage 
    W := sub<V | [V ! ElementToSequence(x * Morphism(N1, S)) :
	x in Generators(N1)]>;
    U := SubPerp(V, W);

    // Store the complement
    N2 := N1 meet sub<S | [S ! ElementToSequence(x) : x in Basis(U)]>;
    Append(~bottomFactors, N2);

    // Do the same procedure with 4-dim spaces, put one at the top and bottom
    
    M := N1;
    factors := [f : f in CompositionFactors(M) | Dimension(f) eq 4];    
    homos := [GHom(M, x) : x in factors];

    f := rep{x : x in homos | Dimension(x) gt 0};
    if Dimension(f) ne 1 then
	return false, _;
    end if;
    
    N3 := Kernel(f.1);
    assert Dimension(N3) eq Dimension(M) - 4;
    Append(~topFactors, N3);
    
    W := sub<V | [V ! ElementToSequence(x * Morphism(N3, S)) :
	x in Generators(N3)]>;
    U := SubPerp(V, W);
    N4 := N3 meet sub<S | [S ! ElementToSequence(x) : x in Basis(U)]>;
    assert Dimension(N4 meet N2) eq Dimension(N2);
    Append(~bottomFactors, N4);
    
    return getOrderedCompSeries(N3, S, V, topFactors, bottomFactors);
end function;

// Find a CBM of a module that exhibits the submodule structure
// This is the same as the CBM returned from CompositionSeries, but we use
// this since we first want to order the composition factors
function getMeatAxeCBM(G, M, V, series, factors)
    local basis, U, mod_basis, mod_map, MA, p;

    F := CoefficientRing(M);
    p := Characteristic(F);
    q := #F;
    m := (Degree(F) - 1) div 2;
    
    MA := MatrixAlgebra(F, Dimension(M));
    basis := [];
    
    for i in [1 .. #series] do
	mod_map := Morphism(series[i], M);
	mod_basis := Basis(series[i]);
	
	// Find basis elements to be added from this submodule
	U := sub<V | basis>;
	newBasis := [];
	oldBasis := basis;
	for j in [1 .. Dimension(factors[i])] do
	    k := Max([l : l in [1 .. #mod_basis] |
		V ! mod_map(mod_basis[l]) notin U]);

	    // Map basis element to full dimension
	    basisElt := V ! mod_map(mod_basis[k]);
	    
	    Append(~newBasis, basisElt);
	    Remove(~mod_basis, k);
	    U := sub<V | U, basisElt>;
	end for;
	
	// Add new basis vectors
	basis cat:= newBasis;
    end for;
    
    // Return complete change of basis
    return MA ! basis;
end function;

function orderedCompSeries(G, M, form)
    local dims, series;

    V := VectorSpace(CoefficientRing(M), Dimension(M), form);    
    flag, series := getOrderedCompSeries(M, M, V, [], []);
    if not flag then
	return false, _, _, _;
    end if;
    
    // Add trivial submodule to get it as a factor
    Append(~series, M);
    Reverse(~series);
    Append(~series, sub<M | >);

    // Compute composition factors
    factors := [series[k] / series[k + 1] : k in [1 .. #series - 1]];
    
    Prune(~series);
    Reverse(~series);
    Reverse(~factors);

    // Compute basis that exhibits submodule structure
    cbm := getMeatAxeCBM(G, M, V, series, factors);
    
    return true, series, factors, cbm;
end function;

// Check composition factors and recognise Sz
// G is the centraliser with module structure in meatAxeData
// slpList are SLPs of G
// largeSLPGroup is Big Ree slp group
function check2ACentraliser(G, meatAxeData, largeSLPGroup, slpList)
    local szIndices, szGroups, bool, H, iso1, iso2, slpHomo, slpHomoInv;
    
    diagonalBlocks := [];

    // This is the number of the Sz factor that we recognise
    middleSzIdx := (#meatAxeData + 1) div 2;
    assert Degree(meatAxeData[middleSzIdx]`image) eq 4;
    
    for i in [1 .. #meatAxeData] do
	// Store data about this composition factor
	Append(~diagonalBlocks, rec<diagonalBlockFormat |
	    group := meatAxeData[i]`image,
	    proj := meatAxeData[i]`mproj,
	    genIndices := meatAxeData[i]`genIndices>);
	
	if i eq middleSzIdx then
	    // Recognise factor
	    bool, iso1, iso2, slpHomo, slpHomoInv :=
		RecogniseSz(meatAxeData[i]`image);
	    if not bool then
		return false, _;
	    end if;
		
	    slpCoercion := SzSLPCoercion(meatAxeData[i]`image);

	    // Evaluates Sz SLPs on centraliser
	    slpHomoLarge := hom<Codomain(slpCoercion) -> G |
	    [G.j : j in meatAxeData[i]`genIndices]>;
	    slpHomoOpt := hom<Domain(slpCoercion) -> G | slpHomoLarge>;
		
	    // Construct homo from small SLP group to large SLP group

	    // Evaluate 4-dim Sz slps on centraliser SLPs
	    smallSLPCoercion := slpCoercion * hom<Codomain(slpCoercion) ->
	    largeSLPGroup | [slpList[j] : j in meatAxeData[i]`genIndices]>;

	    // Save all maps
	    meatAxeData[i]`slpMap := slpHomoOpt;
	    meatAxeData[i]`slpCoercion := smallSLPCoercion;
	    diagonalBlocks[#diagonalBlocks]`slpHomo := slpHomoOpt;
	    diagonalBlocks[#diagonalBlocks]`slpEvalGens :=
		[G.j : j in meatAxeData[i]`genIndices];
	    diagonalBlocks[#diagonalBlocks]`smallSLPHomo := slpHomo;
	    diagonalBlocks[#diagonalBlocks]`smallSLPCoercion :=
		smallSLPCoercion;
	    diagonalBlocks[#diagonalBlocks]`slpGroup := Codomain(slpCoercion);
	    diagonalBlocks[#diagonalBlocks]`iso := iso1;
	    diagonalBlocks[#diagonalBlocks]`invIso := iso2;
	end if;
    end for;

    vprint LargeReeInvolution, 2: "2A centraliser => Sz(q)";
    return true, diagonalBlocks;
end function;

// Return the projection in O_2(G) of the element g, with SLP slpG
function getSolublePartBatch(G, batch, slpBatch)
    local flag, blockNr, element;

    // Take middle diagonal block, which is non-trivial in an ordered series
    blockNr := (#G`LargeReeInvolCentraliserData`diagonalBlocks + 1) div 2;
    assert not IsTrivial(G`LargeReeInvolCentraliserData`
	diagonalBlocks[blockNr]`group);
    
    // Remove diagonal part
    flag, elements := removeSmallCentraliserBatch(
	G`LargeReeInvolCentraliserData`class,
	G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr], batch);
    
    assert flag;
    for i in [1 .. #batch] do
	elements[i]`slp :=
	    G`LargeReeInvolCentraliserData`slpCoercion(slpBatch[i]) *
	    elements[i]`slp^(-1);
    end for;
    
    return elements;
end function;

// Find a random element of even order in the involution centraliser G
// This is done by taking a random element and dividing out by the diagonal
// part, hence obtaining a random element of [q^10]
function getCentraliserEvenOrderElementBatch(G, batchSize)
    local g, slpG;
    
    assert assigned G`RandomProcess;

    batch := [];
    slpBatch := [];

    for i in [1 .. batchSize] do
	// Get random element from centraliser
	g, slpG := Random(G`RandomProcess);
	Append(~batch, g);
	Append(~slpBatch, slpG);
    end for;
	
    return getSolublePartBatch(G, batch, slpBatch);
end function;

// block is a blocksFormat record
// element lies in the O_2 part of the involution centraliser
// multiply element with elements of the centraliser to make sure it has
// zero projection into block
procedure reduceElementInBlock(block, ~element)
    local vector, field, fieldBasis, fieldSpace, inc, coords, fieldCoords,
	projElt, projection;

    // Get projection into block
    vector := Function(block`proj)(element`mat);
    assert vector in block`space;
    
    if not IsZero(vector) then
	// Get GF(q) as vector space over GF(2)
	field := CoefficientRing(element`mat);
	fieldSpace, inc :=
	    VectorSpace(field, PrimeField(field), block`scalars);

	// Get coordinates of projection
	coords := Coordinates(block`space, vector);
	for i in [i : i in [1 .. #coords] | not IsZero(coords[i])] do

	    // Get coordinates of scalar over GF(2)
	    fieldCoords := Coordinates(fieldSpace, inc(coords[i]));

	    // Get scalar multiple of basis element
	    projElt := rec<MatSLP | mat :=
		&*[block`basis[i]`mat^block`multiples[j][1]
		: j in [1 .. #fieldCoords] | not IsZero(fieldCoords[j])],
		slp := &*[block`basis[i]`slp^block`multiples[j][2] 
		: j in [1 .. #fieldCoords] | not IsZero(fieldCoords[j])]>;
	    
	    element`mat *:= projElt`mat;
	    element`slp *:= projElt`slp;
	end for;
    end if;

    assert IsZero(Function(block`proj)(element`mat));
end procedure;

// For a blocksFormat with basis blockBasis and projection proj
// compute matrices of the centraliser that acts as scalar multiples on the
// block. These are all powers of conjugator, which must be the normalising
// q-1 element of the centraliser
function getScalarMultiples(field, blockBasis, proj, conjugator)
    local scalars, multiples, vector, space, element, power,
	scalar, multiple, fieldSpace, inc;
    
    scalars := {@ @};
    multiples := {@ @};
    assert #blockBasis gt 0;
    fieldSpace, inc := VectorSpace(field, PrimeField(field));

    // Choose arbitrary basis element
    element := Rep(blockBasis);
    power := conjugator;
    vector := Function(proj)(element`mat);
    space := KMatrixSpaceWithBasis([vector]);
    scalars := {@ @};
    multiples := {@ @};

    assert not IsZero(element`mat) and not IsZero(vector);
    
    // Need one element for each scalar over the prime field
    for i in [1 .. Degree(field)] do
	// See how this power acts on the block
	multiple := Function(proj)(element`mat^power`mat);
	assert multiple in space;

	// Get scalar multiple as a field element
	scalar := Coordinates(space, multiple)[1];
	assert not IsZero(scalar);

	if scalar in scalars or not
	    IsIndependent(Append(IndexedSetToSequence(inc(scalars)),
	    inc(scalar))) then
	    continue;
	end if;
	
	// Save scalar and powering element
	Include(~scalars, scalar);
	vprint LargeReeInvolution, 8 : "Scalars", scalars;
	
	multiple := <power`mat, power`slp>;
	assert multiple notin multiples;
	Include(~multiples, multiple);
	
	// Check next power of conjugator
	power`mat *:= conjugator`mat;
	power`slp *:= conjugator`slp;
    end for;

    assert #scalars eq Degree(field);
    assert IsIndependent(IndexedSetToSequence(inc(scalars)));
    
    return IndexedSetToSequence(scalars), multiples;
end function;

// Compute generators for each block in the filtration of O_2(G)
// The filtration structure as given by MeatAxeMaps must be given
// The normalising element of G must be given
// The elements that generate the O_2 part as a module for G
// must be given as mandarins
function getSections(G, filtration, normaliser, mandarins)
    local products, submods, sections, section, basis, space, proj, 
	block, scalars, multiples, flag;

    field := CoefficientRing(G);
    sections := [];

    // Generators for first filtration layer
    gens4 := mandarins[1 .. 4];

    // Generator for second filtration layer
    gens1 := [mandarins[5]];

    // Section & block nr, generators, block dimension
    // The other blocks are isomorphic to some of these blocks, and hence will
    // be 0 automatically if these are 0
    nonZeroBlocks := [<1, 1, gens4, 4>, <2, 1, gens1, 1>,
	<3, 1, [rec<MatSLP | mat := g`mat^2, slp := g`slp^2> : g in gens4], 4>,
	<6, 1, [rec<MatSLP | mat := g`mat^2, slp := g`slp^2> :
	g in gens1], 1>];

    for blockNr in nonZeroBlocks do
	gens := blockNr[3];
	i := blockNr[1];
	j := blockNr[2];

	blockBasis := [Function(filtration[i][j]`mproj)(g`mat) : g in gens];
	vprint LargeReeInvolution, 8 : "Block basis", blockBasis;
	
	// Get block vector space basis
	// We need 4 or 1 basis elements for each block
	if not IsIndependent(blockBasis) then
	    return false, _, _, _;
	end if;
	space := KMatrixSpaceWithBasis(blockBasis);
	assert Dimension(space) eq blockNr[4];

	// Find matrices that acts as scalars on the block
	// We need 2m+1 such matrices
	// This way we avoid storing n(2m+1) generators for the block with
	// dimension n, and store only n + 2m + 1 matrices
	scalars, multiples := getScalarMultiples(field, gens,
	    filtration[i][j]`mproj, normaliser);
		
	block := rec<blocksFormat | proj := filtration[i][j]`mproj,
	    basis := gens, space := space, scalars := scalars,
	    multiples := multiples>;
	Append(~sections, [block]);
    end for;
    
    return true, sections, filtration;
end function;

// 2A centraliser submodules
// 26, 25, 21, 20, 17, 16, 15, 11, 10, 9, 6, 5, 1, 0
// 16 and 10 have q+1 non-iso copies each, all other unique

// 2B centraliser submodules
// all dimensions 0 to 26
// 2 non-iso of dim 7,9,10,13,16,17,19
// q+1 non-iso of dim 11,15
// q+2 non-iso of dim 12,14
// all other unique

function checkCentraliserCompletion(G, ree, x, slpMap)
    local field, M, series, factors, cbm, modNr, H, preDim, matrixProj,
	initialiser, bool;
    
    F := CoefficientRing(G);
    q := #F;

    vprint LargeReeInvolution, 1 : "Check centraliser completion";
        
    // Initial check to speed up. We will always need at lest 3 generators.
    if NumberOfGenerators(G) lt 5 then
	vprint LargeReeInvolution, 1 : "Too few centraliser generators";
	return false;
    end if;
    
    assert #slpMap ge 1;
    wordGroup := Parent(slpMap[1]);
    slpCoercion := hom<WordGroup(G) -> wordGroup | slpMap>;
    
    M := GModule(G);

    // Check that the constituents of the natural module is what they should
    // be. If we don't have the full centraliser they might be something else.
    factors := ConstituentsWithMultiplicities(M);
    if exists{x : x in factors | Dimension(x[1]) eq 4 and x[2] eq 4} and
	exists{x : x in factors | Dimension(x[1]) eq 4 and x[2] eq 1} and
	exists{x : x in factors | Dimension(x[1]) eq 1 and x[2] eq 6} then
	class := "2A";

	// This might also fail if we don't have the full centraliser
	vprint LargeReeInvolution, 2 : "Find ordered composition series";
	flag, form := SymmetricBilinearForm(ree);
	assert flag;
	flag, series, factors, cbm := orderedCompSeries(G, M, form);

	if not flag then
	    vprint LargeReeInvolution, 1 : "Centraliser module not correct";
	    return false;
	end if;
    elif exists{x : x in factors | Dimension(x[1]) eq 2 and x[2] eq 4} and
	exists{x : x in factors | Dimension(x[1]) eq 2 and x[2] eq 2} and
	exists{x : x in factors | Dimension(x[1]) eq 2 and x[2] eq 1} and
	exists{x : x in factors | Dimension(x[1]) eq 4 and x[2] eq 2} and
	exists{x : x in factors | Dimension(x[1]) eq 1 and x[2] eq 4} then
	class := "2B";
	
	series, factors, cbm := CompositionSeries(M);	
    else
	vprint LargeReeInvolution, 1 : "Centraliser module not correct";
	return false;
    end if;
    
    vprint LargeReeInvolution, 2 : "Get MeatAxe maps";
    meatAxeData, series, factors, cbm, filtration := MeatAxeMaps(G :
	Factors := func<M | series, factors, cbm>);
    
    G`RandomProcess := RandomProcessWithWords(G : WordGroup := WordGroup(G),
	Scramble := 1);

    // In the 2B case, use special code by Mark Stather
    if class eq "2B" then
	G`BigReeCentraliserLayersData := [* M, series, factors, cbm *];
	
	vprint LargeReeInvolution, 2 :
	    "2B centraliser, initialise membership testing";
    	// Compute kernel generators etc
	flag, slpHomo, slpHomoInv, smallSLPCoercion :=
	    SolveWordReeCentraliser(G, meatAxeData, filtration);

	if flag then
	    vprint LargeReeInvolution, 2 :
		"2B centraliser, membership testing initialised";
	    G`LargeReeInvolCentraliserData := rec<involCentraliserInfo |
		class := class,
		ree := ree,
		slpCoercion := slpCoercion,
		slpHomo := slpHomo>;
	    return true;
	else
	    vprint LargeReeInvolution, 2 :
		"2B centraliser, failed to initialisemembership testing";
	    return false;
	end if;
    end if;

    // Recognise diagonal block Sz's
    vprint LargeReeInvolution, 2 : "Check 2A centraliser";
    bool, diagonalBlocks := check2ACentraliser(G, meatAxeData,
	wordGroup, slpMap);
    if bool then
	vprint LargeReeInvolution, 2 : "2A centraliser ok";
	G`LargeReeInvolCentraliserData := rec<involCentraliserInfo |
	    class := class,
	    involution := x,
	    diagonalBlocks := diagonalBlocks,
	    slpCoercion := slpCoercion,
	    genSLPs := slpMap,
	    cbm := Generic(G) ! cbm^(-1),
	    ree := ree,
	    compFactors := factors,
	    compSeries := series,
	    meatAxeData := meatAxeData,
	    filtration := filtration>;
    else
	vprint LargeReeInvolution, 2 : "Failed to initialise 2A centraliser";
	return false;
    end if;

    vprint LargeReeInvolution, 2 : "Find normalising element";

    // Find element of order q-1 that generates maximal subgroup
    // together with the centraliser
    G`LargeReeInvolCentraliserData`normaliser := getNormalisingElement(G);

    vprint LargeReeInvolution, 2 : "Find kernel generators";

    // Find matrices that generate [q^10] of group [q^10] : (q - 1)
    // Do not find generators of [q^10] since that is too many
    flag, kernelGens := getKernelGens(G);
    if not flag then
	vprint LargeReeInvolution, 2 : "Failed to find kernel generators";
	return false;
    end if;
    
    vprint LargeReeInvolution, 2 : "Found kernel generators";
    G`LargeReeInvolCentraliserData`kernelGens := kernelGens;
    
    vprint LargeReeInvolution, 1 : "Centraliser generated!";
    vprint LargeReeInvolution, 3 : "Number of centraliser generators:",
	NumberOfGenerators(G);
    
    return true;
end function;

function getFirstLayerGens(G)

    // Take a batch of four random elements
    // If we have the full centraliser, these are likely to generate the first
    // layer, which has dimension 4 as module for the centraliser
    elements := [];
    slps := [];    
    for i in [1 .. 4] do
	g, w := Random(G`RandomProcess);
	Append(~elements, g);
	Append(~slps, w);
    end for;
    
    // Get their SLPs in chosen Suzuki block
    smallSLPs := [];
    blockNr := (#G`LargeReeInvolCentraliserData`diagonalBlocks + 1) div 2;
    W := WordGroup(G`LargeReeInvolCentraliserData`
	diagonalBlocks[blockNr]`group);
    
    for i in [1 .. #elements] do
	flag, slp :=
	    getSmallCentraliserSLP(G`LargeReeInvolCentraliserData`class,
	    G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr],
	    elements[i]);
	assert flag;

	Append(~smallSLPs, W ! slp);
    end for;
    
    // Evaluate all SLPs at once (important!) to get the Suzuki parts
    assert NumberOfGenerators(W) eq
	#G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr]`genIndices;
    smallElts := Evaluate(smallSLPs, [G.i : i in
	G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr]`genIndices]);

    // Divide out all Suzuki parts
    kernelGens :=
	[rec<MatSLP | mat := elements[i] * smallElts[i]^(-1),
	slp := G`LargeReeInvolCentraliserData`slpCoercion(slps[i]) *
	G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr]`
	smallSLPCoercion(smallSLPs[i]^(-1))> : i in [1 .. #elements]];

    // get projections in first layer
    vectors :=
	[Function(G`LargeReeInvolCentraliserData`filtration[1][1]`mproj)(g`mat)
	: g in kernelGens];
    
    return IsIndependent(vectors), kernelGens;
end function;

function getKernelGens(G)
    vprint LargeReeInvolution, 3 : "Get first layer gens";
    flag, gens := getFirstLayerGens(G);

    // The first layer elements have order 4 and power up to 2B-elements
    if not (flag and forall{g : g in gens |
	Order(g`mat : Proof := false) eq 4 and
	LargeReeInvolutionClass(g`mat^2) eq "2B"}) then

	vprint LargeReeInvolution, 3 : "Failed to find first layer gens";
	return false, _;
    end if;
    
    vprint LargeReeInvolution, 3 : "Find second layer gens";
    repeat
	// The second layer is generated by an element of order 4 which
	// powers up to an involution in the other class
	repeat
	    g2, w2 := Random(G`RandomProcess);
	    o := Order(g2 : Proof := false);
	    flag, l := IsDivisibleBy(o, 4);
	until flag;

	g2 ^:= l;
	w2 ^:= l;
	h := rec<MatSLP | mat := g2, slp :=
	    G`LargeReeInvolCentraliserData`slpCoercion(w2)>;
    until LargeReeInvolutionClass(h`mat^2) eq "2A";

    Append(~gens, h);
    return true, gens;
end function;

function initialiseCentraliser(G)
    local smallSLPs, slpHomo, slpGroup, slpCoercion, idx, idxMap, flag,
	matrixProj, field, q, dimension;

    F := CoefficientRing(G);
    q := #F;
    
    vprint LargeReeInvolution, 1 : "Initialise centraliser of class",
	G`LargeReeInvolCentraliserData`class;

    if G`LargeReeInvolCentraliserData`class eq "2A" then
	correctDim := 10;
    else
	correctDim := 9;
	return true;
    end if;

    // Get generators for all subdiagonal blocks
    vprint LargeReeInvolution, 2 : "Get section generators";
    flag, sections, filtration := 
	getSections(G, G`LargeReeInvolCentraliserData`filtration,
	G`LargeReeInvolCentraliserData`normaliser,
	G`LargeReeInvolCentraliserData`kernelGens);
    
    if flag then
	vprint LargeReeInvolution, 2 : "Section generators found";
	G`LargeReeInvolCentraliserData`sections := sections;
	G`LargeReeInvolCentraliserData`filtration := filtration;
    else
	vprint LargeReeInvolution, 2 : "Section generators not found";
	return false;
    end if;
    
    // Check dimensions
    dimension := &+[&+[Dimension(block`space) : block in section] : section in
	G`LargeReeInvolCentraliserData`sections];
    vprint LargeReeInvolution, 2: "Got dimension", dimension;
    
    vprint LargeReeInvolution, 1: "Initalised centraliser:",
	dimension eq correctDim;
	
    // Check that we have the whole centraliser
    return dimension eq correctDim;
end function;

function getNormalisingElement(G)
    local slpCoercion, q, conj, y, slp_y, s, r, invol, newInvol, G_slps;

    invol := rec<MatSLP | mat := G.1, slp :=
	G`LargeReeInvolCentraliserData`genSLPs[1]>;
    q := #CoefficientRing(G);

    repeat
	repeat
	    vprint LargeReeInvolution, 2 :
		"Find random involution in centraliser";
	    
	    repeat
		// Find an element of even order that should power up to an
		// involution of the same type as the centraliser
		y, slp_y := RandomInvolution(G : Randomiser :=
		    G`RandomProcess, MaxTries := q);
		newInvol := rec<MatSLP | mat := y, slp :=
		    G`LargeReeInvolCentraliserData`slpCoercion(slp_y)>;

		vprint LargeReeInvolution, 8 : "Found involution",
		    Order(newInvol`mat),
		    LargeReeInvolutionClass(newInvol`mat);

		// Make sure it's not the same as the centralised involution
	    until invol`mat ne newInvol`mat and
		LargeReeInvolutionClass(newInvol`mat) eq
		G`LargeReeInvolCentraliserData`class;
	    
	    // Get element that conjugates the centralised involution to the
	    // newly found one
	    vprint LargeReeInvolution, 2 : "Apply dihedral trick";
	    conj := DihedralTrick(invol, newInvol,
		G`LargeReeInvolCentraliserData`ree`RandomProcess :
		MaxTries := q);
	    
	    // If conj is not in the centraliser and conjugates one
	    // involution to the other, then it must lie in the (q-1)
	    // factor of the maximal subgroup, or completely outside the
	    // maximal subgroup
	    
	    assert invol`mat^conj`mat eq newInvol`mat;
	    vprint LargeReeInvolution, 2 : "Possible q - 1",
		Order(conj`mat : Proof := false);
	    H := sub<Generic(G) | G, conj`mat>;
	    
	    // Make sure we have precisely order q - 1
	    s, r := Quotrem(Order(conj`mat : Proof := false), q - 1);
	until r eq 0 and invol`mat^conj`mat ne invol`mat and
	    not IsIrreducible(H);

	// Obtain element of correct order
	conj`mat ^:= s;
	conj`slp ^:= s;
	assert invol`mat^conj`mat ne invol`mat and not IsIrreducible(H)
	    where H is sub<Generic(G) | G, conj`mat>;

	// Middle Sz block, which is recognised
	blockNr :=
	    (#G`LargeReeInvolCentraliserData`diagonalBlocks + 1) div 2;
	
	// Remove diagonal block part (ie Suzuki part)
	// This is essential for membership testing and for The Formula
	// the filtration blocks might not be over GF(q) if we don't do this
	flag, elements := removeSmallCentraliserBatch(
	    G`LargeReeInvolCentraliserData`class,
	    G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr],
	    [conj`mat]);
	assert flag;
	element := elements[1];
	element`slp := conj`slp * element`slp^(-1);

    until invol`mat^element`mat ne invol`mat and
	Order(element`mat : Proof := false) eq q - 1
	and not IsIrreducible(H)
	where H is sub<Generic(G) | G, element`mat>;
    
    return element;
end function;

// Get an SLP for diagonal part of g, using Sz and SL2 code
function getSmallCentraliserSLP(class, diagonalBlock, g)
    local flag, slp, small;

    small := diagonalBlock`group;
    if class eq "2A" then

	// Use Suzuki code
	vprint LargeReeInvolution, 8 : "Execute Suzuki code";
	flag, slp := SzElementToWord(small, Function(diagonalBlock`proj)(g));
	if not flag then
	    return false, _;
	end if;
    elif class eq "2B" then

	// Use SL2 code
	vprint LargeReeInvolution, 8 : "Execute SL2 code";
	flag, slp := SL2ElementToWord(small, Function(diagonalBlock`proj)(g));
	if not flag then
	    return false, _;
	end if;
    else
	return false, _;
    end if;

    return true, slp;
end function;

function removeSmallCentraliserBatch(class, diagonalBlock, batch)
    local flag, slp, element, h;

    vprint LargeReeInvolution, 3 : "Find small centraliser SLPs";
    
    slps := [];
    for g in batch do
	// g = g_1 * h, where g_1 is unitriangular
	// get SLP for h by mapping to Sz or SL2
	flag, slp := getSmallCentraliserSLP(class, diagonalBlock, g);
	
	if not flag then
	    return false, _;
	end if;

	Append(~slps, slp);
    end for;
    
    vprint LargeReeInvolution, 3 : "Evaluate small centraliser SLPs";

    // Evaluate SLP in Ree group
    assert assigned diagonalBlock`slpEvalGens;
    assert forall{s : s in slps | IsCoercible(diagonalBlock`slpGroup, s)};
    assert NumberOfGenerators(diagonalBlock`slpGroup) eq
	#diagonalBlock`slpEvalGens;
    
    slpsEval := [diagonalBlock`slpGroup ! s : s in slps];
    assert IsComplete(slpsEval);

    if IsEmpty(slpsEval) then
	projs := [];
    else
	projs := Evaluate(slpsEval,	diagonalBlock`slpEvalGens);
    end if;
    
    vprint LargeReeInvolution, 3 : "Obtain random elements of kernel";

    // Remove h from g to get g_1
    elements := [rec<MatSLP | mat := batch[i] * projs[i]^(-1), slp :=
	diagonalBlock`smallSLPCoercion(slps[i])> : i in [1 .. #batch]];

    return true, elements;
end function;

function centraliserMembershipBatch(G, batch)
    local flag, slp, element, h;

    if G`LargeReeInvolCentraliserData`class eq "2B" then
	slps := [];
	for g in batch do
	    slp := G`LargeReeInvolCentraliserData`slpHomo(g);
	    if slp cmpeq false then
		return false, _;
	    else
		Append(~slps, slp);
	    end if;
	end for;

	return true, G`LargeReeInvolCentraliserData`slpCoercion(slps);
    end if;
    
    // Choose middle block, which is non-trivial in an ordered comp series
    blockNr := (#G`LargeReeInvolCentraliserData`diagonalBlocks + 1) div 2;
    
    // Remove diagonal part
    flag, elements := removeSmallCentraliserBatch(
	G`LargeReeInvolCentraliserData`class,
	G`LargeReeInvolCentraliserData`diagonalBlocks[blockNr], batch);
    
    if not flag then
	return false, _;
    end if;

    slps := [];
    for i in [1 .. #elements] do

	// Save diagonal SLP
	slp := elements[i]`slp;
	elements[i]`slp := Identity(Parent(slp));
	
	// Eradicate all subdiagonal blocks,
	// thus getting SLP of unitriangular part
	for section in G`LargeReeInvolCentraliserData`sections do
	    for block in section do
		reduceElementInBlock(block, ~elements[i]);
	    end for;
	end for;
	assert IsIdentity(elements[i]`mat);
	
	// Add diagonal SLP
	Append(~slps, elements[i]`slp^(-1) * slp);
    end for;
    
    return true, slps;
end function;
