/******************************************************************************
 *
 *    mathom.m  Composition Tree Action Wrappers
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: mathom.m 3165 2016-03-05 17:48:46Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare attributes GrpAb  : UserGenerators, FactoredOrder;

//import "recog.m" : SetHomFinderPriorities;
import "node.m" : AschbacherPriorities;
import "recog.m" : ActionMapsInfo, ModuleInfo, NodeTypes, LeafInfo;
import "unipotent.m" : UnipotentLayers;
import "kernel.m" : SetupKnownKernel;
import "../../GrpMat/util/basics.m" : CanApplyDiscreteLog;

import "node.m" : ERROR_CRISIS, AschbacherAlgorithms;
forward PreservesSubspaces, PreservesBlocks, PreservesTensor, BlockDiagonal,
    DeterminantScalarPatch, SmallerFieldScalarPatch, ReductionWithScalar;

// Store one type for each class
AschbacherErrorTypes := recformat<
    reducible : MonStgElt,
    absreducible : MonStgElt,
    imprimitive : MonStgElt,
    smallerfield : MonStgElt,
    semilinear : MonStgElt,
    tensor : MonStgElt,
    induced : MonStgElt,
    extraspecial : MonStgElt,
    determinant : MonStgElt,
    unipotent : MonStgElt,
    classical : MonStgElt,
    almostsimple : MonStgElt,
    cyclic : MonStgElt
    >;

// Error strings inserted in Error objects
AschbacherErrors := rec<AschbacherErrorTypes |
    reducible := "reducible",
    absreducible := "absolute reducible",
    imprimitive := "imprimitive",
    smallerfield := "smaller field",
    semilinear := "semilinear",
    tensor := "tensor",
    induced := "tensor induced",
    extraspecial := "extraspecial normaliser",
    determinant := "determinant",
    unipotent := "unipotent",
    classical := "classical group natural representation",
    almostsimple := "almost simple",
    cyclic := "cyclic group"
    >;

// Error object in exceptions
AschbacherError := recformat<
    Category : MonStgElt, // One of the AschbacherErrors
    Error : Any>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function TrivialCheck(node)
    return IsTrivial(node`Group), _;
end function;

procedure TrivialHom(~node, data)
    // Deal with the node later
    node`Group`UserGenerators := [];
    node`Type := NodeTypes`leaf;
end procedure;

function RefinedSummandSeries(M, summands, sorter)
    // First change of basis that exhibits summands
    // No stuff below blocks, since indecomposable summands!
    V := VectorSpace(M);
    basis := &cat[[V | x * Morphism(N, M) : x in Basis(N)] : N in summands];
    summandCBM := Matrix(basis);

    // Now obtain full comp series which refines summands
    // Obtain individual CBMs which exhibits series of each summand
    series := [sub<M | >];
    summandFactors := [];
    summandCBMs := [* *];
    
    preSum := sub<M | >;
    for i in [1 .. #summands] do
	sumSeries, _, cbm := CompositionSeries(summands[i]);

	// List of comp factors for this summand
	Append(~summandFactors, [#series - 1 + i : i in [1 .. #sumSeries]]);

	// CBM for this summand
	Append(~summandCBMs, cbm);
	
	for N in sumSeries do
	    phi := Morphism(N, summands[i]) * Morphism(summands[i], M);
	    NN := sub<M | [phi(x) : x in Basis(N)]>;
	    
	    assert Dimension(NN meet preSum) eq 0;
	    Append(~series, preSum + NN);
	end for;

	preSum +:= summands[i];
    end for;

    factors := [series[i + 1] / series[i] : i in [1 .. #series - 1]];
    Remove(~series, 1);
    
    cbm := DiagonalJoin(<summandCBMs[i] : i in [1 .. #summandCBMs]>);
    return series, factors, cbm * summandCBM, summandFactors;
end function;

// Initial reduction that changes the basis to exhibit a composition series
// for the module that refines the module indecomposable summands
function InitialCBMCheck(node)
    try
	return not assigned node`ModuleData`Factors and
	not IsIrreducible(node`Group) , _;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end function;

procedure InitialCBMHom(~node, data)
    try
	M := GModule(node`Group);
	assert assigned node`ModuleData`SummandSort;

        vprint CompositionTree, 8 : "Find indecomposable summands", 
	  node`ModuleData`ExhibitSummands;
	
        if node`ModuleData`ExhibitSummands then
           sums := node`ModuleData`SummandSort(IndecomposableSummands(M));
	else
	    sums := [M];
	end if;
	
	vprint CompositionTree, 8 : "Compute CBM through summands and factors";
	series, factors, cbm, summandFactors := 
	  RefinedSummandSeries(M, sums, node`ModuleData`FactorComp);
	cbm := Generic(node`Group) ! cbm^(-1);
	   
	vprint CompositionTree, 8 : "Store MeatAxe reductions maps";

	// Store coordinates of blocks
	dim := [];
	left := [1];
	for i in [1 .. #factors] do
	    Append(~dim, Dimension(factors[i]));
	    Append(~left, left[#left] + dim[#dim]);
	end for;
	Prune(~left);
	
	// Construct reduction hom
	reduction := hom<node`Group -> node`Group | g :-> g^cbm>;

	V := VectorSpace(M);

	// Construct corresponding series of subspaces, for element testing
	seriesV := [sub<V | [ElementToSequence(x * Morphism(N, M)) :
	    x in Basis(N)]> : N in series];
	test := func<g | PreservesSubspaces(seriesV, g)>;

	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	scaling := function(g)
	    s := g[1, 1];
	    ss := Generic(node`Group) ! ScalarMatrix(Degree(node`Group), s);
	    return g / ss;
	end function;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | [scaling(g) : g in seq]>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	// In this we already have the image
	node`Image`InputGens := ChangeUniverse(UserGenerators(node`Group^cbm),
	    Generic(node`Group));
	
	node`Image`Group := sub<Generic(node`Group) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);
	
	node`CBM := func<node | cbm * node`Image`CBM(node`Image)>;

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert node`Image`Scalar eq node`Scalar;
	node`Kernel`Scalar := Identity(node`Group);

	// No kernel since indecomposable summands
	SetupKnownKernel(~node, [Generic(node`Group) | ], [], node`Safe);

	// Save info about modules
	goodFactors := [i : i in [1 .. #factors] | exists{x : x in
	    ActionGenerators(factors[i]) | not IsIdentity(x)}];
	assert not IsEmpty(goodFactors);
        
	node`ModuleData := rec<ModuleInfo | FactorCorners := left,
	    FactorDimensions := dim, CBM := cbm,
	    Factors := factors, RemovedOp := false,
	    Summands := sums, SummandFactors := summandFactors,
	    ProcessedSummands := 0, ProcessedFactors := 0,
	    ChosenSummand := 0, nonTrivials := goodFactors,
	    ExhibitSummands := node`ModuleData`ExhibitSummands,
	    SummandSort := node`ModuleData`SummandSort,
	    FactorComp := node`ModuleData`FactorComp>;
	
	// Skip unipotent check for image
	node`Image`HomFinderPriorities := [2^25, -1, 2^23, 2^22, 2^19, 2^18,
	    2^17, 2^16, 2^15, 2^14, 2^13, 2^12, 2^11, 2^10,
	    2^9, 2^8, 2^7, 2^6, 2^2];
	
	node`Image`ModuleData := node`ModuleData;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end procedure;

// Reduction that projects to the diagonal blocks defined by the composition
// factors, with kernel O_p
function RemoveOpCheck(node)
    try
	return assigned node`ModuleData`Factors and
	not node`ModuleData`RemovedOp, _;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end function;

procedure RemoveOpHom(~node, data)
    try
	// Construct reduction hom
	reduction := hom<node`Group -> node`Group | g :->
	Generic(node`Group) ! BlockDiagonal(g,
	    node`ModuleData`FactorDimensions, node`ModuleData`FactorCorners)>;

	scaling := function(g)
	    s := g[1, 1];
	    ss := Generic(node`Group) ! ScalarMatrix(Degree(node`Group), s);
	    return g / ss;
	end function;
	
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	test := func<g | true>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | [scaling(g) : g in seq]>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(node`Group));
	
	node`Image`Group := sub<Generic(node`Group) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert node`Image`Scalar eq node`Scalar;
	node`Kernel`Scalar := Identity(node`Group);

	node`CBM := func<node | node`Image`CBM(node`Image)>;
	
	node`ModuleData`RemovedOp := true;
	node`Kernel`ModuleData := node`ModuleData;
	node`Image`ModuleData := node`ModuleData;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end procedure;

// Reduction that projects onto a group of diagonal blocks corresponding to
// module composition factors inside one indecomposable summand
function SummandCheck(node)
    try
	return assigned node`ModuleData`Factors and
	node`ModuleData`RemovedOp and node`ModuleData`ChosenSummand eq 0, _;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end function;

function SummandCBM(node, totalDim, preCBM, summandCBM, postCBMs)
    vprint CompositionTree, 10 : "Entering SummandCBM";
    cbm := DiagonalJoin(<x : x in [* summandCBM *] cat postCBMs>);

    // May be trivial summand blocks after, if kernels are trivial
    if NumberOfRows(cbm) lt totalDim then
	n := totalDim - NumberOfRows(cbm);
	cbm := DiagonalJoin(<cbm,
	    IdentityMatrix(CoefficientRing(node`Group), n)>);
    end if;
    
    cbm := DiagonalJoin(<x : x in Append(preCBM, cbm)>);
    vprint CompositionTree, 10 : "Return from SummandCBM", preCBM, cbm;
    return cbm;
end function;

function SummandCBMHelper(node, totalDim, cbmList)
    vprint CompositionTree, 10 :  "Entering SummandCBMHelper";
    if node`Kernel`Type eq NodeTypes`leaf then
        // Ignore leaf CBMs, hence may need to add identity in SummandCBM
	l := [* *];
    else
	cbmK := node`Kernel`CBM(node`Kernel);
	l := [* cbmK *];
    end if;
    cbmI := node`Image`CBM(node`Image);
    vprint CompositionTree, 10 : "Calling SummandCBM";
    cbm := SummandCBM(node, totalDim, cbmList, cbmI, l);
    vprint CompositionTree, 10 : "SummandCBM finished";
    vprint CompositionTree, 10 : "Return from SummandCBMHelper", 
	   Degree(node`Group), NumberOfRows(cbm), NumberOfColumns(cbm);
    return Generic(node`Group) ! cbm;
end function;

procedure SummandHom(~node, data)
    try
	assert assigned node`ModuleData;
        
        // Choose next block in module comp series
	assert node`ModuleData`ProcessedSummands lt #node`ModuleData`Summands;

	// CBMs for each summand
	cbmList := [* *];

	summandDim := node`ModuleData`ProcessedSummands gt 0
	    select &+[&+node`ModuleData`FactorDimensions[
	    node`ModuleData`SummandFactors[j]] :
	    j in [1 .. node`ModuleData`ProcessedSummands]] else 0;
	
	// Find the next summand with a non-trivial comp factor
	// There must be one since the group is not unipotent
	for i in [node`ModuleData`ProcessedSummands + 1 ..
	    #node`ModuleData`Summands] do
	    foundFactor := false;
	    
	    for j in [1 .. #node`ModuleData`SummandFactors[i]] do
		k := node`ModuleData`SummandFactors[i][j];
		if k in node`ModuleData`nonTrivials then
		    top := node`ModuleData`FactorCorners[k] - summandDim;
		    
		    // Construct reduction hom
		    image := GL(node`ModuleData`FactorDimensions[k],
			CoefficientRing(node`Group)); 
		    
		    reduction := hom<node`Group -> image |
		    g :-> Generic(image) !
			Submatrix(g, top, top, Degree(image), Degree(image))>;
		    
		    gens := ChangeUniverse([Function(reduction)(g) :
			g in UserGenerators(node`Group)], Generic(image));   
		    factorGroup := sub<Generic(image) | gens>;
		    
		    if not IsTrivial(factorGroup) then
			foundFactor := true;
			break;
		    end if;
		end if;
	    end for;
	    

	    if foundFactor then
		node`ModuleData`ProcessedSummands := i;
		break;
	    else
		// All factors in this summand are trivial
		Append(~cbmList, Identity(GL(&+
		    node`ModuleData`FactorDimensions[
		    node`ModuleData`SummandFactors[i]],
		    CoefficientRing(node`Group))));
	    end if;
	end for;
		
	preDim := #cbmList gt 0 select &+[Degree(g) : g in cbmList] else 0;
	top := preDim + 1;
	
	// Construct reduction hom to summand
	image := GL(&+ node`ModuleData`FactorDimensions[
	    node`ModuleData`SummandFactors[node`ModuleData`ProcessedSummands]],
	    CoefficientRing(node`Group));
	
	reduction := hom<node`Group -> image | g :-> Generic(image) !
	Submatrix(g, top, top, Degree(image), Degree(image))>;

	scaling := function(g)
	    s := g[top, top];
	    ss := Generic(node`Group) ! ScalarMatrix(Degree(node`Group), s);
	    return g / ss;
	end function;
	
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	node`Image`InputGens := ChangeUniverse([Function(reduction)(g) :
	    g in UserGenerators(node`Group)], Generic(image));
	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;	
	assert not IsTrivial(node`Image`Group);
	
	test := func<g | true>;

	// Last block has trivial kernel
	if node`ModuleData`ProcessedSummands eq
	    #node`ModuleData`Summands then
	    SetupKnownKernel(~node, [Generic(node`Group) | ], [], node`Safe);
	    
	    ToKernelBatch := func<seq | [scaling(g) : g in seq]>;
	    FromKernelBatch := func<seq | seq>;
	    KernelDim := Degree(node`Group);
	else
	    KernelTop := top + Degree(node`Image`Group);
	    KernelDim := Degree(node`Group) - KernelTop + 1;
	    
	    ToKernelBatch :=
		func<seq | [GL(KernelDim, CoefficientRing(node`Group)) |
		Submatrix(scaling(g), KernelTop, KernelTop,
		KernelDim, KernelDim) : g in seq]>;
	    FromKernelBatch := func<seq | [Generic(node`Group) |
		DiagonalJoin(Identity(GL(KernelTop - 1,
		CoefficientRing(node`Group))), g) : g in seq]>;
	end if;

	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := ToKernelBatch,
	    FromKernelBatch := FromKernelBatch,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
		
	totalDim := &+[&+ node`ModuleData`FactorDimensions[
	    node`ModuleData`SummandFactors[j]] :
	    j in [node`ModuleData`ProcessedSummands ..
	    #node`ModuleData`Summands]];
	
	assert totalDim + preDim eq Degree(node`Group);
	node`CBM := func<node | SummandCBMHelper(node, totalDim, cbmList)>;

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert node`Image`Scalar[1, 1] eq node`Scalar[1, 1];
	node`Kernel`Scalar :=
	    node`ActionMaps`ToKernelBatch([Identity(node`Group)])[1];

	node`Kernel`ModuleData := node`ModuleData;
	node`Image`ModuleData := node`ModuleData;
	node`Image`ModuleData`ChosenSummand :=
	    node`ModuleData`ProcessedSummands;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end procedure;

// Reduction that projects onto a diagonal block from a module comp factor
function BlockCheck(node)
    try
	return assigned node`ModuleData`Factors and
	node`ModuleData`RemovedOp and node`ModuleData`ChosenSummand gt 0, _;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end function;

procedure BlockHom(~node, data)
    try
	assert assigned node`ModuleData;
        n := node`ModuleData`ChosenSummand;
	
	summandTop := node`ModuleData`
	    FactorCorners[node`ModuleData`SummandFactors[n][1]];

	factorDim := node`ModuleData`ProcessedFactors gt 0
	    select &+[node`ModuleData`FactorDimensions[j] :
	    j in node`ModuleData`SummandFactors[n][1 ..
	    node`ModuleData`ProcessedFactors]] else 0;
	
	// CBMs for each summand
	cbmList := [* *];
	factorNumbers := [node`ModuleData`ProcessedFactors + 1 ..
			  #node`ModuleData`SummandFactors[n]];
	
	vprint CompositionTree, 10 : "Considering factors ", factorNumbers;
	
	for i in factorNumbers do
	    k := node`ModuleData`SummandFactors[n][i];
	    vprint CompositionTree, 10 : "Considering factor ", k;
	    image := GL(node`ModuleData`FactorDimensions[k],
			CoefficientRing(node`Group));

	    if k in node`ModuleData`nonTrivials then
		vprint CompositionTree, 10 : "Factor is non-trivial";
		top := node`ModuleData`FactorCorners[k] -
		    summandTop - factorDim + 1;
		
		// Construct reduction hom	
		reduction := hom<node`Group -> image | g :-> Generic(image) !
		Submatrix(g, top, top, Degree(image), Degree(image))>;
		
		node`Image`InputGens :=
		    ChangeUniverse([Function(reduction)(g) :
		    g in UserGenerators(node`Group)], Generic(image));
		node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
		
		if not IsTrivial(node`Image`Group) then
		    node`ModuleData`ProcessedFactors := i;
		    break;
		else
		    vprint CompositionTree, 10 : "Trivial factor", i, Degree(image);
		    Append(~cbmList, Identity(image));
		end if;
	    else
		vprint CompositionTree, 10 : "Trivial factor", i, Degree(image);
		Append(~cbmList, Identity(image));
	    end if;
	end for;
	    
	assert not IsTrivial(node`Image`Group);
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	  scaling := function(g)
	    s := g[top, top];
	    assert s ne 0;
	    ss := Generic(node`Group) ! ScalarMatrix(Degree(node`Group), s);
	    return g / ss;
	end function;
	
	test := func<g | true>;
	    	
	// Last block has trivial kernel
	if node`ModuleData`ProcessedFactors eq
	    #node`ModuleData`SummandFactors[n] then
	    SetupKnownKernel(~node, [Generic(node`Group) | ], [], node`Safe);

	  ToKernelBatch := func<seq | [scaling(g) : g in seq]>;
	    FromKernelBatch := func<seq | seq>;
	    KernelDim := Degree(node`Group);
	else
	    KernelTop := top + Degree(node`Image`Group);
	    KernelDim := Degree(node`Group) - KernelTop + 1;
	    ToKernelBatch :=
		func<seq | [GL(KernelDim, CoefficientRing(node`Group)) |
			      Submatrix(scaling(g), KernelTop, KernelTop,
		KernelDim, KernelDim) : g in seq]>;
	    FromKernelBatch := func<seq | [Generic(node`Group) |
		DiagonalJoin(Identity(GL(KernelTop - 1,
		CoefficientRing(node`Group))), g) : g in seq]>;
	end if;

	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := ToKernelBatch,
	    FromKernelBatch := FromKernelBatch,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
		
	totalDim := &+[node`ModuleData`FactorDimensions
	    [node`ModuleData`SummandFactors[n][j]] :
	    j in [node`ModuleData`ProcessedFactors ..
	    #node`ModuleData`SummandFactors[n]]];
        
	node`CBM := func<node | SummandCBMHelper(node, totalDim, cbmList)>;
	
	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert node`Image`Scalar[1, 1] eq node`Scalar[1, 1];
	node`Kernel`Scalar :=
	    node`ActionMaps`ToKernelBatch([Identity(node`Group)])[1];

	node`Kernel`ModuleData := node`ModuleData;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`reducible, Error := err>);
    end try;
end procedure;

function ImprimitivityCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;
	    
	flag := IsPrimitive(node`Group);
        if flag cmpeq "unknown" then
	    return "fail", _;
	end if;

	return not flag, _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`imprimitive, Error := err>);        
    end try;
end function;

procedure ImprimitivityHom(~node, data)
    try
	// Construct reduction hom
        image := BlocksImage(node`Group);
	
	reduction := hom<node`Group -> image | g :->
	ImprimitiveAction(node`Group, g)>;
	
	test := func<g | PreservesBlocks(Blocks(node`Group), g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	cbm := ImprimitiveBasis(node`Group);
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | [g^(cbm^(-1)) : g in seq]>,
	    FromKernelBatch := func<seq | [g^cbm : g in seq]>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	// In this case we already have the image
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(image));

	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);

	node`CBM := func<node | cbm^(-1) * node`Kernel`CBM(node`Kernel)>;
	
	// Setup MeatAxe data for kernel
	blocks := Blocks(node`Group);
	node`Kernel`ModuleData := rec<ModuleInfo |
	    Factors := blocks, Summands := blocks,
	    SummandFactors := [[i] : i in [1 .. #blocks]],
	    ProcessedSummands := 0, ProcessedFactors := 0,
	    nonTrivials := [i : i in [1 .. #blocks]],
	    RemovedOp := true, ChosenSummand := 0,
	    FactorDimensions := [Dimension(B) : B in blocks],
	    FactorCorners := [i gt 1 select Self(i - 1) +
	    Dimension(blocks[i]) else 1 : i in [1 .. #blocks]],
	    ExhibitSummands := node`ModuleData`ExhibitSummands,
	    SummandSort := node`ModuleData`SummandSort,
	    FactorComp := node`ModuleData`FactorComp>;

	// Skip unipotent check for kernel
	node`Kernel`Group := node`Group;
	node`Kernel`HomFinderPriorities := [2^25, -1, 2^23, 2^22, 2^19, 2^18,
	    2^17, 2^16, 2^15, 2^14, 2^13, 2^12, 2^11, 2^10,
	    2^9, 2^8, 2^7, 2^6, 2^2];
	delete node`Kernel`Group;
	
	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert IsIdentity(node`Image`Scalar);
	node`Kernel`Scalar := node`ActionMaps`ToKernelBatch([node`Scalar])[1];
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`imprimitive, Error := err>);	
    end try;
end procedure;

// Is node group absolute reducible?
function AbsoluteReducibleCheck(node)
    try
	// Group must act irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`block]`negative eq 0 then
	    return "N/A", _;
	end if;
		
	// Also store endomorphism generator     
	flag, gen := IsAbsolutelyIrreducible(node`Group);
		
	if flag then
	    return not flag, _;
	else	    
	    return true, Generic(node`Group) ! gen;
	end if;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`absreducible, Error := err>);
    end try;
end function;

procedure AbsoluteReducibleHom(~node, data)
    try
	image, inc := AbsoluteRepresentation(node`Group);
        MA := MatrixAlgebra(CoefficientRing(node`Group), Degree(node`Group));

	reduction := hom<node`Group -> image | g :->
	Generic(image) ! inc(MA ! g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	test := func<g | g^data eq g>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	// In this we already have the image
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(image));
	
	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);

	node`CBM := func<node | node`Kernel`CBM(node`Kernel)>;

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert node`Image`Scalar[1, 1] eq
	    CoefficientRing(image) ! node`Scalar[1, 1];
	node`Kernel`Scalar := node`Scalar;
	
	// The kernel is always trivial in this case
	SetupKnownKernel(~node, [Generic(node`Group) | ], [], true);
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`absreducible, Error := err>);
    end try;
end procedure;

function SemilinearCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;

	flag := IsSemiLinear(node`Group);
        if flag cmpeq "unknown" then
	    return "fail", _;
	end if;

	return flag, _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`semilinear, Error := err>);        
    end try;
end function;

function KernelOfHom(G, W, E, image)

    n, a := XGCD(image cat [#E]);
    g := &*[G.i^a[i] : i in [1 .. Ngens(G)]];
    g_slp := &*[W.i^a[i] : i in [1 .. Ngens(W)]];
    
    /* generators of kernel as normal subgroup */
    H := [G.i * g^(-image[i] div n) : i in [1 .. Ngens(G)]];
    H_slps := [W.i * g_slp^(-image[i] div n) : i in [1 .. Ngens(W)]];
    
    /* add in conjugates to generate kernel as subgroup */
    K := [g^(#E div n)] cat [H[i]^(g^u) : i in [1 .. #H], u in [0 .. #E - 1]];
    K_slps := [g_slp^(#E div n)] cat
	[H_slps[i]^(g_slp^u) : i in [1 .. #H_slps], u in [0 .. #E - 1]];
   
   return K, K_slps;
end function;

procedure SemilinearHom(~node, data)
    try
	// Construct reduction
	q := #CoefficientRing(node`Group);
	C := CentralisingMatrix(node`Group);
	e := DegreeOfFieldExtension(node`Group);
	V := VectorSpace(node`Group);

	image := CyclicGroup(GrpAb, e);
	power := func<g | rep{j : j in [0 .. e - 1] |
	    V.1 * C * g eq V.1 * g * C^(q^j)}>;
	reduction := hom<node`Group -> image | g :-> image.1 * (power(g))>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	
	// Construct semilinearity test
	test := func<g | exists{j : j in [0 .. e - 1] |
	    V.1 * C * g eq V.1 * g * C^(q^j)}>;

	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	vprint CompositionTree, 7 : "Find semilinear images";
	images := [power(g) : g in UserGenerators(node`Group)];
	gens := [image.1 * x : x in images];
	node`Image`Group := sub<image | gens>;
	node`Image`InputGens := gens;
	assert not IsTrivial(node`Image`Group);
	node`Image`Group`UserGenerators := node`Image`InputGens;

	vprint CompositionTree, 7 : "Find semilinear kernel";
	kernelGens, kernelSLPs := KernelOfHom(node`Group, node`WordGroup,
	    image, images);

	vprint CompositionTree, 7 : "Found semilinear kernel";

	node`CBM := func<node | Identity(node`Group)>;

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert IsIdentity(node`Image`Scalar);
	node`Image`ScalarGroup := sub<Generic(node`Image`Group) | node`Image`Scalar>;
	node`Kernel`Scalar := node`Scalar;	
	
	SetupKnownKernel(~node,
	    ChangeUniverse(kernelGens, Generic(node`Group)),
	    kernelSLPs, node`Safe);
	vprint CompositionTree, 7 : "Semilinear setup ok";
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`semilinear, Error := err>);	
    end try;
end procedure;

function TensorCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;
	    
	flag := IsTensor(node`Group : Fast := node`FastTensorTest);
        if flag cmpeq "unknown" then
	    return "fail", _;
	end if;

	return flag, _;
    catch err;
	error Error(rec<AschbacherError |
	    Category := AschbacherErrors`tensor, Error := err>);        
    end try;
end function;

procedure TensorHom(~node, data)
    try
	cbm := TensorBasis(node`Group);
        factors := TensorFactors(node`Group);

	imageNr := node`TensorFactorSort[1];
	kernelNr := node`TensorFactorSort[2];
	
	image := factors[imageNr];
	n := Degree(factors[2]);
	
	// Construct reduction
	reduction := hom<node`Group -> image | g :->
	Generic(image) ! (PreservesTensor([g], cbm, n)[2][1][imageNr])>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	
	// Set scalars
	alpha := PrimitiveElement(CoefficientRing(image));
	node`Image`Scalar := Generic(image) !
	    ScalarMatrix(Degree(image), alpha);

	imageBatch := func<seq | [Generic(image) | g[imageNr] :
	    g in PreservesTensor(seq, cbm, n)[2]],
	    [Identity(node`Group) : i in [1 .. #seq]],
	    [Identity(node`Group) : i in [1 .. #seq]]>;
	
	kernel := factors[kernelNr];

	// Function to move scalars kernel side
	scaleTensor := function(G, pair, outputNr, scaleNr)
	    s := Generic(G) ! ScalarMatrix(Degree(G), pair[scaleNr][1, 1]);
	    g := Generic(G) ! pair[outputNr];
	    return g / s;
        end function;
    
	ToKernelBatch := func<seq | [Generic(kernel) |
	    scaleTensor(kernel, g, kernelNr, imageNr) :
	    g in PreservesTensor(seq, cbm, n)[2]]>;
	
	FromKernelBatch := func<seq | [(Generic(node`Group) !
	    (imageNr eq 2 select TensorProduct(g, Identity(image)) else
	    TensorProduct(Identity(image), g)))^(cbm^(-1)) : g in seq]>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := imageBatch,
	    ToKernelBatch := ToKernelBatch,
	    FromKernelBatch := FromKernelBatch,
	    Test := func<g | PreservesTensor([g], cbm, n)[1]>,
	    BatchTest := func<seq | PreservesTensor(seq, cbm, n)[1]>>;

	// We already know image
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(image));
	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);
	
	node`Kernel`Scalar :=
	    node`ActionMaps`ToKernelBatch([node`Scalar])[1];
	node`CBM := func<node | cbm * (Generic(node`Group) !
	    TensorProduct(node`Image`CBM(node`Image),
	    node`Kernel`CBM(node`Kernel)))>;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`tensor, Error := err>);	
    end try;
end procedure;

function TensorInducedCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;
	    
	flag := IsTensorInduced(node`Group);
        if flag cmpeq "unknown" then
	    return "fail", _;
	end if;

	return flag, _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`induced, Error := err>);        
    end try;
end function;

procedure TensorInducedHom(~node, data)
    try
	cbm := TensorInducedBasis(node`Group);
        genImages := TensorInducedPermutations(node`Group);

	// Construct image
	n := Degree(Universe(genImages));
	image := sub<Sym(n) | genImages>;
	
	// Construct reduction
	reduction := hom<node`Group -> image | g :->
	TensorInducedAction(node`Group, g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	// Tensor induction test
	test := func<g | Category(TensorInducedAction(node`Group, g))
	    eq GrpPermElt>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | [g^cbm : g in seq]>,
	    FromKernelBatch := func<seq | [g^(cbm^(-1)) : g in seq]>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	// Make sure to use normal smaller field test for the kernel
	node`Kernel`Group := node`Group;
	node`Kernel`HomFinderPriorities := [2^25, 2^24, 2^23, 2^22, 2^18,
	    2^17, 2^16,
	    2^15, 2^14, 2^13, 2^12, 2^11, 2^15 + 1,
	    2^9, 2^8, 2^7, 2^6, 2^2, 2];
	delete node`Kernel`Group;

	// We already know image and kernel
	node`Image`InputGens := ChangeUniverse(genImages, Generic(image));

	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);	

	node`CBM := func<node | cbm * node`Kernel`CBM(node`Kernel)>;

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	assert IsIdentity(node`Image`Scalar);
	node`Kernel`Scalar := node`ActionMaps`ToKernelBatch([node`Scalar])[1];
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`induced, Error := err>);	
    end try;
end procedure;

function ExtraSpecialCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;
	    
	flag := HasC6Decomposition(node`Group :
	    Randomiser := node`RandomProcess);
	if flag cmpeq "unknown" then
	    return "fail", _;
	end if;

	if flag then
	    if not IsTrivial(C6Image(node`Group)) then
		return true, _;
	    end if;
	end if;
	
	return false, _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`extraspecial, Error := err>);        
    end try;
end function;

procedure ExtraSpecialHom(~node, data)
    try
        kernel, kernelSLPs := C6Kernel(node`Group);
	image := C6Image(node`Group);

	// Construct reduction
	reduction := hom<node`Group -> image | g :-> C6Action(node`Group, g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	
	// Extraspecial normaliser test
	test := func<g | Category(C6Action(node`Group, g))
	    in {GrpMatElt, GrpPermElt}>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;

	// Adjust priority for kernel hom-finder, IsPrimitive should be high!

	// We already know image and kernel
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(image));
	node`Image`Group := sub<Generic(image) | node`Image`InputGens>;
	assert not IsTrivial(node`Image`Group);

	// Set scalars
	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	node`Kernel`Scalar := node`Scalar;	

	node`CBM := func<node | C6Basis(node`Group) *
	    (Generic(node`Group) ! node`Kernel`CBM(node`Kernel))>;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`extraspecial, Error := err>);	
    end try;
end procedure;

function ProjectiveSmallerFieldCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;

	F := CoefficientRing(node`Group);
	d := Degree(node`Group);
	
	if d ge 2 and CanApplyDiscreteLog(F) then
	    if IsOverSmallerField(node`Group : Scalars := true) then
		// Construct image
		images := [F | ];

		for g in UserGenerators(node`Group) do
		    _, scalar := SmallerFieldImage(node`Group, g);
		    Append(~images, scalar);
		end for;

		// Make sure that we have a non-trivial image
		if not exists{s : s in images | not IsOne(s)} and
		    IsIdentity(node`Scalar) then
		    return "N/A", _;
		end if;
		
		alpha := F ! PrimitiveElement(SmallerField(node`Group));
		Append(~images, alpha);
		return true, images;
	    end if;
	end if;
	return false, _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`smallerfield, Error := err>);        
    end try;
end function;

function SmallerFieldCheck(node)
    try
	// Group must act absolutely irreducibly
        if node`HomFinderStamps[AschbacherAlgorithms`absreducible]`negative
	    eq 0 then
	    return "N/A", _;
	end if;

	return IsOverSmallerField(node`Group : Scalars := false), _;
    catch err;
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`smallerfield, Error := err>);        
    end try;
end function;

procedure SmallerFieldHom(~node, data)
    try
	F := CoefficientRing(node`Group);
    
	// Construct image
        genImages := [];
	scalars := [F | ];
	for g in UserGenerators(node`Group) do
	    image_g, scalar_g := SmallerFieldImage(node`Group, g);
	    Append(~genImages, image_g);
	    Append(~scalars, scalar_g);
	end for;

	assert forall{s : s in scalars | IsOne(s)};
	image := sub<Generic(Universe(genImages)) | genImages>;
	
	// Construct reduction
	reduction := hom<node`Group -> image | g :->
	SmallerFieldImage(node`Group, g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	q := #SmallerField(node`Group);
	n := Order(node`Scalar);
	node`Image`Scalar := Function(reduction)(node`Scalar);
	assert node`Image`Scalar eq
	    Generic(image) ! node`Scalar^(n div GCD(q - 1, n));
	
	// The kernel is always trivial in this case
	SetupKnownKernel(~node, [Generic(node`Group) | ], [], node`Safe);
	// Kernel scalar is arbitrary
	node`Kernel`Scalar := node`Scalar;
		
	// Smaller field test
	test := func<g | Category(SmallerFieldImage(node`Group, g))
	    eq GrpMatElt>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
	
	// We already know image
	node`Image`Group := image;
	node`Image`InputGens := ChangeUniverse(genImages,
	    Generic(node`Image`Group));
	assert Generators(image) subset SequenceToSet(genImages);
	assert not IsTrivial(node`Image`Group);

	_, inc := ExtendField(GL(Degree(node`Group),
	    SmallerField(node`Group)), F);

	node`CBM := func<node | SmallerFieldBasis(node`Group) *
	    inc(node`Image`CBM(node`Image))>;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`smallerfield, Error := err>);	
    end try;
end procedure;

procedure ProjectiveSmallerFieldHom(~node, images)
    try
	F := CoefficientRing(node`Group);
	I, inc := MultiplicativeGroup(F);

	// Discrete log
	toImage := Inverse(inc);

	// We already know image
	node`Image`InputGens := toImage(Prune(images));
	node`Image`Group := sub<I | node`Image`InputGens>;
	node`Image`Group`UserGenerators := node`Image`InputGens;
	I`FactoredOrder := Factorisation(Order(I));
	
	// Construct reduction
	reduction := hom<node`Group -> node`Image`Group | g :-> toImage(s)
	where _, s is SmallerFieldImage(node`Group, g)>;

	// Set scalars
	q := #SmallerField(node`Group);
	n := Order(node`Scalar);
	omega := PrimitiveElement(F);
	node`Image`Scalar := I.1 * (#I div LCM(q - 1, n));
	node`Image`ScalarGroup := sub<I | node`Image`Scalar>;
	fullImage := sub<I | node`Image`Group, node`Image`ScalarGroup>;
	
	assert not IsTrivial(node`Image`ScalarGroup) or
	    #SmallerField(node`Group) eq 2;
	assert not IsTrivial(fullImage);

	// Smaller field test
	test := func<g | toImage(s) in fullImage
	    where _, s is SmallerFieldImage(node`Group, g)>;
    
	// Reduction with cyclic group patch
	reductionScalar := func<g | SmallerFieldScalarPatch(reduction,
	    node`Image`ScalarGroup, inc, node`Scalar, g)>;
			
	_, inc := ExtendField(GL(Degree(node`Group),
	    SmallerField(node`Group)), F);
	cbm := SmallerFieldBasis(node`Group);
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := test,
	    ToKernelBatch := func<seq | [SmallerFieldImage(node`Group, g) :
	    g in seq]>,
	    FromKernelBatch := func<seq | [inc(g)^(cbm^(-1)) : g in seq]>,
	    BatchTest := func<seq | forall{g : g in seq | test(g)}>>;
	
	node`Kernel`Scalar := node`ActionMaps`
	    ToKernelBatch([node`Scalar^(n div GCD(q - 1, n))])[1];
	node`CBM := func<node | cbm * inc(node`Kernel`CBM(node`Kernel))>;
    catch err
	error Error(rec<AschbacherError |
	Category := AschbacherErrors`smallerfield, Error := err>);	
    end try;
end procedure;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Does g preserve the given vector space subspace series?
function PreservesSubspaces(series, g)
    return forall{W : W in series | forall{b : b in Basis(W) | b^g in W}};
end function;

function PreservesBlocks(blocks, g)
    return {Index(blocks, B^g) : B in blocks} eq {1 .. #blocks};
end function;

function PreservesTensor(seq, cbm, n)
    flag, decomp := DecomposeKronecker([g^cbm : g in seq], n);
    
    if flag then
	return <true, decomp>;
    else
	return <false, []>;
    end if;
end function;

function FindPatchElement(order, factors, h)
    c := [[x[1], e] where e is Valuation(Order(h), x[1]) :
	x in factors | IsDivisibleBy(Order(h), x[1])];
    badPrimeIdx := [i : i in [1 .. #c] |
	c[i][2] gt Valuation(order, c[i][1])];
    
    if #badPrimeIdx gt 0 then	
	n := [Order(h) div c[i][1]^c[i][2] : i in [1 .. #c]];
	e, m := XGCD(n);
	assert e eq 1;
	
	elts := [h * (m[i] * n[i]) : i in [1 .. #c]];
	assert &+elts eq h and
	    forall{i : i in [1 .. #elts] | Order(elts[i]) eq c[i][1]^c[i][2]};
	
	patch := &+(elts[badPrimeIdx]);
    else
	patch := Identity(Parent(h));
    end if;
    
    return -patch;
end function;
    
function ReductionScalarPatch(reduction, scalarGroup, g)
    assert Category(Codomain(reduction)) eq GrpAb;
    
    // Make sure that element image always lies in the group generated by
    // the generator images
    h := Function(reduction)(g);
    assert IsDivisibleBy(LCM(#Codomain(reduction), #scalarGroup), Order(h));

    patch := FindPatchElement(#Codomain(reduction),
	Parent(h)`FactoredOrder, h);

    assert IsDivisibleBy(Order(scalarGroup), Order(patch));
    assert IsDivisibleBy(#Codomain(reduction), Order(h + patch));
    
    // Return fixed element and necessary scalar fix
    return h + patch, patch;
end function;

function SpinorScalarPatch(reduction, scalarGroup, scalar, g)
    h, scalar_h := ReductionScalarPatch(reduction, scalarGroup, g);

    bigScalarH := IsIdentity(h - scalar_h) select Identity(Domain(reduction))
	else scalar;
    
    return h, bigScalarH^(-1);
end function;

function DeterminantScalarPatch(reduction, scalarGroup, inc, scalar, g)
    h, s := ReductionScalarPatch(reduction, scalarGroup, g);

    d := Degree(Domain(reduction));
    matScalars := [Generic(Domain(reduction)) | ];

    // Determinant is a d-th power, find d-th roots of the scalar to patch
    roots := [r : r in AllRoots(inc(h - s), d) |
	IsDivisibleBy(Order(scalar), Order(r))];
	
    if #roots gt 0 then
	Append(~matScalars, rep{Generic(Domain(reduction)) !
	    ScalarMatrix(d, r) : r in roots});
    else
	Append(~matScalars, Identity(Domain(reduction)));
    end if;
	
    return h, matScalars[1]^(-1);
end function;

function SmallerFieldScalarPatch(reduction, scalarGroup, inc, scalar, g)
    h, scalar_h := ReductionScalarPatch(reduction, scalarGroup, g);

    // Not necessary to pass back any scalar
    // The kernel scalar is the same as the node scalar
    return h, Identity(Domain(reduction)); 
end function;

function FormScalarPatch(reduction, scalarGroup, inc, scalar, type, g)
    h, s := ReductionScalarPatch(reduction, scalarGroup, g);

    n := Order(scalar);
    d := Degree(Domain(reduction));

    if type ne "unitary" then
	matScalars := [Generic(Domain(reduction)) | ];
	roots := {r : r in AllRoots(inc(h - s), 2) |
	    IsDivisibleBy(n, Order(r))};
	
	if #roots gt 0 then
	    Append(~matScalars, rep{Generic(Domain(reduction)) !
		ScalarMatrix(d, r) : r in roots});
	else
	    Append(~matScalars, Identity(Domain(reduction)));
	end if;

	return h, matScalars[1]^(-1);
    else
	F := CoefficientRing(scalar);
	FF := sub<F | Degree(F) div 2>;
	q := #F;

	matScalars := [Generic(Domain(reduction)) | ];

	// Find some element that maps to g
	flag, r := NormEquation(F, FF ! inc(h - s) : Deterministic := true);
	assert flag;
	assert not IsZero(r);
	assert Norm(r, FF) eq FF ! inc(h - s);
	
	inv := Inverse(inc);
	patch := FindPatchElement(n, Factorisation(q - 1), inv(r));
	r *:= inc(patch);
	
	if IsDivisibleBy(n, Order(r)) and Norm(r, FF) eq FF ! inc(h - s) then
	    Append(~matScalars,
		Generic(Domain(reduction)) ! ScalarMatrix(d, r));
	else
	    Append(~matScalars, Identity(Domain(reduction)));
	end if;

	return h, matScalars[1]^(-1);
    end if;
end function;

function ReductionWithScalar(reduction, elts)
    images := [];
    scalars := [Generic(Universe(elts)) | ];
    assert Category(reduction) eq UserProgram;
    
    for g in elts do
	h, s := reduction(g);
	
	Append(~images, h);
	Append(~scalars, s);
    end for;

    return images, scalars;
end function;

function BlockDiagonal(g, dims, corners)
    return DiagonalJoin(<Submatrix(g, corners[i], corners[i],
	dims[i], dims[i]): i in [1 .. #dims]>);
end function;
