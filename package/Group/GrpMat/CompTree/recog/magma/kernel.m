/******************************************************************************
 *
 *    kernel.m  Composition Tree Kernel Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: kernel.m 3165 2016-03-05 17:48:46Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "recog.m" : RecogError, NodeTypes;
import "mathom.m" : ReductionOrder;
import "node.m" : ERROR_CRISIS, InitialiseRandomProcess, AschbacherAlgorithms;

declare verbose CompositionTreeKernel, 10;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

procedure SetKernelBatchSize(~node)
    assert assigned node`KernelBatchSizeFunc;
    
    if Category(node`Group) eq GrpMat then
	if node`HomFinderStamps[AschbacherAlgorithms`imprimitive]`
	    negative gt 0 then
	    vprint CompositionTree, 3 :
		"Kernel batch size primitive case, depth", node`Depth;
	    
	    // Group is primitive
	    if IsDefined(node`KernelBatchSizeFunc, "Primitive") then
		node`KernelBatchSize := node`KernelBatchSizeFunc["Primitive"];
	    else
		node`KernelBatchSize :=
		    func<G | Max([2 * Floor(Log(2, Degree(G))),
		    NumberOfGenerators(G),
		    IsDefined(node`MinKernelGens, "Primitive") select
		    node`MinKernelGens["Primitive"] else 5])>;
	    end if;
	elif node`HomFinderStamps[AschbacherAlgorithms`removeop]`
	    negative gt 0 then
	    vprint CompositionTree, 3 :
		"Kernel batch size trivial O_p case, depth", node`Depth;

	    // Trivial O_p    
	    if IsDefined(node`KernelBatchSizeFunc, "Irreducible") then
		node`KernelBatchSize := node`KernelBatchSizeFunc["Irreducible"];
	    else
		node`KernelBatchSize :=
		    func<G | Max(NumberOfGenerators(G),
		    IsDefined(node`MinKernelGens, "Irreducible") select
		    node`MinKernelGens["Irreducible"] else 20)>;
	    end if;
	else
	    // Kernel is (subgroup of) O_p
	vprint CompositionTree, 3 :
	    "Kernel batch size unipotent case, depth", node`Depth;

	if IsDefined(node`KernelBatchSizeFunc, "Unipotent") then
		node`KernelBatchSize := node`KernelBatchSizeFunc["Unipotent"];
	    else
		node`KernelBatchSize :=
		    func<G | Max(NumberOfGenerators(G),
		    IsDefined(node`MinKernelGens, "Unipotent") select
		    node`MinKernelGens["Unipotent"] else 100)>;
	    end if;
	end if;
    else
	assert Category(node`Group) eq GrpPerm;
	vprint CompositionTree, 3 :
	    "Kernel batch size permutation case, depth", node`Depth;

	if IsDefined(node`KernelBatchSizeFunc, "Permutation") then
	    node`KernelBatchSize := node`KernelBatchSizeFunc["Permutation"];
	else
	    node`KernelBatchSize :=
		func<G | Max(NumberOfGenerators(G),
		    IsDefined(node`MinKernelGens, "Permutation") select
		    node`MinKernelGens["Permutation"] else 10)>;
	end if;
    end if;
end procedure;

function MaxNodeNumber(tree)
    if tree`Type eq NodeTypes`leaf then
	return tree`Number;
    else
	return MaxNodeNumber(tree`Kernel);
    end if;
end function;

// Take a node element batch and divide out by images
function ObtainKernelElements(node, elts, slps)
    vprint CompositionTree, 3 :
	"Check that elements satisfy reduction, depth", node`Depth;
    if not node`ActionMaps`BatchTest(elts) then
	error ERROR_CRISIS;
    end if;
    
    vprint CompositionTree, 3 : "Map elements to image, depth", node`Depth;

    // Map elements to image
    images := node`ActionMaps`Batch(elts);
    
    vprint CompositionTree, 3 : "Obtain SLPs in image, depth", node`Depth;

    // Recursively obtain SLPs in image (in image NiceGroup gens)
    imageSLPs := node`Image`SLPMaps`EltToSLPBatch(images);
    nodeSLPs := UserGenerators(node`WordGroup);
    vprint CompositionTree, 3 : "Evaluate image SLPs, depth", node`Depth;
    
    // SLPs of preimages, in NiceGens
    preImagesSLPs := Evaluate(node`Image`NiceData`NiceToUserBatch(imageSLPs),
	nodeSLPs[node`Image`GenMap]);
    
    if Category(preImagesSLPs) ne SeqEnum then
	preImagesSLPs := [preImagesSLPs];
    end if;

    vprint CompositionTree, 3 : "Obtain pre-images, depth", node`Depth;
    
    preImages := ChangeUniverse(Evaluate(preImagesSLPs,
	UserGenerators(node`EvalGroup)), Generic(node`EvalGroup));
    
    assert #preImages eq #elts;
    assert Universe(slps) cmpeq Universe(preImagesSLPs);
    
    kernelElts := [elts[i] / preImages[i] : i in [1 .. #elts]];
    _, scalars := node`ActionMaps`Batch(kernelElts);
        
    // Divide out to obtain elements in kernel
    return node`ActionMaps`ToKernelBatch([(Generic(node`EvalGroup) !
	(kernelElts[i] * scalars[i])) : i in [1 .. #elts]]), 
	[slps[i] * preImagesSLPs[i]^(-1) : i in [1 .. #elts]];    
end function;

// Obtain kernel mandarins from node mandarins and SLPs of image mandarins
procedure SetKernelMandarins(~node)
    assert assigned node`Mandarins;
    assert assigned node`MandarinScalars; 
    assert assigned node`Image`MandarinSLPs;
    nodeSLPs := UserGenerators(node`WordGroup);

    // Avoid unnecessary work when node reduction is an isomorphism
    if node`KnownKernel and IsTrivial(node`Kernel`Group) then
	node`Kernel`Mandarins := [Identity(node`Kernel`Group) :
	    i in [1 .. #node`Mandarins]];
    else
	preImagesSLPs :=
	    Evaluate(node`Image`NiceData`NiceToUserBatch(
	    node`Image`MandarinSLPs),
	    nodeSLPs[node`Image`GenMap]);
	
	if Category(preImagesSLPs) ne SeqEnum then
	    preImagesSLPs := [preImagesSLPs];
	end if;

	preImages := ChangeUniverse(Evaluate(preImagesSLPs,
	    UserGenerators(node`EvalGroup)), Generic(node`EvalGroup));
	assert #preImages eq #node`Mandarins;
	
	kernelElts := [node`Mandarins[i] / preImages[i] :
	    i in [1 .. #node`Mandarins]];
	_, scalars := node`ActionMaps`Batch(kernelElts);
    
	vprint CompositionTree, 6 : "Store kernel mandarins, depth", node`Depth;
        
	// Divide out to obtain elements in kernel
	node`Kernel`Mandarins := ChangeUniverse(node`ActionMaps`ToKernelBatch(
	    [(Generic(node`EvalGroup) ! (kernelElts[i] * scalars[i])) :
	    i in [1 .. #node`Mandarins]]), Generic(node`Kernel`Group));
	assert #node`Kernel`Mandarins gt 0;
    end if;
end procedure;

// Obtain random elements from a node using its random process
function RandomElementBatch(randomiser, size)
    elts := [];
    slps := [];

    // Obtain batch of random elements
    for i in [1 .. size] do
	g, slp := randomiser();

	Append(~elts, g);
	Append(~slps, slp);
    end for;
    
    return elts, slps;
end function;

// Obtain kernel generators using the standard Monte-Carlo method
procedure MonteCarloKernel(~node, kernelBatchSize)
    assert assigned node`Kernel`InputGens;
    assert assigned node`KernelSLPs;

    vprintf CompositionTree, 3 :
	"Kernel batch size %o, depth %o\n", kernelBatchSize, node`Depth;

    elts, slps := RandomElementBatch(node`Randomiser, kernelBatchSize);
    
    // Add more generators to kernel
    kernelElts, kernelSLPs := ObtainKernelElements(node, elts, slps);
    node`Kernel`InputGens cat:= ChangeUniverse(kernelElts,
	Generic(Universe(kernelElts)));
        
    // Remove multiple generators in perm groups
    // Important in order to keep number of generators small
    node`Kernel`Group := sub<Generic(Universe(node`Kernel`InputGens)) |
	{@ g : g in node`Kernel`InputGens |
    g ne Identity(Universe(kernelElts)) @}>;
    
    // Book-keeping how generators were mapped into kernel
    node`Kernel`GenMap := [Index(node`Kernel`InputGens, g) :
	g in UserGenerators(node`Kernel`Group)];
    
    node`KernelSLPs cat:= kernelSLPs;
end procedure;

// Set mandarin SLPs from kernel and image
procedure MandarinVerification(~node)
    vprint CompositionTree, 6 :
	"Obtain mandarin pre-image SLPs, depth", node`Depth;
    // SLPs of preimages, in NiceGens
    preImagesSLPs := node`NiceData`FromImageNice(node`Image`MandarinSLPs);
    assert NumberOfGenerators(Universe(preImagesSLPs)) eq
	NumberOfGenerators(node`NiceData`Group);

    vprint CompositionTree, 6 :
	"Obtain kernel mandarin SLPs, depth", node`Depth;

    // SLPs of kernel elements, in NiceGens
    kernelNodeSLPs := node`NiceData`FromKernelNice(node`Kernel`MandarinSLPs);
    assert #preImagesSLPs eq #node`Mandarins;
    assert #kernelNodeSLPs eq #node`Mandarins;
    assert NumberOfGenerators(Universe(kernelNodeSLPs)) eq
	NumberOfGenerators(node`NiceData`Group);
    
    vprint CompositionTree, 6 :
	"Obtain node mandarin SLPs, depth", node`Depth;
    node`MandarinSLPs :=
	[kernelNodeSLPs[i] * preImagesSLPs[i] : i in [1 .. #node`Mandarins]];
    
    // Verify that mandarin SLPs are correct
    mandarins := node`SLPMaps`SLPToEltBatch(node`MandarinSLPs);
    for i in [1 .. #mandarins] do
	g := node`Mandarins[i] / mandarins[i];
	if not IsDivisibleBy(Order(node`Scalar), Order(g)) then
	    error ERROR_CRISIS;
	end if;
    end for;
end procedure;

procedure PresentationKernel(~node)
    vprint CompositionTree, 3 :	"Obtain kernel elements, depth", node`Depth;
    
    // Obtain normal generators of kernel
    kernelGens, kernelSLPs :=
	ObtainKernelElements(node,
	ChangeUniverse(UserGenerators(node`EvalGroup),
	Generic(node`EvalGroup)), UserGenerators(node`WordGroup));
    vprintf CompositionTree, 3 : "%o kernel elements found, depth %o\n",
	#kernelGens, node`Depth;

    ChangeUniverse(~kernelGens, Generic(Universe(kernelGens)));
    gens := UserGenerators(node`WordGroup);
    
    // Map relators from image
    relatorSLPs := Evaluate(node`Image`NiceData`NiceToUserBatch(
	node`Image`PresentationData`SLPRelators), gens[node`Image`GenMap]);
    
    vprintf CompositionTree, 3 : "Image relators: %o, depth %o\n",
	#relatorSLPs, node`Depth;
    
    //assert Universe(kernelGens) eq Generic(node`Group);
    kernelSLPs cat:= relatorSLPs;
    kernelGens cat:= node`ActionMaps`ToKernelBatch(Evaluate(relatorSLPs,
	UserGenerators(node`EvalGroup)));
    
    vprint CompositionTree, 3 : "Image elements found, depth", node`Depth;
    
    // Normal closure of this is the kernel
    node`Kernel`InputGens := ChangeUniverse(kernelGens,
	Generic(Universe(kernelGens)));

    // Remove multiple generators in perm groups
    // Important in order to keep number of generators small
    node`Kernel`Group := sub<Universe(node`Kernel`InputGens) |
	{@ g : g in node`Kernel`InputGens | g ne
    Identity(Universe(node`Kernel`InputGens)) @}>;
    node`KernelSLPs := kernelSLPs;
    
    // Book-keeping how generators were mapped into kernel
    node`Kernel`GenMap := [Index(node`Kernel`InputGens, g) :
	g in UserGenerators(node`Kernel`Group)];

    if not IsTrivial(node`Kernel`Group) then
	vprint CompositionTree, 3 :
	    "Normal kernel generators found, obtain closure, depth",
	    node`Depth;

	preImageKernel := sub<Generic(node`EvalGroup) | node`ActionMaps`
	    FromKernelBatch(UserGenerators(node`Kernel`Group))>;
	assert NumberOfGenerators(preImageKernel) eq
	    NumberOfGenerators(node`Kernel`Group);

	// Now take Monte Carlo normal closure
	kernelClosure, node`KernelSLPs :=
	    NormalClosureMonteCarlo(node`EvalGroup, preImageKernel,
	    UserGenerators(node`WordGroup), kernelSLPs[node`Kernel`GenMap] :
	    SubgroupChainLength := node`Kernel`SubgroupChainLength);

	vprint CompositionTree, 3 : "Normal closure found, depth", node`Depth;
	
	elts := UserGenerators(kernelClosure);
	images, scalars := node`ActionMaps`Batch(elts);
	
	node`Kernel`InputGens := ChangeUniverse(node`ActionMaps`
	    ToKernelBatch([elts[i] * scalars[i] : i in [1 .. #elts]]),
	    Generic(node`Kernel`Group));
	assert #node`Kernel`InputGens eq #node`KernelSLPs;

	node`Kernel`Group := sub<Generic(node`Kernel`Group) |
	    node`Kernel`InputGens>;
	assert Universe(node`Kernel`InputGens) eq Generic(node`Kernel`Group);

	// Book-keeping how generators were mapped into kernel
	node`Kernel`GenMap := [Index(node`Kernel`InputGens, g) :
	    g in UserGenerators(node`Kernel`Group)];
	assert forall{i : i in node`Kernel`GenMap | i gt 0};
    end if;
end procedure;

// In some reductions, we know what the kernel is, or an initial good guess
procedure SetupKnownKernel(~node, kernelGens, kernelSLPs, isSafe)
    node`Kernel`InputGens := kernelGens;
    
    node`Kernel`Group :=
	sub<Generic(Universe(node`Kernel`InputGens)) | node`Kernel`InputGens>;
    node`KernelSLPs := kernelSLPs;

    // Book-keeping how generators were mapped into kernel
    node`Kernel`GenMap := [Index(node`Kernel`InputGens, g) :
	g in UserGenerators(node`Kernel`Group)];

    // In this case we may inherit safety
    node`Kernel`Safe := isSafe;
    node`KnownKernel := true;
end procedure;

// Image is ok, setup kernel before recognition
// Also call if more generators are needed in an unsafe kernel, due to crisis
procedure SetupKernel(~node)
    
    // Sometimes we know kernel already
    if not assigned node`Kernel`Group then
	node`KernelSLPs := [];
	node`Kernel`InputGens := [];
	
	// Has image been verified with a presentation?
	if (node`Image`FastVerify or assigned node`Image`PresentationData) and
	    node`PresentationKernel then
	    // Find kernel using presentation and normal closure
	    vprint CompositionTree, 3 :
		"Find kernel using presentation, depth", node`Depth;

	    // Do not find presentation again
	    if not assigned node`Image`PresentationData then
		node`Image`FindPresentation(~node`Image);
	    end if;
	    PresentationKernel(~node);
	else
	    // Monte-Carlo kernel
	    vprint CompositionTree, 3 :
		"Find kernel using random elements, depth", node`Depth;

	    assert assigned node`KernelBatchSize;
	    // Important to involve number of generators in the first step
	    MonteCarloKernel(~node, node`KernelBatchSize(node`Group));
	end if;
    else
	if not node`KnownKernel then
	    // We must have had a crisis, add more generators
	    
	    vprint CompositionTree, 3 : "Add more elements to kernel";
	    MonteCarloKernel(~node, NumberOfGenerators(node`Kernel`Group));
	end if;
    end if;
	
    vprint CompositionTree, 3 : "Check mandarins in kernel";    
    if node`MandarinVerify then
	if not assigned node`Kernel`Mandarins then
	    SetKernelMandarins(~node);
	end if;
    else
	node`Kernel`Mandarins := [];
    end if;

    node`Kernel`WordGroup := WordGroup(node`Kernel`Group);
    node`Kernel`MandarinVerify := node`MandarinVerify;
    node`Kernel`Number := MaxNodeNumber(node`Image) + 1;
	
    vprint CompositionTree, 3 : "Setup kernel random process";
    vprint CompositionTree, 3 : "Number of kernel gens",
	NumberOfGenerators(node`Kernel`Group);
    
    // In almost simple case we already got the random process
    if not assigned node`Kernel`RandomProcess then
	InitialiseRandomProcess(~node`Kernel);
    end if;

    node`Kernel`EvalGroup := node`Kernel`Group;

    vprint CompositionTree, 3 : "Kernel setup completed";
end procedure;
