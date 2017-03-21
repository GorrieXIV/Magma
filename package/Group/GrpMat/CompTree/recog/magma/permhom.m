/******************************************************************************
 *
 *    permhom.m  Composition Tree Action Wrappers
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 2133                                           $:
 *    Date      : $Date:: 2011-02-08 14:17:48 +1100 (Tue, 08 Feb 2011)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: permhom.m 2133 2011-02-08 03:17:48Z eobr007                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

forward PreservesOrbit, PreservesBlocks;

import "recog.m" : ActionMapsInfo, NodeTypes, LeafInfo;
import "node.m" : ONanScottAlgorithms;
import "c9.m" : AlmostSimpleCheck;
import "mathom.m" : ReductionWithScalar;
import "kernel.m" : SetupKnownKernel;

// Store a type for each class
ONanScottErrorTypes := recformat<
    transitive : MonStgElt,
    imprimitive : MonStgElt,
    altnat : MonStgElt,
    jellyfish : MonStgElt>;

ONanScottErrors := rec<ONanScottErrorTypes |
    transitive := "transitive",
    imprimitive := "imprimitive",
    altnat := "alternating group natural representation",
    jellyfish := "jellyfish">;

// Error object in exceptions
ONanScottError := recformat<
    Category : MonStgElt, // One of the ONanScottErrors
    Error : Any>;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function TransitiveCheck(node)
    try
	return not IsTransitive(node`Group), _;
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`transitive, Error := err>);
    end try;
end function;

procedure TransitiveHom(~node, data)
    try    
	maxMoved := Max(Support(node`Group));
        orbit := Orbit(node`Group, maxMoved);
	outsideOrbit := GSet(node`Group) diff orbit;

	// Take inverse?
	conj := Generic(node`Group) ! (IndexedSetToSequence(orbit) cat
	    IndexedSetToSequence(outsideOrbit));

	reduction := hom<node`Group -> Sym(#orbit) |
	g :-> Sym(#orbit) ! (ElementToSequence(g^(conj^(-1)))[1 .. #orbit])>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;

	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    Test := func<g | PreservesOrbit(orbit, g)>,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    BatchTest := func<seq | forall{g : g in seq |
	    PreservesOrbit(orbit, g)}>>;

	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	node`Kernel`Scalar := node`Scalar;
	
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Sym(#orbit));
	node`Image`Group := sub<Sym(#orbit) | node`Image`InputGens>;

	node`CBM := func<node | Identity(node`Group)>;

	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	node`Kernel`Scalar := node`Scalar;	
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`transitive, Error := err>);
    end try;
end procedure;

function ImprimitiveCheck(node)
    try
	// Group must act transitively
        if node`HomFinderStamps[ONanScottAlgorithms`transitive]`negative
	    eq 0 then
	    return "N/A", _;
	end if;

	return not IsPrimitive(node`Group), _;
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`imprimitive, Error := err>);
    end try;
end function;

// redefine blocks action to avoid magma computing BSGS for perm group G 
MyBlocksAction := function (G, blocks)
    H := Generic (G);
    I := Sym (#blocks);
    return hom<H -> I | g :-> [Position (blocks, b^g): b in blocks]>;
end function;

procedure ImprimitiveHom(~node, data)
    try
	// Take a maximal block partition
	blocks := MaximalPartition(node`Group);

	// Find image and reduction, Magma does not use BSGS for this
	// But a BSGS is computed when reduction is used!
        // to avoid this, we redefine BlocksAction 
	// action := BlocksAction(node`Group, blocks);
	action := MyBlocksAction(node`Group, blocks);
	image := BlocksImage(node`Group, blocks);
	reduction := hom<node`Group -> image | g :-> action(g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    Test := func<g | PreservesBlocks(blocks, g)>,
	    BatchTest := func<seq | forall{g : g in seq |
	    PreservesBlocks(blocks, g)}>>;

	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	node`Kernel`Scalar := node`Scalar;
	
	node`Image`Group := image;
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(node`Image`Group));
	assert UserGenerators(image) eq node`Image`InputGens;

	node`CBM := func<node | Identity(node`Group)>;
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`imprimitive, Error := err>);
    end try;
end procedure;

function AltNatCheck(node)
    try
	return IsAlternating(node`Group), _;
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`altnat, Error := err>);
    end try;
end function;

procedure AltNatHom(~node, data)
    try
	// We want to name the group if is is a simple alternating group
	flag, names := AlmostSimpleCheck(node);
	if flag then
	    if #names[1] gt 1 then
		error Error(rec<ONanScottError | Category :=
		    ONanScottError`altnat,
		    Error := "Multiple names not supported">);	
	    end if;

	    // Fetch name
	    name := names[1][1];

	    vprint CompositionTree, 7 : "Alt name:", name;

	    C := cop<Strings(), Integers(), Booleans()>;
	    
	    node`LeafData := rec<LeafInfo | Family := C ! name[1],
		DefiningField := C ! name[3], LieRank := name[2],
		Name := name>;
	end if;

	// Deal with the node later
	node`Type := NodeTypes`leaf;    
    catch err;
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`altnat, Error := err>);        
    end try;	
end procedure;

function JellyfishCheck(node)
    try
	vprint CompositionTree, 8 : "Entering JellyfishConstruction";
	flag := JellyfishConstruction(node`Group);
	vprint CompositionTree, 8 : "JellyfishConstruction finished";
	return flag, _;
    catch err
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`jellyfish, Error := err>);
    end try;
end function;

procedure JellyfishHom(~node, data)
    try
	image := JellyfishImage(node`Group);
        reduction := hom<node`Group -> image | g :->
	JellyfishImage(node`Group, g)>;
	reductionScalar := func<g | Function(reduction)(g),
	    Identity(node`Group), Identity(node`Group)>;
	
	// Store ActionMaps
	node`ActionMaps := rec<ActionMapsInfo |
	    Single := reduction,
	    Scalar := reductionScalar,
	    Batch := func<seq | ReductionWithScalar(reductionScalar, seq)>,
	    ToKernelBatch := func<seq | seq>,
	    FromKernelBatch := func<seq | seq>,
	    Test := func<g | true>,
	    BatchTest := func<seq | forall{g : g in seq | true}>>;

	node`Image`Scalar := Function(node`ActionMaps`Single)(node`Scalar);
	node`Kernel`Scalar := node`Scalar;

	// No kernel since faithful representation
	SetupKnownKernel(~node, [Generic(node`Group) | ], [], node`Safe);
	
	node`Image`Group := image;
	node`Image`InputGens :=
	    ChangeUniverse(node`ActionMaps`Batch(UserGenerators(node`Group)),
	    Generic(node`Image`Group));
	assert UserGenerators(image) eq node`Image`InputGens;

	node`CBM := func<node | Identity(node`Group)>;
    catch err;
	error Error(rec<ONanScottError |
	Category := ONanScottErrors`jellyfish, Error := err>);        
    end try;	
end procedure;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function PreservesOrbit(orbit, g)
    return orbit^g eq orbit;
end function;

function PreservesBlocks(blocks, g)
    return {Index(blocks, B^g) : B in blocks} eq {1 .. #blocks};
end function;
