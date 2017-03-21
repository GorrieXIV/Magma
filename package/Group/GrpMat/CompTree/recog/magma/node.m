/******************************************************************************
 *
 *    node.m   Composition Tree Node
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: node.m 3165 2016-03-05 17:48:46Z jbaa004                       $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "mathom.m" : BlockCheck, BlockHom, AbsoluteReducibleCheck,
    AbsoluteReducibleHom, ImprimitivityCheck, ImprimitivityHom,
    SemilinearCheck, SemilinearHom, SmallerFieldCheck, SmallerFieldHom,
    TensorCheck, TensorHom, TensorInducedCheck, TensorInducedHom,
    ExtraSpecialCheck, ExtraSpecialHom, SummandCheck, SummandHom,
    RemoveOpHom, RemoveOpCheck, InitialCBMCheck, InitialCBMHom,
    TrivialCheck, TrivialHom, ProjectiveSmallerFieldCheck,
    ProjectiveSmallerFieldHom;
import "c8.m" : ClassicalCheck, ClassicalHom, FormActionCheck, FormActionHom,
    SpinorNormCheck, SpinorNormHom, DeterminantCheck, DeterminantHom;
import "c9.m" : AlmostSimpleCheck, AlmostSimpleHom;
import "permhom.m" : TransitiveCheck, TransitiveHom,
    ImprimitiveCheck, ImprimitiveHom, AltNatCheck, AltNatHom,
    JellyfishCheck, JellyfishHom;
import "recog.m" : SLPMapsInfo, LeafInfo, NiceInfo, CTNodeInfo,
    NodeTypes, PresentationInfo, RecogError, FactorInfo, ModuleInfo;
import "kernel.m" : SetupKernel, MandarinVerification, ObtainKernelElements, SetKernelBatchSize;
import "leaf.m" : RecogniseLeaf;
import "unipotent.m" : UnipotentCheck, UnipotentHomLayer, UnipotentHomDiagonal;

forward RecogniseNode;

// Stores the algorithms that test for a hom, and stores the hom
HomFindInfo := recformat<
    // Takes node as input
    // Test if hom exists, returns BoolElt and optional extra value
    FindHom : UserProgram,
    // Takes node and extra value from FindHom
    // Must set node`ActionMaps, node`Image`Group, node`Image`InputGens
    // May also set node`Kernel`Group, node`Kernel`InputGens
    CreateHom : UserProgram,
    Description : MonStgElt>;

// Stores information about number of calls to each hom finder
HomFindStamp := recformat<
    positive : RngIntElt,
    negative : RngIntElt,
    failure : RngIntElt,
    NA : RngIntElt>;

AschbacherAlgorithmsInfo := recformat<
    trivial : RngIntElt,
    unipotent : RngIntElt,
    initcbm : RngIntElt,
    removeop : RngIntElt,
    summand : RngIntElt,
    block : RngIntElt,
    absreducible : RngIntElt,
    projsmallerfield : RngIntElt,
    smallerfield : RngIntElt,
    semilinear : RngIntElt,
    extraspecial : RngIntElt,
    imprimitive : RngIntElt,
    tensor : RngIntElt,
    induced : RngIntElt,
    determinant : RngIntElt,
    formaction : RngIntElt,
    spinornorm : RngIntElt,
    classical : RngIntElt,
    almostsimple : RngIntElt>;

AschbacherAlgorithms := rec<AschbacherAlgorithmsInfo |
    trivial := 1,
    unipotent := 2,
    initcbm := 3,
    removeop := 4,
    summand := 5,
    block := 6,
    absreducible := 7,
    projsmallerfield := 8,
    smallerfield := 9,
    semilinear := 10,
    imprimitive := 11,
    extraspecial := 12,
    tensor := 13,
    induced := 14,
    determinant := 15,
    formaction := 16,
    spinornorm := 17,
    classical := 18,
    almostsimple := 19>;

// Priorities of the Aschbacher algorithms
AschbacherPriorities := [0 : i in [1 .. #Names(AschbacherAlgorithms)]];
AschbacherPriorities[AschbacherAlgorithms`trivial] := 1000;
AschbacherPriorities[AschbacherAlgorithms`unipotent] := 990;
AschbacherPriorities[AschbacherAlgorithms`initcbm] := 980;
AschbacherPriorities[AschbacherAlgorithms`removeop] := 970;
AschbacherPriorities[AschbacherAlgorithms`summand] := 960;
AschbacherPriorities[AschbacherAlgorithms`block] := 950;
AschbacherPriorities[AschbacherAlgorithms`absreducible] := 940;
AschbacherPriorities[AschbacherAlgorithms`projsmallerfield] := 930;
AschbacherPriorities[AschbacherAlgorithms`smallerfield] := 920;
AschbacherPriorities[AschbacherAlgorithms`semilinear] := 910;
AschbacherPriorities[AschbacherAlgorithms`imprimitive] := 900;
AschbacherPriorities[AschbacherAlgorithms`extraspecial] := 890;
AschbacherPriorities[AschbacherAlgorithms`tensor] := 880;
AschbacherPriorities[AschbacherAlgorithms`induced] := 870;
AschbacherPriorities[AschbacherAlgorithms`determinant] := 860;
AschbacherPriorities[AschbacherAlgorithms`formaction] := 850;
AschbacherPriorities[AschbacherAlgorithms`spinornorm] := 840;
AschbacherPriorities[AschbacherAlgorithms`classical] := 830;
AschbacherPriorities[AschbacherAlgorithms`almostsimple] := 800;

// Ranks of the Aschbacher algorithms
ONanScottAlgorithmInfo := recformat<
    trivial : RngIntElt,
    transitive : RngIntElt,
    imprimitive : RngIntElt,
    altnat : RngIntElt,
    jellyfish : RngIntElt,
    almostsimple : RngIntElt>;

ONanScottAlgorithms := rec<ONanScottAlgorithmInfo |
    trivial := 1,
    transitive := 2,
    imprimitive := 3,
    altnat := 4,
    jellyfish := 5,
    almostsimple := 6>;

ONanScottPriorities := [0 : i in [1 .. #Names(ONanScottAlgorithms)]];
ONanScottPriorities[ONanScottAlgorithms`trivial] := 1000;
ONanScottPriorities[ONanScottAlgorithms`transitive] := 900;
ONanScottPriorities[ONanScottAlgorithms`imprimitive] := 800;
ONanScottPriorities[ONanScottAlgorithms`altnat] := 700;
ONanScottPriorities[ONanScottAlgorithms`jellyfish] := 650;
ONanScottPriorities[ONanScottAlgorithms`almostsimple] := 600;

// An error during the Hom finder process
HomFinderError := recformat<
    Description : MonStgElt, 
    Error : Any>;

// Error that indicates a verification failure
VerifyError := recformat<
    Description : MonStgElt, 
    Depth : RngIntElt>;

// Database of matrix group homomorphism finders
AschbacherLibrary := AssociativeArray();

AschbacherLibrary[AschbacherAlgorithms`determinant] := rec<HomFindInfo |
    FindHom := DeterminantCheck, CreateHom := DeterminantHom,
    Description := "Determinant test">;

AschbacherLibrary[AschbacherAlgorithms`unipotent] := rec<HomFindInfo |
    FindHom := UnipotentCheck, CreateHom := UnipotentHomDiagonal,
    Description := "Unipotent test">;

AschbacherLibrary[AschbacherAlgorithms`initcbm] := rec<HomFindInfo |
    FindHom := InitialCBMCheck, CreateHom := InitialCBMHom,
    Description := "Initial MeatAxe change of basis">;

AschbacherLibrary[AschbacherAlgorithms`removeop] := rec<HomFindInfo |
    FindHom := RemoveOpCheck, CreateHom := RemoveOpHom,
    Description := "Remove O_p">;

AschbacherLibrary[AschbacherAlgorithms`summand] := rec<HomFindInfo |
    FindHom := SummandCheck, CreateHom := SummandHom,
    Description := "Map to module direct summand">;

AschbacherLibrary[AschbacherAlgorithms`block] := rec<HomFindInfo |
    FindHom := BlockCheck, CreateHom := BlockHom,
    Description := "Map to module composition factor">;

AschbacherLibrary[AschbacherAlgorithms`absreducible] := rec<HomFindInfo |
    FindHom := AbsoluteReducibleCheck, CreateHom := AbsoluteReducibleHom,
    Description := "Absolute reducibility test">;

AschbacherLibrary[AschbacherAlgorithms`semilinear] := rec<HomFindInfo |
    FindHom := SemilinearCheck, CreateHom := SemilinearHom,
    Description := "Semilinearity test">;

AschbacherLibrary[AschbacherAlgorithms`imprimitive] := rec<HomFindInfo |
    FindHom := ImprimitivityCheck, CreateHom := ImprimitivityHom,
    Description := "Imprimitivity test">;

AschbacherLibrary[AschbacherAlgorithms`smallerfield] := rec<HomFindInfo |
    FindHom := SmallerFieldCheck, CreateHom := SmallerFieldHom,
    Description := "Smaller field test">;

AschbacherLibrary[AschbacherAlgorithms`projsmallerfield] := rec<HomFindInfo |
    FindHom := ProjectiveSmallerFieldCheck,
    CreateHom := ProjectiveSmallerFieldHom,
    Description := "Smaller field modulo scalars test">;

AschbacherLibrary[AschbacherAlgorithms`tensor] := rec<HomFindInfo |
    FindHom := TensorCheck, CreateHom := TensorHom,
    Description := "Tensor product test">;

AschbacherLibrary[AschbacherAlgorithms`induced] := rec<HomFindInfo |
    FindHom := TensorInducedCheck, CreateHom := TensorInducedHom,
    Description := "Tensor induction test">;

AschbacherLibrary[AschbacherAlgorithms`extraspecial] := rec<HomFindInfo |
    FindHom := ExtraSpecialCheck, CreateHom := ExtraSpecialHom,
    Description := "Extra-special normaliser test">;

AschbacherLibrary[AschbacherAlgorithms`almostsimple] := rec<HomFindInfo |
    FindHom := AlmostSimpleCheck, CreateHom := AlmostSimpleHom,
    Description := "Almost simple test">;

AschbacherLibrary[AschbacherAlgorithms`trivial] := rec<HomFindInfo |
    FindHom := TrivialCheck, CreateHom := TrivialHom,
    Description := "Trivial group test">;
AschbacherLibrary[AschbacherAlgorithms`classical] := rec<HomFindInfo |
    FindHom := ClassicalCheck, CreateHom := ClassicalHom,
    Description := "Classical group natural representation test">;

AschbacherLibrary[AschbacherAlgorithms`formaction] := rec<HomFindInfo |
    FindHom := FormActionCheck, CreateHom := FormActionHom,
    Description := "Action on a classical form">;

AschbacherLibrary[AschbacherAlgorithms`spinornorm] := rec<HomFindInfo |
    FindHom := SpinorNormCheck, CreateHom := SpinorNormHom,
    Description := "Spinor norm test">;


// Database of perm group homomorphism finders
ONanScottLibrary := AssociativeArray();

ONanScottLibrary[ONanScottAlgorithms`trivial] := rec<HomFindInfo |
    FindHom := TrivialCheck, CreateHom := TrivialHom,
    Description := "Trivial group test">;

ONanScottLibrary[ONanScottAlgorithms`transitive] := rec<HomFindInfo |
    FindHom := TransitiveCheck, CreateHom := TransitiveHom,
    Description := "Transitivity test">;

ONanScottLibrary[ONanScottAlgorithms`imprimitive] := rec<HomFindInfo |
    FindHom := ImprimitiveCheck, CreateHom := ImprimitiveHom,
    Description := "Imprimitivity test">;

ONanScottLibrary[ONanScottAlgorithms`almostsimple] := rec<HomFindInfo |
    FindHom := AlmostSimpleCheck, CreateHom := AlmostSimpleHom,
    Description := "Almost simple test">;

ONanScottLibrary[ONanScottAlgorithms`altnat] := rec<HomFindInfo |
    FindHom := AltNatCheck, CreateHom := AltNatHom,
    Description := "Alternating group natural representation test">;

ONanScottLibrary[ONanScottAlgorithms`jellyfish] := rec<HomFindInfo |
    FindHom := JellyfishCheck, CreateHom := JellyfishHom,
    Description := "Jellyfish test">;

// Pointers to databases
HomFinderLibraries := AssociativeArray();
HomFinderLibraries[GrpMat]  := AschbacherLibrary;
HomFinderLibraries[GrpPerm] := ONanScottLibrary;

HomFinderPriorities := AssociativeArray();
HomFinderPriorities[GrpMat]  := AschbacherPriorities;
HomFinderPriorities[GrpPerm] := ONanScottPriorities;

// Empty libraries for abelian and PC groups, treat as leaves!
HomFinderLibraries[GrpPC]  := AschbacherLibrary;
HomFinderLibraries[GrpAb]  := AschbacherLibrary;
HomFinderPriorities[GrpPC]  := [0 : i in [1 .. #Names(AschbacherAlgorithms)]];
HomFinderPriorities[GrpAb] := [0 : i in [1 .. #Names(AschbacherAlgorithms)]];

// Presentations are always found for small groups that we can handle easily
MaxVerifyOrder := AssociativeArray();
MaxVerifyOrder[GrpPC]  := 2^30;
MaxVerifyOrder[GrpAb]  := 2^30;

// Presentations are always found for small groups
MaxVerifyDegree := AssociativeArray();
MaxVerifyDegree[GrpPerm] := 5;
MaxVerifyDegree[GrpMat]  := 0;

// Error strings in try-catch
ERROR_CRISIS      := "RecogCrisis";
ERROR_MEMBERSHIP  := "MembershipError";
ERROR_RECOGNITION := "RecognitionError";
ERROR_VERIFY      := "VerifyError";
ERROR_RYBA        := "RybaError";

ERROR_CATCH_PREFIX := ""; 

ERROR_CRISIS_CATCH      := ERROR_CATCH_PREFIX cat ERROR_CRISIS;
ERROR_MEMBERSHIP_CATCH  := ERROR_CATCH_PREFIX cat ERROR_MEMBERSHIP;
ERROR_RECOGNITION_CATCH := ERROR_CATCH_PREFIX cat ERROR_RECOGNITION;
ERROR_VERIFY_CATCH      := ERROR_CATCH_PREFIX cat ERROR_VERIFY;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

// Test if we should always find a presentation for the node
function IsNodeVerifiable(node)    
    return (IsDefined(MaxVerifyOrder, Category(node`Group)) and
	MaxVerifyOrder[Category(node`Group)] gt Order(node`Group)) or
	(IsDefined(MaxVerifyDegree, Category(node`Group)) and
	MaxVerifyDegree[Category(node`Group)] ge Degree(node`Group));
end function;

procedure InitHomFinderStamps(~node, indices)
    // Initialise stamps and temporary data
    node`HomFinderStamps := AssociativeArray();
    for i in [1 .. #indices] do
	node`HomFinderStamps[i] := rec<HomFindStamp |
	    positive := 0, negative := 0, failure := 0, NA := 0>;
    end for;
end procedure;

// General homomorphism finding routine
procedure FindReduction(~node)
    try
	// Use user defined hom finder library if available
	if assigned node`HomFinderPriorities then
	    priorities := node`HomFinderPriorities;
	else
	    flag, priorities := IsDefined(HomFinderPriorities,
		Category(node`Group));
	    if not flag then
		error Error(rec<HomFinderError |
		    Description := "Unknown group type",
		    Error := Category(node`Group)>);
	    end if;
	end if;
	
	flag, database := IsDefined(HomFinderLibraries,
	    Category(node`Group));
	if not flag then
	    error Error(rec<HomFinderError |
		Description := "Unknown group type",
		Error := Category(node`Group)>);
	end if;
		
	S := Sym(#priorities);
	perm := S ! 1;
	
	sortedprios := priorities;
	// Sort priorities descending
	Sort(~sortedprios, func<x, y | y - x>, ~perm);
	indices := PermuteSequence([1 .. #priorities], perm);
	
	InitHomFinderStamps(~node, indices);
	
	// Read database
	repeat
	    for algNr in indices do
		// Non-positive prio algorithms always fail
		if priorities[algNr] le 0 then
		    node`HomFinderStamps[algNr]`negative := 1;
		end if;
		
		// Skip algorithms that have returned false
		if node`HomFinderStamps[algNr]`negative eq 0 then
		    vprint CompositionTree, 2 : "Trying Hom-finder:",
			database[algNr]`Description;

		    // Check for a homomorphism
		    foundHom, data :=
			database[algNr]`FindHom(node);

		    // Stop if a hom was found
		    if foundHom cmpeq true then
			node`HomFinderStamps[algNr]`positive +:= 1;
			
			vprint CompositionTree, 1 :
			    "Hom-finder ok, setting up maps:",
			    database[algNr]`Description;

			// Setup the action maps for this homomorphism
			if assigned data then
			    database[algNr]`CreateHom(~node, data);
			else
			    database[algNr]`CreateHom(~node, []);
			end if;

			// Store description of algorithm used
			if node`Type eq NodeTypes`internal then
			    assert assigned node`ActionMaps; 
			    node`ActionMaps`Description :=
				database[algNr]`Description;
			end if;
			
			break;
		    end if;

		    // Record result
		    if foundHom cmpeq false then
			node`HomFinderStamps[algNr]`negative +:= 1;
			break;
		    elif foundHom cmpeq "fail" then
			node`HomFinderStamps[algNr]`failure +:= 1;

			// After a number of failures we give up
			if node`HomFinderStamps[algNr]`failure ge
			    node`MaxHomFinderFails then
			    node`HomFinderStamps[algNr]`negative +:= 1;
			end if;
			
			break;
		    else
			node`HomFinderStamps[algNr]`NA +:= 1;
			
			// After a number of failures we give up
			if node`HomFinderStamps[algNr]`NA ge
			    node`MaxHomFinderFails then
			    node`HomFinderStamps[algNr]`negative +:= 1;
			    break;
			end if;
			
		    end if;
		end if;
	    end for;

	    // Go on until we find something or everything has failed
	until exists{i : i in [1 .. #priorities] |
	    node`HomFinderStamps[i]`positive gt 0} or
	    forall{i : i in [1 .. #priorities] |
	    node`HomFinderStamps[i]`negative gt 0};

	// No Hom-finder succeeded, assume node is a leaf
	if forall{i : i in [1 .. #priorities] |
	    node`HomFinderStamps[i]`negative gt 0} then
	    node`Type := NodeTypes`leaf;
	end if;
    catch err
	error Error(rec<HomFinderError | Description := "Error in HomFinder",
	Error := err>);
    end try;
end procedure;

procedure InitialiseRandomProcess(~node)
    node`RandomProcess :=
        RandomProcessWithWords(node`Group :
        Generators := [node`Group.i : i in [1..NumberOfGenerators (node`Group)]],
	WordGroup := node`WordGroup);
    if IsIdentity(node`Scalar) then
	node`Randomiser := func< | Random(node`RandomProcess)>;
    else
	if Category(node`Group) eq GrpAb then
	    G := node`Group + node`ScalarGroup;
	else
	    G := sub<Generic(node`Group) | node`Group, node`Scalar>;
	end if;
	
	R := RandomProcessWithWords(G);
	phi := hom<WordGroup(R) -> node`WordGroup |
	Append(UserGenerators(node`WordGroup), Identity(node`WordGroup))>;
	node`Randomiser := func< | g, phi(w) where g, w is Random(R)>;
    end if;
end procedure;

// Image found, setup image before recognition
procedure SetupImage(~node)
    node`Image`WordGroup := WordGroup(node`Image`Group);
    assert NumberOfGenerators(node`Image`WordGroup) eq
	NumberOfGenerators(node`Image`Group);
    node`Image`MandarinVerify := node`MandarinVerify;
    
    vprint CompositionTree, 3 :
	"Check that mandarins satisfy reduction, depth", node`Depth;
    if node`MandarinVerify then	
	if not node`ActionMaps`BatchTest(node`Mandarins) then
	    error ERROR_CRISIS;
	end if;

	vprintf CompositionTree, 3 :
	    "Obtain image of %o mandarins, depth %o\n",
	    #node`Mandarins, node`Depth;
	// Obtain mandarins for image
	node`Image`Mandarins, node`MandarinScalars :=
	    node`ActionMaps`Batch(node`Mandarins);
    else
	node`Image`Mandarins := [];
	node`Image`MandarinScalars := [];
    end if;
    
    vprint CompositionTree, 3 :
	"Start random process in image, depth", node`Depth;    

    InitialiseRandomProcess(~node`Image);
    
    // Images always inherit safety
    node`Image`Safe := node`Safe;

    // Book-keeping how generators were mapped into image
    node`Image`GenMap := [Index(node`Image`InputGens, g) : g in
	UserGenerators(node`Image`Group)];
    assert forall{x : x in node`Image`GenMap | x ne 0};
    
    vprint CompositionTree, 8 :
	"Check if node should be verified, depth", node`Depth;

    // Always verify easy images
    node`Image`Verify := IsNodeVerifiable(node`Image) or node`Verify;

    if not assigned node`Image`EvalGroup then
	node`Image`EvalGroup := node`Image`Group;
    end if;
    
    vprint CompositionTree, 3 :
	"Image setup completed, depth", node`Depth;
end procedure;

// Set node`FactorData using data from image and kernel
procedure SetupFactorData(~node)
    assert assigned node`Kernel`FactorData;
    assert assigned node`Image`FactorData;

    // Obtain SLPs of image and kernel factors
    imageFactorSLPs := [node`NiceData`FromImageNice(slps) : slps in
	node`Image`FactorData`FactorSLPs];
    kernelFactorSLPs := [node`NiceData`FromKernelNice(slps) : slps in
	node`Kernel`FactorData`FactorSLPs];
    
    // No need to evaluate SLPs in each node
    
    image := function(toFactor, g)
        h := node`ActionMaps`Batch([g])[1];
	return Function(toFactor)(h);
    end function;

    // Add image projection to all image maps
    imageMaps := [* hom<node`NiceData`Group -> Codomain(imageMap) |
    g :-> image(imageMap, g)> :
	imageMap in node`Image`FactorData`ToFactor *];
    
    kernel := function(toFactor, g, node, scalar)
	s1, s2 := node`ActionMaps`Scalar(g);
	h := node`ActionMaps`ToKernelBatch([g * s2])[1];
	return Function(toFactor)(h);
    end function;

    // Change domains of kernel maps
    kernelMaps := [* hom<node`NiceData`Group -> Codomain(kernelMap) |
    g :-> kernel(kernelMap, g, node, node`Scalar)> :
	kernelMap in node`Kernel`FactorData`ToFactor *];
    
    node`FactorData := rec<FactorInfo |
	FactorSLPs := kernelFactorSLPs cat imageFactorSLPs,
	ToFactor := kernelMaps cat imageMaps,
	FactorToSLP := node`Kernel`FactorData`FactorToSLP cat
	node`Image`FactorData`FactorToSLP,
	Refined := node`Image`FactorData`Refined and
	node`Kernel`FactorData`Refined,
	FactorLeaves := node`Kernel`FactorData`FactorLeaves cat
	node`Image`FactorData`FactorLeaves>;
end procedure;


// Set node`NiceData using data from image and kernel
procedure SetupNiceData(~node)
    assert assigned node`Kernel`NiceData;
    assert assigned node`Image`NiceData;
    
    nodeSLPs := UserGenerators(node`WordGroup);

    // SLPs of image nice gens in node user gens
    imageSLPs := Evaluate(node`Image`NiceData`NiceSLPs,
	nodeSLPs[node`Image`GenMap]);

    assert #imageSLPs eq NumberOfGenerators(node`Image`NiceData`Group) or
	#imageSLPs eq NumberOfGenerators(node`Image`NiceData`Group) + 1;
    
    // Image part of node nice gens
    // These should not contain repeats and identities    
    niceFromImage := [Generic(node`Group) | g : g in
	Evaluate(imageSLPs, UserGenerators(node`EvalGroup))];
    niceImageGroupGens := {@ Generic(node`Group) | g :
	g in niceFromImage | not IsIdentity(g) @};
    
    // Check for trivial kernel
    if #node`Kernel`NiceData`NiceSLPs gt 0 then
	// SLPs of kernel nice gens in node user gens
	kernelSLPs := Evaluate(node`Kernel`NiceData`NiceSLPs,
	    node`KernelSLPs[node`Kernel`GenMap]);

	// Kernel part of node nice gens
	// These may contain repeats and identities
	niceFromKernel := [Generic(node`Group) | g : g in
	    Evaluate(kernelSLPs, UserGenerators(node`EvalGroup))];
    else
	kernelSLPs := [];
	niceFromKernel := [];
    end if;
    assert #node`Kernel`NiceData`NiceSLPs eq
	NumberOfGenerators(node`Kernel`NiceData`Group);
    assert #niceFromKernel eq NumberOfGenerators(node`Kernel`NiceData`Group);
    
    niceKernelGroupGens := {@ Generic(node`Group) | g :
	g in niceFromKernel | not IsIdentity(g) @};
    
    // Which kernel generators are used?
    niceKernelMap := [Index(niceFromKernel, g) : g in niceKernelGroupGens];

    // Which image generators are used?
    niceImageMap := [Index(niceFromImage, g) : g in niceImageGroupGens];
    
    // Obtain nice generators from image and kernel
    // This may remove further generators, if image and kernel generators
    // have non-trivial intersection
    niceInputGens := IndexedSetToSequence(niceKernelGroupGens) cat
	IndexedSetToSequence(niceImageGroupGens);
    niceSLPs := kernelSLPs[niceKernelMap] cat imageSLPs[niceImageMap];
    assert #niceSLPs eq #niceInputGens;
    
    niceGroup := sub<Generic(node`Group) | niceInputGens>;
    niceGenMap := [Index(niceInputGens, g) : g in UserGenerators(niceGroup)];

    // Some generators may have disappeared
    assert NumberOfGenerators(niceGroup) le
	#niceKernelGroupGens + #niceImageGroupGens;

    // Create node group on nice generators
    node`NiceData := rec<NiceInfo |
	Group := niceGroup,
	NiceSLPs := niceSLPs[niceGenMap]>;

    assert #node`NiceData`NiceSLPs eq NumberOfGenerators(node`NiceData`Group);
    
    node`NiceData`WordGroup := WordGroup(node`NiceData`Group);
    assert #node`NiceData`NiceSLPs eq
	NumberOfGenerators(node`NiceData`WordGroup);

    // Create coercions of SLPs in image nice gens and kernel nice gens
    // to node nice gens
    niceKernelMap := [Index(niceKernelGroupGens, g) : g in niceFromKernel];
    niceImageMap := [Index(niceImageGroupGens, g) : g in niceFromImage];
    niceGenMap := [Index(ChangeUniverse(UserGenerators(niceGroup),
	Generic(niceGroup)), g) : g in niceInputGens];

    niceKernelInvMap := func<i | niceKernelMap[i] gt 0 select
	niceGenMap[niceKernelMap[i]] else 0>;
    maxKernelGenIdx := (#niceKernelMap gt 0 and Max(niceKernelMap) gt 0) select 
	niceGenMap[Max(niceKernelMap)] else 0;
    niceImageInvMap := func<i | niceImageMap[i] gt 0 select
	niceGenMap[niceImageMap[i] + maxKernelGenIdx] else 0>;

    // Put nice generators from image and kernel at correct positions
    W := node`NiceData`WordGroup;
    if #kernelSLPs gt 0 then
	node`NiceData`FromKernelNice := func<seq | Evaluate(seq,
	    [W.j where j is niceKernelInvMap(i) : i in [1 .. #kernelSLPs]])>;
    else
	node`NiceData`FromKernelNice := func<seq | Evaluate(seq, [Identity(W) :
	    i in [1 .. NumberOfGenerators(W)]])>;
    end if;

    node`NiceData`FromImageNice := func<seq | Evaluate(seq,
	[W.j where j is niceImageInvMap(i) : i in [1 .. #imageSLPs]])>;
    node`NiceData`NiceToUserBatch :=
	func<seq | Evaluate(seq, node`NiceData`NiceSLPs)>;
    node`NiceData`NiceToUser :=
	hom<W -> node`WordGroup | node`NiceData`NiceSLPs>;
    
    node`Image`NiceData`ToParentNice := node`NiceData`FromImageNice;
    node`Kernel`NiceData`ToParentNice := node`NiceData`FromKernelNice;
end procedure;

// Express elts as SLPs in nice gens of node
function Rewriting(node, elts)
    // First do membership testing
    if not node`ActionMaps`BatchTest(elts) then
	error ERROR_CRISIS;
    end if;
    
    // Map elements to image
    images := node`ActionMaps`Batch(elts);
    
    // Recursively obtain SLPs in image (in NiceGroup gens)
    imageSLPs := node`Image`SLPMaps`EltToSLPBatch(images);
    
    // SLPs of preimages, in node`NiceGens
    preImagesSLPs := node`NiceData`FromImageNice(imageSLPs);
    assert NumberOfGenerators(Universe(preImagesSLPs)) eq
	NumberOfGenerators(node`NiceData`Group);
    
    preImages := ChangeUniverse(Evaluate(preImagesSLPs,
	UserGenerators(node`NiceData`Group)), Generic(node`NiceData`Group));
    assert #preImages eq #elts;
    
    kernelPreElts := [elts[i] / preImages[i] : i in [1 .. #elts]];
    _, scalars := node`ActionMaps`Batch(kernelPreElts);
    
    // Divide out to obtain elements in kernel
    kernelElts := node`ActionMaps`ToKernelBatch([(Generic(node`Group) !
	(kernelPreElts[i] * scalars[i])) : i in [1 .. #elts]]);

    vprint CompositionTree, 9 :
	"Rewrite elements in the kernel, depth ", node`Depth;
    
    // Recursively obtain SLPs in kernel (in NiceGroup gens)
    // (also verifies that the elements lie in the kernel)
    kernelSLPs := node`Kernel`SLPMaps`EltToSLPBatch(kernelElts);
    
    // SLPs of kernel elements, in NiceGens
    kernelNodeSLPs := node`NiceData`FromKernelNice(kernelSLPs);	
    assert #kernelNodeSLPs eq #elts;
    assert NumberOfGenerators(Parent(kernelNodeSLPs[1])) eq
	NumberOfGenerators(node`NiceData`Group);

    vprint CompositionTree, 9 :
	"Test that elements evaluate correctly, depth ", node`Depth;
    
    slps := [kernelNodeSLPs[i] * preImagesSLPs[i] : i in [1 .. #elts]];    
    return slps;
end function;

// Set SLPMaps using data from image and kernel
procedure SetupSLPMaps(~node)
    // Specialise rewriting function to this node
    rewriteBatch := func<seq | Rewriting(node, seq)>;
    evaluateBatch := func<seq | Evaluate(seq,
	UserGenerators(node`NiceData`Group))>;
    
    node`SLPMaps := rec<SLPMapsInfo |
	EltToSLPBatch := rewriteBatch,
	EltToSLP := hom<node`Group -> node`NiceData`WordGroup | g :->
    rewriteBatch([g])[1]>,
	SLPToEltBatch := evaluateBatch,
	SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
    UserGenerators(node`NiceData`Group)>>;
end procedure;

// Obtain a presentation on the nice generators, using image and kernel
procedure NicePresentation(~node)
    // Kernel and Image must have presentations already
    // These may not be set when called from kernel generation    
    vprint CompositionTree, 5 :
	"Obtain kernel presentation, depth", node`Depth;
    if not assigned node`Kernel`PresentationData then
	node`Kernel`FindPresentation(~node`Kernel);
    end if;
    
    vprint CompositionTree, 5 :
	"Obtain image presentation, depth", node`Depth;
    if not assigned node`Image`PresentationData then
	node`Image`FindPresentation(~node`Image);
    end if;
    
    assert assigned node`Image`PresentationData;
    assert assigned node`Kernel`PresentationData;
    assert assigned node`SLPMaps;
    
    vprint CompositionTree, 5 :
	"Obtain first relator set, depth", node`Depth;

    
    // Evaluate() doesn't work if the list is empty
    if #node`Image`PresentationData`SLPRelators gt 0 then
	// These should lie in the kernel
	imageRelElts := node`NiceData`FromImageNice(node`Image`
	    PresentationData`SLPRelators);
	elts := node`SLPMaps`SLPToEltBatch(imageRelElts);
	_, scalars := node`ActionMaps`Batch(elts);
	
	vprint CompositionTree, 6 :
	    "Obtain relator SLPs, depth", node`Depth;
	
	// Obtain SLPs in kernel generators of the image relator elements
	imageRelSLPs :=
	    node`NiceData`FromKernelNice(node`Kernel`SLPMaps`EltToSLPBatch(
	    node`ActionMaps`ToKernelBatch([elts[i] * scalars[i] :
	    i in [1 .. #elts]])));

	// Strange MAGMA bug, it sometimes removes [] if length is 1
	if Category(imageRelSLPs) ne SeqEnum then
	    imageRelSLPs := [imageRelSLPs];
	end if;

	// First relator set
	imageRels := [imageRelElts[i] * imageRelSLPs[i]^(-1) :
	    i in [1 .. #imageRelElts]];
    else
	imageRels := [];
    end if;

    vprint CompositionTree, 5 :
	"Obtain second relator set, depth", node`Depth;
    
    // Second relator set
    if #node`Kernel`PresentationData`SLPRelators gt 0 then
	kernelRels := node`NiceData`FromKernelNice(
	    node`Kernel`PresentationData`SLPRelators);
    else
	kernelRels := [];
    end if;
    
    // Conjugate kernel gens by image gens
    W := node`NiceData`WordGroup;
        
    conjugateSLPs := [W.i^W.j : i in
	[1 .. NumberOfGenerators(node`Kernel`NiceData`Group)], j in
	[NumberOfGenerators(node`Kernel`NiceData`Group) + 1 ..
	NumberOfGenerators(node`NiceData`Group)]];

    vprint CompositionTree, 5 :
	"Obtain third relator set, depth", node`Depth;

    if #conjugateSLPs gt 0 then	
	// The elements should lie in the kernel, obtain SLPs
	// First find scalars to put them in the kernel
	elts := node`SLPMaps`SLPToEltBatch(conjugateSLPs);
	_, scalars := node`ActionMaps`Batch(elts);
	
	conjugateRelSLPs :=
	    node`NiceData`FromKernelNice(node`Kernel`SLPMaps`EltToSLPBatch(
	    node`ActionMaps`ToKernelBatch([elts[i] * scalars[i] :
	    i in [1 .. #elts]])));
	
	// Third relator set
	conjugateRels := [conjugateSLPs[i] * conjugateRelSLPs[i]^(-1) :
	    i in [1 .. #conjugateSLPs]];
    else
	conjugateRels := [];
    end if;
    
    // Finally obtain presentation
    rels := imageRels cat kernelRels cat conjugateRels;
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := rels>;
end procedure;

// Create image node and set initial values 
procedure InitialiseImage(~node)
    // Type must not be set
    node`Image := rec<CTNodeInfo | Depth := node`Depth + 1, Parent := node,
	FastVerify := false, Number := node`Number + 1,
	Verify := node`Verify,
	MandarinBatchSize := node`MandarinBatchSize,
	NamingElements := node`NamingElements, 
	MaxQuotientOrder := node`MaxQuotientOrder,
	FastTensorTest := node`FastTensorTest,
	LeafPriorities := node`LeafPriorities,
	MinKernelGens := node`MinKernelGens,
	PresentationKernel := node`PresentationKernel,
	MaxBSGSVerifyOrder := node`MaxBSGSVerifyOrder,
	AnalysePermGroups := node`AnalysePermGroups,
	MaxHomFinderFails := node`MaxHomFinderFails,
	KernelBatchSizeFunc := node`KernelBatchSizeFunc,
	TensorFactorSort := node`TensorFactorSort,
	KnownKernel := false,
	ModuleData := rec<ModuleInfo | 
		SummandSort := node`ModuleData`SummandSort,
		FactorComp := node`ModuleData`FactorComp,
	        ExhibitSummands := node`ModuleData`ExhibitSummands>, 
	SubgroupChainLength := Max(1, node`SubgroupChainLength - 1),
	SafeCrisis := node`SafeCrisis>;
end procedure;

// Create kernel node and set initial values 
procedure InitialiseKernel(~node)
    // If we come here and kernel exists, we got a crisis
    if assigned node`Kernel then
	// In a crisis, only remove the descendants of the kernel and add more
	// generators to it
	delete node`Kernel`Kernel;
	delete node`Kernel`Image;
	delete node`Kernel`RandomProcess;

	delete node`Kernel`PresentationData;
	
	// Force recalculation of reduction
	delete node`Kernel`Type;
	delete node`Kernel`Verified;
    else
	// Type must not be set
	node`Kernel := rec<CTNodeInfo | Depth := node`Depth + 1,
	    FastVerify := false, Parent := node,
	    Verify := node`Verify, Safe := false,
	    ModuleData := rec<ModuleInfo | 
		SummandSort := node`ModuleData`SummandSort, 
		FactorComp := node`ModuleData`FactorComp, 
 	        ExhibitSummands := node`ModuleData`ExhibitSummands>, 
	    MaxHomFinderFails := node`MaxHomFinderFails,
	    NamingElements := node`NamingElements,
	    MaxBSGSVerifyOrder := node`MaxBSGSVerifyOrder,
	    MaxQuotientOrder := node`MaxQuotientOrder,
	    FastTensorTest := node`FastTensorTest,
	    MandarinBatchSize := node`MandarinBatchSize,
	    LeafPriorities := node`LeafPriorities,
	    MinKernelGens := node`MinKernelGens,
	    PresentationKernel := node`PresentationKernel,
	    AnalysePermGroups := node`AnalysePermGroups,
	    KernelBatchSizeFunc := node`KernelBatchSizeFunc,
	    TensorFactorSort := node`TensorFactorSort,
	    KnownKernel := false,
	    SubgroupChainLength := Max(1, node`SubgroupChainLength - 1),
	    SafeCrisis := node`SafeCrisis>;
    end if;
end procedure;

// Find a presentation and verify the node recursively
procedure VerifyNode(~node)
    if not assigned node`Verified then
	if node`Type eq NodeTypes`internal then
	    VerifyNode(~node`Kernel);
	    VerifyNode(~node`Image);
	end if;
		
	// Find presentation of node
	// Should have presentations for image and kernel since they're
	// already verified
	if not assigned node`PresentationData then
	    vprint CompositionTree, 2 :
		"Setup presentation at depth", node`Depth;
	    node`FindPresentation(~node);
	end if;
	
	vprint CompositionTree, 2 :
	    "Verify presentation at depth", node`Depth;
	
	// Verify presentation

	if #node`PresentationData`SLPRelators gt 0 then
	    elts := node`SLPMaps`SLPToEltBatch(
		node`PresentationData`SLPRelators);
	    
	    if not forall{g : g in elts | IsCentral(node`NiceData`Group, g)}
		or exists{g : g in elts | not IsDivisibleBy(Order(node`Scalar),
		Order(g))} then
		delete node`PresentationData;
		error ERROR_VERIFY;
	    end if;
	end if;

	node`Verified := true;
    end if;
end procedure;

procedure PostProcessNode(~node)
    vprint CompositionTree, 2 : "Setup nice data at depth", node`Depth;
    SetupNiceData(~node);
    
    vprint CompositionTree, 2 : "Setup SLP maps at depth", node`Depth;
    SetupSLPMaps(~node);
    
    vprint CompositionTree, 2 : "Mandarin verification at depth", node`Depth;

    // Obtain SLPs of node mandarins
    if node`MandarinVerify then
	MandarinVerification(~node);
    end if;

    // The node is easy if the children are easy
    assert assigned node`Kernel`FastVerify;
    node`FastVerify := node`Kernel`FastVerify and node`Image`FastVerify;

    // Set composition factor finder routine
    node`FindFactors := proc<~node | SetupFactorData(~node)>;
end procedure;

procedure RecogniseKernel(~node : Recurse := true, DebugNodeFile := "")
    // Repeat until the kernel has been found
    kernelOK := false;
    repeat
	try
	    vprint CompositionTree, 2 : "Setup kernel at depth", node`Depth;
	    SetupKernel(~node);
	    node`Kernel`Parent := node;
	    
	    if Recurse then
		vprint CompositionTree, 2 :
		    "Recognise kernel at depth", node`Depth;
		RecogniseNode(~node`Kernel : DebugNodeFile := DebugNodeFile);

		// Setup nice data and SLP maps
		PostProcessNode(~node);
	    else
		node`Kernel`Type := NodeTypes`leaf;
	    end if;

	    if node`Verify then
		// Find and verify presentation for this node
		VerifyNode(~node);
	    end if;
	    
	    kernelOK := true;
	catch err
	    if err`Object cmpeq ERROR_CRISIS_CATCH or
	    err`Object cmpeq ERROR_VERIFY_CATCH then
	        if node`Safe or not node`SafeCrisis then
		    vprint CompositionTree, 2 :
			"Crisis picked up at depth", node`Depth;
			
		    kernelOK := false;
		    InitialiseKernel(~node);
		else
		    // Pass on to a safe node
		    error ERROR_CRISIS;
		end if;
	    else
		error Error(rec<RecogError | Description :=
		    "Error in RecogniseNode", Error := err>);
	    end if;
	end try;
    until kernelOK;
end procedure;

// Main recursive routine that builds the composition tree
procedure RecogniseNode(~node : Recurse := true, DebugNodeFile := "")
    vprint CompositionTree, 1 :
	"Entering Recognise node at depth", node`Depth;

    if #DebugNodeFile gt 0 then
	PrintFileMagma(DebugNodeFile, node`Group);
    end if;
    
    // Initialise image, pass down parameters
    InitialiseImage(~node);
    InitialiseKernel(~node);
    
    // Should we care about permutation groups?
    if Category(node`Group) eq GrpPerm and not node`AnalysePermGroups then
	node`Type := NodeTypes`leaf;
    end if;
    
    // We may already know that the node is a leaf e.g. from C9 case
    if not assigned node`Type then
	// Assume node is internal, we may discover otherwise
	node`Type := NodeTypes`internal;

	vprint CompositionTree, 2 :
	    "Find reduction at depth", node`Depth;
	
	// Try to find image and hom
	FindReduction(~node);
    end if;
    
    // We may have discovered that the node is a leaf
    if node`Type eq NodeTypes`internal then
	assert assigned node`ActionMaps;
	assert assigned node`Image`Group;
	
	// Homomorphism found	
	vprint CompositionTree, 2 : "Setup image at depth", node`Depth;
	SetupImage(~node);
	node`Image`Parent := node;

	vprint CompositionTree, 2 : "Recognise image at depth", node`Depth;
	RecogniseNode(~node`Image : DebugNodeFile := DebugNodeFile);
	
	// Set presentation finder routine
	assert assigned node`Image`FastVerify;
	node`FindPresentation := proc<~node | NicePresentation(~node)>;

	SetKernelBatchSize(~node);
	
	// Find and recognise kernel
	RecogniseKernel(~node : Recurse := Recurse,
	    DebugNodeFile := DebugNodeFile);
    else
	assert node`Type eq NodeTypes`leaf;
	vprint CompositionTree, 2 : "Recognise leaf at depth", node`Depth;
	
	// Leaf node
	RecogniseLeaf(~node);

	// Obtain SLPs for mandarins, for later pullback, or obtain crisis
	// Do not do this if this is the root, so that there is a single node
	if node`MandarinVerify and node`Depth gt 0 then
	    vprint CompositionTree, 2 :
		"Obtain SLPs of mandarins, depth", node`Depth;
	    node`MandarinSLPs := node`SLPMaps`EltToSLPBatch(node`Mandarins);
	end if;

	vprint CompositionTree, 2 :
	    "Mandarin SLPs obtained, depth", node`Depth;
	
        // Verify presentation
	if node`Verify then
	    vprint CompositionTree, 2 : "Verify leaf, depth", node`Depth;

	    try
		VerifyNode(~node);
	    catch err
		error Error(rec<RecogError | Description :=
		"Leaf does not satisfy its presentation", Error := err>);
	    end try;	    
	end if;
    
	// Do not display these
	delete node`Image;
	delete node`Kernel;
    end if;	

    vprint CompositionTree, 1 :
	"Recognise node completed at depth", node`Depth;
end procedure;
