/******************************************************************************
 *
 *    recog.m   Composition Tree
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3204                                           $:
 *    Date      : $Date:: 2016-05-19 08:41:31 +1000 (Thu, 19 May 2016)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: recog.m 3204 2016-05-18 22:41:31Z eobr007                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose CompositionTree, 10;

declare attributes Grp : CTNodeData, CTCompSeries;

import "node.m" : RecogniseNode, HomFinderLibraries, HomFinderPriorities,
    VerifyNode, ERROR_VERIFY, ERROR_MEMBERSHIP, ERROR_CRISIS, PostProcessNode,
    RecogniseKernel, InitialiseKernel, InitHomFinderStamps,
    InitialiseRandomProcess, ERROR_VERIFY_CATCH, ERROR_MEMBERSHIP_CATCH,
    ERROR_CRISIS_CATCH;
import "c9.m" : AlmostSimpleCheck;
import "c8.m" : ClassicalCheck, ClassicalHom;
import "leaf.m" : RecogniseLeaf;
import "kernel.m" : RandomElementBatch;
import "comp-series.m" : CompositionSeriesFromTree;
import "centre.m" : C9Centre;

import "../../GrpMat/util/basics.m" : getMapFunction;

forward RecogniseGroup, FixCompTree, IsCompTree, Flatten, GetTreeLeaves,
    DisplaySubTreeNodes, DisplayNode, DecomposeGroup, ToRootNice;

// Node type constants
NodeTypeInfo := recformat<
    leaf : MonStgElt,
    internal : MonStgElt>;

// Possible values of NodeTypeInfo`leaf
NodeTypes := rec<NodeTypeInfo |
    leaf := "leaf",
    internal := "internal">;

// General error object in exceptions
RecogError := recformat<
    Description : MonStgElt, 
    Error : Any>;

// Aschbacher/O'Nan-Scott reduction hom
ActionMapsInfo := recformat<
    Description : MonStgElt, // Description of hom finder used
    Batch : UserProgram, // Map a SeqEnum of elements
    Single : Map, // Map a single element
    Scalar : UserProgram, // Obtain scalar patch element
    Test : UserProgram, // Test if an element satisfies Aschbacher
    BatchTest : UserProgram, // Test if a SeqEnum satisfy Aschbacher
    FromKernelBatch : UserProgram,
    ToKernelBatch : UserProgram
    >; 

// Constructive membership and SLP evaluation
// Important to do in batches!
// All SLPs are in NiceData`WordGroup, use NiceData`NiceToUser to convert
SLPMapsInfo := recformat<
    EltToSLP : Map, // NiceData`Group -> NiceData`WordGroup
    SLPToElt : Map, // NiceData`WordGroup -> NiceData`Group
    EltToSLPBatch : UserProgram,
    SLPToEltBatch : UserProgram
    >;

// Extra data for leaves
LeafInfo := recformat<
    Name : Tup, // From SimpleGroupName
    DefiningField : CopElt, // Or true/false for Sym/Alt or sporadic name
    LieRank : RngIntElt, // Or Alt/Sym degree, or sporadic number
    Family : CopElt, // Lie name or 17, 18 for Alt/sporadic
    ToGold : Map, // node`Group -> GoldCopy
    FromGold : Map, // GoldCopy -> node`Group
    ToGoldBatch : UserProgram,
    FromGoldBatch : UserProgram,
    GoldCopy : Grp
    >;

// Nice generators data
NiceInfo := recformat<
    // Nice generators = image nice gens + kernel nice gens
    // For leaves nice gens are usually pre-images of gold gens
    Group : Grp, // Node group on nice gens
    WordGroup : GrpSLP, // Should be WordGroup(NiceGroup)
    NiceSLPs : SeqEnum, // SLPs of nice gens in node group gens
    // Image`NiceData`WordGroup -> NiceData`WordGroup    
    FromImageNice : UserProgram, 
    // Kernel`NiceData`WordGroup -> NiceData`WordGroup    
    FromKernelNice : UserProgram, 
    NiceToUser : Map, // Coerce nice SLPs into node SLPs
    NiceToUserBatch : UserProgram,
    ToParentNice : UserProgram
    >;

// Data stored from MeatAxe
ModuleInfo := recformat<
    Factors : SeqEnum, // Composition factors of module of G
    CBM : GrpMatElt,
    Summands : SeqEnum,
    Series : SeqEnum,
    SummandFactors : SeqEnum,
    ProcessedSummands : RngIntElt,
    ProcessedFactors : RngIntElt,
    nonTrivials : SeqEnum,
    FactorCorners : SeqEnum,
    FactorDimensions : SeqEnum,
    RemovedOp : BoolElt,
    ChosenSummand : RngIntElt,
    Layers : SeqEnum,
    ExhibitSummands : BoolElt,
    SummandSort : UserProgram,
    FactorComp : UserProgram
    >; 

PresentationInfo := recformat<
    SLPRelators : SeqEnum>; // Relations as SLPs in nice generators

FactorInfo := recformat<
    Series : SeqEnum, // Sequence of subgroups, only in root
    FactorGens : SeqEnum, // All composition factor generators, only in root
    FactorSLPs : SeqEnum, // SLPs in NiceData`WordGroup for all factor gens
    ToFactor : List, // Maps to standard copies of factors
    FactorToSLP : List, // Obtain SLP of element in factor copy
    FromFactor : List, // Maps from factor standard copies, only in root
    Refined : BoolElt, // Is this a true composition series?
    FactorLeaves : SeqEnum // The leaves corresponding to the factors
    >;

// Main node data structure
CTNodeInfo := recformat<
    Group : Grp,
    WordGroup : GrpSLP,
    RandomProcess : GrpRandProc,
    Randomiser : UserProgram,
    Depth : RngIntElt,
    Number : RngIntElt,
    Parent : Rec,
    CBM : UserProgram,
    EvalGroup : Grp,
    Safe : BoolElt, // Safe to stop crisis here?
    Type : MonStgElt, // Node type, as above
    Verify : BoolElt, // Immediate verification using presentations?
    Verified : BoolElt, // Node has been verified
    MandarinVerify : BoolElt, // Quality control using Mandarins?
    InputGens : SeqEnum, // Input gens, before Magma removals
    GenMap : SeqEnum, // Indices of group gens in input gens
    NiceData : Rec, // NiceInfo record
    ActionMaps : Rec, // ActionMapsInfo record
    Image : Rec, // CTNodeInfo record
    KnownKernel : BoolElt,
    Kernel : Rec, // CTNodeInfo record
    KernelSLPs : SeqEnum, // SLPs of kernel gens in node input gens
    HomFinderPriorities : SeqEnum, // Database of hom finder algorithms, user def order
    HomFinderStamps : Assoc, // Stores HomFindStamp records
    ModuleData : Rec, // ModuleInfo record
    Scalar : GrpElt,
    ScalarGroup : Grp,
    PresentationData : Rec, // PresentationInfo record
    FindPresentation : UserProgram, // Sets PresentationData
    SLPMaps : Rec, // SLPMapsInfo record
    LeafData : Rec, // LeafInfo record
    FactorData : Rec, // FactorInfo record
    // Sets FactorData`FactorSLPs, FactorData`ToFactor, FactorData`FactorToSLP
    FindFactors : UserProgram, 
    KernelBatchSize : UserProgram, // Nr of elements to add at start or crises
    KernelBatchSizeFunc : Assoc,
    MandarinBatchSize : RngIntElt, // Nr of mandarins to compute
    Mandarins : SeqEnum,
    MandarinSLPs : SeqEnum, // SLPs of mandarins in nice gens
    MandarinScalars : SeqEnum,
    // Assume a negative answer after too many Hom-finder failures
    MaxHomFinderFails : RngIntElt,
    // Upper bound on length of subgroup chains, for normal closure algorithm
    SubgroupChainLength : RngIntElt,
    // Should all GrpPerm be treated as leaves?
    AnalysePermGroups : BoolElt,
    // Can we find a short presentation quickly?
    FastVerify : BoolElt,
    // Number of random elements used in naming algorithms
    NamingElements : RngIntElt,
    // Leaves with larger order will not be fully refined using brute force
    MaxQuotientOrder : RngIntElt,
    // Only use fast tensor product test
    FastTensorTest : BoolElt,
    // Maximum group order for use of Verify
    MaxBSGSVerifyOrder : RngIntElt,
    // Use presentations to obtain kernels, where possible
    PresentationKernel : BoolElt,
    LeafPriorities : SeqEnum,
    TensorFactorSort : SeqEnum,
    SafeCrisis : BoolElt,
    MinKernelGens : Assoc
    >;

ParameterDefaults := AssociativeArray();
ParameterDefaults["Verify"] := false;
ParameterDefaults["MandarinBatchSize"] := 100;
ParameterDefaults["MaxQuotientOrder"] := 10^7;
ParameterDefaults["FastTensorTest"] := true;
ParameterDefaults["MaxBSGSVerifyOrder"] := 20000;
ParameterDefaults["AnalysePermGroups"] := true;
ParameterDefaults["NamingElements"] := 200;
ParameterDefaults["Priorities"] := [];
ParameterDefaults["LeafPriorities"] := [];
ParameterDefaults["MaxHomFinderFails"] := 1;
ParameterDefaults["SubgroupChainLength"] := 5;
ParameterDefaults["KnownLeaf"] := false;
ParameterDefaults["PresentationKernel"] := false;
ParameterDefaults["DebugNodeFile"] := "";
ParameterDefaults["SummandSort"] :=
    func<l | Sort(l, func<x, y | Dimension(x) - Dimension(y)>)>;
ParameterDefaults["FactorComp"] :=
    func<x, y | Dimension(x) - Dimension(y)>;
ParameterDefaults["TensorFactorSort"] := [2, 1];
ParameterDefaults["SafeCrisis"] := true;
ParameterDefaults["ExhibitSummands"] := true;

KernelBatchSizeDefault := AssociativeArray();
ParameterDefaults["KernelBatchSize"] := KernelBatchSizeDefault;

MinKernelGensDefault := AssociativeArray();
ParameterDefaults["MinKernelGens"] := MinKernelGensDefault;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

// General interface functions
intrinsic CompositionTree(G :: GrpMat[FldFin] :
    Hard := false,
    Verify := ParameterDefaults["Verify"],
    Scalar := Identity(CoefficientRing(G)),
    MandarinBatchSize := ParameterDefaults["MandarinBatchSize"],
    MaxQuotientOrder := ParameterDefaults["MaxQuotientOrder"],
    FastTensorTest := ParameterDefaults["FastTensorTest"],
    MaxBSGSVerifyOrder := ParameterDefaults["MaxBSGSVerifyOrder"],
    AnalysePermGroups := ParameterDefaults["AnalysePermGroups"],
    NamingElements := ParameterDefaults["NamingElements"],
    Priorities := ParameterDefaults["Priorities"],
    LeafPriorities := ParameterDefaults["LeafPriorities"],
    MaxHomFinderFails := ParameterDefaults["MaxHomFinderFails"],
    SubgroupChainLength := ParameterDefaults["SubgroupChainLength"],
    KnownLeaf := ParameterDefaults["KnownLeaf"],
    PresentationKernel := ParameterDefaults["PresentationKernel"],
    SummandSort := ParameterDefaults["SummandSort"],
    FactorComp := ParameterDefaults["FactorComp"],
    TensorFactorSort := ParameterDefaults["TensorFactorSort"],
    KernelBatchSize := ParameterDefaults["KernelBatchSize"],
    SafeCrisis := ParameterDefaults["SafeCrisis"],
    MinKernelGens := ParameterDefaults["MinKernelGens"],
    ExhibitSummands := ParameterDefaults["ExhibitSummands"],
    DebugNodeFile := ParameterDefaults["DebugNodeFile"]) -> SeqEnum
    { Computes a composition tree, stores it as G`CTNodeData and return tree. }

    require Scalar in CoefficientRing(G) and not IsZero(Scalar) :
	"<Scalar> must be a non-zero element of the field of G";
    
    if HasCompositionTree(G) then
	return G`CTNodeData;
    end if;

    H := Embed(G);

// code to try to address OmegaMinus field problem
F := BaseRing (H);
E<mu> := GF (#F^2);
w := PrimitiveElement (F);
flag := mu^(#F + 1) eq w;

    tree := RecogniseGroup(H : Verify := Verify, Hard := Hard,
	Scalar := Generic(H) ! ScalarMatrix(Degree(H), Scalar),
	MandarinBatchSize := MandarinBatchSize,
	MaxHomFinderFails := MaxHomFinderFails,
	AnalysePermGroups := AnalysePermGroups,
	NamingElements := NamingElements,
	FastTensorTest := FastTensorTest,
	MaxBSGSVerifyOrder := MaxBSGSVerifyOrder,
	MaxQuotientOrder := MaxQuotientOrder,
	Priorities := Priorities,
	LeafPriorities := LeafPriorities,
	KnownLeaf := KnownLeaf,
	DebugNodeFile := DebugNodeFile,
	PresentationKernel := PresentationKernel,
	SummandSort := SummandSort,
	FactorComp := FactorComp,
	TensorFactorSort := TensorFactorSort,
	KernelBatchSize := KernelBatchSize, 
	MinKernelGens := MinKernelGens, 
	SafeCrisis := SafeCrisis,
	ExhibitSummands := ExhibitSummands,
	SubgroupChainLength := SubgroupChainLength);
    G`CTNodeData := tree;

    return tree;
end intrinsic;

// General interface functions
intrinsic CompositionTree(G :: GrpPerm :
    Hard := false,
    Verify := ParameterDefaults["Verify"],
    MandarinBatchSize := ParameterDefaults["MandarinBatchSize"],
    MaxQuotientOrder := ParameterDefaults["MaxQuotientOrder"],
    MaxBSGSVerifyOrder := ParameterDefaults["MaxBSGSVerifyOrder"],
    NamingElements := ParameterDefaults["NamingElements"],
    Priorities := ParameterDefaults["Priorities"],
    LeafPriorities := ParameterDefaults["LeafPriorities"],
    MaxHomFinderFails := ParameterDefaults["MaxHomFinderFails"],
    SubgroupChainLength := ParameterDefaults["SubgroupChainLength"],
    KnownLeaf := ParameterDefaults["KnownLeaf"],
    SafeCrisis := ParameterDefaults["SafeCrisis"],
    KernelBatchSize := ParameterDefaults["KernelBatchSize"],
    MinKernelGens := ParameterDefaults["MinKernelGens"],
    AnalysePermGroups := ParameterDefaults["AnalysePermGroups"],
    PresentationKernel := ParameterDefaults["PresentationKernel"]) -> SeqEnum
    { Computes a composition tree, stores it as G`CTNodeData and return tree. }

    if HasCompositionTree(G) then
	return G`CTNodeData;
    end if;
    
    tree := RecogniseGroup(G : Verify := Verify, Hard := Hard,
	MandarinBatchSize := MandarinBatchSize,
	MaxHomFinderFails := MaxHomFinderFails,
	MaxQuotientOrder := MaxQuotientOrder,
	KnownLeaf := KnownLeaf, PresentationKernel := PresentationKernel,
	Priorities := Priorities, LeafPriorities := LeafPriorities,
	MaxBSGSVerifyOrder := MaxBSGSVerifyOrder,
	NamingElements := NamingElements,
	SafeCrisis := SafeCrisis,
	AnalysePermGroups := AnalysePermGroups,
	KernelBatchSize := KernelBatchSize, 
	MinKernelGens := MinKernelGens, 
	SubgroupChainLength := SubgroupChainLength);

    G`CTNodeData := tree;

    return tree;
end intrinsic;

intrinsic HasCompositionTree(G :: Grp) -> BoolElt
    { Does G have an attached composition tree? }

    if assigned G`CTNodeData then
	if IsCompTree(G`CTNodeData) then
	    return true;
	end if;
    end if;

    return false;
end intrinsic;

intrinsic CleanCompositionTree(G :: Grp)
    { Remove all data related to composition tree from G. }

    delete G`CTNodeData;
end intrinsic;

intrinsic CompositionTreeFastVerification(G :: Grp) -> BoolElt
    { G must have a composition tree. Determines if the tree can 
     be verified easily using presentations, ie if presentations 
     on nice generators are known for all leaves. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    return G`CTNodeData[1]`FastVerify;
end intrinsic;

intrinsic CompositionTreeVerify(G :: Grp) -> BoolElt, []
    { G must have a composition tree. Verify the correctness
     of the composition tree by constructing a presentation for G.
     If G satisfies the presentation, then return true, and the
     relators of the presentation as SLPs; otherwise return false. 
     The presentation is on the group returned by 
     CompositionTreeNiceGroup}

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    try
	root := G`CTNodeData[1];
        VerifyNode(~root);

	// Convert to sequence
	flattened := [];
	Flatten(root, ~flattened);
	
	G`CTNodeData := flattened;
        relators := root`PresentationData`SLPRelators;
	return true, relators;
    catch err
	if err`Object cmpeq ERROR_VERIFY_CATCH or
	   err`Object cmpeq ERROR_CRISIS_CATCH then
	    return false, _;
	else	
	    error Error(err);
	end if;
    end try;
end intrinsic;

intrinsic int_CompositionTreeFix(G :: Grp) 
    { G must have a composition tree. 
      Rebuild parts of a composition tree if a verification failed. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    FixCompTree(~root);

    // Convert to sequence
    flattened := [];
    Flatten(root, ~flattened);

    G`CTNodeData := flattened;
end intrinsic;

intrinsic CompositionTreeElementToWord(G :: Grp, g :: GrpElt) ->
    BoolElt, GrpSLPElt
    { G must have a composition tree. If g is an element of G,
    then return true and an SLP for g in the nice generators of G, 
    otherwise return false.}

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    if Category(g) eq GrpMatElt then
	h := Embed(g);
    else
	h := g;
    end if;
    try
	slp := Function(root`SLPMaps`EltToSLP)(h);
        return true, slp;
    catch err
	if err`Object cmpeq ERROR_MEMBERSHIP_CATCH or
	   err`Object cmpeq ERROR_CRISIS_CATCH then
	    return false, _;
	else
	    error Error(err);
	end if;
    end try;
end intrinsic;

intrinsic CompositionTreeNiceToUser(G :: Grp) -> Map, []
    { G must have a composition tree. Returns the coercion map from SLPs in
    nice generators of G to SLPs in user generators of G, as well as the SLPs
    of the nice generators in the user generators. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];

    W := WordGroup(G);
    slps := Evaluate(root`NiceData`NiceSLPs, UserGenerators(W));
    slpEval := root`NiceData`NiceToUser;
    assert NumberOfGenerators(Codomain(slpEval)) eq
	NumberOfGenerators(W);
    slpCoercion := hom<Domain(slpEval) -> W | slps>;
    
    return slpCoercion, slps;
end intrinsic;

intrinsic CompositionTreeSLPGroup(G :: Grp) -> GrpSLP, Map
    { G must have a composition tree. Returns the nice word group for the
    root node, and the map from the nice word group to the group. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    return root`NiceData`WordGroup, root`SLPMaps`SLPToElt;
end intrinsic;

intrinsic CompositionTreeSLPGroup(G :: GrpMat[FldFin]) -> GrpSLP, Map
    { G must have a composition tree. Returns the nice word group for the
    root node, and the map from the nice word group to the group. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    W, slpEval := WordGroup(G);
    slpCoercion := CompositionTreeNiceToUser(G);
    
    return root`NiceData`WordGroup, slpCoercion * slpEval;
end intrinsic;

intrinsic CompositionTreeNiceGroup(G :: Grp) -> Grp
    { G must have a composition tree. Returns the nice group for the
    root node. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    if Type (root`NiceData`Group) eq GrpMat then 
       return Embed(root`NiceData`Group, CoefficientRing(G));
    else 
       return root`NiceData`Group;
    end if;
end intrinsic;

intrinsic CompositionTreeFactorNumber(G :: Grp, x :: GrpElt) -> RngIntElt
    { Identifies the minimal i such that g lies in G_i of the composition
    series for G. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    series, toFactor := CompositionTreeSeries(G);

    if Category(x) eq GrpMatElt then
	g := Embed(x);
    else
	g := x;
    end if;
    
    for i in Reverse([1 .. #series - 1]) do
	S := Codomain(toFactor[i]);
	h := Function(toFactor[i])(g);
	
	if (Category(S) eq GrpMat select not IsCentral(S, h) else
	    not IsIdentity(h)) then
	    return i + 1;
	end if;
    end for;

    tree := CompositionTree(G);
    assert IsScalar(g) and IsDivisibleBy(Order(tree[1]`Scalar), Order(g));
    return 1;
end intrinsic;

intrinsic CompositionTreeSeries(G :: Grp) ->
    SeqEnum, List, List, List, BoolElt, SeqEnum, SeqEnum 
    { Given a group G with a composition tree, returns:
    
    1. Composition series, 1 = G_0 < G_1 < ... < G_k = G
    2. Maps G_i -> S_i, where S_i is the standard copy of G_i / G_(i-1), i >= 1
    The kernel of this map is G_(i-1). S_i may be the standard copy plus
    scalars Z, and the map is then a homomorphism modulo scalars, so that the
    kernel is (G_(i-1).Z)/Z
    3. Maps S_i -> G_i
    4. Maps S_i -> WordGroup(S_i)
    5. Flag to indicate if the series is a true composition series.
    6. A sequence of the leaf nodes in the composition tree corresponding to
    each composition factor.
    7. Maps S_i -> WordGroup(CompositionTreeNiceGroup(G))
    
    All maps are defined by rules, so Function can be applied on them to avoid
    built-in membership testing.
    In certain cases the series is not a true composition series, because
    certain leaves could not be refined completely, due to too large indices.
    }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    if assigned G`CTCompSeries then 
       data := G`CTCompSeries;
       return data[1], data[2], data[3], data[4], data[5], data[6], data[7];
    end if;

    root := G`CTNodeData[1];

    if not assigned root`FactorData then	
	CompositionSeriesFromTree(~root);
    end if;

    // Convert to sequence
    flattened := [];
    Flatten(root, ~flattened);

    G`CTNodeData := flattened;
    
    assert assigned root`FactorData`Series;	
    assert assigned root`FactorData`ToFactor;	
    assert assigned root`FactorData`FromFactor;	
    assert assigned root`FactorData`FactorToSLP;	
    assert assigned root`FactorData`Refined;
    assert assigned root`FactorData`FactorLeaves;
    
    W := CompositionTreeSLPGroup(G);
    slpCoercions := [hom<Domain(root`FactorData`FromFactor[i]) -> W | x :-> ToRootNice(flattened, root`FactorData`FactorLeaves[i]`Number, Function(root`FactorData`FactorToSLP[i])(x))> : i in [1 .. #root`FactorData`FactorLeaves]];
    
    if Category(G) eq GrpMat then
	series := [Embed(H, CoefficientRing(G)) : H in root`FactorData`Series];
	
	toStd := func<g | Embed(g)>;
	fromStd := func<g | Embed(g, CoefficientRing(G))>;
	
	toFactor := [* hom<series[i + 1] -> Codomain(root`FactorData`ToFactor[i]) |
	g :-> Function(root`FactorData`ToFactor[i])(toStd(g))> :
	    i in [1 .. #root`FactorData`ToFactor] *];
        fromFactor := [* hom<Domain(root`FactorData`FromFactor[i]) -> series[i + 1] |
	g :-> fromStd(Function(root`FactorData`FromFactor[i])(g))> :
	    i in [1 .. #root`FactorData`FromFactor] *];

        // EOB addition -- store data, otherwise recomputed by every call
        // to CompositionTreeFactorNumber 
	data := <series, toFactor, fromFactor, root`FactorData`FactorToSLP,
         root`FactorData`Refined, root`FactorData`FactorLeaves, slpCoercions>;
        G`CTCompSeries := data;

	return series, toFactor, fromFactor, root`FactorData`FactorToSLP,
	    root`FactorData`Refined, root`FactorData`FactorLeaves, slpCoercions;
    else
	return root`FactorData`Series, root`FactorData`ToFactor,
	    root`FactorData`FromFactor, root`FactorData`FactorToSLP,
	    root`FactorData`Refined, root`FactorData`FactorLeaves, slpCoercions;
    end if;
end intrinsic;

intrinsic DisplayCompTreeNodes(G :: Grp : NonTrivial := true, Leaves := false)
    { Show information about the nodes in the composition tree. The tree is
    traversed in-order. If NonTrivial is true, then display only non-trivial
    nodes. If Leaves is true then display only leaves. }
    
    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    treeSize := DisplaySubTreeNodes(root, 1, 1 : NonTrivial := NonTrivial,
	Leaves := Leaves);
    assert treeSize eq #G`CTNodeData;
end intrinsic;

intrinsic SearchForDecomposition(G :: GrpMat) -> Grp, Grp, SeqEnum
    { Compute image and kernel of a decomposition of G. Also return the
    partial composition tree. }

    F := BaseRing(G);
    require ISA(Type(F), FldFin) :
	"Matrix group must be defined over a finite field";

    return DecomposeGroup(G);
end intrinsic;

intrinsic SearchForDecomposition(G :: GrpPerm) -> Grp, Grp, SeqEnum
    { Compute image and kernel of a decomposition of G. Also return the
    partial composition tree. }

    return DecomposeGroup(G);
end intrinsic;

intrinsic CompositionTreeReductionInfo(G :: Grp, nodeNr :: RngIntElt) ->
    MonStgElt, Grp, Grp
    { Return a string description of the reduction at node with number
    nodeNr in the composition tree for G, as well as the image and kernel
    of the reduction. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";
    require nodeNr in {1 .. #G`CTNodeData} : "nodeNr out of range";
    require G`CTNodeData[nodeNr]`Type ne NodeTypes`leaf :
	"nodeNr is a leaf";
    
    return G`CTNodeData[nodeNr]`ActionMaps`Description, 
	G`CTNodeData[nodeNr]`Image`Group,
	G`CTNodeData[nodeNr]`Kernel`Group;
end intrinsic;

intrinsic CompositionTreeCBM(G :: GrpMat) -> GrpMatElt
    { Return a change of basis matrix that exhibits the Aschbacher reductions
    of G given by the composition tree. }

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    root := G`CTNodeData[1];
    return Embed(root`CBM(root), CoefficientRing(G));
end intrinsic;

intrinsic CompositionTreeOrder(G :: Grp) -> RngIntElt
    {return order of group having composition tree}

    require HasCompositionTree(G) :
	"Input must have a composition tree";
    
    return FactorisationToInteger(CompositionTreeFactoredOrder(G));
end intrinsic;

intrinsic CompositionTreeFactoredOrder(G :: Grp) -> RngIntEltFact
    {return factored order of group having composition tree}

    require HasCompositionTree(G) :
	"Input must have a composition tree";

    // Find leaf nodes
    tree := CompositionTree(G);
    leaves := GetTreeLeaves(tree);
    order := Factorisation(1);
    
    for i in [1 .. #leaves] do
	// Order is stored for the gold copy
	S := leaves[i]`LeafData`GoldCopy;

	if Category(S) in {GrpMat} then
	    assert HasAttribute(S, "FactoredOrder");
	end if;
	
	SC := C9Centre(S : NmrTries := 1000);
	C := C9Centre(leaves[i]`NiceData`Group : NmrTries := 1000);

	// Compute order of leaf group
        o := (FactoredOrder(S) / FactoredOrder(SC)) * FactoredOrder(C);

	// Divide out by scalar flag
	order *:= o / GCD(o, Factorisation (Order(leaves[i]`Scalar)));
    end for;

    return order;
end intrinsic;

intrinsic CompositionTreeNonAbelianFactors(G :: Grp) -> List
    {return a list naming the non-abelian composition factors of a group G
    having a composition tree}

    f,a,b,c,d, nodes:= CompositionTreeSeries (G);
    D := [* Domain (phi): phi in b *];
    index := [i : i in [1..#D] | IsAbelian (D[i]) eq false];
    index := [i : i in index | assigned (nodes[i]`LeafData)`Name];
    return [* nodes[i]`LeafData`Name: i in index *];

end intrinsic;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/
    
/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function GetNodeLeaves(node)
    if node`Type eq NodeTypes`leaf then
	return [node];
    else
	return GetNodeLeaves(node`Image) cat GetNodeLeaves(node`Kernel);
    end if;
end function;

function GetTreeLeaves(tree)
    return [x : x in tree | x`Type eq NodeTypes`leaf];
end function;
    
function IsCompTree(seq)
    return #seq gt 0 and forall{x : x in seq | Category(x) eq Rec and
	Format(x) cmpeq CTNodeInfo};
end function;

procedure Flatten(node, ~list)
    Append(~list, node);

    if node`Type ne NodeTypes`leaf then
	Flatten(node`Image, ~list);
	Flatten(node`Kernel, ~list);
    end if;

    assert forall{i : i in [1 .. #list] | i eq list[i]`Number};
end procedure;

procedure FixCompTree(~node)
    try
	// Find the node where the verification failed

	// Is this above the correct node?
	if not assigned node`Verified then
	    // Is this a leaf?
	    if assigned node`Image then
		assert assigned node`Kernel;

		if assigned node`Image`Verified and
		    assigned node`Kernel`Verified then
	            // The node is not a leaf, but the children are verified
                    // This must be the bad node
		    error ERROR_VERIFY;
		else
		    FixCompTree(~node`Image);
		    FixCompTree(~node`Kernel);
		end if;
	    else
		// The leaf is not verified, this must be the bad node
		error ERROR_VERIFY;
	    end if;
	end if;

	if node`Type ne NodeTypes`leaf then
	    PostProcessNode(~node);
	    
	    assert assigned node`Image and assigned node`Kernel and
		assigned node`Image`Verified and assigned node`Kernel`Verified;
	end if;
	
	delete node`PresentationData;
	delete node`FactorData;	
    catch err
	if err`Object cmpeq ERROR_VERIFY_CATCH then
	    if node`Safe then
		//delete node`Kernel;
		delete node`PresentationData;
		delete node`FactorData;
		    
		node`Verify := true;
		InitialiseKernel(~node);
		RecogniseKernel(~node);
		return;
	    else
		error ERROR_VERIFY;
	    end if;
	else
	    error err;
	end if;
    end try;
end procedure;

procedure DisplayNode(node, nodeNr, parentNr : NonTrivial := false,
    Leaves := false)
    // Find the description of the Hom finder used in the node
    if node`Type eq NodeTypes`internal then
	if Leaves then
	    return;
	end if;
	
	info := node`ActionMaps`Description;
    else
	if NonTrivial and IsTrivial(node`Group) then
	    return;
	end if;
	
	// Add information for the leaf
	assert node`Type eq NodeTypes`leaf;
	info := case<Category(node`Group) |
	    GrpPC: Sprintf("abelian group, order %o", #node`NiceData`Group),
	    GrpAb: Sprintf("abelian group, order %o", #node`NiceData`Group),
	    default: assigned node`LeafData`Name select
	    Sprintf("almost simple, %o", node`LeafData`Name) else
	    Sprintf("RandomSchreier, order %o", #node`NiceData`Group)>;
	
	info := Sprintf("leaf, %o, %o", Category(node`Group), info);
    end if;
    
    printf "node = %o\nparent = %o\ndepth = %o\nscalar = %o\ninfo = %o\n" cat
	"fast verify = %o\n----------\n",
	nodeNr, parentNr, node`Depth, Order(node`Scalar),
	info, node`FastVerify;
end procedure;

function DisplaySubTreeNodes(node, nodeNr, parentNr : NonTrivial := false,
    Leaves := false)
    DisplayNode(node, nodeNr, parentNr : NonTrivial := NonTrivial,
    Leaves := Leaves);
    subTreeNodes := 1;

    // Display information for each node
    if node`Type eq NodeTypes`internal then
	imageNodes := DisplaySubTreeNodes(node`Image, nodeNr + 1, nodeNr :
	    NonTrivial := NonTrivial, Leaves := Leaves);
	kernelNodes := DisplaySubTreeNodes(node`Kernel,
	    nodeNr + imageNodes + 1, nodeNr : NonTrivial := NonTrivial,
	    Leaves := Leaves);

	subTreeNodes +:= imageNodes + kernelNodes;
    end if;

    return subTreeNodes;
end function;

function RecogniseGroup(G :
        Hard := false,
        Verify := ParameterDefaults["Verify"],
        Scalar := Identity(G),
	MandarinBatchSize := ParameterDefaults["MandarinBatchSize"],
	MaxQuotientOrder := ParameterDefaults["MaxQuotientOrder"],
	FastTensorTest := ParameterDefaults["FastTensorTest"],
	MaxBSGSVerifyOrder := ParameterDefaults["MaxBSGSVerifyOrder"],
	AnalysePermGroups := ParameterDefaults["AnalysePermGroups"],
	NamingElements := ParameterDefaults["NamingElements"],
	Priorities := ParameterDefaults["Priorities"],
	LeafPriorities := ParameterDefaults["LeafPriorities"],
	MaxHomFinderFails := ParameterDefaults["MaxHomFinderFails"],
	SubgroupChainLength := ParameterDefaults["SubgroupChainLength"],
	KnownLeaf := ParameterDefaults["KnownLeaf"],
	PresentationKernel := ParameterDefaults["PresentationKernel"],
        Recurse := true,
	ExhibitSummands := ParameterDefaults["ExhibitSummands"],        
	SummandSort := ParameterDefaults["SummandSort"],
	FactorComp := ParameterDefaults["FactorComp"],
	TensorFactorSort := ParameterDefaults["TensorFactorSort"],
	KernelBatchSize := ParameterDefaults["KernelBatchSize"],
	MinKernelGens := ParameterDefaults["MinKernelGens"],
	SafeCrisis := ParameterDefaults["SafeCrisis"],
	DebugNodeFile := ParameterDefaults["DebugNodeFile"])

    // Clear interfering attributes from classical package	
    delete G`UserGenerators;
    delete G`SLPGroup;

    if Hard then
	KernelBatchSize["Primitive"] :=
	    func<G | Max(2 * Floor(Log(2, Degree(G))), NumberOfGenerators(G))>;
	KernelBatchSize["Permutation"] :=
	    func<G | Max(NumberOfGenerators(G), Degree(G))>;
	KernelBatchSize["Irreducible"] :=
	    func<G | Max(NumberOfGenerators(G), Degree(G))>;
	KernelBatchSize["Unipotent"] :=
	    func<G | Max(Degree(G)^2 * Degree(CoefficientRing(G)),
	    NumberOfGenerators(G))>;

	if Category(G) eq GrpMat then
	    SubgroupChainLength := Degree(G)^2 * Degree(CoefficientRing(G));
	else
	    SubgroupChainLength := Ceiling(3 * Degree(G) / 2);
	end if;
    end if;
    
    // Initialise structure
    node := rec<CTNodeInfo |
	Safe := true,
	InputGens := [g : g in UserGenerators(G)],
	Group := G,
	WordGroup := WordGroup(G),
	EvalGroup := G,
	Verify := Verify,
	Depth := 0,
	Number := 1,
	Scalar := Identity(G),
	ModuleData := rec<ModuleInfo | 
		    SummandSort := SummandSort,
		    FactorComp := FactorComp,
		    ExhibitSummands := ExhibitSummands>,
	MandarinVerify := true,
	FastVerify := false,
	LeafPriorities := LeafPriorities,
	PresentationKernel := PresentationKernel,
	AnalysePermGroups := AnalysePermGroups,
	NamingElements := NamingElements,
	MaxBSGSVerifyOrder := MaxBSGSVerifyOrder,
	MaxQuotientOrder := MaxQuotientOrder,
	MaxHomFinderFails := MaxHomFinderFails,
	FastTensorTest := FastTensorTest,
	KernelBatchSizeFunc := KernelBatchSize,
	MandarinBatchSize := MandarinBatchSize,
	TensorFactorSort := TensorFactorSort,
	SafeCrisis := SafeCrisis,
	MinKernelGens := MinKernelGens,
	KnownKernel := false,
	SubgroupChainLength := Max(1, SubgroupChainLength)>;

    try	

	for k in Keys(node`KernelBatchSizeFunc) do
	    assert Category(node`KernelBatchSizeFunc[k]) eq UserProgram;
	end for;
	
	// Book-keeping how generators were mapped
	node`GenMap := [Index(node`InputGens, g) :
	    g in UserGenerators(node`Group)];
	InitialiseRandomProcess(~node);

	node`Scalar := Scalar;
	
	if KnownLeaf then
	    InitHomFinderStamps(~node,
		[1 .. #HomFinderPriorities[Category(G)]]);
	    
	    // Try C8 and then C9
	    if ClassicalCheck(node) then
		ClassicalHom(~node, []);
	    else
		node`Type := NodeTypes`leaf;
		flag, names := AlmostSimpleCheck(node);
	    
		if flag then
		    name := names[1][1];
		    C := cop<Strings(), Integers(), Booleans()>;
		    node`LeafData := rec<LeafInfo | Family := C ! name[1],
			DefiningField := C ! name[3], LieRank := name[2],
			Name := name>;
		end if;
	    end if;
	    
	    RecogniseLeaf(~node);
	else	    
	    // Use user-defined priorities for hom finders
	    if #Priorities gt 0 then
		node`HomFinderPriorities := Priorities;
	    end if;
	    
	    // Obtain Mandarins, mapped around in the tree
	    node`Mandarins, node`MandarinSLPs := 
		RandomElementBatch(node`Randomiser, node`MandarinBatchSize);
	    
	    // Do the thing!
	    RecogniseNode(~node : Recurse := Recurse, DebugNodeFile :=
		DebugNodeFile);		
	end if;
	
	vprint CompositionTree, 1 : "Flatten composition tree";

	// Convert to sequence
	flattened := [];
	Flatten(node, ~flattened);
	
	vprint CompositionTree, 1 : "Leaving CompositionTree";

	return flattened;
    catch err
	printf "Error of type %o during composition tree creation\n", err`Type;
	printf "Full error info:\n%o\n", err;
	
	return [];
    end try;
end function;

function DecomposeGroup(G)
    if HasCompositionTree(G) then
	tree := CompositionTree(G);
    else
	tree := RecogniseGroup(G : Recurse := false);
    end if;
    
    root := tree[1];

    // Show decomposition
    DisplayNode(root, 1, 1);

    // Return image and kernel
    if root`Type eq NodeTypes`leaf then
	return root`NiceData`Group, sub<G | >, tree;
    else
	return root`Image`NiceData`Group, root`Kernel`Group, tree;
    end if;
end function;

NameChange := function(t)
/* t should be a triple returned by SimpleGroupName
 * return corresponding triple required by SimpleGroupOrder
 */
  local u,v,w;
  u := Type(t[1]) eq RngIntElt select t[1] else
    case < t[1] |
      "A" : 1,
      "B" : 2,
      "C" : 3,
      "D" : 4,
      "G" : 5,
      "F" : 6,
      "E" : 7,
     "2A" : 10,
     "2B" : 11,
     "2D" : 12,
     "3D" : 13,
     "2G" : 14,
     "2F" : 15,
     "2E" : 16,
    default : t[1] >;

  //<"E",7,q> and <"E",8,q> should become <8,7,q> and <9,8,q>
  if u eq 7 then u := t[2]+1; end if;
  v := t[2];
  w := t[1] cmpeq 18 select 0 else t[3];
  return <u,v,w>;
end function;

function ToRootNice(tree, number, slp)
    while assigned tree[number]`NiceData`ToParentNice do
	node := tree[number];
	slp := node`NiceData`ToParentNice(slp);
	number := node`Parent`Number;
    end while;
    
    // If only one node, then slp lives in gold copy SLP group, 
    // so need to coerce
    return Evaluate(slp, UserGenerators(tree[number]`NiceData`WordGroup));
end function;
