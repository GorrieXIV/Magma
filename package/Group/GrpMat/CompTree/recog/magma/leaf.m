freeze;

/******************************************************************************
 *
 *    leaf.m   Composition Tree Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: leaf.m 3165 2016-03-05 17:48:46Z jbaa004                       $:
 *
 *****************************************************************************/

 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo, RecogError;
import "node.m": AschbacherPriorities, CheckNiceData, MaxVerifyOrder,
    ERROR_CRISIS, ERROR_MEMBERSHIP, ERROR_RECOGNITION, AschbacherAlgorithms,
    ERROR_CRISIS_CATCH, ERROR_MEMBERSHIP_CATCH, ERROR_RECOGNITION_CATCH;
import "twisted.m" : IsSuzuki, SzRecog,
    IsSmallReeDefChar, SmallReeRecogDefChar, IsLargeReeNatRep,
    LargeReeRecogNatRep;
import "classical.m" : AppliesToClassical, ClassicalRecogNatRep,
    IsSporadicClassical;
import "sporadic.m" : BlackBoxSporadic;
import "comp-series.m" : CompositionSeriesC9LeafProjective,
    PullbackCompFactors, FactorError;
import "alt.m" : IsAltLargeDegree, AltLargeDegree, IsSporadicAlt;
import "classical-bb.m" : ClassicalRecogBlackBox, IsClassicalBB;
import "exceptional.m" : IsHighRankExceptional, HighRankExceptionalBlackBox,
    IsSporadicExceptional;
import "c8.m" : DeterminantCheck;
import "mathom.m" : FindPatchElement;
import "centre.m" : C9Centre;

import "../../reduce/reduce.m" : Reduction;
import "../../reduce/parameters.m" : RybaParameters;

forward SchreierSimsLeaf, SimpleLeaf, PermLeaf, PCLeaf, RecogniseLeaf,
    MembershipTesting, MatrixLeaf, CompositeEasyLeafData, UseRyba,
    CompositePCLeafData, GivenMembership, CyclicGrpAbMembership, TrivialLeaf,
    CyclicGrpAbLeaf, BruteForcePresentation, LeafFactorData, RybaLeaf,
    CyclicGrpAbPresentation, StrongGeneratorsPresentation, BuiltinMembership;

// General error during leaf handling
LeafError := recformat<
    Family: Any,
    Description : MonStgElt, 
    Error : Any>;

// Applicability test and the constructive recognition algorithm
LeafAlgInfo := recformat<
    IsApplicable : UserProgram,
    Recognition : UserProgram,
    Description : MonStgElt>;

// Database of constructive recognition algorithms
I := cop<Strings(), Integers(), Booleans()>;
LeafLibrary := AssociativeArray(I);

// Priority names
LeafPrioInfo := recformat<
    WhiteBox : RngIntElt,
    GreyBox  : RngIntElt,
    BlackBox : RngIntElt,
    Ryba     : RngIntElt,
    SS       : RngIntElt>;

LeafPrio := rec<LeafPrioInfo |
    WhiteBox := 4711,
    GreyBox  := 1911,
    BlackBox := 1689,
    Ryba     := 417,
    SS       := 42>;
    
// SL algorithms
RecognisersA := AssociativeArray();
RecognisersA[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Linear group natural representation">;
RecognisersA[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Linear group black box">;

RecognisersA[LeafPrio`BlackBox + 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "AAA Linear group black box (sporadic)">;

RecognisersA[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Linear group, Ryba">;
RecognisersA[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Linear group, RandomSchreier">;
LeafLibrary[I ! "A"] := RecognisersA;

// Omega0 algorithms
RecognisersB := AssociativeArray();
RecognisersB[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Orthogonal group natural representation">;
RecognisersB[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Orthogonal group black box">;
RecognisersB[LeafPrio`BlackBox + 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "Orthogonal group black box (sporadic)">;
RecognisersB[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Orthogonal group, Ryba">;
RecognisersB[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Orthogonal group, RandomSchreier">;
LeafLibrary[I ! "B"] := RecognisersB;

// Sp algorithms
RecognisersC := AssociativeArray();
RecognisersC[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Symplectic group natural representation">;
RecognisersC[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Symplectic group black box">;
RecognisersC[LeafPrio`BlackBox - 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "Symplectic group black box (sporadic)">;
RecognisersC[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Symplectic group, Ryba">;
RecognisersC[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Symplectic group, RandomSchreier">;
LeafLibrary[I ! "C"] := RecognisersC;

// Omega+ algorithms
RecognisersD := AssociativeArray();
RecognisersD[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Orthogonal group natural representation">;
RecognisersD[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Orthogonal group black box">;
RecognisersD[LeafPrio`BlackBox + 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "Orthogonal group black box (sporadic)">;
RecognisersD[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Orthogonal group, Ryba">;
RecognisersD[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Orthogonal group, RandomSchreier">;
LeafLibrary[I ! "D"] := RecognisersD;

// SU algorithms
Recognisers2A := AssociativeArray();
Recognisers2A[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Unitary group natural representation">;
Recognisers2A[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Unitary group black box">;
Recognisers2A[LeafPrio`BlackBox - 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "Unitary group black box (sporadic)">;
Recognisers2A[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
     Description := "Unitary group, Ryba">;
Recognisers2A[LeafPrio`SS] := rec<LeafAlgInfo |
     IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
     Description := "Unitary group, RandomSchreier">;
LeafLibrary[I ! "2A"] := Recognisers2A;

// Omega- algorithms
Recognisers2D := AssociativeArray();
Recognisers2D[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := AppliesToClassical, Recognition := ClassicalRecogNatRep,
    Description := "Orthogonal group natural representation">;
Recognisers2D[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsClassicalBB, Recognition := ClassicalRecogBlackBox,
    Description := "Orthogonal group black box">;
Recognisers2D[LeafPrio`BlackBox + 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := BlackBoxSporadic,
    Description := "Orthogonal group black box (sporadic)">;
Recognisers2D[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Orthogonal group, Ryba">;
Recognisers2D[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Orthogonal group, RandomSchreier">;
LeafLibrary[I ! "2D"] := Recognisers2D;

// Suzuki algorithms
Recognisers2B := AssociativeArray();
Recognisers2B[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsSuzuki, Recognition := SzRecog,
    Description := "Suzuki group">;
Recognisers2B[LeafPrio`BlackBox + 1] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicClassical, Recognition := ClassicalRecogBlackBox,
    Description := "Black box Suzuki group (sporadic)">;
Recognisers2B[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Suzuki group, Ryba">;
Recognisers2B[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Suzuki group, RandomSchreier">;
LeafLibrary[I ! "2B"] := Recognisers2B;

// Small Ree algorithms
Recognisers2G := AssociativeArray();
Recognisers2G[LeafPrio`GreyBox] := rec<LeafAlgInfo |
    IsApplicable := IsSmallReeDefChar, Recognition := SmallReeRecogDefChar,
    Description := "Small Ree group natural representation">;
Recognisers2G[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Small Ree group, Ryba">;
Recognisers2G[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Small Ree group">;
LeafLibrary[I ! "2G"] := Recognisers2G;

// G_2 algorithms
RecognisersG := AssociativeArray();
RecognisersG[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicExceptional,
    Recognition := BlackBoxSporadic,
    Description := "Exceptional group G2, sporadic group">;
RecognisersG[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Exceptional group G2, Ryba">;
RecognisersG[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Exceptional group G2">;
LeafLibrary[I ! "G"] := RecognisersG;

// F_4 algorithms
RecognisersF := AssociativeArray();
RecognisersF[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsHighRankExceptional,
    Recognition := HighRankExceptionalBlackBox,
    Description := "Exceptional group F4, Seitz">;
RecognisersF[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicExceptional,
    Recognition := BlackBoxSporadic,
    Description := "Exceptional group F4, sporadic group">;
RecognisersF[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Exceptional group F4, Ryba">;
RecognisersF[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Exceptional group F4, RandomSchreier">;
LeafLibrary[I ! "F"] := RecognisersF;

// E_n algorithms
RecognisersE := AssociativeArray();
RecognisersE[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicExceptional,
    Recognition := BlackBoxSporadic,
    Description := "Exceptional group E6, sporadic group">;
RecognisersE[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Exceptional group E_n, Ryba">;
RecognisersE[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Exceptional group E_n">;
LeafLibrary[I ! "E"] := RecognisersE;

// 2E_n algorithms
Recognisers2E := AssociativeArray();
Recognisers2E[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicExceptional,
    Recognition := BlackBoxSporadic,
    Description := "Exceptional group 2E6, sporadic group">;
Recognisers2E[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Exceptional group 2E_n, Ryba">;
Recognisers2E[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Exceptional group 2E_n">;
LeafLibrary[I ! "2E"] := Recognisers2E;

// 3D_4 algorithms
Recognisers3D := AssociativeArray();
Recognisers3D[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicExceptional,
    Recognition := BlackBoxSporadic,
    Description := "Exceptional group 3D4, sporadic group">;
Recognisers3D[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Exceptional group 3D4, Ryba">;
Recognisers3D[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Exceptional group 3D4">;
LeafLibrary[I ! "3D"] := Recognisers3D;

// Large Ree algorithms
Recognisers2F := AssociativeArray();
Recognisers2F[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsLargeReeNatRep, Recognition := LargeReeRecogNatRep,
    Description := "Big Ree group natural representation">;
Recognisers2F[LeafPrio`Ryba] := rec<LeafAlgInfo |
    IsApplicable := UseRyba, Recognition := RybaLeaf,
    Description := "Big Ree group, Ryba">;
Recognisers2F[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Big Ree group">;
LeafLibrary[I ! "2F"] := Recognisers2F;

// (2.)Alt(n) algorithms
Recognisers17 := AssociativeArray();
Recognisers17[LeafPrio`WhiteBox] := rec<LeafAlgInfo |
    IsApplicable := IsSporadicAlt, Recognition := BlackBoxSporadic,
    Description := "Alt group, sporadic group">;
Recognisers17[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := IsAltLargeDegree, Recognition := AltLargeDegree,
    Description := "Alt group degree >= 9/8">;
Recognisers17[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Alt group">;
LeafLibrary[I ! 17] := Recognisers17;

// Sporadic algorithms
Recognisers18 := AssociativeArray();
Recognisers18[LeafPrio`BlackBox] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := BlackBoxSporadic,
    Description := "Sporadic group">;
Recognisers18[LeafPrio`SS] := rec<LeafAlgInfo |
    IsApplicable := func<node | true>, Recognition := SchreierSimsLeaf,
    Description := "Sporadic group">;
LeafLibrary[I ! 18] := Recognisers18;

// Leaf handlers for different types of groups
LeafTypes := AssociativeArray();
LeafTypes[GrpMat]  := MatrixLeaf;
LeafTypes[GrpPerm] := PermLeaf;
LeafTypes[GrpPC]   := PCLeaf;
LeafTypes[GrpAb]   := PCLeaf;

// Handlers for small composite leaves
// Must set node`FactorData
CompositeLeafData := AssociativeArray();
CompositeLeafData[GrpMat]  := CompositionSeriesC9LeafProjective;
CompositeLeafData[GrpPerm] := CompositionSeriesC9LeafProjective;
CompositeLeafData[GrpPC]   := CompositeEasyLeafData;
CompositeLeafData[GrpAb]   := CompositeEasyLeafData;

// We use Verify on GrpPerm of smaller degree 
MaxBSGSVerifyPermDegree := 100000;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

procedure SchreierSimsLeaf(~node)
    try   
	vprint CompositionTree, 4 : "Schreier-Sims leaf";

        G := sub<Generic(node`Group) | node`Group, node`Scalar>;

	// Hold your horses...
	RandomSchreier(G);

	// if node`Verify or #node`Group le node`MaxBSGSVerifyOrder or
	if node`Verify or #G le node`MaxBSGSVerifyOrder or
	    (Category(node`Group) eq GrpPerm and
	    Degree(node`Group) le MaxBSGSVerifyPermDegree) then
	    vprint CompositionTree, 4 : "Verify BSGS";
	    Verify(G);
	    vprint CompositionTree, 4 : "Verification finished";
	end if;
	
	// Use strong generators as nice generators
	phi := InverseWordMap(G);
	W := node`WordGroup;
	strongGens := IndexedSetToSequence(StrongGenerators(G));

	if NumberOfGenerators(G) gt NumberOfGenerators(node`Group) then
	    gens := Append(UserGenerators(W), Identity(W));
	else
	    gens := UserGenerators(W);
	end if;

	vprint CompositionTree, 4 : "Obtain nice generators";
	niceSLPs := Evaluate(phi(strongGens), gens);
	niceGens := Evaluate(niceSLPs, UserGenerators(node`Group));
	assert #niceGens eq #strongGens;
	
	vprint CompositionTree, 4 : "Obtain nice group";
	niceGroup := sub<G | niceGens>;
	
	if Category(niceSLPs) ne SeqEnum then
	    niceSLPs := [niceSLPs];
	end if;

        /* ensure we do not invoke TCSS */
	genMap := [Index(ChangeUniverse(niceGens, Generic(niceGroup)), g) :
	    g in UserGenerators(niceGroup)];
	niceSLPs := niceSLPs[genMap];
	
	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
	NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

	// Always easy to find a presentation on the strong generators
	node`FastVerify := #G le node`MaxBSGSVerifyOrder;
	
	// Here we go again...
	RandomSchreier(node`NiceData`Group);

        // EOB -- addition: both G and this group should be identical
        // have observed cases where they don't have same order 
        if #node`NiceData`Group ne #G then 
           vprint CompositionTree, 4: "Input group and nice group have different order from RandomSchreier -- so recurse";
           SchreierSimsLeaf(~node);
           return; 
        end if;
	
	if node`Verify or #G le node`MaxBSGSVerifyOrder or
	    (Category(node`Group) eq GrpPerm and
	    Degree(node`Group) le MaxBSGSVerifyPermDegree) then
	    vprint CompositionTree, 4 : "Verify BSGS";
	    Verify(node`NiceData`Group);
	    vprint CompositionTree, 4 : "Verification finished";
	end if;
	
	vprint CompositionTree, 4 : "Setup SLP maps";
	
	W := node`WordGroup;
	phiN := InverseWordMap(node`NiceData`Group);

	if NumberOfGenerators(G) gt NumberOfGenerators(node`Group) then
	    gens := Append(UserGenerators(node`Group), Identity(node`Group));
	else
	    gens := UserGenerators(node`Group);
	end if;
	
	g2slp := hom<G -> node`NiceData`WordGroup | g :->
	phiN(Evaluate(MembershipTesting(node, func<h |
	    BuiltinMembership(G, h)>, g), gens))>;
	
	slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>;

        // Use group itself as standard copy
	node`LeafData`GoldCopy := node`NiceData`Group;
	node`LeafData`ToGold := hom<G -> node`NiceData`Group |
	g :-> slp2g(Function(g2slp)(g))>;
	node`LeafData`FromGold :=
	    hom<node`NiceData`Group -> G | g :-> g>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := slp2g,
	    SLPToEltBatch := func<slps | Evaluate(slps,
	    UserGenerators(node`NiceData`Group))>>;
	
	node`FindFactors := proc< ~node | LeafFactorData(~node)>;
	node`FindPresentation := proc< ~node |
	    StrongGeneratorsPresentation(~node, G, niceGens, genMap)>;
	
	vprint CompositionTree, 4 : "Leaving Schreier-Sims leaf";
    catch err
	error Error(rec<LeafError |
	Description := "SchreierSims",
	Error := err>);
    end try;	
end procedure;

function UseRyba(node)
    // Only use Ryba on matrix groups which have been named
    if Category(node`Group) eq GrpMat and assigned node`LeafData`Name then
	useRyba := RybaParameters[Retrieve(node`LeafData`Family)](node`Group,
	    Retrieve(node`LeafData`Family), node`LeafData`LieRank,
	    Retrieve(node`LeafData`DefiningField));
	
	return useRyba;
    else
	return false;
    end if;
end function;

procedure RybaLeaf(~node)
    try   
	vprint CompositionTree, 4 : "Ryba leaf";
        ExtendedGroup := sub<Generic(node`Group) | node`Group, node`Scalar>;

	// No special nice generators in this case
	node`NiceData := rec<NiceInfo |
	    Group := node`Group,
	    WordGroup := node`WordGroup,
	    NiceSLPs := UserGenerators(node`WordGroup),
	    NiceToUser := IdentityHomomorphism(node`WordGroup),
	NiceToUserBatch := func<seq | seq>>;

        // We have no method of finding presentations
	node`FastVerify := false;
		
	vprint CompositionTree, 4 : "Setup SLP maps";

	// Remove scalar flag if necessary
	if NumberOfGenerators(ExtendedGroup) gt
	    NumberOfGenerators(node`Group) then
	    gens := Append(UserGenerators(node`WordGroup),
		Identity(node`WordGroup));
	else
	    gens := UserGenerators(node`WordGroup);
	end if;

	// Obtain parameters for this family
	_, params :=
	    RybaParameters[Retrieve(node`LeafData`Family)](ExtendedGroup,
	    Retrieve(node`LeafData`Family), node`LeafData`LieRank,
	    Retrieve(node`LeafData`DefiningField));

	// Setup rewriting map using Ryba
	phi := func<g | Reduction(ExtendedGroup, g : Verify := params[1],
	    CentraliserMethod := params[2], Central := params[4],
	    LieRank := params[5],
	    CentraliserCompletionCheck := func<G, C, g, l |
	    NumberOfGenerators(C) ge params[3]>)>;
	
	g2slp := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node, phi, g), gens)>;
	
	slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>;

        // Use group itself (mod scalars) as standard copy
	node`LeafData`GoldCopy := node`NiceData`Group;
	node`LeafData`ToGold := hom<ExtendedGroup -> node`NiceData`Group | 
	g :-> slp2g(Function(g2slp)(g))>;
	node`LeafData`FromGold :=
	    hom<node`NiceData`Group -> ExtendedGroup | g :-> g>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	assert assigned node`LeafData`Name;
	t := node`LeafData`Name;
	if not HasAttribute(node`LeafData`GoldCopy, "Order") then
	    C := C9Centre(node`LeafData`GoldCopy);
	    
	    if Category(t[1]) eq RngIntElt then
		o := SimpleGroupOrder(t); 
                f := Factorisation (o);
	    else 
                f := FactoredChevalleyGroupOrder (t[1], t[2], t[3]: 
                     Version := "Adjoint");
	    end if;
            f *:= FactoredOrder (C);
 	    // Order attribute now accepts a factorisation
 	    AssertAttribute(node`LeafData`GoldCopy, "Order", f);
	    AssertAttribute(node`NiceData`Group, "Order", f);
	end if;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := slp2g,
	    SLPToEltBatch := func<slps | Evaluate(slps,
	    UserGenerators(node`NiceData`Group))>>;

	// Can only use brute force methods for presentation and comp factors
	node`FindFactors := proc< ~node | LeafFactorData(~node)>;
	node`FindPresentation := proc< ~node | BruteForcePresentation(~node)>;
	
	vprint CompositionTree, 4 : "Leaving Ryba leaf";
    catch err
	error Error(rec<LeafError | Description := "Ryba", Error := err>);
    end try;	
end procedure;

procedure CyclicGrpAbLeaf(~node)
    vprint CompositionTree, 4 : "Cyclic leaf of order", #node`Group;
    vprint CompositionTree, 4 : "Scalar flag order", Order(node`Scalar);

    // Use group itself as standard copy
    node`LeafData`ToGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGoldBatch :=
	func<seq | [node`LeafData`FromGold(g) : g in seq]>;
    node`LeafData`ToGoldBatch :=
	func<seq | [node`LeafData`ToGold(g) : g in seq]>;
    node`LeafData`GoldCopy := node`Group;

    // Easy to find presentation for GrpAb if order is single precision
    node`FastVerify := #node`Group lt MaxVerifyOrder[Category(node`Group)]
	select true else false;

    // Nice generators are the ones Magma has introduced
    // Obtain these as SLPs in user gens
    assert assigned node`Group`UserGenerators;
    W := SLPGroup(#node`Group`UserGenerators);
    assert forall{g : g in node`Group`UserGenerators | g in node`Group};

    // discrete log of generators
    if IsTrivial(node`Group) then
	log := [0 : h in node`Group`UserGenerators];
    else
	log := [ElementToSequence(node`Group ! h)[1] :
	    h in node`Group`UserGenerators];
    end if;
    d, coeffs := XGCD(log);
    
    // Need special membership testing to obtain Magma's generators as words
    // in our generators
    membership := hom<node`Group -> W | g :->
    MembershipTesting(node, func<h | CyclicGrpAbMembership(node`Group,
	W, d, coeffs, h)>, g)>;

    // Our generators must be in the group
    // Make sure that niceSLPs is non-empty, to avoid Magma bugs
    // Add identity as one generator
    try
	niceSLPs := [membership(node`Group.i) : i in
	[0 .. NumberOfGenerators(node`Group)]];
    catch err
	error Error(rec<LeafError | Error := err,
	Description := "Cyclic group generators not in group">);
    end try;
    assert #niceSLPs eq 1 + NumberOfGenerators(node`WordGroup);

    node`NiceData := rec<NiceInfo |
	Group := node`Group,
	WordGroup := SLPGroup(#niceSLPs), 
	NiceSLPs := niceSLPs>;
    
    node`NiceData`NiceToUser := hom<node`NiceData`WordGroup -> W | niceSLPs>;
    node`NiceData`NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>;

    // Hacks to remove the identity generator
    node`NiceData`Group`UserGenerators := [Identity(node`NiceData`Group)] cat
	[node`NiceData`Group.i :
	i in [1 .. NumberOfGenerators(node`NiceData`Group)]];
    assert NumberOfGenerators(node`NiceData`Group) + 1 eq
	NumberOfGenerators(node`NiceData`WordGroup);
    assert #UserGenerators(node`NiceData`Group) eq
	NumberOfGenerators(node`NiceData`WordGroup);

    g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup |
    [node`NiceData`WordGroup.i :
	i in [2 .. NumberOfGenerators(node`NiceData`WordGroup)]]>;
    slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
    UserGenerators(node`NiceData`Group)>;
    
    // Use built-in membership testing, create our own InverseWordMap
    g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
    MembershipTesting(node, func<h | GivenMembership(node`NiceData`Group,
	g2slp, h)>, g)>;
    
    node`SLPMaps := rec<SLPMapsInfo |
	EltToSLP := g2slp,
	EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	SLPToElt := slp2g,
	SLPToEltBatch := func<slps | Evaluate(slps,
	UserGenerators(node`NiceData`Group))>>;

    node`FindFactors := proc< ~node | LeafFactorData(~node)>;
    node`FindPresentation := proc< ~node | CyclicGrpAbPresentation(~node)>;
end procedure;

// GrpPC leaves are easy to handle, use built-in machinery
procedure PCLeaf(~node)
    if IsCyclic(node`Group) then
	CyclicGrpAbLeaf(~node);
	return;
    end if;

    // Use group itself as standard copy
    node`LeafData`ToGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGoldBatch :=
	func<seq | [node`LeafData`FromGold(g) : g in seq]>;
    node`LeafData`ToGoldBatch :=
	func<seq | [node`LeafData`ToGold(g) : g in seq]>;
    node`LeafData`GoldCopy := node`Group;

    // Easy to find a presentation of PC-groups if order is single precision
    flag, order := IsDefined(MaxVerifyOrder, Category(node`Group));
    node`FastVerify := not flag or #node`Group lt order;
    
    // Nice generators are the ones Magma has introduced
    // The given generators have been saved
    assert assigned node`Group`UserGenerators;

    assert NumberOfGenerators(node`WordGroup) eq
	NumberOfGenerators(node`Group);
    gens := node`Group`UserGenerators;
    
    // Obtain these as SLPs in user gens
    W := SLPGroup(#node`Group`UserGenerators);
    g2slp := Homomorphism(node`Group, W, gens, UserGenerators(W));
    niceSLPs := [g2slp(node`Group.i) : i in
	[1 .. NumberOfGenerators(node`Group)]];
    assert #niceSLPs eq NumberOfGenerators(node`WordGroup);
    
    node`NiceData := rec<NiceInfo |
	Group := node`Group,
	WordGroup := node`WordGroup,
	NiceSLPs := niceSLPs,
	NiceToUser := hom<node`WordGroup -> W | niceSLPs>,
    NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;
    
    // Make sure word group has correct number of generators
    node`Group := sub<node`Group | gens>;
    node`Group`UserGenerators := gens;
    node`WordGroup := W;
    
    // Use built-in homs for membership testing
    G := node`NiceData`Group;
    W := node`NiceData`WordGroup;
    node`NiceData`Group`UserGenerators :=
	ChangeUniverse([G.i : i in [1 .. NumberOfGenerators(G)]], Generic(G));

    g2slp := hom<G -> W | [<G.i, W.i> : i in [1 .. NumberOfGenerators(G)]]>;
    slp2g := hom<W -> G | UserGenerators(G)>;

    membership := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
    MembershipTesting(node, func<h | GivenMembership(node`NiceData`Group,
	g2slp, h)>, g)>;
    
    node`SLPMaps := rec<SLPMapsInfo |
	EltToSLP := membership,
	EltToSLPBatch := func<seq | [Function(membership)(g) : g in seq]>,
	SLPToElt := slp2g,
	SLPToEltBatch := func<slps | Evaluate(slps,
	UserGenerators(node`NiceData`Group))>>;

    node`FindFactors := proc< ~node | LeafFactorData(~node)>;
    node`FindPresentation := proc< ~node | BruteForcePresentation(~node)>;
end procedure;

// Trivial groups are handled using built-in machinery, very similar to GrpPC
procedure TrivialLeaf(~node)
    // Use group itself as standard copy
    node`LeafData`ToGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGold := IdentityHomomorphism(node`Group);
    node`LeafData`FromGoldBatch :=
	func<seq | [node`LeafData`FromGold(g) : g in seq]>;
    node`LeafData`ToGoldBatch :=
	func<seq | [node`LeafData`ToGold(g) : g in seq]>;
    node`LeafData`GoldCopy := node`Group;

    node`FastVerify := true;
    
    // Nice generators are the ones Magma has introduced
    // The given generators have been saved
    assert assigned node`Group`UserGenerators;
    assert NumberOfGenerators(node`WordGroup) eq
	NumberOfGenerators(node`Group);
    
    // Obtain these as SLPs in user gens
    W := SLPGroup(#node`Group`UserGenerators);
    g2slp := hom<node`Group -> W | [<node`Group`UserGenerators[i], W.i> :
    i in [1 .. #node`Group`UserGenerators]]>;
    niceSLPs := [g2slp(node`Group.i) : i in
	[1 .. NumberOfGenerators(node`Group)]];
    assert #niceSLPs eq NumberOfGenerators(node`WordGroup);
    
    node`NiceData := rec<NiceInfo |
	Group := node`Group,
	WordGroup := node`WordGroup,
	NiceSLPs := niceSLPs,
	NiceToUser := hom<node`WordGroup -> W | niceSLPs>,
    NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;
    
    // Make sure word group has correct number of generators
    gens := node`Group`UserGenerators;
    node`Group := sub<node`Group | gens>;
    node`Group`UserGenerators := gens;
    node`WordGroup := W;
    
    // Use built-in homs for membership testing
    G := node`NiceData`Group;
    W := node`NiceData`WordGroup;
    node`NiceData`Group`UserGenerators :=
	ChangeUniverse([G.i : i in [1 .. NumberOfGenerators(G)]], Generic(G));

    g2slp := hom<G -> W | [<G.i, W.i> : i in [1 .. NumberOfGenerators(G)]]>;
    slp2g := hom<W -> G | UserGenerators(G)>;

    membership := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
    MembershipTesting(node, func<h | GivenMembership(node`NiceData`Group,
	g2slp, h)>, g)>;
    
    node`SLPMaps := rec<SLPMapsInfo |
	EltToSLP := membership,
	EltToSLPBatch := func<seq | [Function(membership)(g) : g in seq]>,
	SLPToElt := slp2g,
	SLPToEltBatch := func<slps | Evaluate(slps,
	UserGenerators(node`NiceData`Group))>>;

    node`FindFactors := proc< ~node | LeafFactorData(~node)>;
    node`FindPresentation := proc< ~node | BruteForcePresentation(~node)>;
end procedure;

procedure SimpleLeaf(~node)

    try
	assert assigned node`LeafData`Name;

        // Fetch constructive recognition algorithms for this family
	database := LeafLibrary[Retrieve(node`LeafData`Family)];
	
	// Sort priorities descending
	priorities := Sort(SetToSequence(Keys(database)),
	    func<x, y | y - x>);

	prioIdx := [1 .. #priorities];
	if #node`LeafPriorities gt 0 and
	    #priorities eq #node`LeafPriorities then

	    Sort(~prioIdx, func<i, j | node`LeafPriorities[j] -
		node`LeafPriorities[i]>);
	end if;

	vprint CompositionTree, 4 :
	    "Number of possible leaf algorithms", #priorities;

	// Run first applicable constructive recognition
	for idx in prioIdx do
	    if database[priorities[idx]]`IsApplicable(node) then
		try
		    vprint CompositionTree, 4 :
		    "Applicable leaf algorithm found, executing:",
		    database[priorities[idx]]`Description;
		    database[priorities[idx]]`Recognition(~node);
		    return;
		catch err
		    if err`Object cmpeq ERROR_RECOGNITION_CATCH then
		        // Constructive recognition algorithm failed
			// try next
			vprint CompositionTree, 4 :
			    "Leaf algorithm failed, try next";
		    else
			error Error(rec<LeafError | Error := err,
			    Description :=
			    "Error in constructive recognition">);
		    end if;
		end try;
	    end if;
	end for;
	
	// No leaf handling was found
	error Error(rec<LeafError |
	    Description := "No constructive recognition algorithm found">);
    catch err
	error Error(rec<LeafError |
	Description := "Error in leaf handling", Error := err>);
    end try;
end procedure;

// Permutation groups are handled via RandomSchreier unless simple
procedure PermLeaf(~node)
    if assigned node`LeafData`Name then
	vprint CompositionTree, 4 :
	    "Simple perm leaf, depth", node`Depth;
	
	// Simple groups are handled by the general algorithm
	SimpleLeaf(~node);
    else
	vprint CompositionTree, 4 :
	    "Schreier-Sims perm leaf, depth", node`Depth;

	SchreierSimsLeaf(~node);
    end if;
end procedure;

procedure MatrixLeaf(~node)
    // We must not have non-trivial determinants
    // otherwise several leaf algorithms break
    // We may come here from KnownLeaf, in which case we run the test again
    if assigned node`LeafData`Name and
	(assigned node`HomFinderStamps and
	node`HomFinderStamps[AschbacherAlgorithms`determinant]`negative gt 0 or
	not DeterminantCheck(node)) then

	// Either a non-abelian simple group
	SimpleLeaf(~node);
    else
	// Or cyclic or unknown
	SchreierSimsLeaf(~node);
    end if;
end procedure;

procedure RecogniseLeaf(~node)
    if not assigned node`LeafData then
	node`LeafData := rec<LeafInfo | >;
    end if;

    node`CBM := func<node | Identity(node`Group)>;

    // Special case for trivial groups of any category
    if assigned node`Group`UserGenerators then
	if IsEmpty(node`Group`UserGenerators) then
	    TrivialLeaf(~node);
	    return;
	end if;
    end if;
    
    if IsTrivial(node`Group) and (not assigned node`ScalarGroup or
	IsTrivial(node`ScalarGroup)) then 
	TrivialLeaf(~node);
    else
	vprint CompositionTree, 4 : "Leaf type", Category(node`Group);
	assert IsDefined(LeafTypes, Category(node`Group));    
	recogniser := LeafTypes[Category(node`Group)];
	recogniser(~node);
    end if;

    vprint CompositionTree, 4 :
	"Leaf recognition completed, depth", node`Depth;
end procedure;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Membership testing using built-in machinery
function BuiltinMembership(G, g)
    phi := InverseWordMap(G);

    if g in G then
	return true, phi(g);
    else
	return false, _;
    end if;
end function;

// Membership testing using a given rewriting map
function GivenMembership(G, phi, g)
    if g in G then
	return true, phi(g);
    else
	return false, _;
    end if;
end function;

// Constructive membership testing with exception handling
// Throws a RecogCrisis if membership testing fails
// EltToSLP should be UserProgram(GrpElt) -> BoolElt, GrpSLPElt
function MembershipTesting(leaf, EltToSLP, g)
    try
	flag, slp := EltToSLP(g);

        // EltToSLP may involve a Ryba call, which throws MembershipError
	// Throw the same here
        if not flag then
	    error ERROR_MEMBERSHIP;
	end if;
    catch err
	if err`Object cmpeq ERROR_MEMBERSHIP_CATCH then
	    error ERROR_CRISIS;
	else
	    error Error(rec<LeafError |
		Description := "Membership testing failed",
		Error := err>);
	end if;
    end try;

    return slp;
end function;

// Membership testing in a C9 group G
// g2slp takes an element g of G and produces an SLP which evaluates to g times
// a scalar
// centerToSLP is membership testing in the centre of g, produces SLPs in the
// same word group as g2slp
// returns an SLP of g which evaluates to g
function C9Membership(G, g2slp, centerToSLP, g)
    slp := Function(g2slp)(g);
    
    assert NumberOfGenerators(Parent(slp)) eq NumberOfGenerators(G);
    h := g / Evaluate(slp, UserGenerators(G));
    
    if IsIdentity(h) then
	return slp;
    else
	assert IsCentral(G, h);
	w := Function(centerToSLP)(h);
	assert Parent(w) eq Parent(slp);
	//assert Evaluate(slp * w, UserGenerators(G)) eq g;
	
	return w * slp;
    end if;
end function;

function C8Presentation(G, W, relators, centre,
    centerSLP, centerToSLP, scalarFlag)
    assert Universe(relators) eq W;
    assert NumberOfGenerators(W) eq NumberOfGenerators(G);

    // These elements must be central (identity if there is no center)
    elts := Evaluate(relators, UserGenerators(G));
    
    // powers of the center generator, used to patch relators
    centerSLPs := [Function(centerToSLP)(g) : g in elts];
    assert Universe(centerSLPs) eq W;
    
    n := Order(centre.1);
    k := Order(scalarFlag);
    return Append([relators[i] * centerSLPs[i]^(-1) : i in [1 .. #relators]]
	cat [(W.i, centerSLP) : i in [1 .. NumberOfGenerators(W)]],
	centerSLP^(n div GCD(n, k)));
end function;

// Obtain SLP relators for a presentation of a C9 group G with wordgroup W
// relators are SLPs in W, relators for the simple quotient of G
// centerGenNr is the index of the center generator in UserGenerators(G)
// centerToSLP is a Map which does rewriting in the center and
// produces SLPs in W
function C9Presentation(G, W, relators, centerGenNr, centerToSLP, scalarFlag)
    assert Universe(relators) eq W;
    assert NumberOfGenerators(W) eq NumberOfGenerators(G);

    // These elements must be central (identity if there is no center)
    elts := Evaluate(relators, UserGenerators(G));
    
    // powers of the center generator, used to patch relators
    centerSLPs := [Function(centerToSLP)(g) : g in elts];
    assert Universe(centerSLPs) eq W;
    
    n := Order(G.centerGenNr);
    k := Order(scalarFlag);
    return Append([relators[i] * centerSLPs[i]^(-1) : i in [1 .. #relators]]
	cat [(W.i, W.centerGenNr) : i in [1 .. NumberOfGenerators(W)] |
	i  ne centerGenNr], W.centerGenNr^(n div GCD(n, k)));
end function;

// Membership testing in a centre of a C9 matrix group (a cyclic group) 
// G must have a single generator and consists of scalars, and g is also a
// scalar. 
function C9CenterMembership(G, scalarFlag, g)
    assert NumberOfGenerators(G) eq 1;
    assert Category(G) eq GrpMat;
    assert IsScalar(G.1);
    assert IsScalar(g);
    assert IsScalar(scalarFlag);
    
    if not IsDivisibleBy(LCM(Order(G.1), Order(scalarFlag)), Order(g)) then
	return false, _;
    end if;

    F := CoefficientRing(G);
    I, inc := MultiplicativeGroup(F);
    inv := Inverse(inc);
    patch := FindPatchElement(Order(G.1), Factorisation(#F - 1), inv(g[1, 1]));
    patchS := Generic(G) !
	ScalarMatrix(CoefficientRing(G), Degree(G), inc(patch));
    h := g * patchS;

    assert IsDivisibleBy(Order(G.1), Order(h));
    assert IsDivisibleBy(Degree(G), Order(G.1));

    n := -1;
    for i in [0 .. Degree(G) - 1] do
	if G.1^i eq h then
	    n := i;
	    break;
	end if;
    end for;
    assert n ge 0;
    assert G.1^n eq h;
    W := WordGroup(G);
    return true, W.1^n;    
end function;

function CyclicGrpAbMembership(G, W, d, coeffs, g)
    /* first decide membership of g in G */
   if #G mod Order(g) ne 0 then
       return false, _;
   end if;

   // Hack to accomodate trivial G, can occur when scalar flag is non-trivial
   if IsTrivial(G) then
       if IsIdentity(g) then
	   return true, W.0;
       else
	   return false, _;
       end if;
   end if;
   
   // discrete log of g (computed when mapped to G)
   m := ElementToSequence(G ! g)[1];
   
   if Gcd(m, #G) mod Gcd(d, #G) ne 0 then
       return false, _;
   end if;

   k := Solution(d, m, #G);
   coeffs := [c * k : c in coeffs];
   assert #coeffs eq NumberOfGenerators(W);
   return true, &*[W.i^coeffs[i] : i in [1 .. #coeffs]];
end function;

// Just use built-in CompositionSeries for GrpAb and GrpPC
procedure CompositeEasyLeafData(~node)
    // Quotient out the scalar flag
    if Category(node`NiceData`Group) eq GrpAb and IsCyclic(node`NiceData`Group) then
	H := node`NiceData`Group + node`ScalarGroup;
	G, proj := quo<H | node`ScalarGroup>;
	
	C := node`NiceData`Group;
	assert #C mod #G eq 0;
	
	proj1 := function(g)
	    assert g in H;
	    patch := FindPatchElement(#C, Factorisation(#H), g);
	    h := g + patch;
	    assert IsDivisibleBy(#C, Order(h));
	    return C ! h;
	end function;
	
	g2slp := func<seq | node`SLPMaps`EltToSLPBatch([proj1(g) : g in seq])>;
	phi := proj;
    else
	assert IsIdentity(node`Scalar);
	G := node`NiceData`Group;
	phi := IdentityHomomorphism(G);
	g2slp := node`SLPMaps`EltToSLPBatch;
    end if;
    
    series := CompositionSeries(G);
    node`FactorData := PullbackCompFactors(node`NiceData`Group, g2slp,
	phi, series, node`MaxQuotientOrder);
    node`FactorData`FactorLeaves :=
	[node : i in [1 .. #node`FactorData`ToFactor]];
end procedure;

// Obtain a presentation on the strong generators
procedure StrongGeneratorsPresentation(~node, ExtendedGroup,
    niceInputGens, genMap)
    vprint CompositionTree, 4 : "Find presentation on strong generators";
    pres, pres2G := FPGroupStrong(node`NiceData`Group);

    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];	    
    vprintf CompositionTree, 4 : "Strong generator gens %o relators %o\n",
	NumberOfGenerators(pres), #relators;
    
    // Obtain relators as SLPs in nice gens
    wordToSLP := hom<pres -> node`NiceData`WordGroup |
    [<pres.i, Function(node`SLPMaps`EltToSLP)(pres2G(pres.i))> :
    i in [1 .. NumberOfGenerators(pres)]]>;

    node`PresentationData := rec<PresentationInfo |
	SLPRelators := wordToSLP(relators)>;
end procedure;

// Find a presentation for GrpPC or trivial groups
// Simplifies PC-presentations
procedure BruteForcePresentation(~node)
    g2slp := Function(node`SLPMaps`EltToSLP);
    
    pres, pres2G := FPGroup(node`NiceData`Group);
    
    if Category(node`Group) eq GrpPC then
	assert IsIdentity(node`Scalar);

	vprint CompositionTree, 4 :
	    "Simplify PC-presentation, depth", node`Depth;
	presShort, short2pres := Simplify(pres);
    else
	presShort := pres;
	short2pres := IdentityHomomorphism(pres);
    end if;
    
    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(presShort)];
    node`PresentationData := rec<PresentationInfo | >;
	
    // Convert words to SLPs
    if IsTrivial(node`Group) then 
	node`PresentationData`SLPRelators := [];
    else
	// Obtain relators as SLPs in nice gens
	wordToSLP := hom<presShort -> node`NiceData`WordGroup |
	[<presShort.i, g2slp(pres2G(short2pres(presShort.i)))> :
	    i in [1 .. NumberOfGenerators(presShort)]]>;
	    
	node`PresentationData`SLPRelators := wordToSLP(relators);
    end if;

    vprint CompositionTree, 4 :
	"Presentation found, depth", node`Depth;	
end procedure;

procedure CyclicGrpAbPresentation(~node)
    assert IsCyclic(node`NiceData`Group);

    vprint CompositionTree, 4 :
	"Obtain quotient by scalars, depth", node`Depth;
    H := node`NiceData`Group + node`ScalarGroup;
    G, phi := quo<H | node`ScalarGroup>;
    
    // If original group is trivial, there are no relations
    if IsTrivial(node`NiceData`Group) then
	node`PresentationData := rec<PresentationInfo | SLPRelators := []>;
    else
	node`PresentationData := rec<PresentationInfo |
	    SLPRelators := [node`NiceData`WordGroup.2^(#G)]>;
    end if;
end procedure;

// Set node`FactorData using built-in machinery
procedure LeafFactorData(~node)
    if IsTrivial(node`NiceData`Group) then
	node`FactorData := rec<FactorInfo |
	    ToFactor := [* *],
	    FactorSLPs := [],
	    FactorToSLP := [* *],
	    Refined := true,
	    FactorLeaves := []>;
    else
	// Obtain all composition factors and maps
	try
	    // This might fail if quo<> is not possible
	    CompositeLeafData[Category(node`Group)](~node);
	catch err
	    if err`Type eq "ErrUser" and Category(err`Object) eq Rec then
	        if Format(err`Object) cmpeq FactorError then
		    W := WordGroup(node`LeafData`GoldCopy);
		    g2slp := hom<node`LeafData`GoldCopy -> W |
		    UserGenerators(W)>;

		    slps := UserGenerators(node`NiceData`WordGroup);
		    if Category(slps) ne SeqEnum then
			slps := [slps];
		    end if;
		
		    node`FactorData := rec<FactorInfo |
			FactorSLPs := [slps],
			ToFactor := [* node`LeafData`ToGold *],
			FactorToSLP := [* hom<node`LeafData`GoldCopy -> W |
		    g :-> g2slp(g)> *],
			Refined := false, FactorLeaves := [node]>;
		else
		    error Error(rec<RecogError | Description :=
			"Error in composition factor creation", Error := err>);
		end if;
	    else
		error Error(rec<RecogError | Description :=
		    "Error in composition factor creation", Error := err>);
	    end if;		
	end try;
    end if;
end procedure;
