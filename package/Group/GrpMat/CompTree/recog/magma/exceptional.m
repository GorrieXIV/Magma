/******************************************************************************
 *
 *    exceptional.m  Composition Tree Exceptional Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-10-16
 *
 *    Version   : $Revision:: 2724                                           $:
 *    Date      : $Date:: 2014-08-09 04:09:56 +1000 (Sat, 09 Aug 2014)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: exceptional.m 2724 2014-08-08 18:09:56Z jbaa004                $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "leaf.m" : MembershipTesting, LeafError;
import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "sporadic.m" : RybaMembershipInfo, SimpleGroupNameToATLAS;
import "sporadics.m" : SporadicGoldCopy;
import "centre.m" : C9Centre;

import "../../reduce/reduce.m" : Reduction;

RybaMembershipData := AssociativeArray();
RybaMembershipData["F4"] := rec<RybaMembershipInfo |
    CentraliserGenerators  := 50,
    InvolutionSelections   := 100,
    InvolutionConjugations := 100,
    CentraliserMembership  := "CT">;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function IsSporadicExceptional(node)
    atlasName := SimpleGroupNameToATLAS(node);
    return atlasName in Keys(SporadicGoldCopy);
end function;
    
// We cannot yet deal with extensions or even char
function IsHighRankExceptional(node)
    centre := C9Centre(node`Group);
    q := Retrieve(node`LeafData`DefiningField);
    flag, p, e := IsPrimePower(q);
    assert flag;

    return IsTrivial(centre) and (p gt 3);
end function;

// No good method of finding presentations
procedure HighRankExceptionalPresentation(~node)
    pres, pres2G := FPGroup(node`NiceData`Group);
    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
    
    // Convert words to SLPs
    wordToSLP := hom<pres -> node`NiceData`WordGroup |
    node`SLPMaps`EltToSLPBatch(pres2G(UserGenerators(pres)))>;
    
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := wordToSLP(relators)>;	
end procedure;

// Group is simple, one composition factor
procedure HighRankExceptionalFactorData(~node, g2slpGold)
    node`FactorData := rec<FactorInfo |
	FactorSLPs := [UserGenerators(node`NiceData`WordGroup)],
	ToFactor := [* node`LeafData`ToGold *],
	FactorToSLP := [* g2slpGold *],
	Refined := true,
	FactorLeaves := [node]>;
end procedure;

function RybaMembership(G, name, verify)
    return func<h | Reduction(G, h :
	Verify := verify,
	CentraliserMethod := RybaMembershipData[name]`CentraliserMembership,
	ConjugationTries  := RybaMembershipData[name]`InvolutionConjugations,
	MaxTries          := RybaMembershipData[name]`InvolutionSelections,
	CentraliserCompletionCheck := func<G, C, g, l | NumberOfGenerators(C)
	ge RybaMembershipData[name]`CentraliserGenerators>)>;
end function;

procedure HighRankExceptionalBlackBox(~node)
    try
	vprint CompositionTree, 2 :
	"Entering high rank exceptional group leaf case";
	field := GF(Retrieve(node`LeafData`DefiningField));
        family := Retrieve(node`LeafData`Family);

	// Standard copy on Steinberg generators
	stdCopy := ChevalleyGroup(family, node`LeafData`LieRank, field);
	R := RandomProcessWithWords(stdCopy : WordGroup := WordGroup(stdCopy));

	groups := [* node`Group, stdCopy *];
	randomisers := [* node`RandomProcess, R *];
	stdSLPs := [* *];
	niceGroups := [* *];
	
	for i in [1 .. #groups] do
	    vprintf CompositionTree, 3 :
		"Find standard generators of %o, degree %o\n",
		node`LeafData`Name, Degree(groups[i]);
	    	    
	    // Find standard generators
	    flag, gens, slps := HighRankExceptionalStdGens(groups[i], family,
		node`LeafData`LieRank, field : Randomiser := randomisers[i]);
	    
	    if not flag then
		error ERROR_RECOGNITION;
	    end if;

	    vprint CompositionTree, 3 : "Sandard generators found";

	    // Nice generators are the standard generators
	    niceGroup := sub<Generic(groups[i]) | gens>;

	    // Save standard generators
	    Append(~stdSLPs, slps);
	    Append(~niceGroups, niceGroup);
	end for;
	    
	assert NumberOfGenerators(niceGroups[1]) eq #stdSLPs[1];

	niceGroup := niceGroups[1];
	niceSLPs := stdSLPs[1];
	
	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
	NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

	assert NumberOfGenerators(Universe(node`NiceData`NiceSLPs)) eq
	    NumberOfGenerators(node`Group);

	name := family cat IntegerToString(node`LeafData`LieRank);
	node`LeafData`GoldCopy := niceGroups[2];
	AssertAttribute(node`LeafData`GoldCopy, "Order",
	    FactoredChevalleyGroupOrder(family, node`LeafData`LieRank, field));

	vprint CompositionTree, 2 :
	    "Use Ryba for exceptional membership:", name;
	    
	// Ryba needs random processes
	node`NiceData`Group`RandomProcess :=
	    RandomProcessWithWords(node`NiceData`Group :
	    WordGroup := node`NiceData`WordGroup);

	// Projective constructive membership testing
	g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node, RybaMembership(node`NiceData`Group,
	    name, node`Verify), g), UserGenerators(node`NiceData`WordGroup))>;

	slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>;
	
	G := node`LeafData`GoldCopy;
	W := WordGroup(G);

	// Ryba needs random processes
	G`RandomProcess := RandomProcessWithWords(G : WordGroup := W);
	    
	// Constructive membership testing with exception handling
	g2slpGold := hom<G -> W | g :-> MembershipTesting(node,
	RybaMembership(G, name, node`Verify), g)>;

	node`LeafData`ToGold := hom<node`NiceData`Group -> G | g :->
	Evaluate(Function(g2slp)(g), UserGenerators(G))>;
	    
	node`LeafData`FromGold := hom<G -> node`NiceData`Group | g :->
	Evaluate(Function(g2slpGold)(g), UserGenerators(node`NiceData`Group))>;

	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := slp2g,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;
	
	node`FastVerify := false;

	node`FindFactors := proc< ~node |
	    HighRankExceptionalFactorData(~node, g2slpGold)>;
	node`FindPresentation := proc< ~node |
	    HighRankExceptionalPresentation(~node)>;
	
	vprint CompositionTree, 2 :
	    "High rank exceptional group leaf case finished";
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;

	error Error(rec<LeafError | Description := "High rank exceptional",
	    Error := err>);
    end try;
end procedure;
