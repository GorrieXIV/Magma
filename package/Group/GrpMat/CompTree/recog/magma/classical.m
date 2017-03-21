/******************************************************************************
 *
 *    classical.m   Composition Tree Classical Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 3165                                           $:
 *    Date      : $Date:: 2016-03-06 04:48:46 +1100 (Sun, 06 Mar 2016)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: classical.m 3165 2016-03-05 17:48:46Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "centre.m" : CentreOfClassicalGroup;
import "leaf.m" : MembershipTesting, LeafError, LeafFactorData,
    C8Presentation, C9CenterMembership;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo;
import "comp-series.m" : PullbackCompFactors;
import "sporadic.m" : SimpleGroupNameToATLAS;
import "sporadics.m" : SporadicGoldCopy;
import "../../classical/classical.m" : ClassicalConstructiveRecognitionNatural;

forward ClassicalFactorData;

NonSimpleClassicalTypes := {<"linear", 2, 2>, <"linear", 2, 3>, 
                            <"symplectic", 4, 2>};
NonSimpleClassicalNames := {<"A", 1, 2>, <"A", 1, 3>, <"A", 1, 9>, 
                            <"C", 2, 2>};

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function IsSporadicClassical(node)
    atlasName := SimpleGroupNameToATLAS(node);
    return atlasName in Keys(SporadicGoldCopy);
end function;

function AppliesToClassical(node)
    if Category(node`Group) eq GrpMat then
	F := CoefficientRing(node`Group);
	d := Degree(node`Group);
	
       // Check that it is a classical group in natural rep
       // Also check that the form is not just preserved modulo scalars
       // (no form for linear groups)
       flag := RecogniseClassical(node`Group);

       // SL is always ok
       // Orth, Sp and SU are ok for odd char and small fields even char
       if flag then
	   vprintf CompositionTree, 4 :
	       "Found classical leaf natural rep %o %o\n", d, #F;
           vprint CompositionTree, 4 : "Classical type:",
	   ClassicalType(node`Group);
           vprint CompositionTree, 4 : "Scalar flag order", Order(node`Scalar);
	   return true;
       end if;
    end if;
   
    return false;
end function;

// We have some short presentation for classical groups 
procedure ClassicalShortPresentation(~node, d, F, genMapRev, genMap,
    centre, centreSLP, centreMembership)
    q := #F;

    projective := not IsTrivial(centre);
    type := ClassicalType(node`Group);

    // Sp2 = SL2 and will be recognised as SL
    if type eq "symplectic" and d gt 2 then
	// Symplectic groups
        Q, relators := ClassicalStandardPresentation("Sp", d, q :
	    Projective := projective);

	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);
    elif type eq "unitary" and d gt 2 then
	// Unitary groups
	qq := Isqrt(q);
	Q, relators := ClassicalStandardPresentation("SU", d, qq :
	    Projective := projective);
	
	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);
    elif type eq "linear" then
	// Linear groups
	vprint CompositionTree, 7 : "Find SL presentation";
	Q, relators := ClassicalStandardPresentation("SL", d, q :
	    Projective := projective);
	
	vprint CompositionTree, 7 : "Found SL presentation";
	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);	
    elif type eq "orthogonalcircle" and d ge 3 then
	// Linear groups
	vprint CompositionTree, 7 : "Find Omega presentation";
	Q, relators := ClassicalStandardPresentation("Omega", d, q :
	    Projective := projective);
	
	vprint CompositionTree, 7 : "Found Omega presentation";
	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);	
    elif type eq "orthogonalplus" and d ge 4 then
	// Linear groups
	vprint CompositionTree, 7 : "Find Omega+ presentation";
	Q, relators := ClassicalStandardPresentation("Omega+", d, q :
	    Projective := projective);
	
	vprint CompositionTree, 7 : "Found Omega+ presentation";
	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);	
    elif type eq "orthogonalminus" and d ge 4 then
	// Linear groups
	vprint CompositionTree, 7 : "Find Omega- presentation";
	Q, relators := ClassicalStandardPresentation("Omega-", d, q :
	    Projective := projective);
	
	vprint CompositionTree, 7 : "Found Omega- presentation";
	W := node`NiceData`WordGroup;
	slps := Evaluate(relators, [W.i : i in genMapRev]);	
    else 
	pres, pres2G := FPGroup(node`NiceData`Group);
	relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];

	// Convert words to SLPs
	wordToSLP := hom<pres -> node`NiceData`WordGroup |
	node`SLPMaps`EltToSLPBatch(pres2G(UserGenerators(pres)))>;
	slps := wordToSLP(relators);
    end if;
    assert NumberOfGenerators(Universe(slps)) eq
	NumberOfGenerators(node`NiceData`Group);

    if not IsTrivial(centre) then
	// Centre generator is at the end
	slps := C8Presentation(node`NiceData`Group, node`NiceData`WordGroup,
	    slps, centre, centreSLP, centreMembership, node`Scalar);
    end if;
    
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := slps>;	
    vprint CompositionTree, 7 : "Found presentation relators";
end procedure;

// Obtain node`FactorData for a classical leaf with given center
procedure ClassicalFactorData(~node, center, genMapRev)
    type := <ClassicalType(node`Group), Degree(node`Group),
	#CoefficientRing(node`Group)>;

    // Brute force for small exceptional cases
    if type in NonSimpleClassicalTypes then
	LeafFactorData(~node);
	return;
    end if;
    
    // Take centre projectively
    centerPC, phi := AbelianGroup(sub<Generic(node`Group) | center, node`Scalar>);
    centerProj, proj := quo<centerPC | phi(node`Scalar)>;

    series := CompositionSeries(centerProj);
    centerFactors := PullbackCompFactors(node`NiceData`Group,
	node`SLPMaps`EltToSLPBatch, phi * proj, series, #centerPC + 1);

    W := WordGroup(node`LeafData`GoldCopy);

    gold2slp := hom<node`LeafData`GoldCopy -> W |
    g :-> Evaluate(MembershipTesting(node,
	func<h | ClassicalElementToWord(node`Group, h)>,
	Function(node`LeafData`FromGold)(g)),
	[W.i : i in genMapRev])>;
	
    // Setup data about composition factors
    node`FactorData := rec<FactorInfo | Refined := true>;

    if IsTrivial(centerProj) then
	node`FactorData`FactorToSLP := [* gold2slp *];
	node`FactorData`ToFactor := [* node`LeafData`ToGold *];

	node`FactorData`FactorSLPs := [UserGenerators(node`NiceData`WordGroup)];
    else
	node`FactorData`FactorSLPs := Append(centerFactors`FactorSLPs,
	    UserGenerators(node`NiceData`WordGroup));
	node`FactorData`ToFactor := Append(centerFactors`ToFactor,
	    node`LeafData`ToGold);
	node`FactorData`FactorToSLP := Append(centerFactors`FactorToSLP,
	    gold2slp);
    end if;
    
    node`FactorData`FactorLeaves :=
	[node : i in [1 .. #node`FactorData`ToFactor]];
end procedure;

procedure ObtainCentre(~node, ~centre, ~centreSLP, ~centreMembership)
    // Find centre by writing down scalar matrices
    centre := CentreOfClassicalGroup(node`Group);

    if not IsTrivial(centre) then
	assert NumberOfGenerators(centre) eq 1;
	centreSLP := Function(node`SLPMaps`EltToSLP)(centre.1);
    else
	centreSLP := Identity(node`NiceData`WordGroup);
    end if;

    // Centre membership testing
    centreMembership := hom<centre -> node`NiceData`WordGroup | g :->
    Evaluate(MembershipTesting(node, func<h |
	C9CenterMembership(centre, node`Scalar, h)>, g), [centreSLP])>;
end procedure;

procedure ClassicalRecogNatRep (~node)
    try
	vprint CompositionTree, 2 : "Entering Classical Recognition";
	flag := ClassicalConstructiveRecognitionNatural(node`Group);
	vprint CompositionTree, 2 : "Classical Recognition finished";
    
	if not flag then
	    error ERROR_RECOGNITION;
	end if;
	
	// Delete identity generator
	delete node`Group`UserGenerators;
		
	// Use standard generators as nice generators 
	cbm := node`Group`ClassicalRecognitionData`cbmInput;
	niceInputGens := [Generic(node`Group) | g^cbm : g in
	    node`Group`ClassicalRecognitionData`gens];
	niceGroup := sub<Generic(node`Group) | niceInputGens>;

	node`CBM := func<node | Generic(node`Group) ! cbm^(-1)>;
	
	// Some standard generators might coincide
	genMap := [Index(niceInputGens, g) : g in UserGenerators(niceGroup)];

	// For GF(2) there is no identity generator
	if NumberOfGenerators(Universe(node`Group`
	    ClassicalRecognitionData`slps)) eq
	    NumberOfGenerators(node`WordGroup) + 1 then
	    niceSLPs :=
		Evaluate(node`Group`ClassicalRecognitionData`slps[genMap],
		[Identity(node`WordGroup)] cat UserGenerators(node`WordGroup));
	else
	    niceSLPs :=
		Evaluate(node`Group`ClassicalRecognitionData`slps[genMap],
		UserGenerators(node`WordGroup));
	end if;

	assert Universe(niceSLPs) cmpeq node`WordGroup;
	assert #niceSLPs eq NumberOfGenerators(niceGroup);

	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
	    NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

	// Some standard generators might coincide
	genMapRev := [Index(ChangeUniverse(UserGenerators(niceGroup),
	    Generic(niceGroup)), g) : g in niceInputGens];

	// Constructive membership testing with exception handling
	g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node,
	    func<h | ClassicalElementToWord(node`Group, h)>, g),
	    [node`NiceData`WordGroup.i : i in genMapRev])>;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;

	// Standard copy is Magma copy on our standard generators
	// Use standard change of basis to Magma copy
        CB := node`Group`ClassicalRecognitionData`cbmMagma;
	node`LeafData`GoldCopy := node`NiceData`Group^CB;
	node`LeafData`ToGold := hom<node`NiceData`Group ->
	node`LeafData`GoldCopy | g :-> g^CB>;
	node`LeafData`FromGold := hom<node`LeafData`GoldCopy ->
	node`NiceData`Group | g :-> g^(CB^(-1))>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

        //  on rare occasions RecogniseClassical fails
        repeat
           flag := RecogniseClassical (node`LeafData`GoldCopy);
        until flag;
        // change by EOB -- set up factored order 
        f := FactoredClassicalGroupOrder(ClassicalType(node`LeafData`GoldCopy),
	     Degree(node`LeafData`GoldCopy),
             CoefficientRing(node`LeafData`GoldCopy));
	// Order attribute can now be a factorisation
        AssertAttribute (node`LeafData`GoldCopy, "Order", f);

	// Not yet easy to find presentation for all classical groups
	node`FastVerify := true;
	ObtainCentre(~node, ~centre, ~centreSLP, ~centreMembership);
	
	node`FindFactors := proc< ~node |
	    ClassicalFactorData(~node, centre, genMapRev)>;
	node`FindPresentation := proc< ~node |
	    ClassicalShortPresentation(~node, Degree(node`Group),
	    CoefficientRing(node`Group), genMapRev, genMap,
	    centre, centreSLP, centreMembership)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;
	
	error Error(rec<LeafError | Error := err,
	    Description := "Classical natural representation">);
    end try;
end procedure;
