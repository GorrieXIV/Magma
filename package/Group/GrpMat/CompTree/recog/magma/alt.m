/******************************************************************************
 *
 *    alt.m     Composition Tree Alt Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-05-08
 *
 *    Version   : $Revision:: 3001                                           $:
 *    Date      : $Date:: 2015-01-31 16:09:41 +1100 (Sat, 31 Jan 2015)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: alt.m 3001 2015-01-31 05:09:41Z eobr007                        $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "present.m" : PresentationForAlternatingGroup;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "recog.m" : PresentationInfo, FactorInfo, SLPMapsInfo, NiceInfo;
import "leaf.m" : LeafError, MembershipTesting,
    LeafFactorData, C9CenterMembership, C9Membership, C9Presentation;
import "comp-series.m" : PullbackCompFactors;
import "centre.m" : C9Centre;
import "sporadic.m" : SimpleGroupNameToATLAS;
import "sporadics.m" : SporadicGoldCopy;

import "../../GrpMat/util/basics.m" : getMapFunction;

// Different recognition and membership testing functions
// depending on if we have S_n or A_n
AltElementToWord := AssociativeArray();
AltElementToWord[false] := AlternatingElementToStandardWord;
AltElementToWord[true] := C9AlternatingElementToStandardWord;

AltRecognition := AssociativeArray();
AltRecognition[false] := RecogniseAlternating;
AltRecognition[true] := C9RecogniseAlternating;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function IsSporadicAlt(node)    
    atlasName := SimpleGroupNameToATLAS(node);
    return atlasName in Keys(SporadicGoldCopy);
end function;

function IsAltLargeDegree(node)    
    // Use Derek's version of Bratus-Pak when it applies
    if node`LeafData`LieRank ge 9 then
	return true;
    else
	return false;
    end if;
end function;

// We have short presentation for alternating groups
procedure AltShortPresentation(~node, n, center, centerToSLP)
    pres := PresentationForAlternatingGroup(n);
    
    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
    
    if not IsTrivial(center) then
	assert NumberOfGenerators(pres) eq
	    NumberOfGenerators(node`LeafData`GoldCopy);
	assert NumberOfGenerators(pres) + 1 eq
	    NumberOfGenerators(node`NiceData`Group);
	
	// Convert words to SLPs
	wordToSLP := hom<pres -> node`NiceData`WordGroup |
	Prune(UserGenerators(node`NiceData`WordGroup))>;
	
	// Center generator is at the end
	slps := C9Presentation(node`NiceData`Group, node`NiceData`WordGroup,
	    wordToSLP(relators), NumberOfGenerators(node`NiceData`Group),
	    centerToSLP, node`Scalar);
    else
	// Convert words to SLPs
	wordToSLP := hom<pres -> node`NiceData`WordGroup |
	UserGenerators(node`NiceData`WordGroup)>;

	slps := wordToSLP(relators);
    end if;
    
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := slps>;
end procedure;

procedure AltFactorData(~node, center)
    centerPC, phi := AbelianGroup(sub<Generic(node`Group) | center, node`Scalar>);
    centerProj, proj := quo<centerPC | phi(node`Scalar)>;
    series := CompositionSeries(centerProj);

    centerFactors := PullbackCompFactors(node`NiceData`Group,
	node`SLPMaps`EltToSLPBatch, phi * proj, series,
	#center + 1);

    rewrite := function(g)
	W := WordGroup(node`LeafData`GoldCopy);
        h := Evaluate(getMapFunction(node`LeafData`FromGold *
	    node`SLPMaps`EltToSLP)(g),
	    Append(UserGenerators(W), Identity(W)));
        return h;
    end function;

    gold2slp := hom<node`LeafData`GoldCopy ->
    WordGroup(node`LeafData`GoldCopy) | g :-> rewrite(g)>;
    
    if IsTrivial(centerProj) then
	if IsTrivial(centerPC) then
	    slps := [UserGenerators(node`NiceData`WordGroup)];
	else
	    slps := [Prune(UserGenerators(node`NiceData`WordGroup))];
	end if;
	
	tofactor := [* node`LeafData`ToGold *];
	factor2slp := [* gold2slp *];
    else

	slps := Append(centerFactors`FactorSLPs,
	    Prune(UserGenerators(node`NiceData`WordGroup)));
	tofactor := Append(centerFactors`ToFactor, node`LeafData`ToGold);
	factor2slp := Append(centerFactors`FactorToSLP, gold2slp);
    end if;
    
    // Save composition factors
    node`FactorData := rec<FactorInfo |
	FactorSLPs := slps,
	ToFactor := tofactor,
	FactorToSLP := factor2slp,
	Refined := true,
	FactorLeaves := [node : i in [1 .. #centerFactors`ToFactor + 1]]>;
end procedure;

procedure AltLargeDegree(~node)
    try
	Ext := Retrieve(node`LeafData`DefiningField) or
	not IsIdentity(node`Scalar);
    
        // Important to recognise group together with scalar flag
	ExtendedGroup := sub<Generic(node`Group) | node`Group, node`Scalar>;
	
	flag, iso, inv :=
	    AltRecognition[Ext](ExtendedGroup, node`LeafData`LieRank);
	
	if not flag then
	    error ERROR_RECOGNITION;
	end if;

	// information stored by Derek
	// length 7(9): type, degree, 2 standard gens, 2 slps for these,
	assert assigned ExtendedGroup`AltSymData;
	info := ExtendedGroup`AltSymData;
	
	niceGroup := sub<Generic(node`Group) | [info[i] : i in [3, 4]]>;
	niceSLPs := Evaluate([info[i] : i in [5, 6]],
	    Append(UserGenerators(node`WordGroup), Identity(node`WordGroup)));

	// Standard copy has no scalars
	stdCopy := sub<Sym(node`LeafData`LieRank) |
	    [Function(iso)(g) : g in UserGenerators(niceGroup)]>;
	
	node`LeafData`ToGold :=
	    hom<ExtendedGroup -> stdCopy | g :-> Function(iso)(g)>;
	node`LeafData`FromGold := 
	    hom<stdCopy -> ExtendedGroup | g :-> Function(inv)(g)>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;
	node`LeafData`GoldCopy := stdCopy;
	
	AssertAttribute(node`LeafData`GoldCopy, "Order", 
			FactoredOrder(Alt(info[2])));
	    
	// Easy to find a presentation in this case
	node`FastVerify := true;

	// Find centre of input group, not including scalar flag
	center, centerSLP := C9Centre(node`Group);

	// Make sure nice group is the same as the input group
	if not IsTrivial(center) then
	    n := NumberOfGenerators(niceGroup);
	    niceGroup := sub<Generic(niceGroup) | niceGroup, center>;
	    if NumberOfGenerators(niceGroup) gt n then
		Append(~niceSLPs, centerSLP);
	    end if;
	end if;
	
        node`NiceData := rec<NiceInfo |
            Group := niceGroup,
            WordGroup := WordGroup(niceGroup),
            NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
	NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

	// Centre membership testing
	n := NumberOfGenerators(node`NiceData`WordGroup);
	centerMembership := hom<center -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node, func<h |
	    C9CenterMembership(center, node`Scalar,
	    h)>, g), [node`NiceData`WordGroup.n])>;	

	// Use combination of projective membership testing and center patch
	// if there is any centre
	if Ext then
	    assert not IsTrivial(sub<Generic(center) | center, node`Scalar>);
	    	    
	    // Projective membership testing
	    g2slpProj := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	    Evaluate(MembershipTesting(node, func<h |
		AltElementToWord[Ext](ExtendedGroup, h)>, g),
		Prune(UserGenerators(node`NiceData`WordGroup)))>;
	    	
	    // Constructive membership testing with exception handling
	    g2slp := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	    C9Membership(node`NiceData`Group, g2slpProj, centerMembership, g)>;
	else
	    assert IsTrivial(sub<Generic(center) | center, node`Scalar>);
	    
	    // No scalars to remove, use precise membership testing directly
	    g2slp := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	    Evaluate(MembershipTesting(node, func<h |
		AltElementToWord[Ext](ExtendedGroup, h)>, g),
		UserGenerators(node`NiceData`WordGroup))>;
	end if;
	
	slp2g := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>;
	
        // slps for standard generators in user generators
        node`SLPMaps := rec<SLPMapsInfo |
            EltToSLP := g2slp,
            EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := slp2g,
	    SLPToEltBatch := func<seq | Evaluate(seq,
	    UserGenerators(node`NiceData`Group))>>;
		
	node`FindFactors := proc< ~node | AltFactorData(~node, center)>;
	node`FindPresentation := proc< ~node | AltShortPresentation(~node,
	    node`LeafData`LieRank, center, centerMembership)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;
	
	error Error(rec<LeafError | Description := "17",
	    Error := "Error in constructive recognition">);
    end try;    
end procedure;
