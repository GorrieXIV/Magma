/******************************************************************************
 *
 *    twisted.m  Composition Tree Twisted Groups Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm and Eamonn O'Brien
 *    Dev start : 2008-04-05
 *
 *    Version   : $Revision:: 2904                                           $:
 *    Date      : $Date:: 2014-12-02 07:25:31 +1100 (Tue, 02 Dec 2014)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: twisted.m 2904 2014-12-01 20:25:31Z jbaa004                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "comp-series.m" : CompositionSeriesC9Leaf,
    CompositionSeriesC9LeafProjective;
import "leaf.m" : MembershipTesting, LeafError;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo;

import "../../GrpMat/exceptional/suzuki/magma/suzuki.m" :
    is2Sz8, BraySzRelations;
import "../../GrpMat/util/basics.m" : getMapFunction;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function IsSuzuki(node)
    return Category(node`Group) eq GrpMat and IsIdentity(node`Scalar);
end function;

procedure SuzukiPresentation(~node, field)
    if #field eq 8 then
	pres, pres2G := FPGroup(node`NiceData`Group);
	relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
	
	// Convert words to SLPs
	wordToSLP := hom<pres -> node`NiceData`WordGroup |
	node`SLPMaps`EltToSLPBatch(pres2G(UserGenerators(pres)))>;
    
	node`PresentationData := rec<PresentationInfo |
	    SLPRelators := wordToSLP(relators)>;	
    else
	// We have a short presentation for Sz
	relators := SzPresentation(field);
	
	node`PresentationData := rec<PresentationInfo |
	    SLPRelators := relators>;
    end if;
end procedure;

procedure SzFactorData(~node)
    if Retrieve(node`LeafData`DefiningField) eq 8 then
	// We may have 2.Sz(8), obtain composition factor including the center
	CompositionSeriesC9LeafProjective(~node);
    else
	coerce := SzSLPCoercion(node`LeafData`GoldCopy);
	
	node`FactorData := rec<FactorInfo |
	    FactorSLPs := [UserGenerators(node`NiceData`WordGroup)],
	    ToFactor := [* node`LeafData`ToGold *],
	    FactorToSLP := [* hom<node`LeafData`GoldCopy ->
	WordGroup(node`LeafData`GoldCopy) |
	    g :-> coerce(MembershipTesting(node,
	    func<h | SzElementToWord(node`LeafData`GoldCopy, h)>, g))> *],
	    Refined := true,
	    FactorLeaves := [node]>;
    end if;
end procedure;

procedure SzRecog(~node)
    try
	field := GF(Retrieve(node`LeafData`DefiningField));
        G := node`Group;
	
	flag, iso, inv, _, slp2g := RecogniseSz(G :
	Verify := false, FieldSize := #field);
    
        if not flag then
	    error ERROR_RECOGNITION;
	end if;

	stdCopy := Sz(field);
	q := #field;
        multiples := [q^2, q^2 + 1, q - 1];
        AssertAttribute(stdCopy, "Order", 
			&*[Factorisation(x) : x in multiples]);
	    
	node`LeafData`GoldCopy := stdCopy;
	node`LeafData`ToGold := hom<G -> stdCopy | g :-> Function(iso)(g)>;
	node`LeafData`FromGold := hom<stdCopy -> G | g :-> Function(inv)(g)>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	// Easy to find a presentation in this case
	node`FastVerify := true;

	// Obtain SLPs of nice generators in user generators
	coerce := SzSLPCoercion(G);

	if is2Sz8(G, #field) then
	    node`NiceData := rec<NiceInfo |
		Group := G,
		WordGroup := WordGroup(G),
		NiceSLPs := UserGenerators(node`WordGroup),
		NiceToUser := hom<WordGroup(G) ->
	    node`WordGroup | UserGenerators(node`WordGroup)>,
		NiceToUserBatch := func<seq |
		Evaluate(seq, UserGenerators(node`WordGroup))>>;
	    
	    // Constructive membership testing with exception handling
	    g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	    Evaluate(coerce(MembershipTesting(node, func<h |
		SzElementToWord(G, h)>, g)),
		UserGenerators(WordGroup(G)))>;
	else	
	    niceSLPs := [coerce(elt) where _, elt is
		SzElementToWord(G,
		Function(node`LeafData`FromGold)(g)) :
		g in UserGenerators(stdCopy)];
	
	    // Use stdandard copy generators as nice generators 
	    niceGroup := sub<Generic(node`Group) |
		node`LeafData`FromGoldBatch(UserGenerators(stdCopy))>;
	    assert #niceSLPs eq NumberOfGenerators(niceGroup);
	
	    node`NiceData := rec<NiceInfo |
		Group := niceGroup,
		WordGroup := WordGroup(niceGroup),
		NiceSLPs := niceSLPs,
		NiceToUser :=
		hom<WordGroup(niceGroup) -> node`WordGroup |
	    Evaluate(niceSLPs, UserGenerators(node`WordGroup))>,
		NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;
	    
	    flag, iso, inv, _, slp2g := RecogniseSz(stdCopy :
		Verify := false, FieldSize := #field);
	
	    coerce := SzSLPCoercion(stdCopy);
	    assert NumberOfGenerators(WordGroup(stdCopy)) eq
		NumberOfGenerators(node`NiceData`WordGroup);
		
	    // Constructive membership testing with exception handling
	    g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	    Evaluate(coerce(MembershipTesting(node, func<h |
		SzElementToWord(stdCopy, Function(node`LeafData`ToGold)(h))>,
		g)), UserGenerators(node`NiceData`WordGroup))>;
	end if;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;

	node`FindFactors := proc< ~node | SzFactorData(~node)>;
	node`FindPresentation :=
	    proc< ~node | SuzukiPresentation(~node, field)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;

	error Error(rec<LeafError | Description := "2B", Error := err>);
    end try;
end procedure;

function IsSmallReeDefChar(node)
    if Category(node`Group) eq GrpMat then
	F := CoefficientRing(node`Group);
	
	if Characteristic(F) eq 3 and #F gt 3 then
	    assert IsIdentity(node`Scalar);
	    return true;
	end if;
    end if;

    return false;
end function;

// No known short presentation for small Ree
procedure SmallReePresentation(~node)
    pres, pres2G := FPGroup(node`NiceData`Group);
    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
    
    // Convert words to SLPs
    wordToSLP := hom<pres -> node`NiceData`WordGroup |
    node`SLPMaps`EltToSLPBatch(pres2G(UserGenerators(pres)))>;
    
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := wordToSLP(relators)>;	
end procedure;

procedure SmallReeFactorData(~node)
    coerce := ReeSLPCoercion(node`LeafData`GoldCopy);
    
    node`FactorData := rec<FactorInfo |
	FactorSLPs := [UserGenerators(node`NiceData`WordGroup)],
	ToFactor := [* node`LeafData`ToGold *],
	FactorToSLP := [* hom<node`LeafData`GoldCopy ->
    WordGroup(node`LeafData`GoldCopy) | g :->
	coerce(MembershipTesting(node, func<h |
	ReeElementToWord(node`LeafData`GoldCopy, h)>, g))> *],
	Refined := true,
	FactorLeaves := [node]>;
end procedure;

procedure SmallReeRecogDefChar(~node)
    try
	field := GF(Retrieve(node`LeafData`DefiningField));
	flag, iso, inv, _, slp2g := RecogniseRee(node`Group :
	Verify := false, FieldSize := #field);
    
        if not flag then
	    error ERROR_RECOGNITION;
	end if;

	stdCopy := Ree(field);
	
	node`LeafData`GoldCopy := stdCopy;
	node`LeafData`ToGold :=
	    hom<node`Group -> stdCopy | g :-> Function(iso)(g)>;
	node`LeafData`FromGold :=
	    hom<stdCopy -> node`Group | g :-> Function(inv)(g)>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	// No known short presentation in this case
	node`FastVerify := false;
	
	// Obtain SLPs of nice generators in user generators
	coerce := ReeSLPCoercion(node`Group);
	niceSLPs := [coerce(elt)
	    where _, elt is ReeStandardConstructiveMembership(node`Group`
	    ReeReductionData`stdCopy, g : CheckInput := false,
	    Randomiser := node`Group`ReeReductionData`stdCopy`RandomProcess)
	    : g in UserGenerators(stdCopy)];
	
	// Use stdandard copy generators as nice generators 
	niceGroup := sub<Generic(node`Group) |
	    node`LeafData`FromGoldBatch(UserGenerators(stdCopy))>;
	assert #niceSLPs eq NumberOfGenerators(niceGroup);
	    
	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser :=
	    hom<WordGroup(niceGroup) -> node`WordGroup |
	Evaluate(niceSLPs, UserGenerators(node`WordGroup))>,
	    NiceToUserBatch :=
	    func<seq | Evaluate(seq, niceSLPs)>>;

	flag, iso, inv, _, slp2g := RecogniseRee(stdCopy :
	    Verify := false, FieldSize := #field);

        if not flag then
	    error ERROR_RECOGNITION;
	end if;
	
	coerce := ReeSLPCoercion(stdCopy);
	assert NumberOfGenerators(WordGroup(stdCopy)) eq
	    NumberOfGenerators(node`NiceData`WordGroup);
	
	// Constructive membership testing with exception handling
	g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	Evaluate(coerce(MembershipTesting(node, func<h |
	    ReeElementToWord(stdCopy, Function(node`LeafData`ToGold)(h))>, g)),
	    UserGenerators(node`NiceData`WordGroup))>;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;

	node`FindFactors := proc< ~node | SmallReeFactorData(~node)>;
	node`FindPresentation := proc< ~node | SmallReePresentation(~node)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;

	error Error(rec<LeafError | Description := "2G", Error := err>);
    end try;
end procedure;

function IsLargeReeNatRep(node)
    if Category(node`Group) eq GrpMat then
	F := CoefficientRing(node`Group);
    
	if Characteristic(F) eq 2 and Degree(node`Group) eq 26 and
	    #F gt 2  then
	    assert IsIdentity(node`Scalar);
	    return true;
	end if;
    end if;

    return false;
end function;

// No short presentation for large Ree so far
procedure LargeReePresentation(~node)
    pres, pres2G := FPGroup(node`NiceData`Group);
    relators := [LHS(r) * RHS(r)^(-1) : r in Relations(pres)];
    
    // Convert words to SLPs
    wordToSLP := hom<pres -> node`NiceData`WordGroup |
    node`SLPMaps`EltToSLPBatch(pres2G(UserGenerators(pres)))>;
    
    node`PresentationData := rec<PresentationInfo |
	SLPRelators := wordToSLP(relators)>;	
end procedure;

procedure LargeReeFactorData(~node, g2slp)
    coerce := LargeReeSLPCoercion(node`LeafData`GoldCopy);
    
    node`FactorData := rec<FactorInfo |
	FactorSLPs := [UserGenerators(node`NiceData`WordGroup)],
	ToFactor := [* node`LeafData`ToGold *],
	FactorToSLP := [* hom<node`LeafData`GoldCopy ->
    WordGroup(node`LeafData`GoldCopy) | g :->
	coerce(MembershipTesting(node, func<h |
	LargeReeElementToWord(node`LeafData`GoldCopy, h)>, g))> *],
	Refined := true, FactorLeaves := [node]>;
end procedure;
    
procedure LargeReeRecogNatRep(~node)
    try
	field := GF(Retrieve(node`LeafData`DefiningField));
	flag, iso, inv, g2slp, slp2g := RecogniseLargeRee(node`Group :
	Verify := false, FieldSize := #field);
    
        if not flag then
	    error ERROR_RECOGNITION;
	end if;

	stdCopy := LargeRee(field);
	
	node`LeafData`GoldCopy := stdCopy;
	node`LeafData`ToGold := hom<node`Group -> stdCopy |
	g :-> Function(iso)(g)>;
	node`LeafData`FromGold := hom<stdCopy -> node`Group |
	g :-> Function(inv)(g)>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

	// Note yet easy to find a presentation in this case
	node`FastVerify := false;
	
	// Obtain SLPs of nice generators in user generators
	coerce := LargeReeSLPCoercion(node`Group);
	niceSLPs := [coerce(elt)
	    where _, elt is LargeReeStandardConstructiveMembership(node`Group`
	    LargeReeReductionData`stdCopy, g : CheckInput := false,
	    wordGroup := node`Group`LargeReeReductionData`slpGroup,
	    Randomiser :=
	    node`Group`LargeReeReductionData`stdCopy`RandomProcess)
	    : g in UserGenerators(stdCopy)];
	
	// Use stdandard copy generators as nice generators 
	niceGroup := sub<Generic(node`Group) |
	    node`LeafData`FromGoldBatch(UserGenerators(stdCopy))>;
	assert #niceSLPs eq NumberOfGenerators(niceGroup);
	    
	node`NiceData := rec<NiceInfo |
	    Group := niceGroup,
	    WordGroup := WordGroup(niceGroup),
	    NiceSLPs := niceSLPs,
	    NiceToUser := hom<WordGroup(niceGroup) -> node`WordGroup |
	Evaluate(niceSLPs, UserGenerators(node`WordGroup))>,
	    NiceToUserBatch :=
	    func<seq | Evaluate(seq, niceSLPs)>>;

	flag, iso, inv, g2slpStd, slp2g := RecogniseLargeRee(stdCopy :
	    Verify := false, FieldSize := #field);

        if not flag then
	    error ERROR_RECOGNITION;
	end if;
	
	coerce := LargeReeSLPCoercion(stdCopy);
	assert NumberOfGenerators(WordGroup(stdCopy)) eq
	    NumberOfGenerators(node`NiceData`WordGroup);
	
	// Constructive membership testing with exception handling
	g2slp := hom<node`NiceData`Group -> node`NiceData`WordGroup | g :->
	Evaluate(coerce(MembershipTesting(node, func<h |
	    LargeReeElementToWord(stdCopy, Function(node`LeafData`ToGold)(h))>,
	    g)), UserGenerators(node`NiceData`WordGroup))>;
	
	node`SLPMaps := rec<SLPMapsInfo |
	    EltToSLP := g2slp,
	    EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	    SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
	UserGenerators(node`NiceData`Group)>,
	    SLPToEltBatch := func<slps |
	    Evaluate(slps, UserGenerators(node`NiceData`Group))>>;
	
	node`FindFactors := proc< ~node | LargeReeFactorData(~node, g2slpStd)>;
	node`FindPresentation := proc< ~node | LargeReePresentation(~node)>;
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;
	    
	error Error(rec<LeafError | Description := "2F", Error := err>);
    end try;
end procedure;

