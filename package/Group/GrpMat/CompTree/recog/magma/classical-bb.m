/******************************************************************************
 *
 *    classical-bb.m  Composition Tree Classical groups black box Leaf Code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Peter Brooksbank and Henrik B��rnhielm
 *    Dev start : 2008-10-07
 *
 *    Version   : $Revision:: 3191                                           $:
 *    Date      : $Date:: 2016-05-16 18:35:13 +1000 (Mon, 16 May 2016)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: classical-bb.m 3191 2016-05-16 08:35:13Z eobr007               $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "centre.m" : C9Centre;
import "leaf.m" : MembershipTesting, LeafError,
    C9CenterMembership, C9Membership, C9Presentation, BuiltinMembership,
    LeafFactorData, MaxBSGSVerifyPermDegree;
import "recog.m" : LeafInfo, SLPMapsInfo, CTNodeInfo, NiceInfo,
    PresentationInfo, FactorInfo;
import "node.m" : ERROR_RECOGNITION, ERROR_RECOGNITION_CATCH;
import "comp-series.m" : PullbackCompFactors;
import "classical.m" : NonSimpleClassicalNames;
import "c9.m" : PerfectCheckElements;

import "../../reduce/parameters.m" :
    SLRybaParameters, SpRybaParameters, SURybaParameters;
import "../../reduce/reduce.m" : Reduction;

import "../../classical/recognition/standard.m" :
    SpChosenElements, SLChosenElements, SUChosenElements, SOChosenElements, PlusChosenElements, MinusChosenElements;
import "../../GrpMat/util/basics.m" : getMapFunction;
import "../../classical/classical.m" : ClassicalConstructiveRecognitionNatural;

import "../../classical/recognition/modules/basics.m": IsHandledByRecogniseSmallDegree;

forward ClassicalGeneralRecognition, ClassicalShortPresentation, GeneralSLPMaps, GeneralNiceData, SLNiceData, SLRecognition, SUShortPresentation, RecogniseClassicalSmallDegree, ClassicalSolveWrapper, SL2RecognitionBlackBox, ClassicalStandardGenerators;

FamilyTypes := AssociativeArray();
FamilyTypes["A"] := "SL";
FamilyTypes["B"] := "Omega";
FamilyTypes["C"] := "Sp";
FamilyTypes["D"] := "Omega+";
FamilyTypes["2A"] := "SU";
FamilyTypes["2D"] := "Omega-";

StandardCopyInfo := recformat<
    Creator : Intrinsic,
    RankToDim : UserProgram,
    Relators : UserProgram,
    StandardGenerators : UserProgram>;

StandardCopyData := AssociativeArray();

StandardCopyData["Sp"]  := rec<StandardCopyInfo |
    Creator := Sp,
    RankToDim := func<x | 2 * x>,
    StandardGenerators := SpChosenElements>;

StandardCopyData["SL"]  := rec<StandardCopyInfo |
    Creator := SL,
    RankToDim := func<x | x + 1>,
    StandardGenerators := SLChosenElements>;

StandardCopyData["SU"]  := rec<StandardCopyInfo |
    Creator := SU,
    RankToDim := func<x | x + 1>,
    StandardGenerators := SUChosenElements>;

StandardCopyData["Omega"]  := rec<StandardCopyInfo |
    Creator := Omega,
    RankToDim := func<x | 2 * x + 1>,
    StandardGenerators := SOChosenElements>;

StandardCopyData["Omega+"]  := rec<StandardCopyInfo |
    Creator := OmegaPlus,
    RankToDim := func<x | 2 * x>,
    StandardGenerators := PlusChosenElements>;

StandardCopyData["Omega-"]  := rec<StandardCopyInfo |
    Creator := OmegaMinus,
    RankToDim := func<x | 2 * x>,
    StandardGenerators := MinusChosenElements>;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function IsClassicalBB(node) 
    type := FamilyTypes[Retrieve(node`LeafData`Family)];
    G := node`Group;
    q := Retrieve(node`LeafData`DefiningField);
    d := StandardCopyData[type]`RankToDim(node`LeafData`LieRank);

    // EOB added these two lines to exploit Kantor-Seress 
    if type eq "SL" and d gt 2 and q eq 2 then
       return true;
    elif type eq "SL" and d eq 2 then
	return true;
    elif q eq 2 and Degree (G) in [d^2 - 2 .. d] then
        return true;
    elif IsHandledByRecogniseSmallDegree(G, type, d, 
	type eq "SU" select q^2 else q) then
	return true;
    elif (type in ["Omega-", "Omega", "Omega+", "SU", "Sp", "SL"] and q gt 2) then     
        return true;
    else
	return false;
    end if;
end function;

function ObtainRecogniserInput(ExtendedGroup, F, Name)
    vprint CompositionTree, 3 : "Decide if group is perfect";

    if not IsProbablyPerfect(ExtendedGroup :
	NumberRandom := PerfectCheckElements(ExtendedGroup)) then

        vprint CompositionTree, 3 : "Compute derived group";
	repeat
	    D, D_slps := DerivedGroupMonteCarlo(ExtendedGroup);
	    flag, name := LieType(D, Characteristic(F));
	until flag and name eq Name;
    else
	// Possibly remove duplicate generators in GrpPerm context
	if Category(ExtendedGroup) eq GrpPerm then
	    D := sub<Generic(ExtendedGroup) | {@ g : g in
		UserGenerators(ExtendedGroup) |
		g ne Identity(ExtendedGroup) @}>;
	else
	    D := ExtendedGroup;
	end if;
	
	gens := ChangeUniverse(UserGenerators(ExtendedGroup),
	    Generic(ExtendedGroup));
	    
	genMap := [Index(gens, g) : g in UserGenerators(D)];
	D_slps := UserGenerators(WordGroup(ExtendedGroup))[genMap];
    end if;
    
    return D, D_slps;
end function;

procedure BBClassicalFactorData(~node, center, genMapRev)
vprint CompositionTree, 1: "In BBClassicalFactorData";
    F := CoefficientRing(node`LeafData`GoldCopy);
    
    // Brute force for small exceptional cases
    if node`LeafData`Name in NonSimpleClassicalNames then 
// EOB May 2014 turned off the following 
//        or Characteristic(F) eq 2 and
//	not IsLinearGroup(node`LeafData`GoldCopy) then
	LeafFactorData(~node);
	return;
    end if;

    centerPC, phi := AbelianGroup(sub<Generic(node`Group) | center, node`Scalar>);
    centerProj, proj := quo<centerPC | phi(node`Scalar)>;
    
    series := CompositionSeries(centerProj);
    centerFactors := PullbackCompFactors(node`NiceData`Group,
	node`SLPMaps`EltToSLPBatch, phi * proj, series, #centerPC + 1);

    W := WordGroup(node`LeafData`GoldCopy);

    // Need membership testing in gold copy
    flag := ClassicalConstructiveRecognitionNatural(node`LeafData`GoldCopy);
    assert flag;
        
    // Delete identity generator
    delete node`LeafData`GoldCopy`UserGenerators;    
    stdSlps := node`LeafData`GoldCopy`ClassicalRecognitionData`slps;

    gold2slp := hom<node`LeafData`GoldCopy -> W |
    g :-> Evaluate(Evaluate(MembershipTesting(node, func<h |
	ClassicalElementToWord(node`LeafData`GoldCopy, h)>,
	g), stdSlps), UserGenerators(W))>;
    
    if IsTrivial(centerProj) then
	if IsTrivial(centerPC) then
	    slps := [UserGenerators(node`NiceData`WordGroup)];
	else
	    slps := [Prune(UserGenerators(node`NiceData`WordGroup))];
	end if;
	
	factors := [* node`LeafData`ToGold *];
	factor2slp := [* gold2slp *];
    else
	slps := Append(centerFactors`FactorSLPs,
	    Prune(UserGenerators(node`NiceData`WordGroup)));
	factors := Append(centerFactors`ToFactor, node`LeafData`ToGold);
	factor2slp := Append(centerFactors`FactorToSLP, gold2slp);
    end if;
        
    // Setup data about composition factors
    node`FactorData := rec<FactorInfo |
	FactorSLPs := slps,
	ToFactor := factors,
	FactorToSLP := factor2slp,
	Refined := true,
	FactorLeaves := [node : i in [1 .. #centerFactors`ToFactor + 1]]>;    
end procedure;

function ClassicalShortPresentation(G, W, d, F, genMap, genMapRev, g2slp, type)
    if type eq "SU" then
	assert IsEven(Degree(F));
	Fdef := sub<F | Degree(F) div 2>;
    else
	Fdef := F;
    end if;
    Q, relators := ClassicalStandardPresentation(type, d, #Fdef : Projective := true);
    return Evaluate(relators, [W.i : i in genMapRev]);	
end function;

procedure BBClassicalShortPresentation(~node, genMapRev,
    genMap, center, centerToSLP)
    d := Degree(node`LeafData`GoldCopy);
    
    type := FamilyTypes[Retrieve(node`LeafData`Family)];
    slps := ClassicalShortPresentation(
	node`NiceData`Group, node`NiceData`WordGroup, d,
	CoefficientRing(node`LeafData`GoldCopy),
	genMap, genMapRev, node`SLPMaps`EltToSLPBatch, type);

    if not IsTrivial(center) then
	// Center generator is at the end
	slps := C9Presentation(node`NiceData`Group, node`NiceData`WordGroup,
	    slps, NumberOfGenerators(node`NiceData`Group),
	    centerToSLP, node`Scalar);
    end if;

    node`PresentationData := rec<PresentationInfo |
	SLPRelators := slps>;    
end procedure;

function CsabaWrapper(G, gens, type, d, q, g)
    flag, slp := ClassicalRewrite(G, gens, type, d, q, g);

// EOB shoud not be needed 
/* 
if slp cmpne false then 
x := Evaluate (slp, gens);
if IsCentral (G, x * g^-1) eq false then
slp := false;
end if;
end if;
*/
    if slp cmpeq false then
	return false, _;
    else
        return true, slp;
    end if;
end function;

function SL2SLPMaps(node, ExtendedGroup, iso, center, genMap)
    d := Degree(Codomain(iso));
    F := CoefficientRing(Codomain(iso));
    q := #F;
    vprint CompositionTree, 6 : "SL2 SLP maps";

    // Need to recognise standard copy to obtain word map
    flag, _, _, g2slp := RecogniseSL2(node`LeafData`GoldCopy, q);
    assert flag;
    
    if #genMap lt #node`NiceData`NiceSLPs then
	assert not IsTrivial(center);
	n := NumberOfGenerators(node`NiceData`Group);
	assert node`NiceData`Group.n eq center.1;
	
	// We have a center generator
	gens := Prune(UserGenerators(node`NiceData`WordGroup));
    else
	gens := UserGenerators(node`NiceData`WordGroup);
    end if;

    // Test for membership, return word in standard gens
	GtoW := function(g)
	flag := SL2ElementToWord(ExtendedGroup, g);
	if flag then
	    return true, g2slp(Function(iso)(g));
	else
	    return false, _;
	end if;
    end function;
    
    g2slpProj := hom<ExtendedGroup -> node`NiceData`WordGroup |
	g :-> Evaluate(MembershipTesting(node, GtoW, g), gens)>;

    return iso, g2slpProj;
end function;

function GeneralSLPMaps(node, ExtendedGroup, stdGens,
    center, genMap, genMapRev, niceInputGens, type)
    d := Degree(node`LeafData`GoldCopy);
    F := CoefficientRing(node`LeafData`GoldCopy);
    
    if type eq "SU" then
	Fdef := sub<F | Degree(F) div 2>;
    else
	Fdef := F;
    end if;
    q := #Fdef;

    vprint CompositionTree, 6 : "Grey/black box SLP maps";
    
    // FIXME Why is this necessary?
    if type ne "SL" then
    //if not (type in {"SL","SU"})  then
	gens := stdGens;
    else
	gens := [i gt 0 select stdGens[i] else Identity(node`LeafData`GoldCopy) : i in genMapRev];
    end if;

    // projective iso to standard copy
    iso := hom<ExtendedGroup -> node`LeafData`GoldCopy | g :->
	 Evaluate(MembershipTesting(node, func<h |
	  CsabaWrapper(ExtendedGroup, niceInputGens, type, d, q, h)>, g), gens)>;
    
    // Projective membership testing
    g2slpProj := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	Evaluate(MembershipTesting(node, func<h |
	 CsabaWrapper(ExtendedGroup, niceInputGens, type, d, q, h)>, g),
	 [i gt 0 select node`NiceData`WordGroup.i else
	 Identity(node`NiceData`WordGroup) : i in genMapRev])>;
    
    return iso, g2slpProj;
end function;

// Setup nice generators for C9 classical group
// ExtendedGroup may include scalar flag, nice group is node group without
// scalar flag
// inv : gold copy -> (derived group of) ExtendedGroup 
// g2slp is word map for (derived group of) ExtendedGroup
// natCopy is gold copy on generators of (derived group of) ExtendedGroup
//
// niceInputGens are images in input copy of stdGens
procedure SL2NiceData(~node, ~niceInputGens,
    ExtendedGroup, inv, g2slp, stdGens, genMap)

    vprint CompositionTree, 5 : "Find nice generators";
    niceInputGens := [Generic(node`Group) | Function(inv)(g) : g in stdGens];
	
    niceSLPs := [Function(g2slp)(g) : g in niceInputGens];
    vprint CompositionTree, 5 : "Found SLPs of nice generators";
    
    // Remove scalar flag if necessary
    if NumberOfGenerators(ExtendedGroup) gt NumberOfGenerators(node`Group) then
	assert NumberOfGenerators(Universe(niceSLPs)) eq
	    NumberOfGenerators(node`WordGroup) + 1;
	
	niceSLPs := Evaluate(niceSLPs, Append(UserGenerators(node`WordGroup),
	    Identity(node`WordGroup)));
    else
	assert NumberOfGenerators(Universe(niceSLPs)) eq
	    NumberOfGenerators(node`WordGroup);
	
	niceSLPs := Evaluate(niceSLPs, UserGenerators(node`WordGroup));
    end if;
    
    // Remove duplicate generators in GrpPerm context
    niceGroup := sub<Generic(ExtendedGroup) | {@ g : g in niceInputGens |
	g ne Identity(node`Group) @}>;
    niceSLPs := niceSLPs[genMap];
    assert #niceSLPs eq NumberOfGenerators(niceGroup);
    
    node`NiceData := rec<NiceInfo |
	Group := niceGroup,
	WordGroup := WordGroup(niceGroup),
	NiceSLPs := niceSLPs,
	NiceToUser :=
	hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
    NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;

    vprint CompositionTree, 5 : "Found nice group";
end procedure;

// Combine projective word map for extended classical group with centre
// word map to obtain precise word map for ExtendedGroup
procedure ObtainPreciseSLPMaps(~node, ExtendedGroup,
    g2slpProj, center, centerMembership)
	
    // Constructive membership testing with exception handling
    if not IsTrivial(sub<Generic(center) | center, node`Scalar>) then
	g2slp := hom<ExtendedGroup -> node`NiceData`WordGroup | g :->
	C9Membership(node`NiceData`Group, g2slpProj, centerMembership, g)>;
    else
	g2slp := g2slpProj;
    end if;
    
    node`SLPMaps := rec<SLPMapsInfo |
	EltToSLP := g2slp,
	EltToSLPBatch := func<seq | [Function(g2slp)(g) : g in seq]>,
	SLPToElt := hom<node`NiceData`WordGroup -> node`NiceData`Group |
    UserGenerators(node`NiceData`Group)>,
	SLPToEltBatch := func<slps |
	Evaluate(slps, UserGenerators(node`NiceData`Group))>>;
end procedure;

// Assume node`NiceData has already been setup
// Find centre of node group and possibly add centre generators to nice group
// Also setup rewriting in centre
procedure ObtainCenter(~node, ~center, ~centerMembership)    
    // Add extra nice centre generator
    center, centerSLP := C9Centre(node`Group);
    
    if not IsTrivial(center) then
	n := NumberOfGenerators(node`NiceData`Group);
	node`NiceData`Group := sub<Generic(node`Group) |
	    node`NiceData`Group, center>;
	node`NiceData`WordGroup := WordGroup(node`NiceData`Group);
	
	if NumberOfGenerators(node`NiceData`Group) gt n then
	    Append(~node`NiceData`NiceSLPs, centerSLP);
	end if;
    end if;

    // Centre membership testing
    n := NumberOfGenerators(node`NiceData`WordGroup);
    centerMembership := hom<center -> node`NiceData`WordGroup | g :->
    Evaluate(MembershipTesting(node, func<h |
	C9CenterMembership(center, node`Scalar, h)>, g),
	[node`NiceData`WordGroup.n])>;

    niceGens := Evaluate(Prune(node`NiceData`NiceSLPs),
	UserGenerators(node`Group));
    centralElts := [niceGens[i] / node`NiceData`Group.i :
	i in [1 .. #niceGens]];
    
    // Patch nice slps so that they evaluate correctly to the nice generators
    if not IsTrivial(center) then
	patchSLPs := Evaluate([Function(centerMembership)(g) :
	    g in centralElts], node`NiceData`NiceSLPs);

	node`NiceData`NiceSLPs := Append([node`NiceData`NiceSLPs[i] *
	    patchSLPs[i]^(-1) : i in [1 .. #patchSLPs]],
	    node`NiceData`NiceSLPs[#node`NiceData`NiceSLPs]);
    else
	assert SequenceToSet(centralElts) eq {Identity(node`Group)};
    end if;

    node`NiceData`NiceToUser := hom<node`NiceData`WordGroup ->
    node`WordGroup | node`NiceData`NiceSLPs>;
    node`NiceData`NiceToUserBatch :=
	func<seq | Evaluate(seq, node`NiceData`NiceSLPs)>;
end procedure;

procedure NiceDataFromGens(~node, ~niceInputGens, ExtendedGroup,
    DerivedSLPs, stdGens, stdSLPs, genMap)
	
    assert NumberOfGenerators(Universe(stdSLPs)) in
	{#DerivedSLPs, 1 + #DerivedSLPs};

    // Obtain standard gens as words in input group with scalar
    if NumberOfGenerators(Universe(stdSLPs)) eq #DerivedSLPs + 1 then
	niceSLPs := Evaluate(stdSLPs, [Identity(Universe(DerivedSLPs))] cat
	    DerivedSLPs);
    else
	niceSLPs := Evaluate(stdSLPs, DerivedSLPs);
    end if;
    
    assert NumberOfGenerators(Universe(niceSLPs)) eq
	NumberOfGenerators(ExtendedGroup);
    niceInputGens := Evaluate(niceSLPs, UserGenerators(ExtendedGroup));

    // Remove duplicate generators in GrpPerm context
    niceGroup := sub<Generic(ExtendedGroup) | {@ g : g in niceInputGens |
	g ne Identity(node`Group) @}>;

    niceSLPs := niceSLPs[genMap];
    assert #niceSLPs eq NumberOfGenerators(niceGroup);

    // Remove scalar flag if necessary
    if NumberOfGenerators(ExtendedGroup) gt NumberOfGenerators(node`Group) then
	assert NumberOfGenerators(Universe(niceSLPs)) eq
	    NumberOfGenerators(node`WordGroup) + 1;
	
	niceSLPs := Evaluate(niceSLPs, Append(UserGenerators(node`WordGroup),
	    Identity(node`WordGroup)));
    else
	assert NumberOfGenerators(Universe(niceSLPs)) eq
	    NumberOfGenerators(node`WordGroup);
	
	niceSLPs := Evaluate(niceSLPs, UserGenerators(node`WordGroup));
    end if;

    node`NiceData := rec<NiceInfo |
	Group := niceGroup,
	WordGroup := WordGroup(niceGroup),
	NiceSLPs := niceSLPs,
	NiceToUser :=
	hom<WordGroup(niceGroup) -> node`WordGroup | niceSLPs>,
    NiceToUserBatch := func<seq | Evaluate(seq, niceSLPs)>>;    

    vprint CompositionTree, 5 : "Found nice data";    
end procedure;

procedure NiceDataFromNatCopy(~node, ~niceInputGens, ExtendedGroup,
    DerivedSLPs, natCopy, stdGens, genMap)
	
    vprint CompositionTree, 5 : "Find standard generators of natural copy";
    
    // Recognise natural copy on input gens to obtain standard gens as
    // words in input gens
    flag := ClassicalConstructiveRecognitionNatural(natCopy);
    if not flag then
	error ERROR_RECOGNITION;
    end if;

    vprint CompositionTree, 5 : "Obtain SLPs of standard generators";    
    stdSLPs := [];
    for g in stdGens do
	flag, slp := ClassicalElementToWord(natCopy, g);
	if not flag then
	    error ERROR_RECOGNITION;
	end if;

	Append(~stdSLPs, Evaluate(slp, natCopy`ClassicalRecognitionData`slps));
    end for;

    NiceDataFromGens(~node, ~niceInputGens, ExtendedGroup, DerivedSLPs, stdGens, stdSLPs, genMap);
end procedure;

procedure ClassicalRecogBlackBox(~node)
    try
	vprint CompositionTree, 2 : "Entering Classical C9 recognition";
	type := FamilyTypes[Retrieve(node`LeafData`Family)];
	d := StandardCopyData[type]`
	    RankToDim(node`LeafData`LieRank);
	q := Retrieve(node`LeafData`DefiningField);
	goldCopy := StandardCopyData[type]`Creator(d, q);

        if Type (node`Group)  eq GrpMat then 
           vprintf CompositionTree, 2 : "Parameters: type %o, field %o, dim %o, input dim %o, input field %o\n", type, q, d, Degree(node`Group), 
		#CoefficientRing(node`Group);
        else 
           vprintf CompositionTree, 2 : "Parameters: type %o, field %o, input perm group degree %o\n", type, q, d, Degree(node`Group); 
        end if;

	ExtendedGroup := sub<Generic(node`Group) | node`Group, node`Scalar>;
	vprint CompositionTree, 4 : "Setup standard copy";
	
	// Standard copy has no scalars	
	stdGens := ClassicalStandardGenerators(node);
	node`LeafData`GoldCopy := sub<Generic(Universe(stdGens)) | stdGens>;
        F := CoefficientRing(node`LeafData`GoldCopy);

	// Some standard generators might coincide
	genMap := [Index(stdGens, g) :
	    g in UserGenerators(node`LeafData`GoldCopy)];
	genMapRev :=
	    [Index(ChangeUniverse(UserGenerators(node`LeafData`GoldCopy),
	    Generic(node`LeafData`GoldCopy)), g) : g in stdGens];
		
	vprint CompositionTree, 4 :
	    "Entering black box classical constructive recognition";
	verify := node`Verify or
	    (Category(node`Group) eq GrpPerm and
	    Degree(node`Group) le MaxBSGSVerifyPermDegree);
	
	if type eq "SU" then
	    Fdef := sub<F | Degree(F) div 2>;
	else
	    Fdef := F;
	end if;
	Name := Retrieve(node`LeafData`Family);

        general_bb := true;
	if type eq "SL" and d eq 2 then
	    vprint CompositionTree, 3 : "Entering RecogniseSL2";
	    flag, iso, inv, g2slp := RecogniseSL2(ExtendedGroup, #F);
	    if not flag then
		error ERROR_RECOGNITION;
	    end if;
	    SL2NiceData(~node, ~niceInputGens, ExtendedGroup,
			inv, g2slp, stdGens, genMap);
            general_bb := false;
	elif Category(ExtendedGroup) eq GrpMat and 
            IsDivisibleBy(#F, Characteristic(CoefficientRing(ExtendedGroup))) and
            IsHandledByRecogniseSmallDegree(ExtendedGroup, type, d, #F) then
	    D, DerivedSLPs := ObtainRecogniserInput(ExtendedGroup, Fdef, 
			node`LeafData`Name);
	    vprint CompositionTree, 3 : "Entering small degree recognition";
	    flag, iso := RecogniseClassicalSmallDegree(D, 
			node`LeafData`GoldCopy, d, #Fdef, type);
	   if not flag and #Fdef eq 2 then 
	   	error ERROR_RECOGNITION;
           end if;

            if flag then 
               general_bb := false;
   	       natCopy := sub<Generic(node`LeafData`GoldCopy) | [Function(iso)(g) :
		g in UserGenerators(Domain(iso))]>;
	        NiceDataFromNatCopy(~node, ~niceInputGens, ExtendedGroup, 
				DerivedSLPs, natCopy, stdGens, genMap);
            end if;
	    
        end if;

        // EOB -- Brian's code may fail for certain repns 
        // if q > 2 then try to apply general function 
        if general_bb then 
	    D, DerivedSLPs := ObtainRecogniserInput(ExtendedGroup, Fdef, 
						    node`LeafData`Name);

	    vprint CompositionTree, 3 : "Entering ClassicalSolve";
	    flag, gens, slps := Internal_ClassicalSolve(D, type, d, #Fdef);
	    vprint CompositionTree, 3 : "ClassicalSolve finished";
	    if not flag then
		error ERROR_RECOGNITION;
	    end if;

	    NiceDataFromGens(~node, ~niceInputGens, ExtendedGroup, 
				DerivedSLPs, stdGens, slps, genMap);
	end if;
			
	vprint CompositionTree, 4 : "Find center";
	ObtainCenter(~node, ~center, ~centerMembership);

	node`FastVerify := true;
	
	vprint CompositionTree, 4 : "Setup SLP maps";
	if type eq "SL" and d eq 2 then
	    iso, g2slpProj := SL2SLPMaps(node, ExtendedGroup, iso, center, genMap);
	else
	    iso, g2slpProj := GeneralSLPMaps(node, ExtendedGroup, stdGens, 
		center, genMap, genMapRev, niceInputGens, type);
	end if;

	ObtainPreciseSLPMaps(~node, ExtendedGroup,
	    g2slpProj, center, centerMembership);
	
	vprint CompositionTree, 4 : "Setup gold copy maps";
	        
	node`LeafData`ToGold := hom<ExtendedGroup -> node`LeafData`GoldCopy |
	g :-> Generic(node`LeafData`GoldCopy) ! Function(iso)(g)>;

	// We currently don't bother with the inv map. 
	// We could set it up with an extra classical solve in the gold copy.
	// But this is otherwise unnecessary in the main ClassicalSolve case.
	node`LeafData`FromGold := hom<node`LeafData`GoldCopy -> ExtendedGroup |
	g :-> Generic(ExtendedGroup) ! Function(iso)(g)>;
	node`LeafData`FromGoldBatch :=
	    func<seq | [Function(node`LeafData`FromGold)(g) : g in seq]>;
	node`LeafData`ToGoldBatch :=
	    func<seq | [Function(node`LeafData`ToGold)(g) : g in seq]>;

        // change by EOB -- set up order and factored order 
        f := FactoredClassicalGroupOrder(ClassicalType(node`LeafData`GoldCopy),
            Degree(node`LeafData`GoldCopy),
            CoefficientRing(node`LeafData`GoldCopy));
	// Order attribute can now be a factorisation
        AssertAttribute (node`LeafData`GoldCopy, "Order", f);
	
	node`FindFactors := proc< ~node |
	    BBClassicalFactorData(~node, center, genMapRev)>;
	node`FindPresentation := proc< ~node |
	    BBClassicalShortPresentation(~node,
	    genMapRev, genMap, center, centerMembership)>;

	vprint CompositionTree, 2 : "Classical black box leaf case finished";
    catch err
	if err`Object cmpeq ERROR_RECOGNITION_CATCH then
	    error ERROR_RECOGNITION;
	end if;
	
	error Error(rec<LeafError | Description := "Classical black box", 
	    Error := err>);
    end try;
end procedure;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function ClassicalStandardGenerators(node)
    type := FamilyTypes[Retrieve(node`LeafData`Family)];
    d := StandardCopyData[type]`RankToDim(node`LeafData`LieRank);
    q := Retrieve(node`LeafData`DefiningField);
    goldCopy := StandardCopyData[type]`Creator(d, q);
        
    return ChangeUniverse(StandardCopyData[type]`
	StandardGenerators(goldCopy), Generic(goldCopy));
end function;

function SL2RecognitionBlackBox(G, S)
    d := Degree(S);
    F := CoefficientRing(S);
    assert d eq 2;

    vprint CompositionTree, 3 : "Entering SL2 Recognition";
    flag, isoF, invF, g2slp := RecogniseSL2(G, #F);
    if flag then
	gensS := SLChosenElements(S);
	gens := [Function(invF)(g) : g in gensS];
	slps := [Function(g2slp)(g) : g in gens];
	return true, gens, slps, g2slp, UserGenerators(WordGroup(G));
    end if;
end function;

function RecogniseClassicalSmallDegree(G, S, d, q, type)
    vprint CompositionTree, 5 : "Entering RecogniseSmallDegree";
    vprintf CompositionTree, 5 : "Parameters d=%o, q=%o, Degree %o, field size %o, type %o\n", d, q, Degree(G), #CoefficientRing(G), type;
    // flag, H := RecogniseSmallDegree(G, type, d, q: FormTrial := 10^3);
    flag, H := RecogniseSmallDegree(G, type, d, q: Hard := false);
    
    if flag then
        vprint CompositionTree, 5 : "RecogniseSmallDegree succeeded";
	if IsLinearGroup(H) then
	    cbm := Identity(H);
	else
	    cbm := TransformForm(H) * TransformForm(S)^(-1);
	end if;
	iso := hom<G -> S | g :-> w^cbm where _, w := SmallDegreePreimage(G, g)>;

	// No good inv map in this case, but we won't need it!
	return true, iso, iso;
    else
        vprint CompositionTree, 5 : "RecogniseSmallDegree failed";
	return false, _, _;
    end if;
end function;
