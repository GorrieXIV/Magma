/******************************************************************************
 *
 *    involution.m  Ree group involution centraliser code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-05-08
 *
 *    Version   : $Revision:: 1784                                           $:
 *    Date      : $Date:: 2010-04-29 16:38:44 +1000 (Thu, 29 Apr 2010)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: involution.m 1784 2010-04-29 06:38:44Z jbaa004                 $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/
declare verbose ReeInvolution, 10;

declare attributes GrpMat : ReeInvolCentraliserData;

import "stab.m": getSL3Element;
import "../../../util/order.m" : IsProbablySL2;
import "../../../util/centraliser.m" : BrayAlgorithm;
import "../../../util/section.m" : MeatAxeMaps;
import "../../../util/basics.m" : MatSLP, getMapFunction;

forward isCentraliserComplete, isCentraliserCompleteLargeDeg;

ReeInvolCentraliserInfo := recformat<
    cbm : GrpMatElt,
    PointProj : Map,        // Projection from 7-dim to 3-dim space
    MatrixProj : Map,       // Projection from 7-dim to 3-dim group
    LargeSL2 : GrpMat,      // 7-dim PSL(2, q)
    SL2SLPs : SeqEnum,      // SLPs of 7-dim gens in gens of Ree group
    involution : GrpMatElt, // The centralised involution
    genSLPs : SeqEnum,      // SLPs of centraliser gens in gens of Ree group
    SmallSL2 : GrpMat,      // 3-dim PSL(2, q)
    largeToSmall : Map,     // 3-dim PSL to 2-dim PSL
    smallToLarge : Map,     // 2-dim PSL to 3-dim PSL
    slpHomoInv : Map,       // 3-dim PSL to SLP
    slpHomo : Map,          // SLP to 3-dim PSL
    conj : GrpMatElt,       // Extra conjugator to 3-dim symmetric square
    slpGroup : GrpSLP,      // Word group of Ree with SL2SLPs added
    SLPEval : Map,          // Evaluates SLPs from SmallSL2 on LargeSL2 gens
    SLPCoercion : Map,      // Evaluates SLPs from SmallSL2 on SL2SLPs
    sl2Time : FldReElt>;    // Time used by SL2 recognition

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeInvolutionCentraliser(G :: GrpMat, g :: GrpMatElt,
    slp :: GrpSLPElt : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true) -> GrpMat
    { G \leq GL(d, q) is isomorphic to Ree(q) and g is an involution in G,
    with slp being an SLP of g in the generators of G. Return the centraliser
    of g in G. }
    local centraliser, slpMap, completion;

    if CheckInput and not (ReeGeneralRecogniser(G) and IsIdentity(g^2) and
	not IsIdentity(g)) then
	error "Ree invol centraliser:",
	    "G must the a Ree group and g an involution";
    end if;

    vprint ReeInvolution, 2: "Input ok";
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if Degree(G) eq 7 then
	completion := isCentraliserComplete;
    else
	completion := isCentraliserCompleteLargeDeg;
    end if;

    assert IsCoercible(WordGroup(Randomiser), slp);
    centraliser, slpMap := BrayAlgorithm(G, g, slp :
	completionCheck := completion, Randomiser := Randomiser);
    assert forall{x : x in Generators(centraliser) | x * g eq g * x};
    
    if assigned centraliser`ReeInvolCentraliserData then
	centraliser`ReeInvolCentraliserData`genSLPs := slpMap;
	centraliser`ReeInvolCentraliserData`involution := g;
    end if;
    
    return centraliser;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function setupCentraliserData(centraliser, slpMap, G, H, H_slp, largeSL2,
    mproj, pproj, cbm)
	local flag, matrixProj, pointProj, field, V1, V2, conj, sl2SLPs,
	largeToSmall, smallToLarge, slpHomoInv, slpHomo, sl2SmallGens,
	smallSL2, MA, slpGroup, slpCoercion, sl2Time;
	
    field := CoefficientRing(centraliser);

    vprint ReeInvolution, 5: "Recognise PSL(2, q)";    
    sl2Time := Cputime();
    flag, largeToSmall, smallToLarge, slpHomoInv, slpHomo :=
	RecogniseSL2(H, #field);
    sl2Time := Cputime(sl2Time);
    vprint ReeInvolution, 5: "PSL(2, q) recognition done";    
    
    if not flag then
	return false;
    end if;

    // Add change of basis to make symmetric square structure visible
    assert assigned H`SL2Basis;
    
    matrixProj := Function(mproj);

    assert Generators(G) eq {matrixProj(x) : x in Generators(centraliser) |
	not IsIdentity(matrixProj(x))};
	
    vprint ReeInvolution, 5: "Get SL2 generators";
	
    // Get SLPs of PSL(2,q) in Ree group gens
    sl2SLPs := Evaluate(H_slp, slpMap);

    // Get 2x2 SL2 gens from 3x3 SL2 gens
    sl2SmallGens := [Function(largeToSmall)(H.i) :
	i in [1 .. NumberOfGenerators(H)]];

    // Natural representation of PSL(2,q)
    smallSL2 := sub<GL(2, field) | sl2SmallGens>;
    assert UserGenerators(smallSL2) eq sl2SmallGens;
    	
    vprint ReeInvolution, 5: "Get extra conjugator";
    
    MA := MatrixAlgebra(field, 2);
    flag, conj := IsSimilar(SymmetricSquare(MA ! (smallSL2.1^z)), H.1^y)
	where y is H`SL2Basis[4]^(-1) where z is H`SL2Basis[3];
    assert flag;
    
    if not forall{i : i in [1 .. NumberOfGenerators(smallSL2)] |
	conj * SymmetricSquare(MA ! (smallSL2.i^z)) * conj^(-1) eq H.i^y} 
	where y is H`SL2Basis[4]^(-1) where z is H`SL2Basis[3] then
	return false;
    end if;    
    
    vprint ReeInvolution, 5: "Create SLP homos";
    slpHomoLarge :=
	hom<Domain(slpHomo) -> largeSL2 | UserGenerators(largeSL2)>;
    
    slpGroup := Parent(sl2SLPs[1]);
    slpCoercion := hom<Domain(slpHomo) -> slpGroup | sl2SLPs>;

    V1 := VectorSpace(field, Degree(centraliser));
    V2 := VectorSpace(field, Degree(H));

    pointProj := hom<V1 -> V2 | [<x, V2 ! pproj((Domain(pproj) ! x))> :
    x in Basis(V1)]>;
    
    // Save calculations
    centraliser`ReeInvolCentraliserData :=
	rec<ReeInvolCentraliserInfo |
	MatrixProj := mproj,
	PointProj := pointProj,
	LargeSL2 := largeSL2,
	SL2SLPs := sl2SLPs,
	slpGroup := slpGroup,
	conj := Generic(H) ! conj,
	SLPEval := slpHomoLarge,
	SLPCoercion := slpCoercion,
	SmallSL2 := H,
	largeToSmall := largeToSmall,
	smallToLarge := smallToLarge,
	slpHomo := slpHomo,
	slpHomoInv := slpHomoInv,
	sl2Time := sl2Time,
	cbm := Generic(centraliser) ! cbm>;

    return true;
end function;

function isCentraliserCompleteLargeDeg(centraliser, ree, g, slpMap)
    local H;

    // As completion check, just check that we have PSL(2, q) as the
    // derived group
    if NumberOfGenerators(centraliser) gt 1 then
	H := DerivedGroupMonteCarlo(centraliser);
	if IsProbablySL2(H : Projective := true, ErrorProb := 2^(-20)) then
	    return true;
	end if;
    end if;
    
    return false;
end function;
    
function isCentraliserComplete(centraliser, ree, g, slpMap)
    local M, series, factors, cbm, H, field, L, flag, N, meatAxeData, G,
	derivedSLPs, largePSL, sl2SLPs;

    vprint ReeInvolution, 5: "Get composition series";

    field := CoefficientRing(centraliser);
    
    M := GModule(centraliser);
    series, factors, cbm := CompositionSeries(M);
    
    // Check that we have the full centraliser
    if not (#series eq 2 and forall{i : i in [1 .. #factors] |
	Dimension(factors[i]) in {3, 4}}) then
	return false;
    end if;

    vprint ReeInvolution, 5: "Get CBM to 3+4";

    // We want the 4-dim representation at the bottom
    if Dimension(series[1]) eq 3 then
	L := series[1];
	flag, N := HasComplement(M, L);
	assert flag;

	series := [N, M];
	factors := [N, M / N];

	cbm := ChangeOfBasisMatrix(centraliser, N);
    end if;

    vprint ReeInvolution, 5: "Get MeatAxe maps";
    
    // Get maps to irreducible representations
    meatAxeData, series, factors := MeatAxeMaps(centraliser :
	Factors := func<x | series, factors, cbm>, Filtration := false,
	FindForm := false);

    // Want 3-dim representation of PSL(2,q)
    if not exists(factorNr){i : i in [1 .. #meatAxeData] |
	Degree(meatAxeData[i]`image) eq 3} then
	return false;
    end if;
    assert factorNr eq 2;
    
    G := meatAxeData[factorNr]`image;
    
    vprint ReeInvolution, 5: "Get derived group";

    // Construct derived group, ie PSL(2,q)
    H, derivedSLPs := DerivedGroupMonteCarlo(G);
    if not IsAbsolutelyIrreducible(H) then
	return false;
    end if;

    // Get 7-dim generators of PSL(2,q)
    largePSL := sub<centraliser | meatAxeData[factorNr]`slpMap(derivedSLPs)>;

    // Get SLPs of PSL in word group of 7-dim rep
    sl2SLPs := meatAxeData[factorNr]`slpCoercion(derivedSLPs);

    assert Generators(H) eq
	{Function(meatAxeData[factorNr]`mproj)(x) : x in Generators(largePSL)};
    
    return setupCentraliserData(centraliser, slpMap, G, H, sl2SLPs,
	largePSL, 
	meatAxeData[factorNr]`mproj,
	meatAxeData[factorNr]`pproj, cbm);
end function;
