/******************************************************************************
 *
 *    base.m   Kay Magaard's algorithm for G2 and 3D4
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2007-10-14
 *
 *    Version   : $Revision:: 2871                                           $:
 *    Date      : $Date:: 2014-11-02 10:06:36 +1100 (Sun, 02 Nov 2014)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: base.m 2871 2014-11-01 23:06:36Z jbaa004                       $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare attributes Grp : BaseGroupData;

import "g2.m" : G2pElement;

import "../../sl3q/sl3.m" : GetSL2Tester, IsSLGrey, 
    LabelToElement, SLRecogniserGeneral, SL2RootGroups,
    GetSL2Recogniser;
import "../../util/basics.m" : getMapFunction, EltSLP, DiagonaliseMatrix;
import "../../util/chevalley-order.m" : ClassicalCentreOrder;
import "../../util/order.m" : 
    RandomInvolution, IsProbablySL2;
import "../../util/comptree.m" : CTRecogniseSL2, CTRecogniseSL3, SL2pElement;

forward SetupGroups;

ELabelling := recformat<
    root : ModTupFldElt,
    YGroup : GrpMat,
    XGroup : GrpMat,
    labelling : Map,
    SLPLabelling : Map,
    inverseLabelling : Map,
    Nconj : Rec,
    conjRoot : ModTupFldElt,
    FSpace : ModTupFld,
    FSpaceInc : Map>;

// Data stored for root groups
RootGroupInfo := recformat<
    Group : Grp, 
    SLPs : SeqEnum, // SLPs of gens in input gens
    Label : UserProgram, // Field element -> Group element
    LabelSLP : UserProgram, // Field element -> SLP of group element
    InvLabel : UserProgram // Group element -> Field element
    >;

/*
EData := recformat<
    group : GrpMat,
    small : GrpMat,
    iso : Map,
    inv : Map,
    g2slp : UserProgram,
    slps : SeqEnum>;
*/

// Data stored for SL's found
SLInfo := recformat<
    iso : Map,
    inv : Map,
    g2slp : UserProgram
    >;

BaseGroupInfo := recformat<
    Group : Grp,
    RandomProcess : GrpRandProc,
    WordGroup : GrpSLP,
    StdCopy : GrpMat,
    DefiningField : FldFin,
    SLDataL : Rec,
    SLDataS : Rec,
    SLDataC : Rec,
    LongRoots : SetIndx,
    ShortRoots : SetIndx,
    RootIndices : Assoc, // Indices in root system
    StdLongRootIndices : Assoc, // Indices in standard matrices of SL3
    StdShortRootIndices : Assoc, // Indices in standard matrices of SL2
    RootGroupData : SeqEnum,
    RootDataIdx : Assoc, // Indices in RootGroupData
    ShortRootConj : Assoc,
    LieCopy : GrpLie,
    // 1 = G2, 3 = 3D4
    epsilon : RngIntElt,
    // defining field
    field : FldFin,
    // root lattice
    rootSpace : ModTupFld,
    // chosen short root
    alpha : ModTupFldElt,
    // chosen long root
    beta : ModTupFldElt,
    // initial involution, EltSLP
    invol : Rec,
    // long root SL3, EData
    C : Rec,
    // long root SL2, EData
    L : Rec,
    // short root SL3, EData
    S : Rec,
    longRoots : SetIndx,
    shortRoots : SetIndx,
    // torus in C, normalises L, EData
    T : Rec,
    // Weyl group elements in C, EData
    N : Rec,
    // hash with longRoots -> ELabelling
    longLabels : Assoc,
    // hash with shortRoots -> ELabelling
    shortLabels : Assoc,
    // conjugates C into block diagonal form where L is visible
    C_conj : GrpMatElt>;

// Internal errors 
ERROR_ROOTGROUPS := "RootGroupError";
ERROR_SL         := "SLError";
ERROR_BOREL      := "BorelError";
ERROR_INPUT      := "NotExceptionalError";
ERROR_MEMBERSHIP := "MembershipError";
ERROR_INVOLUTION := "InvolutionError";

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

procedure CheckRootGroups(data, T)
    F := data`DefiningField;
    RootIdx := func<root | data`RootDataIdx[root]>;

    print data`LongRoots, data`ShortRoots;
    
    for root in data`LongRoots join data`ShortRoots do
	print "Checking root", root;
	Y := data`RootGroupData[RootIdx(root)]`Group;
	assert #Y eq #F;
	labels := {data`RootGroupData[RootIdx(root)]`Label(x) : x in Y};
	assert #labels eq #F;

	elts := {data`RootGroupData[RootIdx(root)]`InvLabel(x) : x in F};
	assert sub<Generic(data`Group) | elts> eq Y;

	slps := [data`RootGroupData[RootIdx(root)]`LabelSLP(x) : x in F];
	assert SequenceToSet(Evaluate(slps, UserGenerators(data`Group)))
	    eq {g : g in Y};
	
	inv := data`RootGroupData[RootIdx(root)]`InvLabel;
	iso := data`RootGroupData[RootIdx(root)]`Label;
	assert forall{g : g in Y | inv(iso(g)) eq g};
    end for;

    for root in data`LongRoots do
	Y := data`RootGroupData[RootIdx(root)]`Group;
	assert forall{g : g in T | Y^g eq Y};
    end for;
end procedure;

intrinsic testExceptionals(p :: RngIntElt, n :: RngIntElt) -> BoolElt
    { }

    SetVerbose("Exceptional", 5);
    SetVerbose("UserUtil", 5);
    SetVerbose("CompositionTree", 0);
    //SetVerbose("G2SL2", 2);
    F := GF(p, n);
    //G := ChevalleyGroup("3D", 4, F);
    
    epsilon := 1;

    H := G2(F);
    
    // Input copy
    G := RandomConjugate(H);    
    flag := RecogniseG2(G, F : Verify := true);

    return true;
end intrinsic
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic RecogniseG2(G :: Grp, F :: FldFin : Verify := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map
    { }

    try
	return SetupGroups(G, F, Randomiser, 1, Verify);
    catch err
	print err;
	if Category(err`Object) eq MonStgElt and err`Object in
	    {ERROR_SL, ERROR_ROOTGROUPS, ERROR_INPUT, ERROR_BOREL} then
	    return false, _, _, _, _;
	end if;

	error err;
    end try;
end intrinsic;

intrinsic Recognise3D4(G :: Grp, F :: FldFin : Verify := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map
    { }

    try
	return SetupGroups(G, F, Randomiser, 3, Verify);
    catch err
	if Category(err`Object) eq MonStgElt and err`Object in
	    {ERROR_SL, ERROR_ROOTGROUPS, ERROR_INPUT, ERROR_BOREL} then
	    return false, _, _, _, _;
	end if;

	error err;
    end try;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function LabelToSLP(data, root, label)
    return LabelToElement(label,
	data`RootGroupData[data`RootDataIdx[root]]`SLPs);
end function;

function LabelToInput(data, root, label)
    return LabelToElement(label,
	UserGenerators(data`RootGroupData[data`RootDataIdx[root]]`Group));
end function;

// Find standard matrix copy from group of Lie type
function ConstructStandardCopy(F, epsilon)
    // Only G_2 and 3D_4 supported here
    assert epsilon in {1, 3};
    
    if epsilon eq 1 then
	G := SimpleGroupOfLieType("G", 2, F : Isogeny := "SC");
	R := RootDatum(G);
    else
	FF := ext<F | 3>;
	R := RootDatum("D4" : Twist := 3, Isogeny := "SC");
	G := TwistedGroupOfLieType(R, F, FF);
	//G := ChevalleyGroup("3D", 4, FF);
	//G := SimpleGroupOfLieType("D", 4, F : Isogeny := "SC");
	//R := RootDatum(G);
    end if;

    L := RootSpace(R);
    simples := [L ! x : x in RowSequence(SimpleRoots(R))];

    found := false;
    for a in simples do
	for b in simples do
	    if IsLongRoot(R, RootPosition(R, b)) and
		IsShortRoot(R, RootPosition(R, a)) and
		IsShortRoot(R, RootPosition(R, a + b)) and
		IsShortRoot(R, RootPosition(R, 2 * a + b)) and
		IsLongRoot(R, RootPosition(R, 3 * a + b)) and
		IsLongRoot(R, RootPosition(R, 3 * a + 2 * b)) then
		alpha := a;
		beta := b;
		found := true;
		break;
	    end if;
	end for;

	if found then
	    break;
	end if;
    end for;
    assert found;
    
    return G, alpha, beta;
end function;

function InitialiseRecognition(G, F, Randomiser, epsilon)
    S, alpha, beta := ConstructStandardCopy(F, epsilon);
	
    FF := CoefficientRing(S);
    n := Degree(FF);

    // Defining field
    assert IsDivisibleBy(n, epsilon);
    F1 := sub<FF | n div epsilon>;
    assert F1 eq F;
    q := #F1;
    assert q^epsilon eq #FF;

    rep := StandardRepresentation(S);
    stdCopy := sub<Generic(Codomain(rep)) | rep(UserGenerators(S))>;
    
    data := rec<BaseGroupInfo |
	Group := G,
	WordGroup := WordGroup(G),
	StdCopy := stdCopy,
	RandomProcess := Randomiser,
	DefiningField := F,
	epsilon := epsilon,
	alpha := alpha,
	beta := beta,
	LieCopy := S,
	LongRoots := {@ beta, -beta, beta + 3 * alpha, -(beta + 3 * alpha),
	2 * beta + 3 * alpha, -(2 * beta + 3 * alpha) @},
	ShortRoots := {@ alpha, -alpha, alpha + beta, -(alpha + beta),
	2 * alpha + beta, -(2 * alpha + beta) @}
	>;

    StdLongRootIndices := AssociativeArray();
    StdLongRootIndices[beta] := [1, 2];
    StdLongRootIndices[-beta] := [2, 1];
    StdLongRootIndices[beta + 3 * alpha] := [2, 3];
    StdLongRootIndices[-(beta + 3 * alpha)] := [3, 2];
    StdLongRootIndices[2 * beta + 3 * alpha] := [1, 3];
    StdLongRootIndices[-(2 * beta + 3 * alpha)] := [3, 1];

    StdShortRootIndices := AssociativeArray();
    StdShortRootIndices[beta + 2 * alpha] := [1, 2];
    StdShortRootIndices[-(beta + 2 * alpha)] := [2, 1];
    
    RootIndices := AssociativeArray();
    for root in data`LongRoots join data`ShortRoots do
	RootIndices[root] := RootPosition(S, root);
    end for;

    RootDataIdx := AssociativeArray();
    i := 1;
    for root in data`LongRoots join data`ShortRoots do
	RootDataIdx[root] := i;
	i +:= 1;
    end for;
    
    data`StdLongRootIndices := StdLongRootIndices;
    data`StdShortRootIndices := StdShortRootIndices;
    data`RootIndices := RootIndices;
    data`RootDataIdx := RootDataIdx;
    
    return data;
end function;

function ConstructInvolution(data, epsilon)
    F := data`DefiningField;
    q := #F;
    
    vprint Exceptional, 2 : "Find element of even order";

    // Use special trick to find involutions in G2 if char = 2
    if Characteristic(F) eq 2 and epsilon eq 1 then
	invol, slp := G2pElement(data`Group, q);
    else
	if epsilon eq 1 then
	    flag, invol, slp := RandomElementOfOrder(data`Group, 2 :
		Randomiser := data`RandomProcess, Proof := false);
	else
	    flag, invol, slp := RandomElementOfOrder(data`Group, 2 * (#F + 1) :
		Randomiser := data`RandomProcess, Proof := false);
	end if;
    end if;

    vprint Exceptional, 2 : "Find involution from even order element";

    flag, power := PrimeOrderElement(invol, 2);
    error if not flag, ERROR_INVOLUTION;
    
    return rec<EltSLP | elt := invol^power, slp := slp^power>;
end function;

/*
function getSLPMap(X, W)
    coerce := CompositionTreeNiceToUser(X`group);
    slpEval := coerce * hom<WordGroup(X`group) -> W | X`slps>;
    
    return func<x | slpEval(w) where _, w is
	CompositionTreeElementToWord(X`group, x)>;
end function;

procedure RecogniseCSL(~groupData, W, C, C_slps, L, L_slps, S, S_slps)
    
    // Save group gens and SLPs in A-gens
    groupData`C := rec<EData | group := C, slps := C_slps>;
    groupData`L := rec<EData | group := L, slps := L_slps>;
    groupData`S := rec<EData | group := S, slps := S_slps>;

    q := #groupData`field;
    
    // Recognise groups using Comp Tree
    flag, groupData`C`iso, groupData`C`inv :=
	RecogniseSL3(groupData`C`group, q);
    assert flag;
    
    flag, groupData`L`iso, groupData`L`inv :=
	RecogniseSL2(groupData`L`group, q);
    assert flag;
    
    flag, groupData`S`iso, groupData`S`inv :=
	RecogniseSL2(groupData`S`group, q);
    assert flag;
    
    // Setup SLP maps
    groupData`C`g2slp := getSLPMap(groupData`C, W);
    groupData`L`g2slp := getSLPMap(groupData`L, W);
    groupData`S`g2slp := getSLPMap(groupData`S, W);
end procedure;
*/

function blockDiagonalise(G : OrderFactors := func<l | l>)

    V := VectorSpace(G);
    M := GModule(G);
    factors := OrderFactors(CompositionFactors(M));
    homos := [GHom(f, M) : f in factors];
    assert forall{h : h in homos | Dimension(h) eq 1};
        
    basis := &cat[[V ! (x * Morphism(X, M)) :
	x in Basis(X)] where X is Image(homo.1) : homo in homos];
    cbm := Matrix(CoefficientRing(G), Degree(G), Degree(G), basis);
    return Generic(G) ! cbm^(-1);
end function;

/*
function compoundElementLabel(G, g, r)
    F := G`BaseGroupData`field;
    q := #F;
    alpha := G`BaseGroupData`alpha;
    beta := G`BaseGroupData`beta;
    
    z := Function(G`BaseGroupData`longLabels[r]`inverseLabelling)(F ! 1);
    
    zz := Function(G`BaseGroupData`longLabels[-beta]`inverseLabelling)(F ! 1);
    traceT := Function(G`BaseGroupData`longLabels[beta +
	3 * alpha]`labelling)(((g, z), zz));
    
    zz := Function(G`BaseGroupData`longLabels[beta]`inverseLabelling)(F ! 1);
    traceTT := Function(G`BaseGroupData`longLabels[2 * beta +
	3 * alpha]`labelling)(((g, z), zz));

    z1 := Function(G`BaseGroupData`longLabels[2 * beta +
	3 * alpha]`inverseLabelling)(traceT);
    z2 := Function(G`BaseGroupData`longLabels[beta +
	3 * alpha]`inverseLabelling)(traceTT);
    tt := Function(G`BaseGroupData`shortLabels[beta +
	2 * alpha]`labelling)((g, z) * z1^(-1) * z2^(-1));

    if G`BaseGroupData`epsilon eq 1 then
	if q mod 3 ne 0 then
	    t := traceT div 3;
	else
	    t := tt div 2;
	end if;
    else
	error "not G2";
    end if;

    return t;
end function;
*/

/*
function labelUnipotentElement(G, g)
    F := G`BaseGroupData`field;
    q := #F;
    alpha := G`BaseGroupData`alpha;
    beta := G`BaseGroupData`beta;
    
    // FIXME : This ignores signs

    labels := [];
    z := Function(G`BaseGroupData`longLabels[beta +
	3 * alpha]`inverseLabelling)(F ! 1);
    t := Function(G`BaseGroupData`longLabels[2 * beta +
	3 * alpha]`labelling)((g, z));

    Append(~labels, <beta, t>);
    g1 := (Function(G`BaseGroupData`longLabels[beta]`
	inverseLabelling)(t))^(-1) * g;
    
    Append(~labels, <alpha, compoundElementLabel(G, g1, alpha + beta)>);
    g2 := (Function(G`BaseGroupData`longLabels[labels[#labels][1]]`
	inverseLabelling)(labels[#labels][2]))^(-1) * g1;

    z := Function(G`BaseGroupData`longLabels[beta]`inverseLabelling)(F ! 1);
    t := Function(G`BaseGroupData`longLabels[2 * beta +
	3 * alpha]`labelling)((g2, z));

    Append(~labels, <beta + 3 * alpha, t>);
    g3 := (Function(G`BaseGroupData`longLabels[beta + 3 * alpha]`
	inverseLabelling)(t))^(-1) * g2;

    Append(~labels, <alpha + beta, compoundElementLabel(G, g3, alpha)>);
    
    g4 := (Function(G`BaseGroupData`shortLabels[labels[#labels][1]]`
	inverseLabelling)(labels[#labels][2]))^(-1) * g3;
    
    z := Function(G`BaseGroupData`longLabels[-beta]`inverseLabelling)(F ! 1);
    t := Function(G`BaseGroupData`longLabels[2 * beta +
	3 * alpha]`labelling)((g4, z));

    Append(~labels, <2 * beta + 3 * alpha, t>);
    g5 := (Function(G`BaseGroupData`longLabels[2 * beta + 3 * alpha]`
	inverseLabelling)(t))^(-1) * g4;

    t := Function(G`BaseGroupData`shortLabels[beta +
	2 * alpha]`labelling)(g5);
    Append(~labels, <beta + 2 * alpha, t>);
    
    return labels;
end function;

function labelBorelElement(G, g)
    C := G`BaseGroupData`C`group;
    C_slps := G`BaseGroupData`C`slps;
    L3 := Codomain(C`SLData`iso);
    F := CoefficientRing(L3);
    alpha := G`BaseGroupData`alpha;
    beta := G`BaseGroupData`beta;
    conj := G`BaseGroupData`C_conj;

    // h_alpha ?
    z := Function(G`BaseGroupData`shortLabels[alpha]`inverseLabelling)(F ! 1);
    ha := Function(G`BaseGroupData`shortLabels[alpha]`labelling)((g, z));

    // h_beta ?
    z := Function(G`BaseGroupData`longLabels[beta]`inverseLabelling)(F ! 1);
    hb := Function(G`BaseGroupData`longLabels[beta]`labelling)((g, z));
    
    torus_elts := [Generic(L3) | DiagonalMatrix(F, [ha, 1, ha^(-1)]),
	DiagonalMatrix(F, [1, hb, hb^(-1)])];
    
    torus_big := [getMapFunction(C`SLData`inv *
	C`SLData`smallToLarge)(x^(conj^(-1))) : x in torus_elts];
    
    labels := [* [<torus_big[1], ha>, <torus_big[2], hb>],
	labelUnipotentElement(G, (&* torus_big)^(-1) * g) *];

    return labels;
end function;
*/

// h and n as in Carter
function ElementN(data, root, lambda)
    return [<-root, lambda>, <root, -lambda^(-1)>, <-root, lambda>];
    //return LabellingToInput(data, labelling), labelling;
end function;

function ElementH(data, root, lambda)
    label1 := ElementN(data, root, lambda);
    label2 := ElementN(data, root, Parent(lambda) ! -1);
    
    return label1 cat label2;
end function;

// Obtain gold copy element defined by labelling
function LabellingToSL3(data, labelling)
    S := Codomain(data`SLDataC`iso);
    MS := MatrixAlgebra(CoefficientRing(S), Degree(S));

    return Generic(S) ! &*[One(MS) + label[2] * MatrixUnit(MS, idx[1], idx[2])
	where idx is data`StdLongRootIndices[label[1]] : label in labelling];
end function;

// Obtain SLP of element defined by labelling
function LabellingToSLP(data, labelling)
    return &*[data`RootGroupData[data`RootDataIdx[label[1]]]`
	LabelSLP(label[2]) : label in labelling];
end function;

// Obtain input copy element defined by labelling
function LabellingToInput(data, labelling)
    return &*[data`RootGroupData[data`RootDataIdx[label[1]]]`
	InvLabel(label[2]) : label in labelling];
end function;

function ModifyIsomorphismSL2(data, T)
    L2 := Domain(data`SLDataS`inv);
    F := data`DefiningField;
    p := Characteristic(F);
    q := #F;
    
    assert forall{g : g in UserGenerators(T) | Order(g) eq q - 1};

    vprint Exceptional, 3 : "Find T meet S";
    
    // find image of T meet S in standard copy of S
    TS := sub<T | T.1 * T.2>;
    T2 := sub<Generic(L2) | [Function(data`SLDataS`iso)(x) :
	x in Generators(TS)]>;
    assert not IsIrreducible(T2);
    
    conj := blockDiagonalise(T2);

    // From standard copy of S to G, make sure root groups are T-invariant
    iso := hom<Domain(data`SLDataS`iso) ->
    Codomain(data`SLDataS`iso) | g :-> Function(data`SLDataS`iso)(g)^conj>;
    
    inv := hom<Domain(data`SLDataS`inv) ->
    Codomain(data`SLDataS`inv) | g :->
	Function(data`SLDataS`inv)(g^(conj^(-1)))>;
    return iso, inv;
end function;

procedure ConstructShortRootGroups(~data, N)
    F := data`DefiningField;
    standardRootGroups := SL2RootGroups(F);

    for root in data`ShortRoots do
	Append(~data`RootGroupData, rec<RootGroupInfo | >);
    end for;
    
    RootIdx := func<root | data`RootDataIdx[root]>;
    alpha := data`alpha;
    beta := data`beta;

    // short roots that we can label directly
    roots := {@ beta + 2 * alpha, -(beta + 2 * alpha) @};
    
    vprint Exceptional, 3 : "Find short root groups from Sylow subgroups of S";
    indices := [<2, 1>, <1, 2>];
   
    for i in [1 .. #standardRootGroups] do
	data`RootGroupData[RootIdx(roots[i])]`Group :=
	    sub<Generic(data`Group) | [Function(data`SLDataS`inv)(g) :
	    g in UserGenerators(standardRootGroups[i])]>;
	data`RootGroupData[RootIdx(roots[i])]`SLPs := data`SLDataS`g2slp(
	    UserGenerators(data`RootGroupData[RootIdx(roots[i])]`Group));
	assert #data`RootGroupData[RootIdx(roots[i])]`SLPs eq Degree(F);
	assert NumberOfGenerators(data`RootGroupData[RootIdx(roots[i])]`Group)
	    eq Degree(F);
	
	idx := indices[i];	
	data`RootGroupData[RootIdx(roots[i])]`InvLabel := func<a |
	    LabelToInput(data, roots[i], a)>;
	data`RootGroupData[RootIdx(roots[i])]`Label :=
	    func<g | Function(data`SLDataS`iso)(g)[idx[1], idx[2]]>;
	
	data`RootGroupData[RootIdx(roots[i])]`LabelSLP := func<a | 
	    LabelToSLP(data, roots[i], a)>;
    end for;
        
    // Swap sign if necessary
    y := data`RootGroupData[RootIdx(2 * beta + 3 * alpha)]`InvLabel(F ! 1);
    if forall{g : g in UserGenerators(data`RootGroupData[
	RootIdx(-(beta + 2 * alpha))]`Group) | IsIdentity((y, g))} then
	SwapElements(~data`RootGroupData, RootIdx(beta + 2 * alpha),
	    RootIdx(-(beta + 2 * alpha)));
    end if;
    
    vprint Exceptional, 3 : "Found first two short root groups";

    // long root groups that the short group commutes with
    commutingLongRoots := {@ {-beta, 2 * beta + 3 * alpha,
	-2 * beta - 3 * alpha, beta + 3 * alpha},
	{beta, 2 * beta + 3 * alpha, -2 * beta - 3 * alpha,
	-beta - 3 * alpha}, {beta, 2 * beta + 3 * alpha, -beta - 3 * alpha,
	beta + 3 * alpha}, {-2 * beta - 3 * alpha, -beta - 3 * alpha,
	beta + 3 * alpha, -beta} @};

    // corresponding short root
    shortRoots := {@ alpha, -alpha, beta + alpha, -beta - alpha @};
    shortRootsMap := AssociativeArray(shortRoots);
    for i in [1 .. #commutingLongRoots] do
	shortRootsMap[shortRoots[i]] := commutingLongRoots[i];
    end for;

    // We store the n-element that conjugates the short root groups around
    data`ShortRootConj := AssociativeArray();
    for r in roots do
	data`ShortRootConj[r] := <rec<EltSLP | elt := Identity(data`Group),
	    slp := Identity(WordGroup(data`Group))>, r, 1>;
    end for;

    W := WeylGroup(data`LieCopy);
    R := RootDatum(data`LieCopy);
    for root in data`ShortRoots diff roots do
	t := RootPosition(data`LieCopy, root);
	
	for base in roots do
	    s := RootPosition(data`LieCopy, base);

	    // Find long root such that its n-element conjugates the
	    // short roots groups to each other
	    if exists(r){i : i in [1 .. NumPosRoots(data`LieCopy)] |
		s^Reflection(W, i) eq t and IsLongRoot(data`LieCopy, i)} then

		assert IsLongRoot(data`LieCopy, r);
		rootN := Roots(data`LieCopy)[r];
		n_label := ElementN(data, rootN, F ! 1);
		n := LabellingToInput(data, n_label);
		n_w := LabellingToSLP(data, n_label);

		data`RootGroupData[RootIdx(root)]`Group :=
		    data`RootGroupData[RootIdx(base)]`Group^n;
		data`RootGroupData[RootIdx(root)]`SLPs :=
		    [slp^n_w : slp in data`RootGroupData[RootIdx(base)]`SLPs];
		data`ShortRootConj[root] :=
		    <rec<EltSLP | elt := n, slp := n_w>, base,
		    LieConstant_eta(R, r, s)>;

		// find commuting long roots groups
		commuting := {key : key in data`LongRoots |
		    forall{<g, h> : g in
		    UserGenerators(data`RootGroupData[RootIdx(key)]`Group), h
		    in UserGenerators(data`RootGroupData[RootIdx(root)]`Group)
		    | IsIdentity((g, h))}};
		assert commuting eq shortRootsMap[root];
		break;
	    end if;
	end for;
    end for;
    
    vprint Exceptional, 3 : "Found all short root groups";
end procedure;

function BetaAlphaLabel(y, data, n, n_sign, roots)
    F := data`DefiningField;
    q := #F;
    RootIdx := func<root | data`RootDataIdx[root]>;

    assert y in data`RootGroupData[RootIdx(roots[1])]`Group;
    
    z := data`RootGroupData[RootIdx(roots[2])]`InvLabel(F ! 1);    
    R := RootDatum(data`LieCopy);
    yz := ((y, z), z);
    pos := [RootPosition(R, r) : r in roots];

    sign := LieConstant_C(R, 1, 1, pos[2], pos[4]);
    assert sign in {1, -1};

    assert yz in data`RootGroupData[RootIdx(roots[3])]`Group;
    normF := data`RootGroupData[RootIdx(roots[3])]`Label(yz) / sign;

    if normF eq 0 then
	return F ! 0;
    end if;
    
    if data`epsilon eq 1 then
	if q mod 3 in {0, -1} then
	    // normF = q^3
	    // elements have unique 3rd roots
	    assert #AllRoots(normF, 3) eq 1;
	    return Root(normF, 3);
	else
	    sign := LieConstant_C(R, 1, 1, pos[5], pos[1]) / (F ! 3);
	    assert sign in {1, -1};
	    
	    assert y^n in data`RootGroupData[RootIdx(roots[5])]`Group;
	    assert (y, y^n) in data`RootGroupData[RootIdx(roots[4])]`Group;
	    f2 := data`RootGroupData[RootIdx(roots[4])]`Label((y, y^n))
		/ sign;
	    
	    // traceF2 = f^2
	    return 3 * normF / f2;
	end if;
    else
	error "No 3D4 yet";
	// FIXME : ignores signs
	/*
	z1 := Function(longRootGroups[r3]`inverseLabelling)(normF);
	z2 := Function(longRootGroups[r4]`inverseLabelling)(normF);

	// alpha or -alpha?
	k := shortRootGroups[r1]`Nconj`elt *
	    shortRootGroups[alpha]`Nconj`elt^(-1);
	z3 := y^(-k) * (y, z) * (z2 * z1)^(-1);
	
	n1 := shortRootGroups[r5]`Nconj`elt *
	    shortRootGroups[r1]`Nconj`elt^(-1);
	ff := Function(longRootGroups[r4]`labelling)((z3, z3^n1));

	// Return?
	return ff;
        */
    end if;
end function;

procedure LabelShortRootGroups(~data)
    F := data`DefiningField;
    q := #F;
    alpha := data`alpha;
    beta := data`beta;
    RootIdx := func<root | data`RootDataIdx[root]>;

    vprint Exceptional, 3 : "Inverse label short root groups";

    for r in {@ 2 * alpha + beta, -2 *  alpha - beta @} do
	data`RootGroupData[RootIdx(r)]`InvLabel :=
	    func<a | LabelToInput(data, r, a)>;
	data`RootGroupData[RootIdx(r)]`LabelSLP :=
	    func<a | LabelToSLP(data, r, a)>;
    end for;

    R := RootDatum(data`LieCopy);
    
    for r in data`ShortRoots diff {@ 2 * alpha + beta, -2 *  alpha - beta @} do
	n := data`ShortRootConj[r][1]`elt;
	n_w := data`ShortRootConj[r][1]`slp;
	s := data`ShortRootConj[r][2];
	assert s in {@ 2 * alpha + beta, -2 *  alpha - beta @};
	sign := data`ShortRootConj[r][3]^(-1);
	
	data`RootGroupData[RootIdx(r)]`InvLabel :=
	    func<a | data`RootGroupData[RootIdx(s)]`InvLabel(sign * a)^n>;
	data`RootGroupData[RootIdx(r)]`LabelSLP :=
	    func<a | data`RootGroupData[RootIdx(s)]`LabelSLP(sign * a)^n_w>;
    end for;
    
    vprint Exceptional, 3 : "Label beta + alpha";

    assert data`ShortRootConj[beta + alpha][2] eq -beta - 2 * alpha;
    assert data`ShortRootConj[-beta - alpha][2] eq beta + 2 * alpha;
    
    W := WeylGroup(data`LieCopy);
    s := RootPosition(data`LieCopy, beta + alpha);
    t := RootPosition(data`LieCopy, -beta - alpha);
    r := rep{i : i in [1 .. NumPosRoots(data`LieCopy)] |
	s^Reflection(W, i) eq t};
    rootN := Roots(data`LieCopy)[r];
    n_label := ElementN(data, rootN, F ! 1);
    n := LabellingToInput(data, n_label);
    
    // Find labels for \pm (beta + alpha)
    data`RootGroupData[RootIdx(beta + alpha)]`Label := func<y |
	BetaAlphaLabel(y, data, n * data`ShortRootConj[beta + alpha][1]`elt,
	LieConstant_eta(R, r, s) * data`ShortRootConj[beta + alpha][3],
	[beta + alpha, -beta, beta + 3 * alpha, 2 * beta + 3 * alpha,
	beta + 2 * alpha])>;		

    data`RootGroupData[RootIdx(-beta - alpha)]`Label := func<g |
	data`RootGroupData[RootIdx(beta + alpha)]`Label(g^(n^(-1)))>;
    
    vprint Exceptional, 3 : "Label beta + 2alpha";
    
    // Find labels for \pm (beta + 2 alpha) by an N-conjugation
    // The conjugating element was saved when the root groups for beta+alpha
    // were constructed
    
    n := data`ShortRootConj[beta + alpha][1]`elt;
    r := data`ShortRootConj[beta + alpha][2];
    data`RootGroupData[RootIdx(r)]`Label := func<g |
	data`RootGroupData[RootIdx(beta + alpha)]`Label(g^n)>;
    n := data`ShortRootConj[-beta - alpha][1]`elt;
    r := data`ShortRootConj[-beta - alpha][2];
    data`RootGroupData[RootIdx(r)]`Label := func<g |
	data`RootGroupData[RootIdx(-beta - alpha)]`Label(g^n)>;
    
    vprint Exceptional, 3 : "Label alpha";
    assert data`ShortRootConj[alpha][2] ne data`ShortRootConj[-alpha][2];
    n := data`ShortRootConj[alpha][1]`elt;
    r := data`ShortRootConj[alpha][2];
    data`RootGroupData[RootIdx(alpha)]`Label := func<g |
	data`RootGroupData[RootIdx(r)]`Label(g^(n^(-1)))>;

    n := data`ShortRootConj[-alpha][1]`elt;
    r := data`ShortRootConj[-alpha][2];
    data`RootGroupData[RootIdx(-alpha)]`Label := func<g |
	data`RootGroupData[RootIdx(r)]`Label(g^(n^(-1)))>;    
end procedure;

function ConstructTN(data)
    L3 := Codomain(data`SLDataC`iso);
    F := data`DefiningField;
    q := #F;

    // Find two elements to generate whole of T
    repeat
	k := Random([1, q - 1]);
	l := Random([1, q - 1]);
    until GCD(k, l) eq 1 and GCD(k, q - 1) eq 1 and GCD(l, q - 1) eq 1;
    
    // 3-dim gens of T
    // T should normalise SL2 in lower right corner
    lambda := PrimitiveElement(F);
    torus_gens := [Generic(L3) | DiagonalMatrix(F, [lambda^k, 1, lambda^(-k)]),
	DiagonalMatrix(F, [1, lambda^l, lambda^(-l)])];

    vprint Exceptional, 3 : "Find T in input group";
    T := sub<Generic(data`Group) | [Function(data`SLDataC`inv)(x) :
	x in torus_gens]>;
    assert #T eq (q - 1)^2;
    
    N_gens := [elt<Generic(L3) | 0, 1, 0, -1, 0, 0, 0, 0, 1>,
	elt<Generic(L3) | 1, 0, 0, 0, 0, 1, 0, -1, 0>];

    vprint Exceptional, 3 : "Find N in input group";
    N := sub<Generic(data`Group) |
	[Function(data`SLDataC`inv)(x) : x in N_gens]>;

    slps := data`SLDataC`g2slp(UserGenerators(N));
    N`RandomProcess := RandomProcessWithValues(N, slps);

    return T, N;
end function;

// Constructs root groups of standard SL2
function SL3RootGroups(F, indices)
    S := GL(3, F);
    MS := MatrixAlgebra(CoefficientRing(S), Degree(S));

    basis := Basis(F, PrimeField(F));    
    return [sub<S | [S | One(MS) + x * MatrixUnit(MS, idx[1], idx[2]) :
	x in basis]> : idx in indices];
end function;
    
procedure ConstructLongRootGroups(~data)
    F := data`DefiningField;
    q := #F;

    data`RootGroupData := [];
    for root in data`LongRoots do
	Append(~data`RootGroupData, rec<RootGroupInfo | >);
    end for;

    indices := [data`StdLongRootIndices[root] : root in data`LongRoots];
    
    vprint Exceptional, 3 :
	"Obtain long root groups from Sylow subgroups of C";
    standardRootGroups := SL3RootGroups(F, indices);
    assert #standardRootGroups eq #data`RootGroupData;
    S := Generic(Domain(data`SLDataC`inv));
    
    for i in [1 .. #standardRootGroups] do
	data`RootGroupData[i]`Group :=
	    sub<Generic(data`Group) | [Function(data`SLDataC`inv)(g) :
	    g in UserGenerators(standardRootGroups[i])]>;
	data`RootGroupData[i]`SLPs := data`SLDataC`g2slp(
	    UserGenerators(data`RootGroupData[i]`Group));
	assert #data`RootGroupData[i]`SLPs eq Degree(F);
	assert NumberOfGenerators(data`RootGroupData[i]`Group) eq Degree(F);
	
	idx := indices[i];	
	data`RootGroupData[i]`InvLabel := func<a |
	    LabelToInput(data, data`LongRoots[i], a)>;
	data`RootGroupData[i]`Label :=
	    func<g | (Function(data`SLDataC`iso)(g))[idx[1], idx[2]]>;
	
	data`RootGroupData[i]`LabelSLP := func<a | 
	    LabelToSLP(data, data`LongRoots[i], a)>;
    end for;

    vprint Exceptional, 3 : "Long root groups obtained";
end procedure;

// G is the matrix copy of the Lie type group S
// rep : S -> G is the representation
// epsilon = 1, 3
// find root groups directly from S
// alpha, beta = short, long roots from the root datum of S
function findCSLStd(G, S, rep, epsilon, alpha, beta)
    FF := CoefficientRing(G);
    p := Characteristic(FF);
    n := Degree(FF);

    // Find defining field
    assert IsDivisibleBy(n, epsilon);
    F := sub<FF | n div epsilon>;
    q := #F;
    assert q^epsilon eq #FF;
    
    lambda := PrimitiveElement(F);
    W := WordGroup(G);
    q := #F;
    
    // Long root SL3
    C := sub<Generic(G) | rep(&cat[[elt<S | <RootPosition(S, beta), x>>,
	elt<S | <RootPosition(S, -beta), x>>,
	elt<S | <RootPosition(S, beta + 3 * alpha), x>>,
	elt<S | <RootPosition(S, -beta - 3 * alpha), x>>] : x in Basis(F)])>;

    C_slps := [Identity(W) : i in [1 .. NumberOfGenerators(C)]];

    // Long root SL2
    L := sub<Generic(G) | rep(&cat[[elt<S | <RootPosition(S, beta), x>>,
	elt<S | <RootPosition(S, -beta), x>>] : x in Basis(F)])>;
    
    L_slps := [Identity(W) : i in [1 .. NumberOfGenerators(L)]];

    // Short root SL2
    SS := sub<Generic(G) |
	rep(&cat[[elt<S | <RootPosition(S, beta + 2 * alpha), x>>,
	elt<S | <RootPosition(S, -beta - 2 * alpha), x>>] : x in Basis(F)])>;

    SS_slps := [Identity(W) : i in [1 .. NumberOfGenerators(SS)]];

    return [<L, L_slps>, <SS, SS_slps>, <C, C_slps>];    
end function;

// Verifies presentation for root groups
function VerifyRootGroups(data)
    F := CoefficientRing(data`StdCopy);
    p := Characteristic(F);
    q := #data`DefiningField;
    basis := Basis(F, PrimeField(F));

    if data`epsilon gt 1 then
	A, _, inc := AutomorphismGroup(F, data`DefiningField);
	sigma := inc(A.1);
    else
	sigma := hom<F -> F | x :-> x>;
    end if;
    sigma := hom<F -> F | x :-> x^q>;
    
    relators := [];
    roots := data`LongRoots join data`ShortRoots;

    IsLongRoot := func<root | root in data`LongRoots>;
    IsShortRoot := func<root | root in data`ShortRoots>;
    IsShortRoots := func<roots | forall{r : r in roots | IsShortRoot(r)}>;
    IsLongRoots := func<roots | forall{r : r in roots | IsLongRoot(r)}>;
    
    RootIdx := func<root | data`RootDataIdx[root]>;
    R := RootDatum(data`LieCopy);
    
    for mu in roots do
	for nu in {@ x : x in roots | x ne -mu @} do
	    for i in [1 .. #basis] do
		for j in [1 .. #basis] do
		    lhs := (data`RootGroupData[RootIdx(mu)]`LabelSLP(basis[i]),
			data`RootGroupData[RootIdx(mu)]`LabelSLP(basis[j]));
		    r := RootPosition(R, nu);
		    s := RootPosition(R, mu);
		    
		    if mu + nu notin roots then
			patch := Identity(data`WordGroup);
		    elif IsLongRoots([mu, nu, mu + nu]) then
			sign := LieConstant_C(R, 1, 1, r, s);
			assert sign in {1, -1};
			sign := 1;
			patch := data`RootGroupData[RootIdx(mu + nu)]`
			    LabelSLP(sign * basis[i] * basis[j]);
			
		    elif IsShortRoots([mu, nu]) and IsLongRoot(mu + nu) then
			sign := LieConstant_C(R, 1, 1, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * Trace(basis[i] * basis[j]);
			patch := data`RootGroupData[RootIdx(mu + nu)]`
			    LabelSLP(F ! label);
			
		    elif IsShortRoots([mu, nu, mu + nu]) and
			IsLongRoots([2 * mu + nu, mu + 2 * nu]) then
			//sign := LieConstant_C(R, 1, 1, r, s);
			//assert sign in {1, -1};
			sign := 1;
			label := sign * (sigma(basis[i]) * (sigma^2)(basis[j])
			    + (sigma^2)(basis[i]) * sigma(basis[j]));
			patch := data`RootGroupData[RootIdx(mu + nu)]`LabelSLP(
			    F ! label);
			
			sign := LieConstant_C(R, 1, 2, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * Trace(basis[i] * sigma(basis[i]) *
			    (sigma^2)(basis[j]));
			patch *:= data`RootGroupData[RootIdx(2 * mu + nu)]`
			    LabelSLP(F ! label);

			sign := LieConstant_C(R, 2, 1, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * Trace(basis[i] * sigma(basis[j]) *
			    (sigma^2)(basis[j]));
			patch *:= data`RootGroupData[RootIdx(mu + 2 * nu)]`
			    LabelSLP(F ! label);
			
		    elif IsShortRoots([mu, mu + nu, 2 * mu + nu]) and
			IsLongRoots([nu, 3 * mu + nu, 3 * mu + 2 * nu]) then
			sign := LieConstant_C(R, 1, 1, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * basis[i] * basis[j];
			patch := data`RootGroupData[RootIdx(mu + nu)]`
			    LabelSLP(F ! label);

			sign := LieConstant_C(R, 1, 2, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * sigma(basis[i]) * (sigma^2)(basis[i]) *
			    basis[j];
			patch *:= data`RootGroupData[RootIdx(2 * mu + nu)]`
			    LabelSLP(F ! label);

			sign := LieConstant_C(R, 1, 3, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * basis[i] * sigma(basis[i]) *
			    (sigma^2)(basis[i]) * basis[j];
			patch *:= data`RootGroupData[RootIdx(3 * mu + nu)]`
			    LabelSLP(F ! label);

			sign := LieConstant_C(R, 2, 3, r, s);
			assert sign in {1, -1};
			sign := 1;
			label := sign * basis[i] * sigma(basis[i]) *
			    (sigma^2)(basis[i]) * basis[j]^2;
			patch *:= data`RootGroupData[RootIdx(3 * mu + 2 * nu)]`
			    LabelSLP(F ! label);
		    else
			continue;
			//error "Strange roots", mu, nu;
		    end if;

		    Append(~relators, lhs * patch^(-1));
		end for;
	    end for;
	end for;
    end for;
    
    print SequenceToSet(Evaluate(relators, UserGenerators(data`Group)));
    return SequenceToSet(Evaluate(relators, UserGenerators(data`Group))) eq
	{Identity(data`Group)};
end function;

function ObtainSL2(G, h, power, Randomiser, IsSL2)
    S := sub<Generic(G) | >;
    S_slps := [];
    repeat
	g1, w1 := Random(Randomiser);
	g2, w2 := Random(Randomiser);
	
	S := sub<Generic(G) | S, [i gt 1 select Self(1)^g2 else
	    (h`elt^power)^g1 : i in [1 .. 2]]>;
	S_slps cat:= [i gt 1 select Self(1)^w2 else (h`slp^power)^w1
	    : i in [1 .. 2]];
    until IsSL2(S);

    return S, S_slps;
end function;

function IsSL3Black(G, p, q)
    flag, name := LieType(G, p);
    if flag then
	flag and:= name eq <"A", 2, q>;
    end if;

    return flag;
end function;

function GetSL3Tester(G, F)
    q := #F;
    p := Characteristic(F);

    if Category(G) eq GrpMat and p eq Characteristic(CoefficientRing(G)) then
	// Must use both tests even in grey box context
	// A grey box module may not have a natural comp factor
	return func<H | IsSLGrey(H, 3) or IsSL3Black(H, p, q)>;
    else
	return func<H | IsSL3Black(H, p, q)>;
    end if;
end function;

function SL3RecogniserGreyBox(G, F, slpsG)
    W := WordGroup(G);
    return SLRecogniserGeneral(G, F, UserGenerators(W), slpsG, CTRecogniseSL3);
end function;

function SL3RecogniserBlackBox(G, F, slpsG)
    W := WordGroup(G);
    return SLRecogniserGeneral(G, F, UserGenerators(W), slpsG, RecogniseSL3);
end function;

function GetSL3Recogniser(G, F)
    if (Category(G) eq GrpMat and
	Characteristic(F) eq Characteristic(CoefficientRing(G))) or
	ClassicalCentreOrder["linear"](3, #F) eq 1 then
	return SL3RecogniserGreyBox;
    else
	return SL3RecogniserBlackBox;
    end if;
end function;

function ModifyIsomorphism(iso, inv, L)
    // SL2 inside SL3
    L3 := sub<Generic(Domain(inv)) | [Function(iso)(x) :
	x in UserGenerators(L)]>;
    assert not IsIrreducible(L3);

    // Put 2-dim SL2 in upper left corner
    conj := Generic(L3) ! blockDiagonalise(L3 : OrderFactors :=
	func<l | Sort(l, func<x, y | Dimension(y) - Dimension(x)>)>);

    // From standard copy of L inside C to G
    inv := hom<Domain(inv) -> Codomain(inv) |
    g :-> Function(inv)(g^(conj^(-1)))>;

    // From standard copy of L inside C to G
    iso := hom<Domain(iso) -> Codomain(iso) |
    g :-> Function(iso)(g)^conj>;
    
    return iso, inv;
end function;
    
// G is G2 or 3D4, according to epsilon, q is odd
// evenElt is an element of even order
// finds long and short root SL2 and an SL3 as in Kay's method
procedure ConstructCSL(~data, invol)
    F := data`DefiningField;
    q := #F;
    
    vprint Exceptional, 1 : "Find involution centraliser";
    
    Ci, Ci_slps := CentraliserOfInvolution(data`Group, invol`elt, invol`slp
	: Randomiser := data`RandomProcess,
	CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 100>);
    
    vprint Exceptional, 1 : "Find element of order",
	(q^data`epsilon + 1) * (q - 1);

    R := RandomProcessWithValues(Ci, Ci_slps);
    flag, h, h_slp := RandomElementOfOrder(Ci, (q^data`epsilon + 1) * (q - 1) :
	Randomiser := R, Proof := true);
    error if not flag, ERROR_SL;
    h := rec<EltSLP | elt := h, slp := h_slp>;

    vprint Exceptional, 1 : "Find short root SL2";
    
    S, S_slps := ObtainSL2(data`Group, h, q - 1, R,
	GetSL2Tester(data`Group, F, false));
    
    vprint Exceptional, 1 : "Find long root SL2";

    L, L_slps := ObtainSL2(data`Group, h, q^data`epsilon + 1,
	R, GetSL2Tester(data`Group, F, false));
    
    IsSL3 := GetSL3Tester(data`Group, F);
    
    repeat
	vprint Exceptional, 1 : "Find SL2 p-element";
	// Find a p-element using SL2 oracle
	x, x_slp := SL2pElement(L, q);
	k, k_slp := Random(data`RandomProcess);

	// This is SL3 or G2
	C := sub<Generic(L) | L, x^k>;
	C_slps := Append(L_slps, Evaluate(x_slp, L_slps)^k_slp);
	
	flag := IsSL3(C);
	vprint Exceptional, 5 : "Check for SL3 or G2";
	if not flag then
	    assert data`epsilon eq 1;

	    // Swap L and S
	    flag := false;
	    X := L;
	    X_slps := L_slps;
	    L := S;
	    L_slps := S_slps;
	    S := X;
	    S_slps := X_slps;
	end if;
    until flag;
    
    vprint Exceptional, 1 : "Found SL's";
    SL2Recogniser := GetSL2Recogniser(data`Group, F);
    SL3Recogniser := GetSL3Recogniser(data`Group, F);

    try
	W := WordGroup(S);
        flag, iso, inv, g2slp :=
	    SL2Recogniser(S, F, UserGenerators(W), S_slps);
    catch err
	error ERROR_SL;
    end try;
    error if not flag, ERROR_SL;

    data`SLDataS := rec<SLInfo |
	iso := iso,
	inv := inv,
	g2slp := g2slp>;

    vprint Exceptional, 1 : "Recognised short root SL2";
    
    try
	W := WordGroup(L);
        flag, iso, inv, g2slp :=
	    SL2Recogniser(L, F, UserGenerators(W), L_slps);
    catch err
	error ERROR_SL;
    end try;
    error if not flag, ERROR_SL;

    data`SLDataL := rec<SLInfo |
	iso := iso,
	inv := inv,
	g2slp := g2slp>;

    vprint Exceptional, 1 : "Recognised long root SL2";
    
    try
	W := WordGroup(C);
        flag, iso, inv, g2slp :=
	    SL3Recogniser(C, F, C_slps);
    catch err
	error ERROR_SL;
    end try;
    error if not flag, ERROR_SL;

    iso, inv := ModifyIsomorphism(iso, inv, L);
    
    data`SLDataC := rec<SLInfo |
	iso := iso,
	inv := inv,
	g2slp := g2slp>;

    vprint Exceptional, 1 : "Recognised long root SL3";
end procedure;


function SetupGroups(G, F, Randomiser, epsilon, Verify)
    if Verify then
	if epsilon eq 1 then
	    correctName := <"G", 2, #F>;
	else
	    correctName := <"3D", 4, #F>;
	end if;
	
	flag, name := LieType(G, Characteristic(F));
	error if not flag or name ne correctName, ERROR_INPUT;
    end if;

    vprint Exceptional, 1 : "Initialise data structure";
    data := InitialiseRecognition(G, F, Randomiser, epsilon);    
    groups := [<data`Group, true>, <data`StdCopy, false>];

    R := RandomProcessWithWords(data`StdCopy :
	WordGroup := WordGroup(data`StdCopy));
    groupData := [data, InitialiseRecognition(data`StdCopy, F, R, epsilon)];
    
    for i in [1 .. #groups] do
	data := groupData[i];

	vprint Exceptional, 1 : "Find an involution";
	invol := ConstructInvolution(data, epsilon);
	    
	vprint Exceptional, 1 : "Find SL2's and SL3";
	ConstructCSL(~data, invol);
	
	vprint Exceptional, 1 : "Find and label long root groups";
	ConstructLongRootGroups(~data);

	vprint Exceptional, 1 : "Find T and N";
	T, N := ConstructTN(data);

	vprint Exceptional, 1 : "Modify short SL2 isomorphisms";
	iso, inv := ModifyIsomorphismSL2(data, T);
	data`SLDataS`iso := iso;
	data`SLDataS`inv := inv;
	
	vprint Exceptional, 1 : "Find short root groups";
	ConstructShortRootGroups(~data, N);

	vprint Exceptional, 1 : "Label short root groups";
	LabelShortRootGroups(~data);

	CheckRootGroups(data, T);
	
	if Verify then
	    vprint Exceptional, 1 : "Verify root groups";
	    error if not VerifyRootGroups(data), ERROR_INPUT;
	end if;
    end for;
    
    return true;
end function;
