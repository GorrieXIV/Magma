/******************************************************************************
 *
 *    sl3.m       Constructive recognition of (P)SL(3,q)
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm 
 *    Dev start : 2008-11-14
 *
 *    Version   : $Revision:: 3127                                           $:
 *    Date      : $Date:: 2015-08-08 12:30:04 +1000 (Sat, 08 Aug 2015)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: sl3.m 3127 2015-08-08 02:30:04Z eobr007                          $:
 *
 *****************************************************************************/

freeze;

forward SL3ClassicalRewrite; 

/*
   Constructive recognition and membership testing of (P)SL(3, q)
   Black box algorithm if given an SL2 oracle.
   From the paper by L�beck-Magaard-O'Brien.
   Math Reviews 2356848
*/

/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "../util/basics.m" : getMapFunction, EltSLP;
import "../util/chevalley-order.m" : ClassicalCentreOrder;
import "../../recog/magma/centre.m" : EstimateCentre;
import "../util/order.m" : MyRandomElementOfOrder, IsProbablySL2;
import "../util/basics.m" : DiagonaliseMatrix;
import "small-to-large.m": SL3SmallToLargeNew, SetupSL3StandardConstructiveMembership;

declare verbose sl3q, 10;

declare attributes Grp : SL3Data;

// Data stored for SL2's found
SL2Info := recformat<
    iso : Map,
    inv : Map,
    g2slp : UserProgram
>;

// Data stored for root groups
RootGroupInfo := recformat<
    Group : Grp,
    SLPs : SeqEnum, // SLPs of gens in input SL3 gens
    //Basis : SeqEnum, // Group elts corresponding to field basis
    //BasisSLPs : SeqEnum, 
    Label : UserProgram, // Field element -> Group element
    LabelSLP : UserProgram, // Field element -> SLP of group element
    InvLabel : UserProgram // Group element -> Field element
>;

SL3MapInfo := recformat<
    iso : Map,
    inv : Map,
    g2slp : Map,
    slp2g : Map,
    gens : SeqEnum,
    slps : SeqEnum
>;

SL3Info := recformat<
    Group : Grp,
    RandomProcess : GrpRandProc,
    WordGroup : GrpSLP,
    StdCopy : GrpMat,
    Projective : BoolElt, // PSL rather than SL ?
    Roots : Assoc, // Same as RootIndices below
    RootGroupData : SeqEnum, // Sequence of RootGroupInfo
    SL2DataK : Rec, // SL2Info for K
    SL2DataM : Rec, // SL2Info for M
    SL2Time : FldReElt,
    TotalTime : FldReElt,
    VerifyTime : FldReElt,
    RecognitionMaps : Rec,
    StandardRootData : List
>;

// Internal errors 
ERROR_ROOTGROUPS := "RootGroupError";
ERROR_SL2        := "SL2Error";
ERROR_BOREL      := "BorelError";
ERROR_NOTSL3     := "NotSL3Error";
ERROR_MEMBERSHIP := "MembershipError";

// Root space of SL3
SL3RootSpace := StandardLattice(3);
alpha := SL3RootSpace ! [1, -1, 0];
beta := SL3RootSpace ! [0, 1, -1];
gamma := alpha + beta;
SL3Roots := {alpha, -alpha, beta, -beta, gamma, -gamma};

// Data for the C function
DataC := AssociativeArray();
DataC[<alpha, beta>]   := -1;
DataC[<beta, -gamma>]  := -1;
DataC[<gamma, -beta>]  := -1;
DataC[<-alpha, gamma>] := -1;
DataC[<-beta, -alpha>] := -1;
DataC[<-gamma, alpha>] := -1;

// Ordering of roots, used in SL3Data`RootGroupData
// Need to be the same as in small-to-large.m !!
RootIndices := AssociativeArray(SL3Roots);
RootIndices[alpha] := 1;
RootIndices[beta] := 2;
RootIndices[gamma] := 3;
RootIndices[-gamma] := 6;
RootIndices[-beta] := 5;
RootIndices[-alpha] := 4;

// Indices of non-zero entry in standard root group matrix
// Corresponds to root order defined by RootIndices
StandardIndices := AssociativeArray(SL3Roots);
StandardIndices[alpha] := [2, 1];
StandardIndices[beta] := [3, 2];
StandardIndices[gamma] := [3, 1];
StandardIndices[-gamma] := [1, 3];
StandardIndices[-beta] := [2, 3];
StandardIndices[-alpha] := [1, 2];

// Maximum number of RecogniseSL trials in black box context
MaxRunsKS := 20;
    
forward SetupSL3, SL3ElementToSLP;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

function UserGenerators(G)
    return [G.i : i in [1 .. NumberOfGenerators(G)]];
end function;

/* 
intrinsic testSL3Recognition(p :: RngIntElt, e :: RngIntElt) -> BoolElt
    { }

    SetVerbose("sl3q", 5);
    SetVerbose("STCS", 1);
    SetVerbose("RandomSchreier", 1);
    //SetVerbose("UserUtil", 2);
    SetVerbose("CompositionTree", 0);
    
    F := GF(p, e);
    G := RandomConjugate(ActionGroup(SymmetricPower(GModule(SL(3, F)), 4)));
    //G := RandomConjugate(SL(3, F));
    //F := GF(11);
    //G := PermutationGroup("L311", 1);
    
    M := PermutationModule(PSL(3, F), GF(7));
    G := RandomConjugate(rep{ActionGroup(x) : x in Constituents(M) |
	Dimension(x) gt 1});

    G := RandomConjugate(MatrixGroup("L311", 19, 1));
    
    //G := RandomConjugate(PSL(3, F));
    //print Degree(G), 
    
    print Degree(G);
    
    t := Cputime();
    flag, iso, inv, g2slp, slp2g := RecogniseSL3(G, F : Verify := false);
    assert flag;
    print "Time:", Cputime(t);
    
    R := RandomProcess(G);
    times := [];
    for i in [1 .. 10] do
	g := Random(R);

	t := Cputime();
	assert getMapFunction(iso * inv)(g) eq g;
	t1 := Cputime(t);
	assert slp2g(Function(g2slp)(g)) eq g;
	Append(~times, [t1, Cputime(t1)]);
    end for;
    print times;
    
    return true;
end intrinsic;

*/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function UserGenerators(G)
    return [G.i : i in [1 .. NumberOfGenerators(G)]];
end function;

intrinsic RecogniseSL3(G :: Grp, F :: FldFin : Verify := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map, [], []
    { If G is isomorphic, possibly modulo scalars, to (P)SL(3, q),
    where F and GF(q) have the same characteristic, 
    then return true and homomorphism from G to (P)SL(3, q), homomorphism
    from (P)SL(3, q) to G, the map from G to its word group and the map 
    from the word group to G; otherwise return false.
    }

    try
	return SetupSL3(G, F, Randomiser, Verify);
    catch err
	if Category(err`Object) eq MonStgElt and err`Object in
	    {ERROR_SL2, ERROR_ROOTGROUPS, ERROR_NOTSL3, ERROR_BOREL} then
	    return false, _, _, _, _;
	end if;
	
	error err;
    end try;
end intrinsic;

intrinsic RecogniseSL3(G :: Grp, q :: RngIntElt :
    Verify := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map, [], []
    { If G is isomorphic, possibly modulo scalars, to (P)SL(3, q),
    where F and GF(q) have the same characteristic, 
    then return true and homomorphism from G to (P)SL(3, q), homomorphism
    from (P)SL(3, q) to G, the map from G to its word group and the map 
    from the word group to G; otherwise return false.
    }

    return RecogniseSL3(G, GF(q) : Verify := Verify, Randomiser := Randomiser);
end intrinsic;

intrinsic RecogniseSL3(G :: Grp: Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map, [], []
    { If G is isomorphic, possibly modulo scalars, to (P)SL(3, q),
    then return true and homomorphism from G to (P)SL(3, q), homomorphism
    from (P)SL(3, q) to G, the map from G to its word group and the map
    from the word group to G; otherwise return false.
    }
    p := LieCharacteristic (G);
    flag, name := LieType (G, p);
    if not flag then  error "Input group is not SL3"; end if;
    q := name[3];
    return RecogniseSL3(G, GF(q) : Verify := false, Randomiser := Randomiser);
end intrinsic;


intrinsic RecogniseSL3(G :: Grp, q :: RngIntElt :
    Verify := false, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) ->
    BoolElt, Map, Map, Map, Map, [], []
    { If G is isomorphic, possibly modulo scalars, to (P)SL(3, q),
    where F and GF(q) have the same characteristic, 
    then return true and homomorphism from G to (P)SL(3, q), homomorphism
    from (P)SL(3, q) to G, the map from G to its word group and the map 
    from the word group to G; otherwise return false.
    }

    return RecogniseSL3(G, GF(q) : Verify := Verify, Randomiser := Randomiser);
end intrinsic;

intrinsic SL3ElementToWord (G:: Grp, g:: GrpElt) -> BoolElt, GrpSLPElt 
{ If g is element of G which has been constructively recognised to have
 central quotient isomorphic to PSL(3, q), then return true and 
 element of word group of G which evaluates to g, else false.
 }
     try
	 error if not assigned G`SL3Data, ERROR_NOTSL3;     
         value := Function(G`SL3Data`RecognitionMaps`g2slp)(g);
         if Type (value) eq BoolElt then return false, _; else
            return true, value; end if;
    catch err
	if Category(err`Object) eq MonStgElt and
	err`Object in {ERROR_SL2, ERROR_ROOTGROUPS, ERROR_NOTSL3, ERROR_BOREL,
	ERROR_MEMBERSHIP} then
	     return false, _, _, _, _;
	end if;

	error err;
    end try;     
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// SL2 naming functions
function IsSL2Black(G, p, q, Projective)
   if Degree (G) eq 1 then return false; end if;

   // LieType is very expensive on occasion 
   // hence use this test in preference to LieType 
    flag := IsProbablySL2(G : Projective := Projective, q := q);
    vprint sl3q, 5 : "IsProbablySL2", flag;
    if flag then
	flag, name := LieType(G, p);
	vprint sl3q, 5 : "IsSL2Black", flag;
	if flag then
	    vprint sl3q, 5 : name;
	    flag and:= name eq <"A", 1, q>;
	end if;
    end if;

    return flag;
end function;

function IsSLGrey(G, d, p, q, Projective)
    sections := Sections(G);
    flag := exists{S : S in sections | (Degree(S) eq d and IsLinearGroup(S))};
    if not flag then
	flag := exists{S : S in sections | IsSL2Black(S, p, q, Projective)};
    end if;
    vprint sl3q, 5 : "IsSLGrey", flag;
    return flag;
end function;

function GetSL2Tester(G, F, Projective)
    q := #F;
    p := Characteristic(F);

    if Category(G) eq GrpMat and p eq Characteristic(CoefficientRing(G)) then
	// Must use both tests even in grey box context
	// A grey box module may not have a natural comp factor
	return func<H | IsSLGrey(H, 2, p, q, Projective) or
	    IsSL2Black(H, p, q, Projective)>;
    else
	return func<H | IsSL2Black(H, p, q, Projective)>;
    end if;
end function;

function SLRecogniserGeneral(G, d, F, slpsG, slpsH)
    flag, iso, inv, g2slp, slp2g, gens, slps := 
       ClassicalConstructiveRecognition(G, "SL", d, #F);

    if flag then
	slps := Evaluate(slpsG, slpsH);
	g2slpBatch := func<seq | Evaluate([Function(g2slp)(g) : g in seq], slps)>;
	return true, iso, inv, g2slpBatch;
    else
	return false, _, _, _;
    end if;
end function;

function SL2RecogniserGeneral(G, F, slpsG, slpsH)
    return SLRecogniserGeneral(G, 2, F, slpsG, slpsH);
end function;

function GetSL2Recogniser(G, F)
    return SL2RecogniserGeneral;
end function;

// SL3 functions

function InitialiseSL3Recognition(G, F, Randomiser)
    data := rec<SL3Info |
	Roots := RootIndices,
	Group := G,
	WordGroup := WordGroup(G),
	StdCopy := SL(3, F),
        SL2Time := 0.0,
	TotalTime := 0.0,
        VerifyTime := 0.0,
	RandomProcess := Randomiser>;

    return data;
end function;

/*
   A "labelling" is [<rootIdx, fieldElt>, ..., <rootIdx, fieldElt>]
   which defines a product of elements of root groups
   rootIdx is index in SL3Data`RootGroupData
   fieldElt is label
*/


// Obtain SLP or element of given label
// only works in alpha/beta groups, where generators are defined from
// basis of F_q over F_p
function LabelToElement(label, elements)
    coords := ChangeUniverse(ElementToSequence(label), Integers());
    assert #elements eq #coords;    
    return &*[elements[i]^coords[i] : i in [1 .. #coords]];
end function;

function LabelToSLP(data, root, label)
    return LabelToElement(label,
	data`RootGroupData[RootIndices[root]]`SLPs);
end function;

function LabelToInput(data, root, label)
    return LabelToElement(label,
	UserGenerators(data`RootGroupData[RootIndices[root]]`Group));
end function;

// Obtain SLP of element defined by labelling
function LabellingToSLP(data, labelling)
    return &*[data`RootGroupData[RootIndices[label[1]]]`LabelSLP(label[2]) :
	label in labelling];
end function;

// Obtain gold copy element defined by labelling
function LabellingToGold(data, labelling)
    S := data`StdCopy;
    MS := MatrixAlgebra(CoefficientRing(S), Degree(S));

    return Generic(S) ! &*[One(MS) + label[2] * MatrixUnit(MS, idx[1], idx[2])
	where idx is StandardIndices[label[1]] : label in labelling];
end function;

// Obtain input copy element defined by labelling
function LabellingToInput(data, labelling)
    return &*[data`RootGroupData[RootIndices[label[1]]]`Label(label[2]) :
	label in labelling];
end function;

// h and n as in paper
function ElementN(data, root, lambda)
    labelling := [<-root, lambda>, <root, -lambda^(-1)>, <-root, lambda>];
    return LabellingToInput(data, labelling), labelling;
end function;

function ElementH(data, root, lambda)
    n1, label1 := ElementN(data, root, lambda);
    n2, label2 := ElementN(data, root, Parent(lambda) ! -1);
    
    return n1 * n2, label1 cat label2;
end function;

// Random(?) element in root groups
function RandomLabelling(data)
    F := CoefficientRing(data`StdCopy);
    Fm, inc := MultiplicativeGroup(F);

    // Choose more sensible numbers?
    n := Random(1, 1);
    return [<Random(Keys(data`Roots)), inc(Random(Fm))> : i in [1 .. n]];
end function;

// Labelling of inverse of corresponding element
function InvertLabelling(labelling)
    return [<label[1], IsZero(label[2]) select label[2]
	else -label[2]> : label in Reverse(labelling)];
end function;

// Lemma 5.1
function BorelLabel(data, x)
    F := CoefficientRing(data`StdCopy);
    p := Characteristic(F);

    alpha1 := data`RootGroupData[data`Roots[alpha]]`Label(F ! 1);
    beta1 := data`RootGroupData[data`Roots[beta]]`Label(F ! 1);
    gamma1 := data`RootGroupData[data`Roots[gamma]]`Label(F ! 1);

    c := data`RootGroupData[data`Roots[gamma]]`InvLabel(gamma1^x);
    a := data`RootGroupData[data`Roots[gamma]]`InvLabel(
	(alpha1^x, beta1^(-1)));
    b := data`RootGroupData[data`Roots[gamma]]`InvLabel(
	(alpha1^(-1), beta1^x));

    d := data`RootGroupData[data`Roots[gamma]]`InvLabel(
	data`RootGroupData[data`Roots[alpha]]`Label(-a) * alpha1^x);
    e := data`RootGroupData[data`Roots[gamma]]`InvLabel(
	data`RootGroupData[data`Roots[beta]]`Label(-b) * beta1^x);
    
    s_beta := -d / a;
    s_alpha := e / b;

    X_beta := data`RootGroupData[data`Roots[beta]]`Label(-s_beta);
    X_alpha := data`RootGroupData[data`Roots[alpha]]`Label(-s_alpha);
    
    roots := AllRoots(a * c, 3);
    error if IsEmpty(roots), ERROR_BOREL;
    for t_alpha in roots do
	t_beta := c / t_alpha;

	h_alpha, h_alpha_label := ElementH(data, alpha, t_alpha);
	h_beta, h_beta_label := ElementH(data, beta, t_beta);
	
	test := (h_alpha * h_beta)^(-1) * x * X_beta * X_alpha;
	if data`Projective or IsIdentity(test^p) then
	    s_gamma :=
		data`RootGroupData[data`Roots[gamma]]`InvLabel(test);
	    break;
	end if;
    end for;

    error if not data`Projective and not IsIdentity(test^p), ERROR_BOREL;

    return h_alpha_label cat h_beta_label cat
	[<alpha, s_alpha>, <beta, s_beta>, <gamma, s_gamma>];
end function;

// The group B, ie the Borel subgroup
// Used for testing purposes
function ConstructB(data)
    F := CoefficientRing(data`StdCopy);

    hElts := &cat[[ElementH(data, alpha, b), ElementH(data, beta, b)] :
	b in F | b ne 0]; 
    
    return sub<Generic(data`Group) | hElts,
	data`RootGroupData[data`Roots[alpha]]`Group,
	data`RootGroupData[data`Roots[beta]]`Group,
	data`RootGroupData[data`Roots[gamma]]`Group>;
end function;

// Obtain label of lower triangular standard copy matrix
function StandardLTLabel(data, g)
    return [<alpha, g[2, 1]>, <beta, g[3, 2]>, <gamma, g[3, 1]>];
end function;

// G is <X, Y> \cong SL2
// Obtain element in G which normalises X and Y
// Uses linear algebra in standard SL2 
function SL2ElementOfNormaliser(G, F, iso, inv)
    lambda := PrimitiveElement(F);
    S := Generic(Domain(inv));
    n := NumberOfGenerators(G);

    rows := [];
    for g in [Function(iso)(x) : x in [G.1, G.n]] do
	eigs := {@ e[1] : e in Eigenvalues(g) @};
	Append(~rows, ElementToSequence(Rep(Basis(Eigenspace(g, eigs[1])))));
    end for;

    cbm := S ! rows;
    return Function(inv)((S ! DiagonalMatrix(F, [lambda, lambda^(-1)]))^cbm);
end function;

// Lemma 5.2
function EffectiveConjugation(data, root, H)
    F := CoefficientRing(data`StdCopy);
    lambda := PrimitiveElement(F);

    sl2Time := Cputime();
    W := WordGroup(H);
    recogniser := GetSL2Recogniser(data`Group, F);
    flag, iso, inv := recogniser(H, F, UserGenerators(W), UserGenerators(W));
    if not flag then
	error if not flag, ERROR_SL2;
    end if;
    //K_elt, K_label := ElementH(data, -root, lambda);
    //K := sub<Generic(data`Group) | K_elt>;
    
    K_prime := sub<Generic(data`Group) | SL2ElementOfNormaliser(H, F, iso, inv)>;
    sl2Time := Cputime(sl2Time);
    vprint sl3q, 8 : "SL2 recognition finished";
    //vprint sl3q, 8 : "K_prime", NumberOfGenerators(K_prime);

    //K_gold := LabellingToGold(data, K_label);
    K_prime_gold := LabellingToGold(data, BorelLabel(data, K_prime.1));
    assert IsLowerTriangular(K_prime_gold);
    //vprint sl3q, 8 : "K_prime_gold", K_prime_gold, K_gold;
    
    assert Degree(K_prime_gold) eq 3;
    K_prime_gold *:= Parent(K_prime_gold) ! 
		     ScalarMatrix(3, K_prime_gold[2, 2]^(-1));
    mu := K_prime_gold[1, 1];
    rho := K_prime_gold[2, 1];
    tau := K_prime_gold[3, 1];
    sigma := K_prime_gold[3, 2];
    assert K_prime_gold[3, 3] eq mu^(-1);

    conj := Generic(data`StdCopy) !
	[[1, 0, 0],
	[rho / (1 - mu), 1, 0],
	[(rho * sigma + (mu^(-1) - 1) * tau) /
	((mu^(-1) - mu) * (mu^(-1) - 1)), sigma / (mu^(-1) - 1), 1]];
    vprint sl3q, 8 : "Conjugator", conj, Determinant(conj);
    
    //assert IsDiagonal(K_prime_gold^conj^(-1));
    //assert K_prime_gold^conj^(-1) in sub<Generic(data`StdCopy) | K_gold>;

    // Invert conj first? Yes!
    b_label := StandardLTLabel(data, conj^(-1));
    //b := LabellingToInput(data, b_label);
    //assert K_prime^b eq K;
    return b_label, sl2Time;
end function;

// Main constructive membership routine
// Produces a labelling of g
function SL3ElementToLabel(G, g : MaxTries :=
    Max(1000, 10 * Degree(G)))
    data := G`SL3Data;
    F := CoefficientRing(data`StdCopy);
    q := #F;
    p := Characteristic(F);
    x_label := [];
    
    vprint sl3q, 2 : "Take random conjugate to obtain SL2";

    // Obtain function that tests for SL2
    IsSL2 := GetSL2Tester(data`Group, F, data`Projective);

    t := Cputime();
    
    NmrTries := MaxTries;
    repeat
	x_label cat:= RandomLabelling(data);
	x := LabellingToInput(data, x_label);
	
	H := sub<Generic(data`Group) |
	    data`RootGroupData[data`Roots[gamma]]`Group,
	    data`RootGroupData[data`Roots[-gamma]]`Group^(g * x)>;
	
	sl2Time := Cputime();
	flag := IsSL2(H);
	G`SL3Data`SL2Time +:= Cputime(sl2Time);
	NmrTries -:= 1;
    until flag or NmrTries eq 0;
    
    error if NmrTries eq 0, ERROR_MEMBERSHIP;
    
    vprint sl3q, 2 : "Time for SL2 recognition:", Cputime(t);
    
    t := Cputime();

    vprint sl3q, 2 : "Perform effective conjugation";
    b_label, sl2Time := EffectiveConjugation(data, -gamma, H);
    vprint sl3q, 2 : "Time for effective recognition:", Cputime(t);
    G`SL3Data`SL2Time +:= sl2Time;

    t := Cputime();
    
    b := LabellingToInput(data, b_label);
    // gxb fixes X_{-\gamma}
    //assert data`RootGroupData[data`Roots[-gamma]]`Group^(g * x * b) eq
	//   data`RootGroupData[data`Roots[-gamma]]`Group;
    n1, n1_label := ElementN(data, gamma, F ! 1);    
    //assert data`RootGroupData[data`Roots[-gamma]]`Group^n1 eq
	//   data`RootGroupData[data`Roots[gamma]]`Group;
    b1 := (g * x * b)^n1;
    
    vprint sl3q, 2 : "Express Borel element";
    b1_label := BorelLabel(data, b1);

    vprint sl3q, 2 : "Time for Borel labelling:", Cputime(t);
    
    return n1_label cat b1_label cat InvertLabelling(n1_label) cat
	InvertLabelling(b_label) cat InvertLabelling(x_label);
end function;

function SL3ElementToSLP(G, g)
    if not IsIdentity(g) then
	totalTime := Cputime();
	labelling := SL3ElementToLabel(G, g);
	slp := LabellingToSLP(G`SL3Data, labelling);
        G`SL3Data`TotalTime +:= Cputime(totalTime);
	return slp;
    else
	return Identity(G`SL3Data`WordGroup);
    end if;
end function;

// Produces image of g in standard copy
function LargeToSmall(G, g)
    totalTime := Cputime();
    labelling := SL3ElementToLabel(G, g);
    g := LabellingToGold(G`SL3Data, labelling);
    G`SL3Data`TotalTime +:= Cputime(totalTime);
    return g;
end function;

// Construction functions

function CoefficientC(mu, nu)
    if IsDefined(DataC, <mu, nu>) then
	return DataC[<mu, nu>];
    else
	return 1;
    end if;
end function;

// Verifies presentation for root groups
// Hence verifies that input is (P)SL3
function VerifyRootGroups(data)
    verifyTime := Cputime();
    F := CoefficientRing(data`StdCopy);
    p := Characteristic(F);
    basis := Basis(F, PrimeField(F));

    relators := [];

    for mu in SL3Roots do
	for i in [1 .. #basis] do
	    Append(~relators,
		data`RootGroupData[data`Roots[mu]]`LabelSLP(basis[i])^p);
	    
	    for j in [1 .. #basis] do
		if j gt i then
		    Append(~relators, (data`RootGroupData[data`Roots[mu]]`
			LabelSLP(basis[i]),
			data`RootGroupData[data`Roots[mu]]`
			LabelSLP(basis[j])));
		end if;
		
		for nu in Exclude(SL3Roots, -mu) do
		    if mu + nu in SL3Roots then
			patchLabel := CoefficientC(mu, nu) *
			    basis[i] * basis[j];
			patch := data`RootGroupData[data`Roots[mu + nu]]`
			    LabelSLP(patchLabel);
		    else
			patch := Identity(data`WordGroup);
		    end if;

		    Append(~relators, 
			(data`RootGroupData[data`Roots[mu]]`LabelSLP(basis[i]),
			data`RootGroupData[data`Roots[nu]]`LabelSLP(basis[j]))
			* patch^(-1));
		end for;
	    end for;
	end for;
    end for;

    flag := SequenceToSet(Evaluate(relators, UserGenerators(data`Group))) eq
	{Identity(data`Group)};
    data`VerifyTime +:= Cputime(verifyTime);
    return flag;
end function;

// Obtain a GL2 as <x, s^g> for random g
function ObtainGL2(data, x, s, MaxTries, projective)
    F := CoefficientRing(data`StdCopy);
    q := #F;
    p := Characteristic(F);

    // Obtain function that tests for SL2
    IsSL2 := GetSL2Tester(data`Group, F, projective);
    
    NmrTries := MaxTries;
    totalSL2Time := 0;
    repeat
	g, w := Random(data`RandomProcess);
	t := rec<EltSLP | elt := s`elt^g, slp := s`slp^w>;
	
	H := sub<Generic(data`Group) | x`elt, t`elt>;

	sl2Time := Cputime();
	flag := IsSL2(H);
	totalSL2Time +:= Cputime(sl2Time);
	NmrTries -:= 1;
    until flag or NmrTries eq 0;

    error if NmrTries eq 0, ERROR_SL2;
    
    return H, [x`slp, t`slp], totalSL2Time;
end function;

// iso : standard SL2 -> input SL2
// inv : input SL2 -> standard SL2
// g is g_alpha or g_beta
function ModifyIsomorphism(iso, inv, g)
    S := Domain(iso);
    F := CoefficientRing(S);
    MS := MatrixAlgebra(F, Degree(S));
    
    A := [Generic(S) | One(MS) + MatrixUnit(MS, idx[1], idx[2]) :
	idx in [[1, 2], [2, 1]]];
    
    vprint sl3q, 5 : "Apply SL2 isomorphism";
    sl2Time := Cputime();
    A_prime := [MS | Function(inv)((Function(iso)(a))^g) : a in A];
    sl2Time := Cputime(sl2Time);

    // Setup variables for finding T
    P := PolynomialAlgebra(F, 4);
    MP := MatrixAlgebra(P, Degree(S));
    T_vars := MP ! [P.i : i in [1 .. Rank(P)]];

    // Setup linear equations for T
    eqns := &cat[ElementToSequence((MP ! A[i]) * T_vars -
	T_vars * (MP ! A_prime[i])) : i in [1 .. #A]];
    coeffs := [[Coefficient(eqn, i, 1) : i in [1 .. Rank(P)]] : eqn in eqns];
    
    // Obtain T
    C := NullspaceOfTransposeMatrix(SparseMatrix(Matrix(F, coeffs)));
    flag, T := IsCoercible(Generic(S), ElementToSequence(C));
    if not flag then
	return false, _, _, sl2Time;
    end if;
    
    assert IsDivisibleBy(#F - 1, Order(T));
    _, conj := DiagonaliseMatrix(T);

    // Should we invert conj? No!
    conj := Generic(S) ! conj;

    return true, hom<S -> Codomain(iso) | g :-> Function(iso)(g^conj)>,
    hom<Codomain(iso) -> S | g :-> Function(inv)(g)^(conj^(-1))>, sl2Time;
end function;

// Constructs root groups of standard SL2
function SL2RootGroups(F)
    S := GL(2, F);
    MS := MatrixAlgebra(CoefficientRing(S), Degree(S));

    basis := Basis(F, PrimeField(F));    
    return [sub<S | [S | One(MS) + x * MatrixUnit(MS, 2, 1) : x in basis]>,
	sub<S | [S | One(MS) + x * MatrixUnit(MS, 1, 2) : x in basis]>];
end function;
    
procedure LabelRootGroups(~data)
    F := CoefficientRing(data`StdCopy);
    S := Generic(Domain(data`SL2DataK`inv));
    MS := MatrixAlgebra(F, Degree(S));

    vprint sl3q, 2 : "Label alpha groups";
    
    // Labels \pm alpha groups
    data`RootGroupData[data`Roots[alpha]]`LabelSLP := func<a | 
	LabelToSLP(data, alpha, a)>;
    data`RootGroupData[data`Roots[alpha]]`Label := func<a |
	LabelToInput(data, alpha, a)>;
    data`RootGroupData[data`Roots[-alpha]]`LabelSLP := func<a | 
	LabelToSLP(data, -alpha, a)>;
    data`RootGroupData[data`Roots[-alpha]]`Label := func<a |
	LabelToInput(data, -alpha, a)>;
    
    vprint sl3q, 2 : "Choose beta identity labels";

    // Choose \pm beta image of 1
    Ybeta1 := rec<EltSLP | elt := data`RootGroupData[data`Roots[beta]]`Group.1,
	slp := data`RootGroupData[data`Roots[beta]]`SLPs[1]>;
    Ymbeta1 := rec<EltSLP | elt :=
	data`RootGroupData[data`Roots[-beta]]`Group.1,
	slp := data`RootGroupData[data`Roots[-beta]]`SLPs[1]>;

    vprint sl3q, 2 : "Label gamma groups";

    // Label \pm gamma groups
    data`RootGroupData[data`Roots[gamma]]`Label := func<a |
	(Ybeta1`elt, data`RootGroupData[data`Roots[alpha]]`Label(a))>;
    data`RootGroupData[data`Roots[gamma]]`LabelSLP := func<a | 
	(Ybeta1`slp, data`RootGroupData[data`Roots[alpha]]`LabelSLP(a))>;
    data`RootGroupData[data`Roots[-gamma]]`Label := func<a |
	(data`RootGroupData[data`Roots[-alpha]]`Label(a), Ymbeta1`elt)>;
    data`RootGroupData[data`Roots[-gamma]]`LabelSLP := func<a | 
	(data`RootGroupData[data`Roots[-alpha]]`LabelSLP(a), Ymbeta1`slp)>;
    
    vprint sl3q, 2 : "Label beta groups";

    // Label beta groups
    data`RootGroupData[data`Roots[beta]]`Label := func<a |
	(data`RootGroupData[data`Roots[gamma]]`Label(F ! 1),
	data`RootGroupData[data`Roots[-alpha]]`Label(a))>;
    data`RootGroupData[data`Roots[beta]]`LabelSLP := func<a | 
	(data`RootGroupData[data`Roots[gamma]]`LabelSLP(F ! 1),
	data`RootGroupData[data`Roots[-alpha]]`LabelSLP(a))>;

    // Label -beta groups
    data`RootGroupData[data`Roots[-beta]]`Label := func<a |
	(data`RootGroupData[data`Roots[alpha]]`Label(a),
	data`RootGroupData[data`Roots[-gamma]]`Label(F ! 1))>;    
    data`RootGroupData[data`Roots[-beta]]`LabelSLP := func<a | 
	(data`RootGroupData[data`Roots[alpha]]`LabelSLP(a),
	data`RootGroupData[data`Roots[-gamma]]`LabelSLP(F ! 1))>;

    // Inverse labellings
    
    vprint sl3q, 2 : "Inverse label alpha groups";
    data`RootGroupData[data`Roots[alpha]]`InvLabel := func<g |
	(Function(data`SL2DataK`iso)(g))[2, 1]>;
    data`RootGroupData[data`Roots[-alpha]]`InvLabel := func<g |
	(Function(data`SL2DataK`iso)(g))[1, 2]>;
    
    vprint sl3q, 2 : "Inverse label gamma groups";
    data`RootGroupData[data`Roots[gamma]]`InvLabel := func<g |
	data`RootGroupData[data`Roots[alpha]]`InvLabel((Ymbeta1`elt, g))>;
    data`RootGroupData[data`Roots[-gamma]]`InvLabel := func<g |
	data`RootGroupData[data`Roots[-alpha]]`InvLabel((g, Ybeta1`elt))>;

    vprint sl3q, 2 : "Inverse label beta groups";

    Ygamma1 := data`RootGroupData[data`Roots[gamma]]`Label(F ! 1);
    Ymgamma1 := data`RootGroupData[data`Roots[-gamma]]`Label(F ! 1);
    
    data`RootGroupData[data`Roots[beta]]`InvLabel := func<g |
	data`RootGroupData[data`Roots[-alpha]]`InvLabel((Ymgamma1, g))>;
    data`RootGroupData[data`Roots[-beta]]`InvLabel := func<g |
	data`RootGroupData[data`Roots[alpha]]`InvLabel((g, Ygamma1))>;
end procedure;

procedure ConstructRootGroups(~data)
    F := CoefficientRing(data`StdCopy);
    smallRootGroups := SL2RootGroups(F);

    data`RootGroupData := [];
    for root in Keys(data`Roots) do
	Append(~data`RootGroupData, rec<RootGroupInfo | >);
    end for;
    
    sl2Time := Cputime();
    data`RootGroupData[data`Roots[alpha]]`Group :=
	sub<Generic(data`Group) | [Function(data`SL2DataK`inv)(g) :
	g in UserGenerators(smallRootGroups[1])]>;
    data`RootGroupData[data`Roots[alpha]]`SLPs :=
	data`SL2DataK`g2slp(UserGenerators(
	data`RootGroupData[data`Roots[alpha]]`Group));
    assert NumberOfGenerators(data`RootGroupData[data`Roots[alpha]]`Group)
	eq Degree(F);
    assert #data`RootGroupData[data`Roots[alpha]]`SLPs eq Degree(F);
    
    data`RootGroupData[data`Roots[-alpha]]`Group :=
	sub<Generic(data`Group) | [Function(data`SL2DataK`inv)(g) :
	g in UserGenerators(smallRootGroups[2])]>;
    data`RootGroupData[data`Roots[-alpha]]`SLPs :=
	data`SL2DataK`g2slp(UserGenerators(
	data`RootGroupData[data`Roots[-alpha]]`Group));
    assert NumberOfGenerators(data`RootGroupData[data`Roots[-alpha]]`Group)
	eq Degree(F);
    assert #data`RootGroupData[data`Roots[-alpha]]`SLPs eq Degree(F);

    MRoot1 := sub<Generic(data`Group) | [Function(data`SL2DataM`inv)(g) :
	g in UserGenerators(smallRootGroups[1])]>;
    MRoot2 := sub<Generic(data`Group) | [Function(data`SL2DataM`inv)(g) :
	g in UserGenerators(smallRootGroups[2])]>;
    
    if forall{<g, h> : g in UserGenerators(MRoot1),
	h in UserGenerators(data`RootGroupData[data`Roots[-alpha]]`Group) |
	IsIdentity((g, h))} then
	data`RootGroupData[data`Roots[beta]]`Group := MRoot1;

	assert forall{<g, h> : g in UserGenerators(MRoot2),
	    h in UserGenerators(data`RootGroupData[data`Roots[alpha]]`Group) |
	    IsIdentity((g, h))};
	    
	data`RootGroupData[data`Roots[-beta]]`Group := MRoot2;
    else
	assert forall{<g, h> : g in UserGenerators(MRoot1),
	    h in UserGenerators(data`RootGroupData[data`Roots[alpha]]`Group) |
	    IsIdentity((g, h))};
	data`RootGroupData[data`Roots[-beta]]`Group := MRoot1;

	assert forall{<g, h> : g in UserGenerators(MRoot2),
	    h in UserGenerators(data`RootGroupData[data`Roots[-alpha]]`Group) |
	    IsIdentity((g, h))};
	
	data`RootGroupData[data`Roots[beta]]`Group := MRoot2;
    end if;
    
    data`RootGroupData[data`Roots[beta]]`SLPs := data`SL2DataM`g2slp(
	UserGenerators(data`RootGroupData[data`Roots[beta]]`Group));
    assert NumberOfGenerators(data`RootGroupData[data`Roots[beta]]`Group)
	eq Degree(F);
    assert #data`RootGroupData[data`Roots[beta]]`SLPs eq Degree(F);

    data`RootGroupData[data`Roots[-beta]]`SLPs :=
	data`SL2DataM`g2slp(UserGenerators(
	data`RootGroupData[data`Roots[-beta]]`Group));
    data`SL2Time +:= Cputime(sl2Time);
    assert NumberOfGenerators(data`RootGroupData[data`Roots[-beta]]`Group)
	eq Degree(F);
    assert #data`RootGroupData[data`Roots[-beta]]`SLPs eq Degree(F);
        
    data`RootGroupData[data`Roots[gamma]]`Group := 
	sub<Generic(data`Group) | [(g, h) : g in
	UserGenerators(data`RootGroupData[data`Roots[alpha]]`Group),
	h in UserGenerators(data`RootGroupData[data`Roots[beta]]`Group)]>;
    data`RootGroupData[data`Roots[gamma]]`SLPs :=
	[(g, h) : g in data`RootGroupData[data`Roots[alpha]]`SLPs,
	h in data`RootGroupData[data`Roots[beta]]`SLPs];

    data`RootGroupData[data`Roots[-gamma]]`Group :=
	sub<Generic(data`Group) | [(g, h) : g in UserGenerators(
	data`RootGroupData[data`Roots[-alpha]]`Group), h in
	UserGenerators(data`RootGroupData[data`Roots[-beta]]`Group)]>;
    data`RootGroupData[data`Roots[-gamma]]`SLPs := [(g, h) : g in
	data`RootGroupData[data`Roots[-alpha]]`SLPs,
	h in data`RootGroupData[data`Roots[-beta]]`SLPs];
end procedure;

procedure ConstructSL2s(~data : MaxTries :=
    Max(1000, 10 * Degree(data`Group)))
    F := CoefficientRing(data`StdCopy);
    q := #F;

    // Proportion of (q^2 - 1)-elements in SL3 and GL2
    proportion := EulerPhi(q^2 - 1) / (2 * (q^2 - 1));

    // Expected number of selections of (q^2 - 1)-elements
    selections := Max([Ceiling(1 / proportion)^2, q, MaxTries]);

   // EOB April 2014 -- removed q
   selections := Max([Ceiling(1 / proportion)^2, MaxTries]);

    SL2Recogniser := GetSL2Recogniser(data`Group, F);
    order := q^2 - 1;

    // centre order if group is SL
    centreOrder := ClassicalCentreOrder["linear"](3, q);
    C, words, correct := EstimateCentre(data`Group, centreOrder);
    // if centre is found then we have SL
    data`Projective := not correct;
    if data`Projective then
	vprint sl3q, 2 : "Group appears to be PSL(3, q)";
    end if;

    if data`Projective and q mod 3 eq 1 then
	order div:= 3;

	flag, x, x_slp := MyRandomElementOfOrder(data`Group, order :
	    Proof := false, Randomiser := data`RandomProcess, Central := false,
	    MaxTries := selections);
    else
	vprint sl3q, 2 : "Find torus element";
	flag, x, x_slp := MyRandomElementOfOrder(data`Group, order :
	   Proof := false, Randomiser := data`RandomProcess, Central := false,
	   MaxTries := selections);
    end if;

    error if not flag, ERROR_SL2;

    s := rec<EltSLP | elt := x^(q + 1), slp := x_slp^(q + 1)>;

    // Obtain a GL2 as <s, s^g> for some g
    vprint sl3q, 2 : "Find first SL2";
    H1, H1_slps, sl2Time := ObtainGL2(data, s, s, MaxTries, data`Projective);
    data`SL2Time +:= sl2Time;
    R1 := RandomProcessWithValues(H1, H1_slps);

    gAlphaTries := MaxTries;
    repeat
	vprint sl3q, 2 : "Find torus element";
	flag, y, y_slp := MyRandomElementOfOrder(H1, order : Proof := false,
	    Central := false, Randomiser := R1,
	    MaxTries := selections);
	error if not flag, ERROR_SL2;
	
	g_alpha := rec<EltSLP | elt := y^(q + 1), slp := y_slp^(q + 1)>;
	assert IsCentral(H1, g_alpha`elt);
	
	// Obtain a GL2 as <g_alpha, s^g> for some g
	vprint sl3q, 2 : "Find second SL2";
	H2, H2_slps, sl2Time := ObtainGL2(data, g_alpha, s, MaxTries, data`Projective);
	data`SL2Time +:= sl2Time;
	R2 := RandomProcessWithValues(H2, H2_slps);
	
	gBetaTries := MaxTries;
	repeat
	    vprint sl3q, 2 : "Find torus element";
	    flag, w, w_slp := MyRandomElementOfOrder(H2, order :
		Proof := false, Central := false, Randomiser := R2,
		MaxTries := selections);
	    error if not flag, ERROR_SL2;
    
	    g_beta := rec<EltSLP | elt := w^(q + 1), slp := w_slp^(q + 1)>;
	    assert IsCentral(H2, g_beta`elt);
	    
	    vprint sl3q, 2 : "Recognise first SL2";
	    K, K_slps := DerivedGroupMonteCarlo(H1);
	    
	    try
		sl2Time := Cputime();
		flag, iso, inv, g2slp := SL2Recogniser(K, F, K_slps, H1_slps);
	        data`SL2Time +:= Cputime(sl2Time);
	    catch err
		error ERROR_SL2;
	    end try;
	    error if not flag, ERROR_SL2;
	    flag, inv, iso, sl2Time := ModifyIsomorphism(inv, iso, g_beta`elt);
	    data`SL2Time +:= sl2Time;
            vprint sl3q, 2 : "First ModifyIsomorphism worked?", flag eq true;
	    gBetaTries -:= 1;
	until flag;

	data`SL2DataK := rec<SL2Info |
	    iso := iso,
	    inv := inv,
	    g2slp := g2slp>;

	vprint sl3q, 2 : "Recognise second SL2";
	M, M_slps := DerivedGroupMonteCarlo(H2);
	try
	    sl2Time := Cputime();
	    flag, iso, inv, g2slp := SL2Recogniser(M, F, M_slps, H2_slps);
	    data`SL2Time +:= Cputime(sl2Time);
	catch err
	    error ERROR_SL2;
        end try;
	error if not flag, ERROR_SL2;
	
	flag, inv, iso, sl2Time := ModifyIsomorphism(inv, iso, g_alpha`elt);
	data`SL2Time +:= sl2Time;
        vprint sl3q, 2 : "Second ModifyIsomorphism worked?", flag eq true;
    until flag;

    data`SL2DataM := rec<SL2Info |
	iso := iso,
	inv := inv,
	g2slp := g2slp>;
end procedure;

function ObtainStandardGenerators(G, F, data, RootElementSLPs)
   EH := ClassicalStandardGenerators("SL", 3, #F);   
   W := [SL3SmallToLargeNew(data, g, RootElementSLPs) : g in EH];
   E := Evaluate(W, UserGenerators(G));
   return E, W;
end function;

function ObtainStandardGeneratorsSmall(G, F, inv, g2slp)
   EH := ClassicalStandardGenerators("SL", 3, #F);   
   W := [getMapFunction(inv * g2slp)(h): h in EH];
   E := Evaluate(W, UserGenerators(G));
   return E, W;
end function;

function SetupSmallFieldSL3(G, F, verify)
    vprint sl3q, 1 : "About to run Kantor-Seress black box version";

    q := #F;
    trial := 1;
    sl2time := Cputime();
    repeat 
	flag, phi, tau := RecogniseSL(G, 3, q);
	trial +:= 1;
    until flag or trial gt MaxRunsKS;
    G`SL3Data`SL2Time +:= Cputime(sl2time);

    vprint sl3q, 1 : "Result of Kantor-Seress:", flag;
    
    if flag eq false then
	return flag;
    end if;

    RandomSchreier(G);
    if verify then
	verifyTime := Cputime();
	Verify(G);
        G`SL3Data`VerifyTime +:= Cputime(verifyTime);
    end if;
    W, delta := WordGroup(G);
    
    word := hom<G -> W | UserGenerators(W)>;
    wordRule := hom<G -> W | g :-> word(g)>;
    phiRule := hom<G -> SL(3, F) | g :-> phi(g)>;
    tauRule := hom<SL(3, F) -> G | g :-> tau(g)>;
    gens, slps := ObtainStandardGeneratorsSmall(G, F, tauRule, wordRule);
    
    G`SL3Data`RecognitionMaps := rec<SL3MapInfo |
       iso := phiRule,
       inv := tauRule,
       g2slp := wordRule,
       slp2g := delta, 
       gens := gens,
       slps := slps>;
    return true;
end function;
    
// use ClassicalRewrite except if input is matrix group in defining characteristic 
// and not absolutely irreducible; in this special case, it is faster to use specific 
// SL3 rewriting which uses various SL2 subgroups processed using CompositionTree 
function SetupSL3(G, F, Randomiser, Verify : 
     UseClassicalRewrite := not (Type (G) eq GrpMat and Characteristic (BaseRing (G)) eq Characteristic (F) 
     and IsAbsolutelyIrreducible (G) eq false))

    vprint sl3q, 1 : "Entering SL3 recognition";
    if assigned G`SL3Data then
	maps := G`SL3Data`RecognitionMaps;
	return true, maps`iso, maps`inv, maps`g2slp, maps`slp2g;
    end if;

    totalTime := Cputime();
    if Verify then
	if Degree(G) eq 3 then
	    error if not IsLinearGroup(G), ERROR_NOTSL3;
	end if;	
	flag, name := LieType(G, Characteristic(F));
	error if not flag or name ne <"A", 2, #F>, ERROR_NOTSL3;
    end if;

    vprint sl3q, 1 : "Initialise data structure";
    data := InitialiseSL3Recognition(G, F, Randomiser);
    data`VerifyTime +:= Cputime(totalTime);
	    
    // Algorithm cannot handle small cases
    if #F in {2,3,4,7} then 
	G`SL3Data := data;
	flag := SetupSmallFieldSL3(G, F, Verify);
        // EOB -- we should return false, not go into error 
	// error if not flag, ERROR_NOTSL3;
        G`SL3Data`TotalTime := Cputime(totalTime);
        if flag then
	    return true, 
		   G`SL3Data`RecognitionMaps`iso,
		   G`SL3Data`RecognitionMaps`inv,
		   G`SL3Data`RecognitionMaps`g2slp,
		   G`SL3Data`RecognitionMaps`slp2g,
		   G`SL3Data`RecognitionMaps`gens,
		   G`SL3Data`RecognitionMaps`slps;
        else
	    return false, _, _, _, _, _, _;
	end if;
    end if;
        
    vprint sl3q, 1 : "Find SL2's inside SL3";
    ConstructSL2s(~data);
    
    vprint sl3q, 1 : "Construct root groups from SL2's";
    ConstructRootGroups(~data);
    
    vprint sl3q, 1 : "Label root groups";
    LabelRootGroups(~data);

    if Verify then
	vprint sl3q, 1 : "Verify root groups";
	error if not VerifyRootGroups(data), ERROR_NOTSL3;
    end if;
    
    data`StandardRootData := SetupSL3StandardConstructiveMembership(data`StdCopy, F);
    G`SL3Data := data;
    vprint sl3q, 1 : "SL3 recognition finished, now set up maps";    
    iso := hom<Generic(G) -> data`StdCopy | g :-> LargeToSmall(G, g)>;

    W, slp2g := WordGroup(G);
    vprint sl3q, 2 : "Calculating root elements for rewriting";    
    // Rewriting writes standard SL3 elements as SLPs in these elements
    // Order must match RootIndices
    basis := Basis(F, PrimeField(F));
    RootElements := &cat[[data`RootGroupData[i]`Label(b) : b in basis] :
			 i in [1 .. #Keys(data`Roots)]];
    RootElementSLPs := &cat[[data`RootGroupData[i]`LabelSLP(b) : b in basis] :
			    i in [1 .. #Keys(data`Roots)]];
    // inv := hom<data`StdCopy -> G | g :-> SL3SmallToLargeNew(data, g, RootElements)>;
    inv := hom<data`StdCopy -> Generic (G) | g :-> SL3SmallToLargeNew(data, g, RootElements)>;
    g2slp := hom<Generic(G) -> W | g :-> SL3ElementToSLP(G, g)>;
    vprint sl3q, 1 : "Obtain standard generators";    
    gens, slps := ObtainStandardGenerators(G, F, data, RootElementSLPs);

    if UseClassicalRewrite eq true then
	vprint sl3q, 1: "Use ClassicalRewrite to provide maps";
	SL3ClassicalRewrite(G, F, gens, slps);
    else
	vprint sl3q, 1: "Use standard SL3 rewriting";
	G`SL3Data`RecognitionMaps := rec<SL3MapInfo |
          iso := iso,
          inv := inv,
          g2slp := g2slp,
          slp2g := slp2g,
          gens := gens,
          slps := slps>;
    end if;
    G`SL3Data`TotalTime := Cputime(totalTime);
    vprint sl3q, 1 : "Leaving SL3 recognition";    
    return true, 
	   G`SL3Data`RecognitionMaps`iso,
	   G`SL3Data`RecognitionMaps`inv,
	   G`SL3Data`RecognitionMaps`g2slp,
	   G`SL3Data`RecognitionMaps`slp2g,
	   G`SL3Data`RecognitionMaps`gens,
	   G`SL3Data`RecognitionMaps`slps;
end function;

// set up maps for SL3 using ClassicalRewrite
procedure SL3ClassicalRewrite(G, F, E, W)
   n := 3; 
   q := #F;
   EH := ClassicalStandardGenerators("SL", n, q);

   LargeToSmall := function(G, E, q, g : type := "SL")
      f, w := ClassicalRewrite(G, E, type, n, q, g);
      return Evaluate(w, EH);
   end function;

   SmallToLarge := function(E, g : type := "SL")
      P := Parent (g);
      q := #BaseRing (P);
      X := EH;
      f, w := ClassicalRewrite(sub<Universe (X) | X>, X, type, n, q, g);
      return Evaluate(w, E);
   end function;

   LargeToWordGroup := function(G, E, W, q, g : type := "SL")
      f, w := ClassicalRewrite(G, E, type, n, q, g);
      if not f then return false; else return Evaluate(w, W); end if;
   end function;

   K := SL(n, q);
   phi := hom<Generic(G) -> K | x :-> LargeToSmall(G, E, q, x)>;
   tau := hom<Generic(K) -> G | x :-> SmallToLarge(E, x)>;
   WG := WordGroup(G);
   gamma := hom<Generic(G) -> WG | x :-> LargeToWordGroup(G, E, W, q, x)>;
   delta := hom<WG -> G | x :-> Evaluate(x, UserGenerators(G))>;
   G`SL3Data`RecognitionMaps := rec<SL3MapInfo |
      iso := phi,
      inv := tau,
      g2slp := gamma,
      slp2g := delta,
      gens := E,
      slps := W>;
end procedure;
