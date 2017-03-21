/******************************************************************************
 *
 *    stdgens.m Gary Seitz's method for exceptional groups of rank > 1
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2008-02-01
 *
 *    Version   : $Revision:: 2759                                           $:
 *    Date      : $Date:: 2014-10-08 13:10:08 +1100 (Wed, 08 Oct 2014)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: stdgens.m 2759 2014-10-08 02:10:08Z eobr007                    $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose Exceptional, 10;

// Structure for storing a matrix and its SLP
EltSLP := recformat<elt : GrpElt, slp : GrpSLPElt>;

import "../../util/basics.m" : getMapFunction;
import "../../util/forms.m" : SubPerp;
import "../../../recog/magma/recog.m" : NodeTypes;
import "../../util/comptree.m" : CTRecogniser, CTRecogniseSL2;
import "../../../classical/recognition/standard.m" : SLChosenElements;

forward getAllGroupsData, findFirstCentraliser, findCommutingInvolutions,
    findGlueInvolution, splitFirstCentraliser, splitSecondCentraliser,
    findSL2ConjugatorE6, findSL2ConjugatorF4, findSL2ConjugatorE7,
    findSL2ConjugatorE8;

// Static data about exceptional groups
StaticGroupInfo := recformat<
    NaturalDim : RngIntElt,
    NaturalData : Rec,
    GlueFinder : UserProgram,
    Field : FldFin,
    TorusOrders : SeqEnum,
    CentraliserDim : RngIntElt,
    CentraliserFactorTypes : SeqEnum>;

NaturalRepInfo := recformat<
    JordanFormOnes : RngIntElt,
    FirstFactors : SeqEnum,
    FirstFactorNr : RngIntElt,
    FirstMeatAxeData : SeqEnum>;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

intrinsic testExceptional(type :: MonStgElt, rank :: RngIntElt,
    p :: RngIntElt, e :: RngIntElt) -> BoolElt
    { }

    SetVerbose("User1", 0);
    SetVerbose("User2", 0);
    SetVerbose("User3", 0);
    SetVerbose("User4", 0);
    SetVerbose("User5", 0);
    SetVerbose("SRMethod", 0);
    SetVerbose("Exceptional", 4);
    SetVerbose("ClassicalRecognition", 0);
    SetVerbose("RandomSchreier", 0);
    SetVerbose("CompositionTree", 0);
    F := GF(p, e);
    q := #F;
    
    groupStr := type cat IntegerToString(rank);
    S := RandomConjugate(ChevalleyGroup(type, rank, F));
    /*
    M := GModule(S);
    N := rep{f : f in Constituents(ExteriorSquare(M)) | Dimension(f) eq 52};
    G := ActionGroup(N);
    
    G`Order := q^24 * (q^12 - 1) * (q^8 - 1) * (q^6- 1) * (q^2 - 1);
    */
    G := S;
    
    flag, gensG, slpsG, glueG := HighRankExceptionalStdGens(G, type, rank, F);
    assert flag;
    assert Evaluate(slpsG, UserGenerators(G)) eq gensG;
    GG := sub<Generic(G) | gensG>;
    print LieType(GG, p);
    
    H := RandomConjugate(G);
    flag, gensH, slpsH, glueH := HighRankExceptionalStdGens(H, type, rank, F);
    assert flag;
    assert Evaluate(slpsH, UserGenerators(H)) eq gensH;
    HH := sub<Generic(G) | gensH>;
    print LieType(HH, p);

    assert #gensG eq #gensH;

    X := sub<Generic(GG) | Prune(gensG)>;
    print LieType(X, p);
    MG := GModule(X);
    MH := GModule(X, Prune(gensH));

    for i in [0 .. Degree(F)] do
	print i, IsIsomorphic(MG, FrobeniusImage(MH, X, i));
    end for;
    
    flag := IsIsomorphic(MG, MH);
    assert flag;

    for x in glueG do
	for y in glueH do
	    X := sub<Generic(GG) | Prune(gensG), x`elt>;
	    print LieType(X, p);
	    MG := GModule(X);
	    MH := GModule(X, Append(Prune(gensH), y`elt));

	    for i in [0 .. Degree(F)] do
		print i, IsIsomorphic(MG, FrobeniusImage(MH, X, i));
	    end for;
	end for;
    end for;
    
    //flag := IsIsomorphic(MG, MH);
    //assert flag;

    
    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic HighRankExceptionalStdGens(G :: GrpMat, name :: MonStgElt,
    rank :: RngIntElt, F :: FldFin : Randomiser := RandomProcessWithWords(G :
    WordGroup := WordGroup(G), Scramble := 1)) -> BoolElt, [], []
    { }

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    q := #F;
    p := Characteristic(F);

    if IsEven(q) then
	error "Characteristic 2 not implemented";
    end if;
        
    vprint Exceptional, 1 : "Initialise static group data";
    allGroupData := getAllGroupsData(F);
    name := name cat IntegerToString(rank);
    
    repeat
	vprint Exceptional, 1 : "Find first centraliser";
	
	// Hopefully obtain correct centraliser type
	invol, C1, C1_slps :=
	    findFirstCentraliser(G, allGroupData[name]);
	
	vprint Exceptional, 1 : "Split first centraliser";
	H1, H2, H1_slps, H2_slps := splitFirstCentraliser(C1, C1_slps,
	    allGroupData[name]`Field,
	    allGroupData[name]`CentraliserFactorTypes[1]);

	// H1 is SL2, H2 is other classical
	assert HasCompositionTree(H1);
	assert HasCompositionTree(H2);
	
	vprint Exceptional, 1 :
	    "Find commuting involutions and second centraliser";

	flag, otherInvol, C2, C2_slps, H3, H3_slps :=
	    findCommutingInvolutions(G, H2, H2_slps, invol, 
	    allGroupData[name]`CentraliserFactorTypes[1],
	    allGroupData[name]`CentraliserFactorTypes[2],
	    allGroupData[name]`CentraliserFactorTypes[3],
	    allGroupData[name]`CentraliserDim,
	    allGroupData[name]`Field);

	// Other centraliser does not contain a natural copy
	if not flag then
	    return false, _, _, _;
	end if;
	vprint Exceptional, 1 : "Found second centraliser";

	vprint Exceptional, 1 : "Find glue involution";
	flag, glueElts := findGlueInvolution(G, C2, C2_slps, invol, otherInvol,
	    [* H1, H1_slps, H2, H2_slps, H3, H3_slps *],
	    allGroupData[name]`CentraliserFactorTypes[3],
	    allGroupData[name]`GlueFinder);
    until flag;

    // The standard generators are the classical standard generators and
    // the extra glue involution
    HS2 := CompositionTreeNiceGroup(H2);
    _, slps2 := CompositionTreeNiceToUser(H2);
    
    stdGens := Append(ChangeUniverse(UserGenerators(HS2),
	Generic(G)), glueElts[1]`elt);   
    stdSLPs := Append(Evaluate(slps2, H2_slps), glueElts[1]`slp);
    
    vprint Exceptional, 1 : "Standard generators found";
    return true, stdGens, stdSLPs, glueElts;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function getAllGroupsData(F)
    q := #F;

    if q mod 4 eq 1 then
	sign := 1;
    else
	sign := -1;
    end if;

    if IsEven(Degree(F)) then
	FF := sub<F | Degree(F) div 2>;
	qq := #FF;
    else
	qq := q;
	FF := F;
    end if;
    
    groups := ["F4", "E6", "2E6", "E7", "E8"];
    groupData := AssociativeArray(groups);

    groupData["F4"] := rec<StaticGroupInfo |
	TorusOrders := [(q - 1) * (q^3 + 1)],
	NaturalDim := 26,
	GlueFinder := findSL2ConjugatorF4, 
	Field := F,
	CentraliserFactorTypes := [<"C", 3, q>, <"C", 2, q>, <"B", 4, q>],
	CentraliserDim := 9,
	NaturalData := rec<NaturalRepInfo |
	JordanFormOnes := 14,
	FirstFactors := [12, 14],
	FirstFactorNr := 2>>;
    groupData["E6"] := rec<StaticGroupInfo |
	TorusOrders := [(q + 1) div d, (q^3 + 1) * (q^2 + q + 1) div d]
	where d is GCD(3, q - 1),
	NaturalDim := 27,
	GlueFinder := findSL2ConjugatorE6, 
	Field := F,
	CentraliserFactorTypes := [<"A", 5, q>, <"A", 3, q>, <"D", 5, q>],
	CentraliserDim := 10,
	NaturalData := rec<NaturalRepInfo |
	JordanFormOnes := 15,
	FirstFactors := [12, 15],
	FirstFactorNr := 2>>;
    groupData["2E6"] := rec<StaticGroupInfo |
	TorusOrders := [(qq + 1) div d, (qq^3 + 1) * (qq^2 + qq + 1) div d]
	where d is GCD(3, qq + 1),
	NaturalDim := 27,
	GlueFinder := findSL2ConjugatorE6, 
	Field := FF,
	CentraliserFactorTypes := [<"2A", 5, q>, <"2A", 3, q>, <"2D", 5, qq>],
	CentraliserDim := 10,
	NaturalData := rec<NaturalRepInfo |
	JordanFormOnes := 15,
	FirstFactors := [12, 15],
	FirstFactorNr := 2>>;
    groupData["E7"] := rec<StaticGroupInfo |
	TorusOrders := [(q + sign) div 2, (q^6 - 1) div 2],
	NaturalDim := 56,
	GlueFinder := findSL2ConjugatorE7, 
	Field := F,
	CentraliserFactorTypes := [<"D", 6, q>, <"D", 4, q>, <"D", 6, q>],
	CentraliserDim := 12,
	NaturalData := rec<NaturalRepInfo |
	JordanFormOnes := 32,
	FirstFactors := [24, 32],
	FirstFactorNr := 1>>;
    groupData["E8"] := rec<StaticGroupInfo |
	TorusOrders := [(q + 1) * (q^7 - 1)],
	NaturalDim := 248,
	GlueFinder := findSL2ConjugatorE8, 
	Field := F,
	CentraliserFactorTypes := [<"E", 7, q>, <"D", 8, q>, <"D", 8, q>],
	CentraliserDim := 16,
	NaturalData := rec<NaturalRepInfo |
	JordanFormOnes := 136,
	FirstFactors := [3, 112, 133],
	FirstFactorNr := 2>>;

    return groupData;
end function;

function ConstructFactor(G, slps : NumberOfTrials := 7)
    assert assigned G`RandomProcess;
    R := G;
    R_slps := slps;
    
    while NumberOfTrials gt 0 do
	g, w := Random(R`RandomProcess);
	n := Order(g : Proof := false);

	primes := PrimeBasis(n);
	for p in primes do
	    h := rec<EltSLP | elt := g^(n div p), slp := w^(n div p)>;
	    
	    if not IsCentral(G, h`elt) then
		H := sub<Generic(G) | h`elt>;
		
		R, R_slps := NormalClosureMonteCarlo(G, H, slps, [h`slp] :
		    SubgroupChainLength := 1);
		R`RandomProcess := RandomProcessWithValues(R, R_slps);
	    end if;
	end for;

	NumberOfTrials -:= 1;
    end while;

    return R, R_slps;
end function;

function ConstructComplement(G, slps, N, N_slps : NumberOfTrials := 7)
    assert assigned G`RandomProcess;
    C := sub<Generic(G) | >;
    C_slps := [];
    
    while NumberOfTrials gt 0 do
	g, w := Random(G`RandomProcess);
	n := Order(g : Proof := false);

	primes := PrimeBasis(n);
	for p in primes do
	    h := rec<EltSLP | elt := g^(n div p), slp := w^(n div p)>;
	    
	    if IsCentral(N, h`elt) then
		H := sub<Generic(G) | h`elt>;
		M, M_slps := NormalClosureMonteCarlo(G, H, slps, [h`slp] :
		    SubgroupChainLength := 1);

		gens := ChangeUniverse(UserGenerators(C), Generic(G)) cat
		    ChangeUniverse(UserGenerators(M), Generic(G));
		
		C := sub<Generic(G) | gens>;
		C_slps cat:= M_slps;
		genMap := [Index(gens, g) : g in UserGenerators(C)];
		C_slps := C_slps[genMap];
		assert NumberOfGenerators(C) eq #C_slps;
	    end if;
	end for;

	NumberOfTrials -:= 1;
    end while;
    
    return C, C_slps;
end function;

function SplitCentralProduct(G, slps)
    vprint Exceptional, 3 : "Construct central factor";
    N, N_slps := ConstructFactor(G, slps);

    vprint Exceptional, 3 : "Construct complement";
    C, C_slps := ConstructComplement(G, slps, N, N_slps);

    return N, N_slps, C, C_slps;
end function;

function splitFirstCentraliser(H, slps, F, classicalType)
    // Obtain central product of classical groups
    repeat
	vprint Exceptional, 4 : "Find derived group";
	D, D_slps := DerivedGroupMonteCarlo(H);
	assert #D_slps eq NumberOfGenerators(D);
	assert NumberOfGenerators(Universe(D_slps)) eq #slps;
    
	slps2 := Evaluate(D_slps, slps);
	D_slps := slps2;
	
	vprint Exceptional, 4 : "Start random process";
	assert #D_slps eq NumberOfGenerators(D);
	D`RandomProcess := RandomProcessWithValues(D, D_slps);

	flag1 := false;
	flag2 := false;
	
	vprint Exceptional, 2 : "Split central product";
	G1, G1_slps, G2, G2_slps := SplitCentralProduct(D, D_slps);
	factors := [G1, G2];
	factor_slps := [G1_slps, G2_slps];
    
	vprintf Exceptional, 2 : "Recognise SL(2, %o)\n", #F;
	flags := [CTRecogniseSL2(A, #F) : A in factors];
	assert HasCompositionTree(G1) and HasCompositionTree(G2);
	
	flag1 := #{b : b in flags | b} eq 1;
	if not flag1 then
	    vprintf Exceptional, 2 : "Could not find SL(2, %o)\n", #F;

	    CleanCompositionTree(G1);
	    CleanCompositionTree(G2);
	    continue;
	end if;
	
	vprintf Exceptional, 2 : "Recognise classical <%o, %o, %o>\n",
	    classicalType[1], classicalType[2], classicalType[3];
	flags := [CTRecogniser(A, classicalType[1],
	    classicalType[2], classicalType[3]) : A in factors];

	flag2 := #{b : b in flags | b} eq 1;
	if not flag2 then
	    vprintf Exceptional, 2 : "Could not find <%o, %o, %o>\n",
		classicalType[1], classicalType[2], classicalType[3];

	    CleanCompositionTree(G1);
	    CleanCompositionTree(G2);
	    continue;
	end if;
    until flag1 and flag2;

    k := rep{i : i in [1 .. #flags] | not flags[i]};
    H1 := factors[k];
    H1_slps := factor_slps[k];
    k := rep{i : i in [1 .. #flags] | flags[i]};
    H2 := factors[k];
    H2_slps := factor_slps[k];

    assert HasCompositionTree(H1);
    assert HasCompositionTree(H2);
    return H1, H2, H1_slps, H2_slps;
end function;

function findFirstCentraliser(G, groupData)
    assert assigned G`RandomProcess;
    
    vprint Exceptional, 2 : "Find random element of orders",
	groupData`TorusOrders;
    F := groupData`Field;
    q := #F;
    p := Characteristic(F);
    
    repeat
	for o in groupData`TorusOrders do
	    name := groupData`CentraliserFactorTypes[3];
	    flag1 := true;
	    
	    flag, g, w := RandomElementOfOrder(G, o : 
		Randomiser := G`RandomProcess, Proof := false);
	    if not flag then
		continue;
	    end if;
	    
	    vprint Exceptional, 2 : "Power up to involution";
	    flag, s := PrimeOrderElement(g, 2);
	    if not flag then
		continue;
	    end if;
	    
	    g ^:= s;
	    w ^:= s;

	    // If in natural rep, check Jordan form to validate involution
	    if Degree(G) eq groupData`NaturalDim and
		Multiplicity({* x : x in Diagonal(JordanForm(g)) *}, 1) ne
		groupData`NaturalData`JordanFormOnes then
		flag := false;
		continue;
	    end if;

	    vprint Exceptional, 2 : "Find involution centraliser";
	    
	    H, slps := CentraliserOfInvolution(G, g, w :
		Randomiser := G`RandomProcess, CompletionCheck :=
		func<G, C, g, l | NumberOfGenerators(C) ge 50>);
	end for;
    until flag;

    vprint Exceptional, 2 : "First involution centraliser found";
    return rec<EltSLP | elt := g, slp := w>, H, slps;    
end function;

/*
function findCommutingInvolutionsE7(G, C, slps, invol, firstName,
    middleName, productName, productDegree, F)

    // Centraliser should contain an SL2 and another classical group
    // Find comp tree and obtain maps to standard copies of these
    q := #F;
    p := Characteristic(F);
    assert HasCompositionTree(C);
        
    vprintf Exceptional, 3 : "Recognise classical <%o, %o, %o>\n",
	firstName[1], firstName[2], firstName[3];
    flag2, _, fromClassical :=
	CTRecogniser(C, firstName[1], firstName[2], firstName[3]);
    assert flag2;

    H2_gens := UserGenerators(CompositionTreeNiceGroup(C));
    _, H2_slps := CompositionTreeNiceToUser(C);

    vprint Exceptional, 3 : "Obtain other SL2";

    // Pick out generators of SL2 from classical standard generators
    H3_slps := Evaluate([H2_slps[i] : i in [1 .. 3]], slps);
    H3 := sub<Generic(G) | [H2_gens[i] : i in [1 .. 3]]>;
    
    flag := RecogniseSL2(H3, q);
    assert flag;

    S3 := CompositionTreeNiceGroup(H3);
    _, slps := CompositionTreeNiceToUser(H3);

    print [Order(x) : x in UserGenerators(H3)];
    
    // This involution commutes with the first, and their product is not
    // conjugate to the first
    invols := [* rec<EltSLP | elt := H3.2^2, slp := H3_slps[2]^2>,
	rec<EltSLP | elt := S3.2^2, slp := Evaluate(slps[2]^2, H3_slps)>,
	rec<EltSLP | elt := H3.1, slp := H3_slps[1]>,
	rec<EltSLP | elt := S3.1, slp := Evaluate(slps[1], H3_slps)>,
	rec<EltSLP | elt := H3.1 * invol`elt, slp := H3_slps[1] * invol`slp>,
	rec<EltSLP | elt := S3.1 * invol`elt,
	slp := Evaluate(slps[1], H3_slps) * invol`slp>,
	rec<EltSLP | elt := S3.2^2 * invol`elt,
	slp := Evaluate(slps[2]^2, H3_slps) * invol`slp>,
	rec<EltSLP | elt := H3.2^2 * invol`elt,
	slp := H3_slps[2]^2 * invol`slp> *];

    print [Order(x`elt) : x in invols];
    print [ProjectiveOrder(x`elt) : x in invols];

    print [Order(x`elt * invol`elt) : x in invols];
    print [ProjectiveOrder(x`elt * invol`elt) : x in invols];
    
    vprint Exceptional, 3 : "Find product involution centraliser";
    
    // Repeat until we have the whole centraliser
    for otherInvol in invols do
	print IsIdentity((otherInvol`elt, invol`elt));
	
	CO, CO_slps := CentraliserOfInvolution(G, otherInvol`elt,
	    otherInvol`slp :
	    Randomiser := G`RandomProcess,
	    CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 50>);
	
	flag, name := LieType(CO, p);
	print flag;
	if flag then
	    print name;
	end if;
    end for;
    //until flag and name eq productName;

    flag, toFactor, fromFactor := CTRecogniser(CO, productName[1],
	productName[2], productName[3]);
    assert flag;

    // Must have a natural copy
    if Degree(Codomain(toFactor)) ne productDegree then
	return false, _, _, _, _, _;
    end if;
    
    return true, invols[1], CO, CO_slps, H3, H3_slps;    
end function;
*/

function findCommutingInvolutions(G, C, slps, invol, firstName,
    middleName, productName, productDegree, F)
    
    // Centraliser should contain an SL2 and another classical group
    // Find comp tree and obtain maps to standard copies of these
    q := #F;
    p := Characteristic(F);
    assert HasCompositionTree(C);
        
    vprintf Exceptional, 3 : "Recognise classical <%o, %o, %o>\n",
	firstName[1], firstName[2], firstName[3];
    flag2, _, fromClassical :=
	CTRecogniser(C, firstName[1], firstName[2], firstName[3]);
    assert flag2;

    H2_gens := UserGenerators(CompositionTreeNiceGroup(C));
    _, H2_slps := CompositionTreeNiceToUser(C);

    vprint Exceptional, 3 : "Obtain other SL2";

    // Pick out generators of SL2 from classical standard generators
    if firstName[1] in {"D", "E"} then
	H3_slps := Evaluate([H2_slps[i] : i in [1 .. 3]], slps);
	H3 := sub<Generic(G) | [H2_gens[i] : i in [1 .. 3]]>;

	//print "E7 case";
	otherInvol := rec<EltSLP | elt := H3.2^2, slp := H3_slps[2]^2>;
    else
	H3_slps := Evaluate([H2_slps[i] : i in [1, 3, 4]], slps);
	H3 := sub<Generic(G) | [H2_gens[i] : i in [1, 3, 4]]>;

	otherInvol := rec<EltSLP | elt := H3.1^2, slp := H3_slps[1]^2>;
    end if;

    // This involution commutes with the first, and their product is not
    // conjugate to the first
    assert Order(otherInvol`elt) eq 2;
    assert IsIdentity((invol`elt, otherInvol`elt));
    
    flag := CTRecogniseSL2(H3, q);
    assert flag;


    vprint Exceptional, 3 : "Find product involution centraliser";
    
    // Repeat until we have the whole centraliser
    repeat
	CO, CO_slps := CentraliserOfInvolution(G, otherInvol`elt * invol`elt,
	    otherInvol`slp * invol`slp :
	    Randomiser := G`RandomProcess,
	    CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 50>);
	
	flag, name := LieType(CO, p);
    until flag and name eq productName;

    vprint Exceptional, 3 : "Recognise product involution centraliser";
    
    flag, toFactor, fromFactor := CTRecogniser(CO, productName[1],
	productName[2], productName[3]);
    assert flag;

    // Must have a natural copy
    if Degree(Codomain(toFactor)) ne productDegree then
	return false, _, _, _, _, _;
    end if;

    return true, otherInvol, CO, CO_slps, H3, H3_slps;    
end function;

function SL2ElementsTensor(F)
    sl2gens := SLChosenElements(SL(2, F));
    
    repeat
	a := Random(F);
    until not IsSquare(a);
    
    diags := [GL(2, F) ! DiagonalMatrix(F, [t, 1]) : t in [F ! 1, a]];
    invT := [GL(2, F) ! Transpose(x^(-1)) : x in sl2gens];
    stdgens := [sl2gens, [x * diags[2] : x in sl2gens], invT,
	[x * diags[2] : x in invT]];

    TensorSL2_gens := [];
    
    for i in [1 .. #stdgens] do
	gens := stdgens[i];
	
	G := GL(4, F);
	MA := MatrixAlgebra(F, 2);
	gens1 := [G ! DiagonalJoin(gens[i], gens[i]) : i in [1, 3, 4]];
	
	gens2 := [];
	Append(~gens2, G ! BlockMatrix([[MA ! 0, MA ! 1], [MA ! -1, MA ! 0]]));
	Append(~gens2, G ! BlockMatrix([[MA ! 1, MA ! 1], [MA ! 0, MA ! 1]]));
	
	alpha := sl2gens[4][2, 2];
	Append(~gens2, G ! BlockMatrix([[MA ! alpha^(-1), MA ! 0],
	    [MA ! 0, MA ! alpha]]));

	Append(~TensorSL2_gens, gens1 cat gens2);
    end for;

    return TensorSL2_gens;
end function;

function findSL2ConjugatorF4(G, C, C_slps, H1, H2, productName)
    F := CoefficientRing(C);
    
    flag, toFactor, fromFactor := CTRecogniser(C, productName[1],
	productName[2], productName[3]);
    assert flag;

    flag, form := SymmetricBilinearForm(Codomain(toFactor));
    assert flag;
    
    HC1 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H1)]>;
    HC2 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H2)]>;
    
    HC := sub<Generic(HC1) | HC1, HC2>;
    
    // Find basis that puts SL2.SL2 in upper left corner
    V := VectorSpace(F, Degree(HC), form);
    M := GModule(HC);
    factors := CompositionFactors(M);
    k := rep{i : i in [1 .. #factors] | Dimension(factors[i]) eq 4};
    homo := GHom(factors[k], M);
    assert Dimension(homo) eq 1;
    basis := [V ! (x * Morphism(N, M)) : x in Basis(N)]
	where N is Image(homo.1);
    W := SubPerp(V, sub<V | basis>);
    basis cat:= Basis(W);
    cbm1 := (Generic(HC) ! Matrix(F, Degree(HC), Degree(HC), basis))^(-1);
    
    // Pick out SL2.SL2
    S := sub<GL(4, F) | [Submatrix(g, 1, 1, 4, 4) :
	g in UserGenerators(HC^cbm1)]>;
    
    sl2Gens := SL2ElementsTensor(F);
    conjs := [];
    
    for stdGens in sl2Gens do 
	SM1 := GModule(S);
	SM2 := GModule(S, stdGens);
	flag, cbm2 := IsIsomorphic(SM2, SM1);
	if flag then
	    assert flag;
	    cbm2 := Generic(S) ! cbm2;
	    
	    // Obtain conjugating element
	    MA := MatrixAlgebra(F, Degree(HC) - Degree(S));
	    g1 := (Generic(S) ! PermutationMatrix(F, [1, 3, 2, 4]))^cbm2;
	    g2 := MA ! -1;    
	    conj := (Generic(HC) ! DiagonalJoin(<g1, g2>))^(cbm1^(-1));
	    
	    assert IsIdentity(conj^2);
	    assert conj * form * Transpose(conj) eq form;
	    assert IsOne(Determinant(conj));
	
	    Append(~conjs, conj);
	end if;
    end for;

    vprint Exceptional, 4 : "Spinor norms:",
	[SpinorNorm(x, form) : x in conjs];
    
    if not exists{x : x in conjs | IsZero(SpinorNorm(x, form))} then
	return false, _;
    end if;
    
    conj := rep{x : x in conjs | IsZero(SpinorNorm(x, form))};
    
    bigConj := Function(fromFactor)(conj);
    coerce := CompositionTreeNiceToUser(C);
    
    if not IsIdentity(bigConj^2) then
	centralInvol := H1.1^2;
	assert IsIdentity(centralInvol^2);
	assert IsCentral(H1, centralInvol);
	assert IsCentral(H2, centralInvol);
	
	bigConj *:= centralInvol;
    end if;
    
    flag, slp := CompositionTreeElementToWord(C, bigConj);
    assert flag;

    return true, [rec<EltSLP | elt := bigConj,
	slp := Evaluate(coerce(slp), C_slps)>];
end function;

function NrC2Descendants(node)
    if node`Type eq NodeTypes`leaf then
	if Category(node`LeafData`GoldCopy) in {GrpAb, GrpPC, GrpPerm} and
	    #node`LeafData`GoldCopy ge 2 then	
	    return 1, [node`Number];
	else
	    return 0, [];
	end if;
    else
	i1, l1 := NrC2Descendants(node`Image);
	i2, l2 := NrC2Descendants(node`Kernel);

	return i1 + i2, l1 cat l2;
    end if;
end function;

function findSL2ConjugatorE6(G, C, C_slps, H1, H2, productName)
    
    flag, toFactor, fromFactor, leaf := CTRecogniser(C, productName[1],
	productName[2], productName[3]);
    assert flag;

    tree := CompositionTree(C);
    leaf := tree[leaf`Number];
    flag, form := SymmetricBilinearForm(Codomain(toFactor));
    assert flag;
    
    HC1 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H1)]>;
    HC2 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H2)]>;
    
    HC := sub<Generic(HC1) | HC1, HC2>;
    
    // Find basis that puts SL2.SL2 in upper left corner 
    F := CoefficientRing(Codomain(toFactor));
    V := VectorSpace(F, Degree(HC), form);
    M := GModule(HC);
    factors := CompositionFactors(M);
    if not exists{i : i in [1 .. #factors] | Dimension(factors[i]) eq 4} then
	return false, _;
    end if;
    
    k := rep{i : i in [1 .. #factors] | Dimension(factors[i]) eq 4};
    homo := GHom(factors[k], M);
    assert Dimension(homo) eq 1;
    basis := [V ! (x * Morphism(N, M)) : x in Basis(N)]
	where N is Image(homo.1);
    U := sub<V | basis>;
    W := SubPerp(V, U);
    basis cat:= Basis(W);
    cbm1 := (Generic(HC) ! Matrix(F, Degree(HC), Degree(HC), basis))^(-1);
    
    // Pick out SL2.SL2
    S := sub<GL(4, F) | [Submatrix(g, 1, 1, 4, 4) :
	g in UserGenerators(HC^cbm1)]>;
    
    sl2Gens := SL2ElementsTensor(F);
    conjs := [];
    centralInvol := HC1.1^2;

    formW := InnerProduct(W);
    formU := InnerProduct(U);
    cbm3 := TransformForm(formW, FormType(Codomain(toFactor)));
    for stdGens in sl2Gens do 
	SM1 := GModule(S);
	SM2 := GModule(S, stdGens);
	flag, cbm2 := IsIsomorphic(SM2, SM1);
	if flag then
	    assert flag;
	    cbm2 := Generic(S) ! cbm2;
	    
	    // Obtain conjugating element
	    MA := MatrixAlgebra(F, Degree(HC) - Degree(S));
	    g1 := (Generic(S) ! PermutationMatrix(F, [1, 3, 2, 4]))^cbm2;
	    assert g1 * formU * Transpose(g1) eq formU;
	    for i in [1, -1] do
		g2 := MA ! i; 
		assert g2 * formW * Transpose(g2) eq formW;
		conj := (Generic(HC) ! DiagonalJoin(<g1, g2>))^(cbm1^(-1));

		assert HC1^conj eq HC2;
		assert IsIdentity(conj^2);
		assert conj * form * Transpose(conj) eq form;

		Append(~conjs, Function(leaf`LeafData`FromGold)(conj));
	    end for;
	end if;
    end for;
    
    flag, form := SymmetricBilinearForm(leaf`Group);
    assert flag;
    assert forall{x : x in conjs | x * form * Transpose(x) eq form};
    
    vprint Exceptional, 4 : "Spinor norms:",
	[SpinorNorm(x, form) : x in conjs];
    
    if not exists{x : x in conjs | IsZero(SpinorNorm(x, form))} then
	return false, _;
    end if;

    /*
    _, _, fromFactors := CompositionTreeSeries(C);
    for f in fromFactors do
	if Category(Domain(f)) in {GrpPC, GrpAb} and #Domain(f) eq 2 then
	    bigCentralInvol := Function(f)(Rep(Generators(Domain(f))));
	    break;
	end if;
    end for;
    assert IsIdentity(bigCentralInvol^2);
    assert IsCentral(C, bigCentralInvol);
    
    MA := MatrixAlgebra(F, Degree(C));
    //print leaf`OpData`factors, Degree(HC);
    idx := rep{i : i in [1 .. #leaf`OpData`factors] |
	Dimension(leaf`OpData`factors[i]) eq Degree(HC)};

    bigConjs := [];
    for conj in conjs do
	for i in [1, -1] do
	    bigConj := MA ! i;
	    InsertBlock(~bigConj, conj, leaf`OpData`top[idx],
		leaf`OpData`left[idx]);
	    
	    bigConj := Generic(C) ! bigConj;
	    bigConj ^:= leaf`OpData`cbm^(-1);
	    
	    coerce := CompositionTreeNiceToUser(C);
	    //print FactoredOrder(bigConj);
	    
	    if not IsIdentity(bigConj^2) then
		centralInvol := H1.1^2;
		assert IsIdentity(centralInvol^2);
		assert IsCentral(H1, centralInvol);
		assert IsCentral(H2, centralInvol);
		
		bigConj *:= centralInvol;
	    end if;
	    
	    assert IsIdentity(bigConj^2);
	    if H1^bigConj eq H2 then
		flag, slp := CompositionTreeElementToWord(C, bigConj);
		assert flag;
		
		Append(~bigConjs, rec<EltSLP | elt := bigConj,
		    slp := Evaluate(coerce(slp), C_slps)>);
	    end if;

	    bigConj *:= bigCentralInvol;
	    if not IsIdentity(bigConj^2) then
		centralInvol := H1.1^2;
		assert IsIdentity(centralInvol^2);
		assert IsCentral(H1, centralInvol);
		assert IsCentral(H2, centralInvol);
		
		bigConj *:= centralInvol;
	    end if;

	    if IsIdentity(bigConj^2) and H1^bigConj eq H2 then
		flag, slp := CompositionTreeElementToWord(C, bigConj);
		assert flag;
		
		Append(~bigConjs, rec<EltSLP | elt := bigConj,
		    slp := Evaluate(coerce(slp), C_slps)>);
	    end if;
	end for;
    end for;
    print #bigConjs;
    
    assert #bigConjs gt 0;
    return true, bigConjs;
    */

    
    // Find parent with determinant test
    node := leaf;
    repeat
	//print node`Number, assigned node`Parent;
	node := tree[node`Parent`Number];
    until NrC2Descendants(node) gt 0;
    
    DisplayCompTreeNodes(C);
    print node`Number;

    flag, form2 := SymmetricBilinearForm(node`Group : Scalars := true);
    assert flag;
    for x in conjs do
	print IsScalar(x * form2 * Transpose(x) * form2^(-1));
	print x * form2 * Transpose(x) eq form2;
    end for;
    
    /*

    print node`Group : Magma;
    
    print [Determinant(x) : x in UserGenerators(node`Group)];
    print [Determinant(x) : x in UserGenerators(leaf`Group)];
    print [SpinorNorm(x, form) : x in UserGenerators(leaf`Group)];
    
    //RandomSchreier(node`Group);
    //print conj in node`Group;
    //print conjs[1] in node`Group;
    //print conjs[2] in node`Group;

    print form;
    print FormType(node`Group);
    print FormType(node`Group : Scalars := true);
    flag, form2 := SymmetricBilinearForm(node`Group : Scalars := true);
    assert flag;
    print IsScalar(conj * form2 * Transpose(conj) * form2^(-1));
    */
    //RandomSchreier(node`Group);
    //print conj in node`Group;
    //print CompositionFactors(node`Group);
    
    // The element lies in this node group
    /*
    slp := Function(node`SLPMaps`EltToSLP)(conj);

    // Coerce SLP up to root
    while node`Number gt 1 do
	slp := node`NiceData`ToParentNice(slp);
	node := tree[node`Parent`Number];
    end while;

    _, slpEval := CompositionTreeSLPGroup(C);
    bigConj := slpEval(slp);
    */

    /*
    X := Codomain(toFactor);
    print Degree(X);
    print CoefficientRing(X);
    assert RecogniseClassical(X);
    flag, form := SymmetricBilinearForm(X);
    assert flag;
    print [Determinant(x) : x in UserGenerators(X)];
    print [SpinorNorm(x, form) : x in UserGenerators(X)];
    RandomSchreier(X);
    for conj in conjs do
	print Determinant(conj);
	print conj * form * Transpose(conj) eq form;
	print SpinorNorm(conj, form);
	print HC1^conj eq HC2;
	print Order(conj);
	print conj in X;
    end for;
    */
    
    _, _, fromFactors := CompositionTreeSeries(C);
    for f in fromFactors do
	if Category(Domain(f)) in {GrpPC, GrpAb} and #Domain(f) eq 2 then
	    bigCentralInvol := Function(f)(Rep(Generators(Domain(f))));
	    break;
	end if;
    end for;
    assert IsIdentity(bigCentralInvol^2);
    assert IsCentral(C, bigCentralInvol);
    
    //RandomSchreier(node`Group);
    bigConjs := [];
    for conj in {x : x in conjs} do
	//print conj in node`Group;
	//read xx;
	try
	    slp := Function(node`SLPMaps`EltToSLP)(conj);
	    flag := true;
	catch err
	    print err;
	    flag := false;
        end try;
	
	if not flag then
	    continue;
	end if;
	
	// Coerce SLP up to root
	while node`Number gt 1 do
	    slp := node`NiceData`ToParentNice(slp);
	    node := tree[node`Parent`Number];
	end while;
	
	_, slpEval := CompositionTreeSLPGroup(C);
	bigConj := slpEval(slp);

	//bigConj := Function(fromFactor)(conj);
	coerce := CompositionTreeNiceToUser(C);
	//print FactoredOrder(bigConj);
	
	if not IsIdentity(bigConj^2) then
	    centralInvol := H1.1^2;
	    assert IsIdentity(centralInvol^2);
	    assert IsCentral(H1, centralInvol);
	    assert IsCentral(H2, centralInvol);
	    
	    bigConj *:= centralInvol;
	end if;
	
	assert IsIdentity(bigConj^2);
	assert H1^bigConj eq H2;
	flag, slp := CompositionTreeElementToWord(C, bigConj);
	assert flag;

	Append(~bigConjs, rec<EltSLP | elt := bigConj,
	    slp := Evaluate(coerce(slp), C_slps)>);

	bigConj *:= bigCentralInvol;
	assert IsIdentity(bigConj^2);
	assert H1^bigConj eq H2;
	flag, slp := CompositionTreeElementToWord(C, bigConj);
	assert flag;

	Append(~bigConjs, rec<EltSLP | elt := bigConj,
	slp := Evaluate(coerce(slp), C_slps)>);
    end for;
    assert #bigConjs gt 0;
    
    return true, bigConjs;
end function;

function findSL2ConjugatorE7(G, C, C_slps, H1, H2, productName)
    F := CoefficientRing(C);
    
    flag, toFactor, fromFactor, leaf := CTRecogniser(C, productName[1],
	productName[2], productName[3]);
    assert flag;
    
    tree := CompositionTree(C);
    leaf := tree[leaf`Number];
    DisplayCompTreeNodes(C);
    
    flag, form := SymmetricBilinearForm(Codomain(toFactor));
    assert flag;
    
    HC1 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H1)]>;
    HC2 := sub<Generic(Codomain(toFactor)) | [Function(toFactor)(g) :
	g in UserGenerators(H2)]>;
    
    HC := sub<Generic(HC1) | HC1, HC2>;
    
    // Find basis that puts SL2.SL2 in upper left corner
    V := VectorSpace(F, Degree(HC), form);
    M := GModule(HC);
    factors := CompositionFactors(M);
    print factors;
    
    k := rep{i : i in [1 .. #factors] | Dimension(factors[i]) eq 4};
    homo := GHom(factors[k], M);
    assert Dimension(homo) eq 1;
    basis := [V ! (x * Morphism(N, M)) : x in Basis(N)]
	where N is Image(homo.1);
    W := SubPerp(V, sub<V | basis>);
    basis cat:= Basis(W);
    cbm1 := (Generic(HC) ! Matrix(F, Degree(HC), Degree(HC), basis))^(-1);
    
    // Pick out SL2.SL2
    S := sub<GL(4, F) | [Submatrix(g, 1, 1, 4, 4) :
	g in UserGenerators(HC^cbm1)]>;
    
    sl2Gens := SL2ElementsTensor(F);
    conjs := [];
    
    for stdGens in sl2Gens do 
	SM1 := GModule(S);
	SM2 := GModule(S, stdGens);
	flag, cbm2 := IsIsomorphic(SM2, SM1);
	if flag then
	    assert flag;
	    cbm2 := Generic(S) ! cbm2;
	    
	    // Obtain conjugating element
	    MA := MatrixAlgebra(F, Degree(HC) - Degree(S));
	    g1 := (Generic(S) ! PermutationMatrix(F, [1, 3, 2, 4]))^cbm2;
	    for i in [1, -1] do
		g2 := MA ! i;    
		conj := (Generic(HC) ! DiagonalJoin(<g1, g2>))^(cbm1^(-1));
	    
		assert IsIdentity(conj^2);
		assert conj * form * Transpose(conj) eq form;
		//assert IsOne(Determinant(conj));
		assert HC1^conj eq HC2;
	    
		Append(~conjs, Function(leaf`LeafData`FromGold)(conj));
	    end for;
	end if;
    end for;

    flag, form := SymmetricBilinearForm(leaf`Group);
    assert flag;
    assert forall{x : x in conjs | x * form * Transpose(x) eq form};
    
    vprint Exceptional, 4 : "Spinor norms:",
	[SpinorNorm(x, form) : x in conjs];
    
    if not exists{x : x in conjs | IsZero(SpinorNorm(x, form))} then
	return false, _;
    end if;
    
    // Find parent with determinant test
    node := leaf;
    repeat
	//print node`Number, assigned node`Parent;
	node := tree[node`Parent`Number];
    until NrC2Descendants(node) gt 1;

    //RandomSchreier(node`Group);
    
    print node`Number, #conjs;
    bigConjs := [];
    for conj in {x : x in conjs} do
	//print conj in node`Group;
	//read xx;
	
	try
	    slp := Function(node`SLPMaps`EltToSLP)(conj);
	flag := true;
	catch err
	    print err;
	    flag := false;
        end try;

	if not flag then
	    continue;
	end if;
	    
	// Coerce SLP up to root
	while node`Number gt 1 do
	    slp := node`NiceData`ToParentNice(slp);
	    node := tree[node`Parent`Number];
	end while;
	
	_, slpEval := CompositionTreeSLPGroup(C);
	bigConj := slpEval(slp);

	//bigConj := Function(fromFactor)(conj);
	coerce := CompositionTreeNiceToUser(C);
	//print FactoredOrder(bigConj);
	
	if not IsIdentity(bigConj^2) then
	    centralInvol := H1.1^2;
	    assert IsIdentity(centralInvol^2);
	    assert IsCentral(H1, centralInvol);
	    assert IsCentral(H2, centralInvol);
	    
	    bigConj *:= centralInvol;
	end if;
	
	assert IsIdentity(bigConj^2);
	assert H1^bigConj eq H2;
	flag, slp := CompositionTreeElementToWord(C, bigConj);
	assert flag;

	Append(~bigConjs, rec<EltSLP | elt := bigConj,
	    slp := Evaluate(coerce(slp), C_slps)>);

	/*
	bigConj *:= bigCentralInvol;
	assert IsIdentity(bigConj^2);
	assert H1^bigConj eq H2;
	flag, slp := CompositionTreeElementToWord(C, bigConj);
	assert flag;

	Append(~bigConjs, rec<EltSLP | elt := bigConj,
	slp := Evaluate(coerce(slp), C_slps)>);
        */
    end for;
    assert #bigConjs gt 0;
    
    return true, bigConjs;
    
    /*
    bigConj := Function(fromFactor)(conj);
    coerce := CompositionTreeNiceToUser(C);
    
    if not IsIdentity(bigConj^2) then
	centralInvol := H1.1^2;
	assert IsIdentity(centralInvol^2);
	assert IsCentral(H1, centralInvol);
	assert IsCentral(H2, centralInvol);
	
	bigConj *:= centralInvol;
    end if;
    
    flag, slp := CompositionTreeElementToWord(C, bigConj);
    assert flag;

    return true, [rec<EltSLP | elt := bigConj,
	slp := Evaluate(coerce(slp), C_slps)>];
    */
end function;

function findSL2ConjugatorE8(G, C, C_slps, H1, H2, productName)
    return false, _;
end function;

function findGlueInvolution(G, C, C_slps, invol1, invol2, groups, productName,
    glueFinder)
    
    H1 := CompositionTreeNiceGroup(groups[1]);
    H3 := CompositionTreeNiceGroup(groups[5]);

    assert forall{<g, h> : g in UserGenerators(H1), h in UserGenerators(H3) |
	IsIdentity((g, h))};

    j := invol1`elt * invol2`elt;
    V := sub<Generic(G) | invol1`elt, invol2`elt>;
    assert #V eq 4 and not IsCyclic(V);
    
    assert IsCentral(H1, j);
    assert IsCentral(H3, j);
    assert IsCentral(H1, invol1`elt);
    assert IsCentral(H3, invol1`elt);
    assert IsCentral(H1, invol2`elt);
    assert IsCentral(H3, invol2`elt);
    
    return glueFinder(G, C, C_slps, H1, H3, productName);
end function;
