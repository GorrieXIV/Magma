/******************************************************************************
 *
 *    prospect.mag  Product Replacement Prospector
 *
 *    File      : $RCSfile: prospect.mag,v $
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-10-06
 *
 *    Version   : $Revision: 1.27 $
 *    Date      : $Date: 2007/05/03 15:04:19 $
 *    Last edit : $Author: hb $
 *
 *    @(#)$Id: prospect.mag,v 1.27 2007/05/03 15:04:19 hb Exp $
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

// Information about one statistical test
ProspectorTestInfo := recformat<
    // Evaluates group elements into integers
    TestPropertyEval : UserProgram,
    // For debug and log output
    Description : MonStgElt,
    // The current batch of test values from the Sampler
    SamplerTestValues : SeqEnum,
    // The current batch of test values from the Seeker
    SeekerTestValues : SeqEnum,
    // The value of each bucket for this test
    Buckets : SetIndx,
    // Expected sizes of each bucket
    ExpectedValues : SeqEnum,
    // Indicates whether the expectations are theoretical ones
    KnownDistribution : BoolElt,
    // First position when the Sampler test accepted
    SamplerOKPos : RngIntElt,
    // First position when the Seeker test accepted
    SeekerOKPos : RngIntElt
>;

// Information about the sampling of elements
ProspectorSamplingInfo := recformat<
    // Sequence of ProspectorTestInfo
    TestData : SeqEnum,
    // The size of the test batches
    TestSampleSize : RngIntElt,
    // The current test batch of Sampler elements
    SamplerTestElements : SeqEnum,
    // The current test batch of Seeker elements
    SeekerTestElements : SeqEnum,
    // The number of steps between the statistical tests
    TestFrequency : RngIntElt,
    // The threshold used in the Sampler chi^2 tests
    SamplerThreshold : FldReElt,
    // The threshold used in the Seeker chi^2 tests
    SeekerThreshold : FldReElt,
    // The maximum number of accepted tests until the Sampler stops
    MaxOKSampleBatches : RngIntElt,
    // The current number of accepted Sampler tests
    nOKSampleBatches : RngIntElt
>;

// General Prospector data
ProspectorInfo := recformat<
    // The Sampler random process
    Sampler : GrpRandProc,
    // The Seeker random process seed
    SeekerSeed  : SeqEnum,
    SeekerIndices  : SeqEnum,
    SeekerSeedSLPs : SeqEnum,
    // The Sampler random process seed, for normal closure version
    SamplerSeed  : SeqEnum,
    SamplerIndices  : SeqEnum,
    SamplerSeedSLPs : SeqEnum,
    // The Seeker random process seed for the current good vertex
    GoodSeekerSeed : SeqEnum,
    GoodSeekerIndices : SeqEnum,
    GoodSeekerSeedSLPs : SeqEnum,
    // The number of steps the Seeker walks away from a good vertex
    ArmLength : RngIntElt,
    // The maximum number of times the Seeker returns to a good vertex
    nReturnsToGoodVertex : RngIntElt,
    // The number of times the Seeker has returned to the current good vertex
    CurGoodVertexReturns : RngIntElt,
    // Have we found a good vertex?
    GoodVertexFound : BoolElt,
    // Has the Samper process stopped?
    AdvanceSampler : BoolElt,
    // Should the PR variants be used?
    UseAccelerator : BoolElt,
    UseNormalClosure : BoolElt,
    // List of generators of a supergroup, and if non-empty the
    // Prospector will find random elements of the normal closure in this group
    SuperGenerators : SeqEnum,
    // The number of invocations of the Prospector
    CurPos : RngIntElt,
    // ProspectorSamplingInfo
    SamplingData : Rec,
    // The Prospector behaviour can be switched off
    UseProspector : BoolElt,
    // Make Rattle biased towards using unused members of the team 
    BiasUnusedGenerators : BoolElt,
    // Number of initial generators in Rattle
    nInitialGenerators : RngIntElt
    >;

declare attributes Grp : ProspectorData;
declare verbose PRProspection, 10;

forward InitPRNormalClosure, InitPRWithSLPs, AdvanceProspector;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic InitialiseProspector(G :: GrpPerm :
    ArmLength := 10, nReturnsToGoodVertex := 10,
    PRSlots := Max([NumberOfGenerators(G), 10]),
    PRScramble := 100, TestSampleSize := 10, TestFrequency := 20,
    MaxOKSampleBatches := 5, SuperGroup := G, SLPsInSuper := [],
    UseAccelerator := false,
    SamplerSignificanceLevel := 0.01, SeekerSignificanceLevel := 0.01,
    UseProspector := true, BiasUnusedGenerators := false) -> BoolElt
    { Initialises the Prospector on a permutation group. The test used is
    t : g |-> number of cycles of g.}

    TestPropertyEvals := [];
    TestPropertyNames := [];
    
    // As random variable, use number of cycles
    Append(~TestPropertyEvals, func<g, elts, vals | &+[x[2] :
	x in CycleStructure(g)]>);
    Append(~TestPropertyNames, "Nof cycles");
    
    return InitProspector(G, TestPropertyEvals : ArmLength := ArmLength,
	PRSlots := PRSlots, PRScramble := PRScramble,
	nReturnsToGoodVertex := nReturnsToGoodVertex,
	TestSampleSize := TestSampleSize, TestFrequency := TestFrequency,
	MaxOKSampleBatches := MaxOKSampleBatches,
	TestPropertyNames := TestPropertyNames, SuperGroup := SuperGroup,
	UseAccelerator := UseAccelerator,
	SamplerSignificanceLevel := SamplerSignificanceLevel,
	SeekerSignificanceLevel := SeekerSignificanceLevel,
	UseProspector := UseProspector, SLPsInSuper := SLPsInSuper,
	BiasUnusedGenerators := BiasUnusedGenerators);
end intrinsic;

intrinsic InitialiseProspector(G :: GrpMat :
    ArmLength := 10, nReturnsToGoodVertex := 10,
    PRSlots := Max([NumberOfGenerators(G), 10]),
    PRScramble := 50, TestSampleSize := 10, TestFrequency := 20,
    MaxOKSampleBatches := 5, SuperGroup := G, SLPsInSuper := [],
    UseAccelerator := false,
    SamplerSignificanceLevel := 0.01, SeekerSignificanceLevel := 0.01,
    UseProspector := true, BiasUnusedGenerators := false) -> BoolElt
    { Initialises the Prospector on a matrix group. The test used is
    t : g |-> number of factor of characteristic polynomial of g.}

    // As random variable, use number of factors in char poly
    vprint PRProspection, 3 : "Test: Nof factors of char poly";
    TestPropertyEval := func<g, elts, vals |
	#FactoredCharacteristicPolynomial(g)>;

    return InitProspector(G, [TestPropertyEval] : TestPropertyNames :=
	["Nof factors of char poly"], ArmLength := ArmLength,
	PRSlots := PRSlots, PRScramble := PRScramble,
	nReturnsToGoodVertex := nReturnsToGoodVertex,
	TestSampleSize := TestSampleSize, TestFrequency := TestFrequency,
	MaxOKSampleBatches := MaxOKSampleBatches, SuperGroup := SuperGroup,
	UseAccelerator := UseAccelerator,
	SamplerSignificanceLevel := SamplerSignificanceLevel,
	SeekerSignificanceLevel := SeekerSignificanceLevel,
	UseProspector := UseProspector, SLPsInSuper := SLPsInSuper,
	BiasUnusedGenerators := BiasUnusedGenerators);
end intrinsic;

intrinsic InitProspector(G :: Grp, TestPropertyEvals :: SeqEnum[UserProgram] :
    ArmLength := 10,
    nReturnsToGoodVertex := 10,
    PRSlots := 10,
    PRScramble := 100,
    TestSampleSize := 10, 
    TestFrequency := 20,
    MaxOKSampleBatches := 5,
    SamplerSignificanceLevel := 0.01,
    SeekerSignificanceLevel := 0.01,
    UseAccelerator := false,
    SuperGroup := G,
    SLPsInSuper := [],
    UseProspector := true,
    BiasUnusedGenerators := false,
    TestBuckets := [{@ 0 @} : i in [1 .. #TestPropertyEvals]],
    TestExpectations := [[1] : i in [1 .. #TestPropertyEvals]],
    KnownDistributions := [false : i in [1 .. #TestPropertyEvals]],
    TestPropertyNames :=
    [Sprintf("Test %o", i) : i in [1 .. #TestPropertyEvals]]) -> BoolElt
    { The Product Replacement Prospector

    An extension of the product replacement algorithm that tries to
    keep the resulting straight line programs short, using heuristics
    and statistical tests.

    This initialises the Prospector on the generators of G. The
    function TestPropertyEval takes group elements and produces their
    corresponding values that are used to collect statistics. It
    should take 3 arguments:
    1. The element g of G whose value is to be calculated.
    2. The batch of elements selected so far.
    3. The values of the batch.

    The return value should be the value of g. }
	
    // Save info about the various tests
    TestData := [];
    for i in [1 .. #TestPropertyEvals] do
	Append(~TestData, rec<ProspectorTestInfo |
	    TestPropertyEval := TestPropertyEvals[i],
	    Description := TestPropertyNames[i],
	    SeekerTestValues := [],
	    SamplerTestValues := [],
	    Buckets := TestBuckets[i],
	    ExpectedValues := TestExpectations[i],
	    KnownDistribution := KnownDistributions[i],
	    SeekerOKPos := 0,
	    SamplerOKPos := 0>);
    end for;

    // Save general Prospector info
    G`ProspectorData := rec<ProspectorInfo |
	ArmLength := ArmLength,
	nReturnsToGoodVertex := nReturnsToGoodVertex,
	CurGoodVertexReturns := 0,
	GoodVertexFound := false,
	AdvanceSampler := true,
	UseAccelerator := UseAccelerator,
	UseProspector := UseProspector,
	BiasUnusedGenerators := BiasUnusedGenerators,
	CurPos := 0,
	SamplingData := rec<ProspectorSamplingInfo |
	TestSampleSize := TestSampleSize,
	SeekerTestElements := [],
	SamplerTestElements := [],
	TestFrequency := TestFrequency,
	TestData := TestData,
	SamplerThreshold := Probit(1 - SamplerSignificanceLevel),
	SeekerThreshold := Probit(1 - SeekerSignificanceLevel),
	MaxOKSampleBatches := MaxOKSampleBatches,
	nOKSampleBatches := 0>
	>;

    // Determine if we want the normal closure version
    if Generators(G) ne Generators(SuperGroup) then
	if #SLPsInSuper ne NumberOfGenerators(G) then
	    error "Must provide SLPs of generators in supergroup";
	end if;
	
	G`ProspectorData`SamplerSeed :=
	    InitPRNormalClosure(G, SuperGroup :
	    SLP_G := SLPsInSuper, nSlots := Max([PRSlots, 10]),
	    nScrambles := PRScramble, wordGroup := WordGroup(SuperGroup));
	
	G`ProspectorData`SeekerSeed, G`ProspectorData`SeekerSeedSLPs,
	    G`ProspectorData`SeekerIndices :=
	    InitPRNormalClosure(G, SuperGroup : SLP_G := SLPsInSuper,
	    nSlots := Max([PRSlots, 10]),
	    nScrambles := PRScramble, wordGroup := WordGroup(SuperGroup));
	
	G`ProspectorData`GoodSeekerSeed := G`ProspectorData`SeekerSeed;
	G`ProspectorData`GoodSeekerIndices := G`ProspectorData`SeekerIndices;
	G`ProspectorData`GoodSeekerSeedSLPs := G`ProspectorData`SeekerSeedSLPs;

	G`ProspectorData`UseNormalClosure := true;
    else
	G`ProspectorData`Sampler :=
	    RandomProcess(G : Slots := Max([PRSlots, 10]),
	    Scramble := PRScramble);
	
	G`ProspectorData`SeekerSeed,
	    G`ProspectorData`SeekerSeedSLPs,
	    G`ProspectorData`SeekerIndices :=
	    InitPRWithSLPs(G : nSlots := Max([PRSlots, 10]),
	    nScrambles := PRScramble);
	
	G`ProspectorData`GoodSeekerSeed := G`ProspectorData`SeekerSeed;
	G`ProspectorData`GoodSeekerIndices := G`ProspectorData`SeekerIndices;
	G`ProspectorData`GoodSeekerSeedSLPs := G`ProspectorData`SeekerSeedSLPs;

	G`ProspectorData`UseNormalClosure := false;
    end if;

    return true;
end intrinsic;
    
intrinsic Prospector(G :: Grp, WantedPropertyCheck :: UserProgram :
    MaxTries := 1000) -> BoolElt, GrpElt, GrpSLPElt
    { The Product Replacement Prospector

    An extension of the product replacement algorithm that tries to
    keep the resulting straight line programs short, using heuristics
    and statistical tests.

    This executes an already initialised Prospector on G and tries to
    find elements that satisfy a given property. The function
    WantedPropertyCheck should take GrpElt from G and produce
    BoolElt. The Prospector makes at most MaxTries random selections
    until it has found an element where the function returns true. }
    local nTries, elementOK, element, slp;
    
    if not assigned G`ProspectorData then
	error "Prospector has not been initialised";
    end if;

    // Run the Prospector engine until the element is found
    nTries := 0;
    element := Identity(G);
    slp := element;
    
    repeat
	delete element;
	delete slp;
	
	vprint PRProspection, 6 : "Advance prospector";
	element, slp := AdvanceProspector(G);
	nTries +:= 1;

	vprint PRProspection, 6 : "Testing element", element;
	elementOK := WantedPropertyCheck(element);
	vprint PRProspection, 6 : "Element OK:", elementOK;
    until elementOK or nTries ge MaxTries;

    if elementOK then
	return true, element, slp, nTries;
    else
	return false, _, _, nTries;
    end if;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// The three variants of PR, described in L-G & Murray,
// 'Variants of product replacement', Contemporary Mathematics 298, 2002

procedure RattleWithSLP(~slots, ~slps, ~indices :
    BiasUnusedGenerators := false, nGens := #slots - 1)

    i := Random(1, #slots - 1);

    repeat
	j := Random(1, #slots - 1);
    until j ne i;

    if BiasUnusedGenerators and #indices[#slots] lt nGens then
	sort := [1 .. #slots - 1];
	Sort(~sort, function(i, j)
	    n := #(indices[i] diff indices[#slots]) -
	    #(indices[j] diff indices[#slots]);
	    if n eq 0 then
		return #indices[i] - #indices[j];
	    else
		return n;
	    end if;
	end function);
	
	k := sort[1];
	indices[i] join:= indices[j];
	indices[#slots] join:= indices[k];
    else
	k := Random(1, #slots - 1);
    end if;
    
    slots[i] *:= slots[j];    
    slots[#slots] *:= slots[k];
    
    slps[i] *:= slps[j];    
    slps[#slps] *:= slps[k];    
end procedure;

// Rattle with accelerator, ie one slot which is heavily biased
procedure RattleWithAccelerator(~slots, ~slps, ~indices :
    BiasUnusedGenerators := false, nGens := #slots - 1)
    local i, j, k;
    
    i := Random(2, #slots - 1);
    j := Random(2, #slots - 1);

    if BiasUnusedGenerators and #indices[#slots] lt nGens then
	sort := [1 .. #slots - 1];
	Sort(~sort, function(i, j)
	    n := #(indices[i] diff indices[#slots]) -
	    #(indices[j] diff indices[#slots]);

	    if n eq 0 then
		return #indices[i] - #indices[j];
	    else
		return n;
	    end if;
	end function);

	k := sort[1];
	indices[i] join:= indices[j];
	indices[#slots] join:= indices[k];
    else
	k := Random(1, #slots - 1);
    end if;

    slots[i] *:= slots[1];
    slots[1] *:= slots[j];
    slots[#slots] *:= slots[k];

    slps[i] *:= slps[1];
    slps[1] *:= slps[j];
    slps[#slps] *:= slps[k];
end procedure;

// Rattle that finds random elements of a normal closure in a supergroup
// Useful for finding random elements of a derived group
procedure RattleNormalClosure(~slots, ~slps)
    local i, j, k, a, b, c;

    i := Random(1, #slots[1]);
    repeat
	j := Random(1, #slots[1]);
    until j ne i;
    k := Random(1, #slots[1]);

    a := Random(1, #slots[2] - 1);
    repeat
	b := Random(1, #slots[2] - 1);
    until j ne i;
    c := Random(1, #slots[2] - 1);

    slots[1][i] *:= slots[1][j];
    slots[2][a] *:= slots[2][b]^slots[1][k];
    slots[2][#slots[2]] *:= slots[2][c];

    slps[1][i] *:= slps[1][j];
    slps[2][a] *:= slps[2][b]^slps[1][k];
    slps[2][#slps[2]] *:= slps[2][c];
end procedure;

procedure RattleNormalClosureNoSLP(~slots)
    local i, j, k, a, b, c;

    i := Random(1, #slots[1]);
    repeat
	j := Random(1, #slots[1]);
    until j ne i;
    k := Random(1, #slots[1]);

    a := Random(1, #slots[2] - 1);
    repeat
	b := Random(1, #slots[2] - 1);
    until j ne i;
    c := Random(1, #slots[2] - 1);

    slots[1][i] *:= slots[1][j];
    slots[2][a] *:= slots[2][b]^slots[1][k];

    slots[2][#slots[2]] *:= slots[2][c];
end procedure;

// Initialise our Rattle
function InitPRWithSLPs(G : nScrambles := 50, Gens := UserGenerators(G),
    wordGroup := WordGroup(G),
	SLPs := [W.i : i in [1 .. NumberOfGenerators(G)]] where W is wordGroup,
	nSlots := Max([#Gens, 10]))
	local seed, seedSLPs, indices;

    // Initial seed
    vprint PRProspection, 6 : "Create initial seed SLP";
    if #Gens eq 0 then
	Gens := [Identity(G)];
	SLPs := [Identity(wordGroup)];
    end if;

    G`ProspectorData`nInitialGenerators := #Gens;
    assert #SLPs eq #Gens;

    indices := [{i mod #Gens + 1} : i in [1 .. nSlots]];
    seed := [Gens[Rep(indices[i])] : i in [1 .. nSlots]];
    seedSLPs := [SLPs[Rep(indices[i])] : i in [1 .. nSlots]];
    
    // Add accumulator
    Append(~seed, Identity(G));
    Append(~seedSLPs, Identity(wordGroup));
    Append(~indices, {});

    // Initial scrambling
    vprint PRProspection, 6 : "Scramble initial seed SLP";
    while nScrambles gt 0 do
	if G`ProspectorData`UseAccelerator then
	    RattleWithAccelerator(~seed, ~seedSLPs, ~indices :
		BiasUnusedGenerators := G`ProspectorData`BiasUnusedGenerators,
		nGens := G`ProspectorData`nInitialGenerators);
	else
	    RattleWithSLP(~seed, ~seedSLPs, ~indices :
		BiasUnusedGenerators := G`ProspectorData`BiasUnusedGenerators,
		nGens := G`ProspectorData`nInitialGenerators);
	end if;
	
	nScrambles -:= 1;
    end while;
    
    return seed, seedSLPs, indices;
end function;

// Initialise our Rattle, normal closure version
// G is the group, H is the supergroup in which the normal closure of G is used
function InitPRNormalClosure(G, H : gens := UserGenerators(G),
    superGens := UserGenerators(H),
	nScrambles := 50, nSlots := Max([#gens, #superGens, 10]),
	wordGroup := WordGroup(G), superWordGroup := WordGroup(H),
	SLP_G := [W.i : i in [1 .. NumberOfGenerators(G)]]
	where W is wordGroup,
	SLP_H := [W.i : i in [1 .. NumberOfGenerators(H)]]
	where W is superWordGroup)
	local seed, seedSLPs;
    
    G`ProspectorData`nInitialGenerators := #gens;
    nSlots := Max([nSlots, #gens]);
    
    // Initial seed
    vprint PRProspection, 6 : "Create initial seed SLP";
    if #superGens eq 0 then
	assert #gens eq 0;

	gens := [Identity(G)];
	SLP_G := [Identity(wordGroup)];
	superGens := [Identity(H)];
	SLP_H := [Identity(superWordGroup)];
    else
	if #gens eq 0 then
	    gens := [Identity(G)];
	    SLP_G := [Identity(wordGroup)];
	end if;
    end if;
    
    // Initial seed
    vprint PRProspection, 6 : "Create initial seed";
    seed := [];
    seedSLPs := [];
    
    Append(~seed, [superGens[(i mod #superGens) + 1] :
	i in [1 .. nSlots]]);
    Append(~seedSLPs, [SLP_H[(i mod #SLP_H) + 1] : i in [1 .. nSlots]]);

    Append(~seed, [gens[(i mod #gens) + 1] : i in [1 .. nSlots]]);
    Append(~seedSLPs, [SLP_G[(i mod #SLP_G) + 1] : i in [1 .. nSlots]]);
    
    // Add accumulator
    Append(~seed[2], Identity(G));
    Append(~seedSLPs[2], Identity(wordGroup));

    // Initial scrambling
    vprint PRProspection, 6 : "Scramble initial seed SLP";
    while nScrambles gt 0 do
	RattleNormalClosure(~seed, ~seedSLPs);

	nScrambles -:= 1;
    end while;
    
    return seed, seedSLPs, [];
end function;

// Chi^2 test, given buckets and expected buckets
// threshold is the test threshold for a N(0, 1) distribution
function ChiSquareTest(values, expectations, threshold)
    local R, f, vals, expect, c, r, n, N, value;
    
    assert #values eq #expectations;
    R := RealField();
    
    // degrees of freedom
    f := R ! (#values - 1);
    
    // Chi-square distributed value, using Yates correction
    // Use 'test for homogeniety' to see if two samples seem to come from
    // the same distribution
    
    // Remove zeros, they don't contribute
    vals := [values[i] : i in [1 .. #values] | values[i] ne 0 or
	expectations[i] ne 0];
    expect := [expectations[i] : i in [1 .. #values] | values[i] ne 0 or
	expectations[i] ne 0];
    
    c := [R | vals[i] + expect[i] : i in [1 .. #vals]];
    r := [R | &+vals, &+expect];   
    n := &+ r;
    N := Matrix(R, 2, #vals, vals cat expect);

    // The chi^2 test statistic
    value := n * &+[&+[(N[i, j] - r[i] * c[j] / n - 0.5)^2  / (r[i] * c[j]):
	j in [1 .. NumberOfColumns(N)]] : i in [1 .. NumberOfRows(N)]];
    
    // Wilson-Hilferty approximation of chi^2   
    // approximately N(0, 1) distributed
    value := (Root(value / f, 3) - (1 - 2 / (9 * f))) / Sqrt(2 / (9 * f));
    
    vprintf PRProspection, 4 : "Value %o, Threshold %o\n", value, threshold;
    if value gt threshold then
	return false;
    else
	return true;
    end if;
end function;

// Takes a batch of sample values, puts them into buckets and performs a
// chi^2 test
function StatisticalTest(sampleValues, bucketValues, expectations, threshold)
    local valuesMult, valuesSet, buckets;
    
    valuesMult := SequenceToMultiset(sampleValues);
    valuesSet := SetToIndexedSet(MultisetToSet(valuesMult));

    // Fill buckets for already known bucket values
    assert #bucketValues eq #expectations;
    buckets := [Multiplicity(valuesMult, value) : value in bucketValues];
    valuesSet diff:= bucketValues;

    // Fill new buckets 
    if #valuesSet gt 0 then
	buckets cat:= [Multiplicity(valuesMult, value) : value in valuesSet];
	bucketValues join:= valuesSet;
	expectations cat:= [0 : i in [1 .. #valuesSet]];
    end if;

    assert #buckets eq #expectations;    
    vprint PRProspection, 4 : bucketValues, buckets, expectations;
    delete valuesMult;
    delete valuesSet;
    
    return ChiSquareTest(buckets, expectations,
	threshold), bucketValues, buckets, expectations;
end function;

// Evaluate a test function and add element to batch
procedure TestEval(element, elements,
    testPropertyEval, ~values, testSampleSize)

    // Calculate sample value
    value := testPropertyEval(element, elements, values);
    
    // Check sampler batch
    Append(~values, value);
    if #values gt testSampleSize then
	Remove(~values, 1);
    end if;
end procedure;

// Advance a process with SLPs (eg the Seeker process)
procedure AdvanceProcessSLP(~seed, ~elements, ~SLPs, ~indices, testSampleSize,
    UseNormalClosure, UseAccelerator, BiasUnusedGenerators, nGens)
	local element, value;
    
    // One PR step, using the different PR variants
    if UseNormalClosure then
	RattleNormalClosure(~seed, ~SLPs);

	element := seed[2][#seed[2]];
    elif UseAccelerator then
	RattleWithAccelerator(~seed, ~SLPs, ~indices :
	    BiasUnusedGenerators := BiasUnusedGenerators, nGens := nGens);

	element := seed[#seed];
    else
	RattleWithSLP(~seed, ~SLPs, ~indices :
	    BiasUnusedGenerators := BiasUnusedGenerators, nGens := nGens);
	
	element := seed[#seed];
    end if;
    
    // Check sampler batch
    Append(~elements, element);
    if #elements gt testSampleSize then
	Remove(~elements, 1);
    end if;
end procedure;

// Advance a built-in Magma process (eg the Sampler process)
procedure AdvanceMagmaProcess(process, ~elements, testSampleSize)
    local value;
    
    // One PR step
    element := Random(process);
    
    // Check sampler batch
    Append(~elements, element);
    if #elements gt testSampleSize then
	Remove(~elements, 1);
    end if;
end procedure;

// Advance a normal closure process (without SLPs)
procedure AdvanceProcessNormalClosure(~seed, ~elements, testSampleSize)
    local value;

    // One PR step
    RattleNormalClosureNoSLP(~seed);
    element := seed[2][#seed[2]];

    // Check sampler batch
    Append(~elements, element);
    if #elements gt testSampleSize then
	Remove(~elements, 1);
    end if;
end procedure;

procedure ProspectorStatisticalTests(G)
    local testsOK, flag, bucketValues, buckets, expectations;

    if G`ProspectorData`AdvanceSampler then
	// Compare sample experiment against expected distribution
	testsOK := true;
	
	for i in [1 .. #G`ProspectorData`SamplingData`TestData] do
	    // Perform statistical test on Sampler batch
	    flag, bucketValues, buckets, expectations :=
		StatisticalTest(G`ProspectorData`
		SamplingData`TestData[i]`SamplerTestValues,
		G`ProspectorData`SamplingData`TestData[i]`Buckets,
		G`ProspectorData`SamplingData`TestData[i]`ExpectedValues,
		G`ProspectorData`SamplingData`SamplerThreshold);
	    
	    // If the distribution is not known, compare next batch against
	    // this one, to see if they are changing
	    delete G`ProspectorData`SamplingData`TestData[i]`ExpectedValues;
	    delete G`ProspectorData`SamplingData`TestData[i]`Buckets;
	    
	    if G`ProspectorData`SamplingData`TestData[i]`KnownDistribution then
		G`ProspectorData`SamplingData`TestData[i]`ExpectedValues :=
		    expectations;
		G`ProspectorData`SamplingData`TestData[i]`Buckets :=
		    bucketValues;
		delete buckets;
	    else
		G`ProspectorData`SamplingData`TestData[i]`ExpectedValues :=
		    buckets;
		G`ProspectorData`SamplingData`TestData[i]`Buckets :=
		    bucketValues;
		delete expectations;
	    end if;
	    
	    if not flag then
		vprintf PRProspection, 4 : "Sampler test %o rejects!\n", i;
		testsOK := false;
	    else
		if G`ProspectorData`SamplingData`TestData[i]`SamplerOKPos
		    eq 0 then
		    G`ProspectorData`SamplingData`TestData[i]`SamplerOKPos:=
			G`ProspectorData`CurPos;
		end if;
	    end if;
	end for;
	
	if testsOK then
	    // Sampler data seems to fit
	    G`ProspectorData`SamplingData`nOKSampleBatches +:= 1;
	    
	    // Stop sampler if data seems to be OK
	    if G`ProspectorData`SamplingData`nOKSampleBatches ge
		G`ProspectorData`SamplingData`MaxOKSampleBatches then
		G`ProspectorData`AdvanceSampler := false;
		
		vprint PRProspection, 3 : "Stopping sampler at position ",
		    G`ProspectorData`CurPos;
	    end if;
	else
	    G`ProspectorData`SamplingData`nOKSampleBatches := 0;
	end if;	    
    end if;

    testsOK := true;
    for i in [1 .. #G`ProspectorData`SamplingData`TestData] do
	
	vprintf PRProspection, 6 :
	    "Running Seeker statistical test %o with values %o\n",
	    i, G`ProspectorData`SamplingData`TestData[i]`SeekerTestValues;

	// Perform statistical test on Seeker batch	
	flag, bucketValues, buckets, expectations :=
	    StatisticalTest(G`ProspectorData`
	    SamplingData`TestData[i]`SeekerTestValues,
	    G`ProspectorData`SamplingData`TestData[i]`Buckets,
	    G`ProspectorData`SamplingData`TestData[i]`ExpectedValues,
	    G`ProspectorData`SamplingData`SeekerThreshold);

	delete bucketValues;
	delete buckets;
	delete expectations;
	
	if not flag then
	    vprintf PRProspection, 4 : "Seeker test %o rejects!\n", i;
	    testsOK := false;
	else
	    if G`ProspectorData`SamplingData`TestData[i]`SeekerOKPos eq 0 then
		G`ProspectorData`SamplingData`TestData[i]`SeekerOKPos :=
		    G`ProspectorData`CurPos;
	    end if;
	end if;
    end for;

    if testsOK then
	// Seeker data seems to fit
	G`ProspectorData`GoodVertexFound := true;
	vprint PRProspection, 4 : "Seeker found a good spot at position ",
	    G`ProspectorData`CurPos;
    else
	G`ProspectorData`GoodVertexFound := false;
    end if;  
end procedure;

procedure UpdateProspectorPosition(G)
    // See if we have reached the end of an Arm
    if G`ProspectorData`CurPos mod G`ProspectorData`ArmLength eq 0 then
	// Start new Arm

	if G`ProspectorData`GoodVertexFound and
	    G`ProspectorData`CurGoodVertexReturns lt
	    G`ProspectorData`nReturnsToGoodVertex then
	    
	    // Move back to last good vertex, if one is known
	    delete G`ProspectorData`SeekerSeed;
	    delete G`ProspectorData`SeekerSeedSLPs;

	    G`ProspectorData`SeekerSeed := G`ProspectorData`GoodSeekerSeed;
	    G`ProspectorData`SeekerSeedSLPs :=
		G`ProspectorData`GoodSeekerSeedSLPs;
	    
	    // Have we stayed long enough at this good vertex?
	    G`ProspectorData`CurGoodVertexReturns +:= 1;
	else
	    // If no good vertex known, try the one at the end of this Arm
	    delete G`ProspectorData`GoodSeekerSeed;
	    delete G`ProspectorData`GoodSeekerSeedSLPs;
	    
	    G`ProspectorData`GoodSeekerSeed := G`ProspectorData`SeekerSeed;
	    G`ProspectorData`GoodSeekerSeedSLPs :=
		G`ProspectorData`SeekerSeedSLPs;
	    
	    G`ProspectorData`CurGoodVertexReturns := 0;
	end if;
    end if;
end procedure;

function AdvanceProspector(G)
    local sampleElement, seekerElement, seekerSLP;
    
    G`ProspectorData`CurPos +:= 1;

    if G`ProspectorData`UseProspector and G`ProspectorData`AdvanceSampler then
	vprint PRProspection, 4 : "Advance sampler";
	
	// Advance the sampler process one step
	if G`ProspectorData`UseNormalClosure then
	    AdvanceProcessNormalClosure(~G`ProspectorData`SamplerSeed,
		~G`ProspectorData`SamplingData`SamplerTestElements,
		G`ProspectorData`SamplingData`TestSampleSize);
	    
	    sampleElement := G`ProspectorData`SamplingData`
		SamplerTestElements[#G`ProspectorData`SamplingData`
		SamplerTestElements];
	else	    
	    AdvanceMagmaProcess(G`ProspectorData`Sampler,
		~G`ProspectorData`SamplingData`SamplerTestElements,
		G`ProspectorData`SamplingData`TestSampleSize);
	    
	    sampleElement := G`ProspectorData`SamplingData`
		SamplerTestElements[#G`ProspectorData`SamplingData`
		SamplerTestElements];
	end if;

	vprint PRProspection, 4 : "Execute sampler tests";

	// Evaluate all the tests on the new sample element
	for i in [1 .. #G`ProspectorData`SamplingData`TestData] do
	    TestEval(sampleElement,
		G`ProspectorData`SamplingData`SamplerTestElements,
		G`ProspectorData`SamplingData`TestData[i]`TestPropertyEval,
		~G`ProspectorData`SamplingData`TestData[i]`SamplerTestValues,
		G`ProspectorData`SamplingData`TestSampleSize);
	end for;
    end if;
    
    vprint PRProspection, 4 : "Advance seeker";
    
    // Advance the seeker process one step
    AdvanceProcessSLP(~G`ProspectorData`SeekerSeed,
	~G`ProspectorData`SamplingData`SeekerTestElements,
	~G`ProspectorData`SeekerSeedSLPs,
	~G`ProspectorData`SeekerIndices,
	G`ProspectorData`SamplingData`TestSampleSize,
	G`ProspectorData`UseNormalClosure,
	G`ProspectorData`UseAccelerator,
	G`ProspectorData`BiasUnusedGenerators,
	G`ProspectorData`nInitialGenerators);

    if G`ProspectorData`UseNormalClosure then
	seekerElement :=
	    G`ProspectorData`SeekerSeed[2][#G`ProspectorData`SeekerSeed[2]];
	seekerSLP := G`ProspectorData`SeekerSeedSLPs[2]
	    [#G`ProspectorData`SeekerSeedSLPs[2]];
    else
	seekerElement :=
	    G`ProspectorData`SeekerSeed[#G`ProspectorData`SeekerSeed];
	seekerSLP :=
	    G`ProspectorData`SeekerSeedSLPs[#G`ProspectorData`SeekerSeedSLPs];
    end if;
    
    if G`ProspectorData`UseProspector then
	assert #G`ProspectorData`SamplingData`SamplerTestElements eq
	    #G`ProspectorData`SamplingData`SeekerTestElements;
	
	vprint PRProspection, 4 : "Exexcute seeker tests";
	
	// Evaluate all the tests on the new seeker element
	for i in [1 .. #G`ProspectorData`SamplingData`TestData] do
	    TestEval(seekerElement,
		G`ProspectorData`SamplingData`SeekerTestElements,
		G`ProspectorData`SamplingData`TestData[i]`TestPropertyEval,
		~G`ProspectorData`SamplingData`TestData[i]`SeekerTestValues,
		G`ProspectorData`SamplingData`TestSampleSize);
	end for;
	
	// Perform statistical checks to see if sampler data is changing and if
	// seeker data corresponds with sample data
	if G`ProspectorData`CurPos mod
	    G`ProspectorData`SamplingData`TestFrequency eq 0 and
	    #G`ProspectorData`SamplingData`SamplerTestElements ge
	    G`ProspectorData`SamplingData`TestSampleSize then
	    
	    vprint PRProspection, 4 : "Exexcute statistical tests";
	    ProspectorStatisticalTests(G);
	end if;
	
	// Update arm counters etc
	vprint PRProspection, 4 : "Update Prospector position";    
	UpdateProspectorPosition(G);
    end if;
    
    return seekerElement, seekerSLP;
end function;
/*****************************************************************************/
/* INTRINSICS FOR PROBABILITIES						     */
/*****************************************************************************/

intrinsic InverseErf(z :: FldReElt) -> FldReElt
    { Calculate inverse error function using well-known series expansion.

    http://mathworld.wolfram.com/InverseErf.html
    http://functions.wolfram.com/GammaBetaErf/InverseErf/06/
    }
    // Approximation that is ok when z is close to 1
    x := Log(2 / (Pi(RealField()) * (z - 1)^2));
    return Sqrt((x - Log(x)) / 2);
end intrinsic;

intrinsic Probit(p :: FldReElt) -> FldReElt
    { The inverse of the normal cumulative distribution function. }
    return Sqrt(2) * InverseErf(2 * p - 1);
end intrinsic;


