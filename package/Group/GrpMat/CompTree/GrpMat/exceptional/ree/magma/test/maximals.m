//
// Test file for presentations in Suzuki package. 
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("ReeGeneral", 5);
SetVerbose("ReeConjugate", 5);
SetVerbose("ReeInvolution", 0);
SetVerbose("ReeTrick", 5);
SetVerbose("ReeTensor", 5);
SetVerbose("ReeStandard", 5);
SetVerbose("ReeCrossChar", 5);
SetVerbose("ReeSylow", 5);
SetVerbose("ReeMembership", 0);

// Low and high values of m used in the test, where the field size is
// q = 3^(2 * m + 1)
start := 1;
stop  := 10;

// Number of conjugations for each maximal subgroup
nMaximalConj := 1;
    
// Number of random conjugates to check for each field size
nConjugates := 2;

// Number of 27-dim representations to recognise
nSymSquares := 0;

// Test will check tensor products of 7-dim representations of degree up to
// 7^n, where n is the following:
maxDegreePower := 1;

// Test will check reps of degree 27 * 7^n with maximum n as follows:
maxTensor := 0;

// Test will check reps of degree 27^n with maximum n as follows:
maxSymTensor := 0;

// Number of iterations of cross characteristic tests
// Smallest cross char rep has dimension almost 20000, so it's not practical
nofCrossChar := 0;

// For each iteration, and for each field size q \leq p^n, a cross char
// representation will be checked. p and n are given here:
maxPrimeNr := 2;
maxDeg     := 2;


procedure testReeCopy(G)
    
    print "Get derived group";
    G := DerivedGroupMonteCarlo(G);

    print "Recognise group";
    flag, _, _, _, slp2g := RecogniseRee(G);
    assert flag;
    print "Recognition successful";

    print "Find maximal subgroups";
    maximals, slps := ReeMaximalSubgroups(G);

    print "Check maximal subgroup SLPs";
    assert forall{i : i in [1 .. #slps] | forall{x : x in slps[i] |
	IsCoercible(Domain(slp2g), x)}};
    assert forall{i : i in [1 .. #slps] | UserGenerators(maximals[i]) eq
	slp2g(slps[i])};

    for M in maximals[1 .. #maximals - 3] do

	print "Conjugating maximal subgroup of order", #M;
	for i in [1 .. nMaximalConj] do
	    assert assigned G`RandomProcess;

	    g := Random(G`RandomProcess);
	    N := M^g;

	    print "Find conjugating element";
	    conj, slp := ReeMaximalSubgroupsConjugacy(G, M, N);

	    print "Check conjugating element";
	    assert IsCoercible(Domain(slp2g), slp);
	    assert slp2g(slp) eq conj;
	    assert M^conj eq N;
	end for;

	print "Conjugations successful";
    end for;
end procedure;


for m in [start .. stop] do
    field := GF(3, 2 * m + 1);
    G := Ree(field);

    print "Test standard copy";
    testReeCopy(G);
    
    for i in [1 .. nConjugates] do
	print "Test conjugate";
	testReeCopy(RandomConjugate(G));
    end for;

    for i in [1 .. nSymSquares] do
	tuple := [27, 0];
	
	// Create 27-dim Ree copy
	GG := ReeIrreducibleRepresentation(field, [tuple]);
	
	assert IsAbsolutelyIrreducible(GG);
	assert Degree(GG) eq 27;
	assert CoefficientRing(GG) eq field;
	assert not IsOverSmallerField(GG);

	print "Test 27-dim";
	testReeCopy(RandomConjugate(GG));
    end for;
    
    for i in [2 .. maxDegreePower] do
	
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 7^i;
	
	// Check each twist
	for tuple in twists do
	    if forall{i : i in [1 .. #tuple - 1] |
		tuple[i] lt tuple[i + 1]} then

		// Create Ree tensor product
		GG := ReeIrreducibleRepresentation(field,
		    [[7, tuple[i]] : i in [1 .. #tuple]]);
		
		assert IsAbsolutelyIrreducible(GG);
		assert Degree(GG) eq degree;
		assert CoefficientRing(GG) eq field;

		// Map to a smaller field if possible
		flag, HH := IsOverSmallerField(GG);
		if flag then
		    print "over smaller field", #CoefficientRing(HH);
		    GG := HH;
		end if;

		printf "Test tensor product of degree %o and twists %o\n",
		    degree, tuple;
		testReeCopy(RandomConjugate(GG));
	    end if;
	end for;
    end for;

    for i in [2 .. maxTensor] do
	
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 27 * 7^(i - 1);
	
	// Check each twist
	for tuple in twists do
	    if forall{i : i in [1 .. #tuple - 1] |
		tuple[i] lt tuple[i + 1]} then

		// Create Ree tensor product
		GG := ReeIrreducibleRepresentation(field,
		    [[27, tuple[1]]] cat [[7, tuple[i + 1]] :
		    i in [1 .. #tuple - 1]]);
		
		assert IsAbsolutelyIrreducible(GG);
		assert Degree(GG) eq degree;
		assert CoefficientRing(GG) eq field;

		// Map to a smaller field if possible
		flag, HH := IsOverSmallerField(GG);
		if flag then
		    print "over smaller field", #CoefficientRing(HH);
		    GG := HH;
		end if;

		printf "Test tensor product of degree %o and twists %o\n",
		    degree, tuple;
		testReeCopy(RandomConjugate(GG));
	    end if;
	end for;
    end for;

    for i in [2 .. maxSymTensor] do
	
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 27^i;
	
	// Check each twist
	for tuple in twists do
	    if forall{i : i in [1 .. #tuple - 1] |
		tuple[i] lt tuple[i + 1]} then

		// Create Ree tensor product
		GG := ReeIrreducibleRepresentation(field,
		    [[27, tuple[i]] : i in [1 .. #tuple]]);
		
		assert IsAbsolutelyIrreducible(GG);
		assert Degree(GG) eq degree;
		assert CoefficientRing(GG) eq field;

		// Map to a smaller field if possible
		flag, HH := IsOverSmallerField(GG);
		if flag then
		    print "over smaller field", #CoefficientRing(HH);
		    GG := HH;
		end if;

		printf "Test tensor product of degree %o and twists %o\n",
		    degree, tuple;
		testReeCopy(RandomConjugate(GG));
	    end if;
	end for;
    end for;
    
    
    for k in [1 .. nofCrossChar] do
	for i in [1 .. maxPrimeNr] do
	    p := NthPrime(i + 1);
	    
	    for j in [1 .. maxDeg] do

		// Create a cross char representation over GF(p^j)
		_, P := ReePermutationRepresentation(G);
		M := PermutationModule(P, GF(p, j));
		series, factors := CompositionSeries(M);
		dim := Min([Dimension(f) : f in factors |
		    Dimension(f) gt 1]);

		// Take smallest dimensional representation
		factor := rep{f : f in factors | Dimension(f) eq dim};
		GG := ActionGroup(factor);

		// Make sure input is absolutely irreducible and over
		// the minimal field
		if not IsAbsolutelyIrreducible(GG) then
		    GG := AbsoluteRepresentation(GG);
		end if;

		flag, HH := IsOverSmallerField(GG);
		if flag then
		    GG := HH;
		end if;

		testReeCopy(RandomConjugate(GG));
	    end for;
	end for;
    end for;
end for;
