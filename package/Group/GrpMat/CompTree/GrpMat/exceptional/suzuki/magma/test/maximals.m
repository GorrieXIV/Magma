//
// Test file for presentations in Suzuki package. 
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("SuzukiGeneral", 5);
SetVerbose("SuzukiTensor", 5);
SetVerbose("SuzukiStandard", 5);
SetVerbose("SuzukiCrossChar", 5);
SetVerbose("SuzukiMembership", 0);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 1;
stop  := 10;

// Number of conjugations for each maximal subgroup
nMaximalConj := 2;

// Number of random conjugates to check for each field size
nConjugates := 2;

// Test will check representations of degree up to 4^n, where n is the
// following:
maxDegreePower := 1;

// Number of iterations of cross characteristic tests
nofCrossChar := 0;

// For each iteration, and for each field size q \leq p^n, a cross char
// representation will be checked. p and n are given here:
maxPrimeNr := 2;
maxDeg     := 2;

procedure testSzCopy(G)

    print "Get derived group";

    // Move to another generating set
    G := DerivedGroupMonteCarlo(G);
    
    print "Recognise Suzuki copy", NumberOfGenerators(G);
    flag, _, _, _, slp2g := RecogniseSz(G);
    assert flag;
    
    print "Find maximal subgroups";
    maximals, slps := SuzukiMaximalSubgroups(G);

    print "Check maximal subgroup SLPs";
    assert forall{i : i in [1 .. #slps] | forall{x : x in slps[i] |
	IsCoercible(Domain(slp2g), x)}};
    assert forall{i : i in [1 .. #slps] | UserGenerators(maximals[i]) eq
	slp2g(slps[i])};

    for M in maximals do

	print "Conjugating maximal subgroup of order", #M;
	for i in [1 .. nMaximalConj] do
	    assert assigned G`RandomProcess;

	    g := Random(G`RandomProcess);
	    N := M^g;

	    print "Find conjugating element";
	    conj, slp := SuzukiMaximalSubgroupsConjugacy(G, M, N);

	    print "Check conjugating element";
	    assert IsCoercible(Domain(slp2g), slp);
	    assert slp2g(slp) eq conj;
	    assert M^conj eq N;
	end for;

	print "Conjugations successful";
    end for;
end procedure;

for m in [start .. stop] do
    q := 2^(2 * m + 1);
    G := Sz(q);
    field := CoefficientRing(G);

    print "Checking field size", q, m;
    
    testSzCopy(G);
    
    for i in [1 .. nConjugates] do
	testSzCopy(RandomConjugate(G));
    end for;

    print "Checking tensor products";
    
    for i in [2 .. maxDegreePower] do
	
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 4^i;
	
	// Check each twist
	for tuple in twists do
	    if forall{i : i in [1 .. #tuple - 1] |
		tuple[i] lt tuple[i + 1]} then

		// Create Suzuki tensor product
		GG := SuzukiIrreducibleRepresentation(field,
		    [tuple[i] : i in [1 .. #tuple]]);
		
		assert IsAbsolutelyIrreducible(GG);
		assert Degree(GG) eq degree;
		assert CoefficientRing(GG) eq field;

		// Map to a smaller field if possible
		flag, HH := IsOverSmallerField(GG);
		if flag then
		    print "over smaller field", #CoefficientRing(HH);
		    GG := HH;
		end if;

		testSzCopy(RandomConjugate(GG));
	    end if;
	end for;
    end for;

    print "Checking odd char reps";
    
    for k in [1 .. nofCrossChar] do
	for i in [1 .. maxPrimeNr] do
	    p := NthPrime(i + 1);
	    
	    for j in [1 .. maxDeg] do

		// Create a cross char representation over GF(p^j)
		_, P := SuzukiPermutationRepresentation(G :
		    CheckInput := false, FieldSize := q);
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

		testSzCopy(RandomConjugate(GG));
	    end for;
	end for;
    end for;
end for;
