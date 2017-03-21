//
// Test file Sylow subgroup creation/conjugation part of Suzuki package.
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("SuzukiGeneral", 5);
SetVerbose("SuzukiTensor", 5);
SetVerbose("SuzukiStandard", 5);
SetVerbose("SuzukiCrossChar", 5);
SetVerbose("SuzukiMembership", 0);
SetVerbose("SuzukiSylow", 1);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 1;
stop  := 3;

// Number of pairs of Sylow p-subgroups to create and conjugate for each
// prime p dividing the order of Sz(q)
nSylows := 2;

// Number of random conjugates to consider for each field size
nConjugates := 5;

// Test will consider representations of degree up to 4^n, where n is the
// following:
maxDegreePower := 0;

// Number of iterations of cross characteristic tests
nofCrossChar := 0;

// For each iteration, and for each field size q \leq p^n, a cross char
// representation will be considered. p and n are given here:
maxPrimeNr := 0;
maxDeg     := 0;


procedure testSzCopy(G)
    // Move to another generating set
    G := DerivedGroupMonteCarlo(G);
    flag, _, _, _, SLP2G := RecogniseSz(G);
    assert flag;

    q := #CoefficientRing(G`SuzukiReductionData`stdCopy);
	
    for p in [x[1] : x in Factorization(#G`SuzukiReductionData`stdCopy) | x[1] eq 2] do

	print "Consider Sylow p-subgroups for p =", p;
	
	// For each prime, conjugate a number of Sylows
	for i in [1 .. nSylows] do

	    print "Find subgroups";
	    
	    // Create Sylow p-subgroups
	    R, l := SuzukiSylow(G, p);
	    assert forall{x : x in l | IsCoercible(Domain(SLP2G), x)};
	    assert SLP2G(l) eq UserGenerators(R);
	    S, l := SuzukiSylow(G, p);
	    assert forall{x : x in l | IsCoercible(Domain(SLP2G), x)};
	    assert SLP2G(l) eq UserGenerators(S);

	    // Check generator orders
	    assert forall{g : g in Generators(R) |
		IsDivisibleBy(Order(g : Proof := false), p) or
		Order(g : Proof := false) eq 4};
	    assert forall{g : g in Generators(S) |
		IsDivisibleBy(Order(g : Proof := false), p) or
		Order(g : Proof := false) eq 4};

	    print "Find conjugating element";

	    // Conjugate Sylow subgroups
	    conj, slp := SuzukiSylowConjugacy(G, R, S, p);

	    print "Check conjugating element";
	    assert IsCoercible(Domain(SLP2G), slp);
	    assert SLP2G(slp) eq conj;
	    assert R^conj eq S;
	end for;
    end for;
end procedure;

for m in [start .. stop] do

    q := 2^(2 * m + 1);
    G := Sz(q);
    field := CoefficientRing(G);
    print "Checking field size", m, q;

    testSzCopy(G);    
    
    for i in [1 .. nConjugates] do
	testSzCopy(RandomConjugate(G));
    end for;

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
