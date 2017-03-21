//
// Main test file for Suzuki package. Should be a comprehensive test of the
// constructive recognition functionality.
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("SuzukiGeneral", 5);
SetVerbose("SuzukiTensor", 5);
SetVerbose("SuzukiStandard", 5);
SetVerbose("SuzukiCrossChar", 7);
SetVerbose("SuzukiMembership", 0);
SetVerbose("SuzukiNewTrick", 5);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 10;
stop  := 20;

// Number of random conjugates to constructively recognise for each field size
nConjugates := 2;

// Test will recognise representations of degree up to 4^n, where n is the
// following:
maxDegreePower := 0;

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 5;

// For each recognised copy, the following number of random elements will be
// expressed as words in the given generators:
nofMembershipTests := 5;

// Number of iterations of cross characteristic tests
nofCrossChar := 0;

// For each iteration, and for each field size q \leq p^n, a cross char
// representation will be constructively recognised. p and n are given here:
maxPrimeNr := 3;
maxDeg     := 3;

// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

procedure testSzCopy(G : Verify := true, FieldSize := 0)

    print "Get derived group";
    G := DerivedGroupMonteCarlo(G);
    
    print "Recognise Suzuki copy";
    flag, iso, inv, G2SLP, SLP2G := RecogniseSz(G : Verify := Verify,
	FieldSize := FieldSize);
    assert flag;
    W := WordGroup(G);

    print "Test explicit isomorphism maps";
    assert Generators(Domain(iso)) eq Generators(G);
    assert Generators(Codomain(inv)) eq Generators(G);
    
    WW := Domain(SLP2G);
    assert forall{i : i in [1 .. NumberOfGenerators(W)] |
	IsCoercible(WW, W.i)};
    assert forall{i : i in [1 .. NumberOfGenerators(WW)] |
	IsCoercible(W, WW.i)};
    assert Codomain(SzSLPCoercion(G)) cmpeq WordGroup(G);

    print "Test explicit isomorphism 1";
    
    // Test explicit isomorphism to standard copy and back
    for i in [1 .. nofIsoTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	assert SuzukiStandardMembership(Function(iso)(g));
	assert getMapFunction(iso * inv)(g) eq g;
    end for;
    
    print "Test explicit isomorphism 2";

    // Test explicit isomorphism the other way around
    H := Codomain(iso);
    assert assigned H`RandomProcess;
    for i in [1 .. nofIsoTests] do
	g := Generic(H) ! ElementToSequence(Random(H`RandomProcess));
	assert getMapFunction(inv * iso)(g) eq g;
    end for;

    print "Test constructive membership";
    
    // Test constructive membership
    for i in [1 .. nofMembershipTests] do
	g := Random(G`RandomProcess);
	flag, slp := SzElementToWord(G, g);
	assert IsCoercible(WW, slp);
	assert flag and SLP2G(slp) eq g;
    end for;
end procedure;


for m in [start .. stop] do
    q := 2^(2 * m + 1);
    G := Sz(q);
    field := CoefficientRing(G);

    print "Recognise standard copy";
    testSzCopy(G);    
    
    for i in [1 .. nConjugates] do
	// Test conjugate
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

		print "Find permutation module";
		M := PermutationModule(P, GF(p, j));

		print "Chop permutation module", M;
		series, factors := CompositionSeries(M);
		dim := Min([Dimension(f) : f in factors |
		    Dimension(f) gt 1]);
		
		// Take smallest dimensional representation
		factor := rep{f : f in factors | Dimension(f) eq dim};
		GG := ActionGroup(factor);

		print "Check absolute irreducibility";
		// Make sure input is absolutely irreducible and over
		// the minimal field
		if not IsAbsolutelyIrreducible(GG) then
		    GG := AbsoluteRepresentation(GG);
		end if;

		print "Check smaller field";
		flag, HH := IsOverSmallerField(GG);
		if flag then
		    GG := HH;
		end if;

		print "Recognise group";
		testSzCopy(RandomConjugate(GG));
	    end for;
	end for;
    end for;
end for;
