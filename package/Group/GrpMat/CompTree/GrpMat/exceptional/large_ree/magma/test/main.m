//
// Main test file for Large Ree package. Should be a comprehensive test of the
// constructive recognition functionality.
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("LargeReeGeneral", 1);
SetVerbose("LargeReeTrick", 0);
SetVerbose("LargeReeStandard", 0);
SetVerbose("LargeReeRyba", 0);
SetVerbose("LargeReeConjugacy", 0);
SetVerbose("LargeReeInvolution", 0);
SetVerbose("UserUtil", 2);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 1;
stop  := 1;

// Number of random conjugates to constructively recognise for each field size
nConjugates := 1;

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 10;

// For each recognised copy, the following number of random elements will be
// expressed as words in the given generators:
nofMembershipTests := 10;

// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

procedure testLargeReeCopy(G : Verify := true, FieldSize := 0)

    print "Get derived group";
    //G := DerivedGroupMonteCarlo(G);
    
    print "Recognise Large Ree copy";
    flag, iso, inv, G2SLP, SLP2G := RecogniseLargeRee(G : Verify := Verify,
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
    assert Codomain(LargeReeSLPCoercion(G)) cmpeq WordGroup(G);

    // Test explicit isomorphism to standard copy and back
    print "Test explicit isomorphism maps one way";
    for i in [1 .. nofIsoTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	assert LargeReeStandardMembership(Function(iso)(g));
	assert getMapFunction(iso * inv)(g) eq g;
    end for;
    
    // Test explicit isomorphism the other way around
    print "Test explicit isomorphism maps other way";
    H := Codomain(iso);
    assert assigned H`RandomProcess;
    for i in [1 .. nofIsoTests] do
	g := Generic(H) ! ElementToSequence(Random(H`RandomProcess));
	assert getMapFunction(inv * iso)(g) eq g;
    end for;

    // Test constructive membership
    print "Test explicit membership";
    for i in [1 .. nofMembershipTests] do
	g := Random(G`RandomProcess);
	flag, slp := LargeReeElementToWord(G, g);
	assert IsCoercible(WW, slp);
	assert flag and SLP2G(slp) eq g;
    end for;
end procedure;


for m in [start .. stop] do
    F := GF(2, 2 * m + 1);
    G := LargeRee(F);
    field := CoefficientRing(G);
    q := #field;

    print "Recognise standard copy over field size", q, m;
    testLargeReeCopy(G : Verify := false, FieldSize := q);    
    
    for i in [1 .. nConjugates] do
	testLargeReeCopy(RandomConjugate(G) : Verify := false, FieldSize := q);
    end for;
end for;
