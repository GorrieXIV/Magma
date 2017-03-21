//
// Test file for cross-char representations of small Ree
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("ReeGeneral", 5);
SetVerbose("ReeConjugate", 5);
SetVerbose("ReeInvolution", 5);
SetVerbose("ReeTrick", 5);
SetVerbose("ReeTensor", 5);
SetVerbose("ReeStandard", 5);
SetVerbose("ReeCrossChar", 5);
SetVerbose("ReeMembership", 0);
SetVerbose("ReeMaximals", 3);

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 5;

// For each recognised copy, the following number of random elements will be
// expressed as words in the given generators:
nofMembershipTests := 5;

// Get reps of Sz(8) and Sz(32)
A1 := ATLASGroup("R27");
groups := [<MatrixGroup(rep), 27> : rep in MatRepKeys(A1)];

// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

// Constructively recognise all representations of Ree
for GG in groups do
    print "Recognise crosschar Ree copy, defining field size", GG[2];
    print "Degree:", Degree(GG[1]), "over field:", CoefficientRing(GG[1]);

    // Scramble generators
    G := DerivedGroupMonteCarlo(RandomConjugate(GG[1]));
    
    print "Recognise Ree copy";
    flag, iso, inv, G2SLP, SLP2G := RecogniseRee(G : Verify := false,
	FieldSize := GG[2]);
    assert flag;
    W := WordGroup(G);
    
    print "Check explicit isomorphisms";
    assert Generators(Domain(iso)) eq Generators(G);
    assert Generators(Codomain(inv)) eq Generators(G);
    assert Codomain(G2SLP) cmpeq Domain(SLP2G);
    WW := Domain(SLP2G);
    assert forall{i : i in [1 .. NumberOfGenerators(W)] |
	IsCoercible(WW, W.i)};
    assert forall{i : i in [1 .. NumberOfGenerators(WW)] |
	IsCoercible(W, WW.i)};
    assert Codomain(ReeSLPCoercion(G)) cmpeq WordGroup(G);
    assert Domain(ReeSLPCoercion(G)) cmpeq WW;
    
    print "Test isomorphism to standard copy";
    for i in [1 .. nofIsoTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	assert ReeStandardMembership(Function(iso)(g));
	assert getMapFunction(iso * inv)(g) eq g;
    end for;
    
    print "Test isomorphism from standard copy";
    H := Codomain(iso);
    for i in [1 .. nofIsoTests] do
	g := Generic(H) ! ElementToSequence(Random(H`RandomProcess));
	assert getMapFunction(inv * iso)(g) eq g;
    end for;

    print "Test constructive membership";
    for i in [1 .. nofMembershipTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	flag, slp := ReeElementToWord(G, g);
	assert flag and SLP2G(slp) eq g;
    end for;
end for;
