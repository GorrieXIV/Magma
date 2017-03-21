// Test for 2Sz8 hack in Suzuki package

SetVerbose("SuzukiGeneral", 5);
SetVerbose("SuzukiTensor", 5);
SetVerbose("SuzukiStandard", 5);
SetVerbose("SuzukiCrossChar", 5);
SetVerbose("SuzukiMembership", 0);

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 100;

// For each recognised copy, the following number of random elements will be
// expressed as words in the given generators:
nofMembershipTests := 5;

// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

// Get reps of 2.Sz(8) and 2^2.Sz(8)
A1 := ATLASGroup("2Sz8");
A2 := ATLASGroup("4Sz8d3");
groups := [MatrixGroup(rep) : rep in MatRepKeys(A1)] cat
    [DerivedGroupMonteCarlo(MatrixGroup(rep)) : rep in MatRepKeys(A2)];

// Constructively recognise all representations of 2Sz8
for GG in groups do
    print "Recognise 2Sz8 copy or 4Sz8";
    print "Degree:", Degree(GG), "over field:", CoefficientRing(GG);

    // Scramble generators
    G := DerivedGroupMonteCarlo(GG);
    G ^:= Random(Generic(G));
    
    flag, iso, inv, G2SLP, SLP2G := RecogniseSz(G : Verify := false,
	FieldSize := 8);
    assert flag;
    W := WordGroup(G);
        
    // Test explicit isomorphism to standard copy and back
    for i in [1 .. nofIsoTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	assert IsScalar(getMapFunction(iso * inv)(g) * g^(-1));
    end for;
    
    // Test explicit isomorphism the other way around
    H := Codomain(iso);
    assert assigned H`RandomProcess;
    for i in [1 .. nofIsoTests] do
	g := Generic(H) ! ElementToSequence(Random(H`RandomProcess));
	assert getMapFunction(inv * iso)(g) eq g;
    end for;

    // Test constructive membership
    for i in [1 .. nofMembershipTests] do
	g := Random(G`RandomProcess);
	flag, slp := SzElementToWord(G, g);
	assert flag and SLP2G(slp) eq g;
    end for;    
end for;

print "Done checking 2Sz8 and 4Sz8";
