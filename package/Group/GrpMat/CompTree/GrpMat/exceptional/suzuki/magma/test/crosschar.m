// Test some cross char representations for Sz

SetVerbose("SuzukiGeneral", 5);
SetVerbose("SuzukiTensor", 5);
SetVerbose("SuzukiStandard", 5);
SetVerbose("SuzukiCrossChar", 5);
SetVerbose("SuzukiMembership", 0);

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 10;

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

// Get reps of Sz(8) and Sz(32)
A1 := ATLASGroup("Sz8");
A2 := ATLASGroup("Sz32");
groups := //[<MatrixGroup(rep), 8> : rep in MatRepKeys(A1)] cat
    [<MatrixGroup(rep), 32> : rep in MatRepKeys(A2)];

// Constructively recognise all representations of 2Sz8
for GG in groups do
    print "Recognise crosschar Sz copy, defining field size", GG[2];
    print "Degree:", Degree(GG[1]), "over field:", CoefficientRing(GG[1]);

    // Scramble generators
    G := DerivedGroupMonteCarlo(GG[1]);
    G ^:= Random(Generic(G));
    
    flag, iso, inv, G2SLP, SLP2G := RecogniseSz(G : Verify := false,
	FieldSize := GG[2]);
    assert flag;
    W := WordGroup(G);
    
    print "Test iso * inv";
    
    // Test explicit isomorphism to standard copy and back
    for i in [1 .. nofIsoTests] do
	g := Generic(G) ! ElementToSequence(Random(G`RandomProcess));
	h := Function(iso)(g);
	hh := Function(inv)(h);
	assert IsScalar(hh / g);
    end for;
    
    print "Test inv * iso";
    
    // Test explicit isomorphism the other way around
    H := Codomain(iso);
    assert assigned H`RandomProcess;
    for i in [1 .. nofIsoTests] do
	g := Generic(H) ! ElementToSequence(Random(H`RandomProcess));
	assert getMapFunction(inv * iso)(g) eq g;
    end for;

    print "Test membership";
    
    // Test constructive membership
    for i in [1 .. nofMembershipTests] do
	g := Random(G`RandomProcess);
	flag, slp := SzElementToWord(G, g);
	assert flag and SLP2G(slp) eq g;
    end for;    
end for;

print "Done checking cross char";
