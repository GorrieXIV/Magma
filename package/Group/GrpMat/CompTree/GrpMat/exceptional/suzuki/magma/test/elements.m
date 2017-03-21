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
stop  := 4;

nNonConjTests := 10;
nConjTests := 10;

// Number of random conjugates to check for each field size
nConjugates := 5;

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
    
    print "Recognise Suzuki copy";
    print "Number of generators:", NumberOfGenerators(G);
    flag, _, _, _, slp2g := RecogniseSz(G);
    assert flag;

    print "Finding rational classes";
    ratClasses, genIndices := SzRationalConjugacyClasses(G);

    print ratClasses;
    
    print "Finding classes";
    classes := SzConjugacyClasses(G);
    assert &+[x[2] : x in classes] eq #G`SuzukiReductionData`stdCopy;
    print "Number of classes", #classes;

    print "Check rational class indices";
    reps := &cat[[ratClasses[i][3]^j : j in genIndices[i]()] :
	i in [1 .. #ratClasses]];
    assert SequenceToSet(reps) eq SequenceToSet([x[3] : x in classes]);
	
    assert forall{i : i in [1 .. #classes] |
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`classes[i][3] eq
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`
	representatives[i]};
    classMap := SzClassMap(G);

    print "Testing conjugacy";
    for i in [1 .. #classes] do
	print "Testing class", i;
	for j in [1 .. nConjTests] do
	    g := classes[i][3]^Random(G`RandomProcess);
	    h := classes[i][3]^Random(G`RandomProcess);
	    
	    rep, conj := SzClassRepresentative(G, g);
	    assert rep eq classes[i][3];
	    assert g^conj eq rep;

	    assert Function(classMap)(g) eq i;
	    assert Function(classMap)(h) eq i;
	    
	    flag, conj := SzIsConjugate(G, g, h);
	    assert flag;
	    assert g^conj eq h;
	end for;
    end for;

    pairs := [];
    nTests := nNonConjTests;
    while nTests gt 0 do
	i := Random(1, #classes);

	repeat
	    j := Random(1, #classes);
	until j ne i;

	Append(~pairs, <i, j>);
	nTests -:= 1;
    end while;

    print "Testing non-conjugacy";
    for pair in pairs do
	g := classes[pair[1]][3]^Random(G`RandomProcess);
	h := classes[pair[2]][3]^Random(G`RandomProcess);

	flag := SzIsConjugate(G, g, h);
	assert not flag;
    end for;	
end procedure;

for m in [start .. stop] do
    q := 2^(2 * m + 1);
    G := Sz(q);
    field := CoefficientRing(G);

    print "Checking field size", q, m;
    
    testSzCopy(G);
    
    for i in [1 .. nConjugates] do
	G ^:= Random(Generic(G));
	testSzCopy(G);
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

		GG ^:= Random(Generic(GG));
		testSzCopy(GG);
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

		GG ^:= Random(Generic(GG));
		testSzCopy(GG);
	    end for;
	end for;
    end for;
end for;
