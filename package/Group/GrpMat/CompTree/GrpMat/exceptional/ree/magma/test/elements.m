//
// Main test file for small Ree package. Should be a comprehensive test of the
// constructive recognition functionality.
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
SetVerbose("ReeMaximals", 0);
SetVerbose("ReeElements", 5);

// Low and high values of m used in the test, where the field size is
// q = 3^(2 * m + 1)
start := 1;
stop  := 10;

// Number of random conjugates to check for each field size
nConjugates := 100;

// Number of 27-dim representations to recognise
nSymSquares := 0;

// Test will check tensor products of 7-dim representations of degree up to
// 7^n, where n is the following:
maxDegreePower := 1;

// Test will check reps of degree 27 * 7^n with maximum n as follows:
maxTensor := 0;

// Test will check reps of degree 27^n with maximum n as follows:
maxSymTensor := 0;

// For each recognised copy, the following number of random elements will be
// mapped to the standard copy and back:
nofIsoTests := 5;

// For each recognised copy, the following number of random elements will be
// expressed as words in the given generators:
nofMembershipTests := 5;

// Number of iterations of cross characteristic tests
// Smallest cross char rep has dimension almost 20000, so it's not practical
nofCrossChar := 0;

// For each iteration, and for each field size q \leq p^n, a cross char
// representation will be checked. p and n are given here:
maxPrimeNr := 2;
maxDeg     := 2;


// Get composed Function on a composition of Maps    
function getMapFunction(mapping)
    local f;

    f := func<x | x>;
    for g in Components(mapping) do
	f := func<x | Function(g)(f(x))>;
    end for;

    return f;
end function;

procedure testReeCopy(G)

    print "Get derived group";

    // Move to another generating set
    G := DerivedGroupMonteCarlo(G);
    
    print "Recognise Ree copy";
    print "Number of generators:", NumberOfGenerators(G);
    flag := RecogniseRee(G);
    assert flag;

    print "Finding classes";
    classes := ReeConjugacyClasses(G);
    print [classes[i][1] : i in [1 .. #classes]];
    print &+[x[2] : x in classes], #G`ReeReductionData`stdCopy;
    assert &+[x[2] : x in classes] eq #G`ReeReductionData`stdCopy;
    print "Number of classes", #classes;
    
    assert forall{i : i in [1 .. #classes] |
	G`ReeReductionData`stdCopy`ReeConjugacyClassData`classes[i][3] eq
	G`ReeReductionData`stdCopy`ReeConjugacyClassData`
	representatives[i]};
end procedure;


for m in [start .. stop] do
    field := GF(3, 2 * m + 1);
    G := Ree(field);

    print "Recognise standard copy";
    testReeCopy(G);
    
    for i in [1 .. nConjugates] do

	print "Recognise conjugate";
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

	print "Recognise 27-dim";
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

		printf "Recognise tensor product of degree %o and twists %o\n",
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

		printf "Recognise tensor product of degree %o and twists %o\n",
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

		printf "Recognise tensor product of degree %o and twists %o\n",
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
