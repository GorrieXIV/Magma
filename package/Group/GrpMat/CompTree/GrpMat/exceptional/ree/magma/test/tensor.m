//
// Test file for tensor decomposition code of Ree package. 
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("ReeGeneral", 5);
SetVerbose("ReeTensor", 5);
SetVerbose("ReeStandard", 5);
SetVerbose("ReeCrossChar", 5);
SetVerbose("ReeMembership", 0);

// Low and high values of m used in the test, where the field size is
// q = 3^(2 * m + 1)
startM := 2;
stopM  := 10;

// Number of tensor decompositions for each field size and degree
nChecks := 1;

// Test will check tensor products of 7-dim representations of degree up to
// 7^n, where n is the following:
maxDegreePower := 2;

// Test will check reps of degree 27 * 7^n with maximum n as follows:
maxTensor := 1;

// Test will check reps of degree 27^n with maximum n as follows:
maxSymTensor := 2;

procedure testReeCopy(G, tuple)
    assert IsAbsolutelyIrreducible(G);
    q := #CoefficientRing(G);
    
    // Map to a smaller field if possible
    flag, HH := IsOverSmallerField(G);
    if flag then
	print "over smaller field", #CoefficientRing(HH);
	G := HH;
    end if;

    printf "Test tensor product of degree %o and twists %o\n",
	Degree(G), tuple;

    print "Randomising generators";
    G := DerivedGroupMonteCarlo(RandomConjugate(G));
    G`RandomProcess := RandomProcessWithWords(G :
	WordGroup := WordGroup(G), Scramble := 1);

    print "Decomposing group";
    _ := ReeTensorDecompose(G : Randomiser := G`RandomProcess,
	CheckInput := false, FieldSize := q);
end procedure;

for m in [startM .. stopM] do
    q := 3^(2 * m + 1);
    field := GF(3, 2 * m + 1);
    print "Checking field size", m, q;
    
    for i in [2 .. maxDegreePower] do
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 7^i;
	
	print "Checking degree", degree;
	
	// Check each field size specified number of times
	for j in [1 .. nChecks] do
	    
	    // Check each twist
	    for tuple in twists do
		if forall{i : i in [1 .. #tuple - 1] |
		    tuple[i] lt tuple[i + 1]} then
		    
		    // Create Ree tensor product
		    G := ReeIrreducibleRepresentation(field,
			[[7, tuple[i]] : i in [1 .. #tuple]]);

		    testReeCopy(G, tuple);
		end if;
	    end for;
	end for;
    end for;

    for i in [1 .. maxTensor] do
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i + 1);
	assert #twists eq (2 * m + 1)^(i + 1);
	degree := 27 * 7^i;

	print "Checking degree", degree;
	
	// Check each field size specified number of times
	for j in [1 .. nChecks] do
	    
	    // Check each twist
	    for tuple in twists do
		if forall{i : i in [1 .. #tuple - 1] |
		    tuple[i] lt tuple[i + 1]} then
		    
		    // Create Ree tensor product
		    G := ReeIrreducibleRepresentation(field,
			[[27, tuple[1]]] cat [[7, tuple[i + 1]] :
			i in [1 .. #tuple - 1]]);

		    testReeCopy(G, tuple);
		end if;
	    end for;
	end for;
    end for;
    
    for i in [2 .. maxSymTensor] do
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	degree := 27^i;
	
	print "Checking degree", degree;
	
	// Check each field size specified number of times
	for j in [1 .. nChecks] do
	    
	    // Check each twist
	    for tuple in twists do
		if forall{i : i in [1 .. #tuple - 1] |
		    tuple[i] lt tuple[i + 1]} then
		    
		    // Create Ree tensor product
		    G := ReeIrreducibleRepresentation(field,
			[[27, tuple[i]] : i in [1 .. #tuple]]);

		    testReeCopy(G, tuple);
		end if;
	    end for;
	end for;
    end for;
end for;
