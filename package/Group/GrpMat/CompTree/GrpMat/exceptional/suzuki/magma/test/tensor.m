//
// Test file for tensor decomposition code of Suzuki package. 
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
startM := 1;
stopM  := 10;

// Low and high values of n used in the test, where the dimension of the
// representations are 4^n
startN := 2;
stopN  := 4;

// Number of tensor decompositions for each field size and degree
nChecks := 3;

// Check specified degrees
for i in [startN .. stopN] do
    degree := 4^i;
    print "Checking degree", degree;
		
    // Check specified field sizes
    for m in [startM .. stopM] do
	q := 2^(2 * m + 1);
	field := GF(2, 2 * m + 1);
	print "Checking field size", q;
	
	// Get all possible twists
	twists := CartesianPower([0 .. 2 * m], i);
	assert #twists eq (2 * m + 1)^i;
	
	// Check each field size specified number of times
	for j in [1 .. nChecks] do
	    // Check each twist
	    for tuple in twists do
		if forall{i : i in [1 .. #tuple - 1] |
		    tuple[i] lt tuple[i + 1]} then
		    
		    G := SuzukiIrreducibleRepresentation(field,
			[tuple[i] : i in [1 .. #tuple]]);
		    assert IsAbsolutelyIrreducible(G);
		    assert Degree(G) eq degree;
		    assert CoefficientRing(G) eq field;
			
		    print "Checking twist:", tuple;
		    flag, GG := IsOverSmallerField(G);
		    if flag then
			print "over smaller field", #CoefficientRing(GG);
			G := GG;
		    end if;

		    G := DerivedGroupMonteCarlo(RandomConjugate(G));
		    G`RandomProcess := RandomProcessWithWords(G :
			WordGroup := WordGroup(G), Scramble := 1);
		    
		    print "Execute tensor decomposition";
		    _ := SuzukiTensorDecompose(G :
			Randomiser := G`RandomProcess);
		end if;
	    end for;
	end for;
    end for;
end for;
