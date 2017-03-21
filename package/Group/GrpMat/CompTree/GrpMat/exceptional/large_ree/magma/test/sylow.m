//
// Tests Sylow subgroup facilities for Large Ree package. 
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("LargeReeGeneral", 5);
SetVerbose("LargeReeStandard", 5);
SetVerbose("LargeReeRyba", 5);
SetVerbose("LargeReeConjugacy", 5);
SetVerbose("LargeReeInvolution", 5);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 1;
stop  := 4;

// Number of random conjugates to constructively recognise for each field size
nConjugates := 10;

// Number of pairs of Sylow p-subgroups to create and conjugate for each
// prime p dividing the order of LargeRee(q)
nSylows := 2;

procedure testLargeReeCopy(G)

    print "Get derived group";
    //G := DerivedGroupMonteCarlo(G);

    print "Recognise group";
    flag, _, _, _, SLP2G := RecogniseLargeRee(G);
    assert flag;
    print "Recognition successful";
    
    q := #CoefficientRing(G`LargeReeReductionData`stdCopy);
    
    for p in [x[1] : x in Factorization(#G`LargeReeReductionData`stdCopy) |
	not IsDivisibleBy(q + 1, x[1])] do

	// For each prime, find a number of Sylows
	for i in [1 .. nSylows] do

	    printf "Create Sylow p-subgroups with p = %o\n", p;
	    
	    // Create Sylow p-subgroups
	    R, l := LargeReeSylow(G, p);
	    assert forall{x : x in l | IsCoercible(Domain(SLP2G), x)};
	    assert SLP2G(l) eq UserGenerators(R);
	    S, l := LargeReeSylow(G, p);
	    assert forall{x : x in l | IsCoercible(Domain(SLP2G), x)};
	    assert SLP2G(l) eq UserGenerators(S);	    
	end for;
    end for;
end procedure;

for m in [start .. stop] do
    G := LargeRee(m);
    field := CoefficientRing(G);
    q := #field;

    print "Test standard copy";
    testLargeReeCopy(G);    
    
    for i in [1 .. nConjugates] do
	print "Test conjugate";
	testLargeReeCopy(RandomConjugate(G));
    end for;
end for;
