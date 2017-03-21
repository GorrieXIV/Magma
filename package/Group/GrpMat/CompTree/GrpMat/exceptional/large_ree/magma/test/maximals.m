//
// Tests maximal subgroup facilities for Large Ree package. 
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

procedure testLargeReeCopy(G)

    print "Get derived group";
    //G := DerivedGroupMonteCarlo(G);

    print "Recognise group";
    flag, _, _, _, slp2g := RecogniseLargeRee(G);
    assert flag;
    print "Recognition successful";

    print "Find maximal subgroups";
    maximals, slps := LargeReeMaximalSubgroups(G);

    print "Check maximal subgroup SLPs";
    assert forall{i : i in [1 .. #slps] | forall{x : x in slps[i] |
	Domain(slp2g) cmpeq Parent(x)}};
    assert forall{i : i in [1 .. #slps] | UserGenerators(maximals[i]) eq
	slp2g(slps[i])};
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
