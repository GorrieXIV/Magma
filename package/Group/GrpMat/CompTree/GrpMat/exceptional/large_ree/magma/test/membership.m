//
// Test file for Large Ree package, constructive membership testing. 
//
// Most of the test is in the form of asserts, so it will die immediately if
// something has gone wrong.

SetVerbose("LargeReeGeneral", 5);
SetVerbose("LargeReeStandard", 5);
SetVerbose("LargeReeRyba", 5);
SetVerbose("LargeReeConjugacy", 5);
SetVerbose("LargeReeInvolution", 5);

SetAssertions(false);

// Low and high values of m used in the test, where the field size is
// q = 2^(2 * m + 1)
start := 1; //StringToInteger(m);
stop  := 4;//StringToInteger(m);

// Number of random conjugates to constructively recognise for each field size
nConjugates := 0;

// Membership testing batch size
startBatchSize := 5;//StringToInteger(batch);
stopBatchSize := 30;//StringToInteger(batch);

// Number of tests per batch size
nTests := 1;

//SetLogFile("batch.out");

procedure testLargeReeCopy(G : Verify := false, FieldSize := 0)

    print "Testing field:", CoefficientRing(G);
    
    print "Get derived group";
    //G := DerivedGroupMonteCarlo(G);
    
    print "Recognise Large Ree copy";
    flag, iso, inv, G2SLP, SLP2G := RecogniseLargeRee(G : Verify := Verify,
	FieldSize := FieldSize);
    assert flag;
    W := WordGroup(G);
    WW := Domain(SLP2G);

    timings := [];
    
    for batchSize in [startBatchSize .. stopBatchSize] do

	batchTimings := [];
	noBatchTimings := [];

	for i in [1 .. nTests] do
	    elements := [Random(G`RandomProcess) : i in [1 .. batchSize]];

	    //SetProfile(true);
	    //ProfileReset();
	    
	    slps := [];
	    t2 := Cputime();
	    for element in elements do
		flag, slp := LargeReeElementToWord(G, element);
		assert flag;
		Append(~slps, slp);
	    end for;
	    t2 := Cputime(t2);
	    
	    //graph := ProfileGraph();
	    //ProfilePrintByTotalTime(graph : Percentage := false, Max := 20);
	    //SetProfile(false);

	    assert forall{slp : slp in slps | Parent(slp) cmpeq WW and
		IsCoercible(W, slp)};
	    slpsEval := [W ! slp : slp in slps];
	    assert Evaluate(slpsEval, UserGenerators(G)) eq elements; 

	    //SetProfile(true);
	    //ProfileReset();
	    
	    t1 := Cputime();
	    flag, slps := LargeReeElementToWord(G, elements);
	    t1 := Cputime(t1);
	    assert flag;
	    assert forall{slp : slp in slps | Parent(slp) cmpeq WW and
		IsCoercible(W, slp)};

	    //graph := ProfileGraph();
	    //ProfilePrintByTotalTime(graph : Percentage := false, Max := 20);
	    //SetProfile(false);
	    
	    slpsEval := [W ! slp : slp in slps];
	    assert Evaluate(slpsEval, UserGenerators(G)) eq elements;
	    
	    print "Batch time:", t1;
	    print "Non-batch time:", t2;
	    Append(~batchTimings, t1);
	    Append(~noBatchTimings, t2);
	end for;
	
	Append(~timings, [RealField(3) | &+batchTimings / nTests,
	    &+noBatchTimings / nTests]);
    end for;

    print Matrix(timings);
end procedure;


for m in [start .. stop] do
    F := GF(2, 2 * m + 1);
    G := LargeRee(F);
    field := CoefficientRing(G);
    q := #field;

    print "Recognise standard copy";
    testLargeReeCopy(G : FieldSize := q);    
    
    for i in [1 .. nConjugates] do
	testLargeReeCopy(RandomConjugate(G));
    end for;
end for;
