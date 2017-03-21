//
// Benchmark of Suzuki conjugation

ClearVerbose();

// Number of executions for each field size
nTests := 100;

function testSzCopy(G)

    G := DerivedGroupMonteCarlo(G);
    
    SetAssertions(false);
    testTime := Cputime();
    _, g := SuzukiConjugacy(G : CheckInput := false);
    testTime := Cputime(testTime);
    SetAssertions(true);

    assert SuzukiStandardRecogniser(G^g);
    delete G;
    return testTime;
end function;

reals := RealField();
    F := GF(2, 2 * StringToInteger(m) + 1 : Optimize := false);
    G := Sz(F);

    printf "Testing field: %o\n", F;
    
    fieldTime := Cputime();
    for i in [1 .. 1000000] do
	_ := Random(F) * Random(F);
    end for;
    fieldTime := Cputime(fieldTime);

    // Initial run to initialise discrete log
    //_ := testSzCopy(G);
    
    testTime := 0;
    for i in [1 .. nTests] do
	G ^:= Random(Generic(G));
	
	curTestTime := testSzCopy(G);
	testTime +:= curTestTime;
    end for;

printf "%o %o %o\n", char, m, reals ! (testTime / (nTests * fieldTime));
