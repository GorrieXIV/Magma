//
// Benchmark of Ree conjugation

ClearVerbose();

// Number of executions for each field size
nTests := StringToInteger(nTests);

function testReeCopy(G)

    G := DerivedGroupMonteCarlo(G);
    
    SetAssertions(false);
    G`RandomProcess := RandomProcessWithWords(G : WordGroup := WordGroup(G), Scramble := 1);
    testTime := Cputime();
    _, g, sl2Time := ReeConjugacy(G : CheckInput := false, Randomiser := G`RandomProcess);
    testTime := Cputime(testTime);
    SetAssertions(true);

    assert ReeStandardRecogniser(G^g);
    delete G;
    return testTime, sl2Time;
end function;

reals := RealField();
F := GF(3, 2 * StringToInteger(m) + 1 : Optimize := false);
G := Ree(F);

printf "Testing field: %o\n", F;

fieldTime := Cputime();
for i in [1 .. 1000000] do
    _ := Random(F) * Random(F);
end for;
fieldTime := Cputime(fieldTime);

// Initial run to initialise discrete log
_ := testReeCopy(G);
    
testTime := 0;
sl2Time  := 0;
for i in [1 .. nTests] do
    G := RandomConjugate(G);
	
    curTestTime, curSL2Time := testReeCopy(G);
    testTime +:= curTestTime;
    sl2Time +:= curSL2Time;
end for;

SetAutoColumns(false);
SetColumns(0);

printf "%o %o %o %o\n", char, m,
    reals ! (testTime / (nTests * fieldTime)),
    reals ! (sl2Time / (nTests * fieldTime));
quit;
