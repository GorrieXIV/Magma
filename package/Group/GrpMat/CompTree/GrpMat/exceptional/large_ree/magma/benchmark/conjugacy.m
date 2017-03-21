//
// Benchmark of Large Ree conjugation

ClearVerbose();

// Number of executions for each field size
nTests := StringToInteger(nTests);

function testLargeReeCopy(G, q)

    G := DerivedGroupMonteCarlo(G);
    
    SetAssertions(false);
    testTime := Cputime();
    flag := RecogniseLargeRee(G : Verify := false, FieldSize := q);
    testTime := Cputime(testTime);
    SetAssertions(true);

    //assert LargeReeStandardRecogniser(G^cbm);
    delete G;
    return testTime;
end function;

reals := RealField();
m := StringToInteger(m);
F := GF(2, 2 * m + 1 : Optimize := false);
G := LargeRee(F);

printf "Testing field: %o\n", F;

fieldTime := Cputime();
for i in [1 .. 1000000] do
    _ := Random(F) * Random(F);
end for;
fieldTime := Cputime(fieldTime);

print "Initial run";

// Initial run to initialise discrete log
_ := testLargeReeCopy(G, #F);

print "Start testing";

testTime := 0;
for i in [1 .. nTests] do
    G := RandomConjugate(G);
    
    curTestTime := testLargeReeCopy(G, #F);
    testTime +:= curTestTime;
end for;

printf "%o %o %o\n", char, m, reals ! (testTime / (nTests * fieldTime));

