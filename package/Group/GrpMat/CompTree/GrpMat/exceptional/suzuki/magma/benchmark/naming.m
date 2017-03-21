//
// Benchmark of non-explicit Suzuki recognition

ClearVerbose();

// Number of executions for each field size
nTests := 100;

function testSzCopy(G)

    H := DerivedGroupMonteCarlo(G);

    SetAssertions(false);
    testTime := Cputime();
    flag := SuzukiRecognition(H);
    testTime := Cputime(testTime);
    SetAssertions(true);
    assert flag;

    delete H;
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

print "Test standard copies";

testTime := 0;
for i in [1 .. nTests] do
    testTime +:= testSzCopy(G);    
end for;
stdTime := reals ! (testTime / (nTests * fieldTime));
    
print "Test conjugates";

testTime := 0;
for i in [1 .. nTests] do
    G ^:= Random(Generic(G));
    
    testTime +:= testSzCopy(G);
end for;
conjTime := reals ! (testTime / (nTests * fieldTime));

printf "%o %o %o %o\n", char, m, stdTime, conjTime;
