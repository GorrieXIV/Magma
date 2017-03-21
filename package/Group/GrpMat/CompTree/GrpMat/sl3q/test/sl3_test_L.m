SetLogFile("sl3_test_L.out" : Overwrite := true);
SetVerbose("sl3q", 0);

SetSeed(1);

load "SL3";
load "../../../test/suites/testgroup.m";

procedure TestSL3CT(H)
    G := RandomConjugate(H);
    TestGroup(G : Verify := true);
end procedure;

printf "Number of L groups: %o\n", #L;

for i in [1 .. #L] do
    G := L[i];
    printf "Testing L group %o\n", i;
    TestSL3CT(G);
end for;
