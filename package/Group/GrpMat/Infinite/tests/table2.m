SetEchoInput (true);
load "tests.m";
SetVerbose ("Infinite", 1);

SetSeed (1);
H1 := TestFF2 (MonomialGroup(17, 20));
SetSeed (1);
time IsFinite (H1);
time f, I := IsomorphicCopy (H1);

SetSeed (1);
H2 := TestNilpotentBlockFF(20,5,7,3^10);
SetSeed (1);
time IsFinite (H2);
time f, I := IsomorphicCopy (H2);

SetSeed (1);
H3 := TestMixedNilFF(4,3,5,7^2,3,2);
SetSeed (1);
time IsFinite (H3);
time f, I := IsomorphicCopy (H3);

SetSeed (1);
H4 := TestUnipotentFF(34, 2, 1);
SetSeed (1);
time IsFinite (H4);
time f, I := IsomorphicCopy (H4);
