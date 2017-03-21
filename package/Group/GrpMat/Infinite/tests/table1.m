load "start.m";
SetEchoInput (true);
SetVerbose ("Infinite", 1);

SetSeed (1);
G, H := TestMixedNilFF(6,3,5,7^8,3,4);
SetSeed (1);
time IsFinite (G);
time f, I := IsomorphicCopy (G);
"#I is ", #I;
time  IsFinite (H);

SetSeed (1);
G, H := TestSingleElementFF(10,10,3^2);
time IsFinite (G);
time f, J := IsomorphicCopy (G);
"#J is ", #J;
time IsFinite (H);

SetSeed (1);
G, H := PositiveTestFF(40,5^7);
time IsFinite (G);
time IsFinite (H);
time f, I := IsomorphicCopy (G);
// "#I is ", #I;

SetSeed (1);
G, H := TestNonCredFF(6,29^4,9,10);
time IsFinite (G);
time f, I := IsomorphicCopy (G);
SetSeed (1);
time IsFinite (H);
time f := IsFinite (H);
f;
