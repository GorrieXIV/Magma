// let's try a larger field
q := 2^121;
G := Sz(q);

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// non-constructive recognition is now a bit harder
time SuzukiRecognition(G);

// and is your machine up for this?
time flag, iso, inv, g2slp, slp2g := RecogniseSz(G);

// each call to constructive membership is then easy
R := RandomProcess(G);
g := Random(R);
time w := Function(g2slp)(g);

// evaluating SLPs always takes some time
time print slp2g(w) eq g;

