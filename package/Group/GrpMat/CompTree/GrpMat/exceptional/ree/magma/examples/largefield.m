// let's try a larger field
m := 15;
F := GF(3, 2 * m + 1);
q := #F;
print q;
G := Ree(F);

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// non-constructive recognition is now a bit harder
time ReeRecognition(G);

// and is your machine up for this?
time flag, iso, inv, g2slp, slp2g := RecogniseRee(G);

// each call to constructive membership is then easy
R := RandomProcess(G);
g := Random(R);
time w := Function(g2slp)(g);

// evaluating SLPs always takes some time
time print slp2g(w) eq g;

