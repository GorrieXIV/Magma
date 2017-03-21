// let's try a 64-dimensional Suzuki group
F := GF(2, 9);
twists := [0, 3, 6];
G := SuzukiIrreducibleRepresentation(F, twists);
print Degree(G), IsAbsolutelyIrreducible(G);

// conjugate it to hide the tensor product
G ^:= Random(Generic(G));

// and write it over a smaller field to make things difficult
flag, GG := IsOverSmallerField(G);
print flag, CoefficientRing(GG);

// non-constructive recognition is harder in this case
// and will give us the defining field size
time print SuzukiRecognition(GG);

// constructive recognition will decompose the tensor product
time flag, iso, inv, g2slp, slp2g := RecogniseSz(GG);
print iso;

// constructive membership is again easy
R := RandomProcess(GG);
g := Random(R);
time w := Function(g2slp)(g);

// but SLP evaluation is harder in large dimensions
time print slp2g(w) eq g;

// we still have a Suzuki group
time print SatisfiesSzPresentation(GG);
