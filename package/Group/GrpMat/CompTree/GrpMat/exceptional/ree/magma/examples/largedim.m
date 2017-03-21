/*
// first try a 189-dimensional Ree group
F := GF(3, 3);
twists := [[27, 0], [7, 1]];
G := ReeIrreducibleRepresentation(F, twists);
print Degree(G), IsAbsolutelyIrreducible(G);

// conjugate it to hide the tensor product
G ^:= Random(Generic(G));

// constructive recognition will decompose the tensor product
time flag, iso, inv, g2slp, slp2g := RecogniseRee(G);
print iso;

// constructive membership is again easy
R := RandomProcess(G);
g := Random(R);
time w := Function(g2slp)(g);

// but SLP evaluation is harder in large dimensions
time print slp2g(w) eq g;


// now let's try a 343-dimensional Ree group
F := GF(3, 9);
twists := [[7, 0], [7, 3], [7, 6]];
G := ReeIrreducibleRepresentation(F, twists);
print Degree(G), IsAbsolutelyIrreducible(G);

// conjugate it to hide the tensor product
G ^:= Random(Generic(G));

// and write it over a smaller field to make things difficult
flag, GG := IsOverSmallerField(G);
print flag, CoefficientRing(GG);

// constructive recognition will decompose the tensor product
time flag, iso, inv, g2slp, slp2g := RecogniseRee(GG);
print iso;

// constructive membership is again easy
R := RandomProcess(GG);
g := Random(R);
time w := Function(g2slp)(g);

// but SLP evaluation is harder in large dimensions
time print slp2g(w) eq g;
*/

// finally let's try a 729-dimensional Ree group
F := GF(3, 3);
twists := [[27, 0], [27, 1]];
G := ReeIrreducibleRepresentation(F, twists);
print Degree(G), IsAbsolutelyIrreducible(G);

// conjugate it to hide the tensor product
G ^:= Random(Generic(G));

// constructive recognition will decompose the tensor product
time flag, iso, inv, g2slp, slp2g := RecogniseRee(G);
print iso;

// constructive membership is again easy
R := RandomProcess(G);
g := Random(R);
time w := Function(g2slp)(g);

// but SLP evaluation is harder in large dimensions
time print slp2g(w) eq g;
