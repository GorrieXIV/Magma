// Let's try a conjugate of the the standard copy
G := Sz(32);
G ^:= Random(Generic(G));

// perform non-constructive recognition
flag, q := SuzukiRecognition(G);
print flag, q eq 32;

// perform constructive recognition
flag, iso, inv, g2slp, slp2g := RecognizeSz(G);
print flag;

// the explicit isomorphisms are defined by rules
print iso, inv;

// so we can use Function to avoid Magma built-in membership testing
// we might not obtain the shortest possible SLP
w := Function(g2slp)(G.1);
print #w;

// and the algorithm is probabilistic, so different executions will most
// likely give different results
ww := Function(g2slp)(G.1);
print w eq ww;

// the resulting SLPs are from another word group
W := WordGroup(G);
print NumberOfGenerators(Parent(w)), NumberOfGenerators(W);

// but can be coerced into W
flag, ww := IsCoercible(W, w);
print flag;

// so there are two ways to get the element back
print slp2g(w) eq Evaluate(ww, UserGenerators(G));

// an alternative is this intrinsic, which is better if the elements are not
// known to lie in the group
flag, ww := SzElementToWord(G, G.1);
print flag, slp2g(w) eq slp2g(ww);

// let's try something just outside the group
H := Sp(4, 32);
flag, ww := SzElementToWord(G, H.1);
print flag;

// in this case we will not get an SLP
ww := Function(g2slp)(H.1);
print ww;

// we do indeed have a Suzuki group
print SatisfiesSzPresentation(G);

// finally, let's try 2.Sz(8)
A := ATLASGroup("2Sz8");
reps := MatRepKeys(A);
G := MatrixGroup(reps[3]);
print Degree(G), CoefficientRing(G);

// we can handle constructive recognition, although it takes some time
time flag, iso, inv, g2slp, slp2g := RecognizeSz(G);
print flag;

// and constructive membership testing
R := RandomProcess(G);
g := Random(R);
w := Function(g2slp)(g);

// in this case the elements is determined up to a scalar
print IsScalar(slp2g(w) * g^(-1));
