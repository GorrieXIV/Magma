// Let's try a conjugate of the the standard copy
F := GF(2, 7);
G := LargeRee(F);
G ^:= Random(Generic(G));

// perform non-constructive recognition
flag, q := LargeReeRecognition(G);
print flag, q eq #F;

// perform constructive recognition
time flag, iso, inv, g2slp, slp2g := RecognizeLargeRee(G);
print flag;

// the explicit isomorphisms are defined by rules
print iso, inv;

// so we can use Function to avoid Magma built-in membership testing
// we might not obtain the shortest possible SLP
time w := Function(g2slp)(G.1);
print #w;

// and the algorithm is probabilistic, so different executions will most
// likely give different results
time ww := Function(g2slp)(G.1);
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
time flag, ww := LargeReeElementToWord(G, G.1);
print flag, slp2g(w) eq slp2g(ww);

// let's try something just outside the group
H := ChevalleyGroup("F", 4, 128);
time flag, ww := LargeReeElementToWord(G, H.1);
print flag;

// in this case we will not get an SLP
time ww := Function(g2slp)(H.1);
print ww;
