// Let's try a Suzuki group in cross characteristic
G := Sz(8);
_, P := SuzukiPermutationRepresentation(G);

// for example over GF(9)
M := PermutationModule(P, GF(3, 2));
factors := Sort(CompositionFactors(M), func<x, y | Dimension(x) - Dimension(y)>);
H := ActionGroup(factors[2]);

// we actually end up with a group over GF(3)
print IsAbsolutelyIrreducible(H);
flag, G := IsOverSmallerField(H);
print Degree(G), CoefficientRing(G);

// constructive recognition is easy in this case
time flag, iso, inv, g2slp, slp2g := RecogniseSz(G);
print iso;

// as well as constructive membership
R := RandomProcess(G);
g := Random(R);
time w := Function(g2slp)(g);
time print slp2g(w) eq g;

// we still have a Suzuki group
time print SatisfiesSzPresentation(G);
