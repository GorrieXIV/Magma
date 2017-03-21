d := 60;
p := NthPrime(60);

// Use a bad generating set for SL(d, p)
G := sub<GL(d, p) | GeneratingTransvections(d, p)>;

// Use the Prospector with the accelerator version of product replacement
// For a good comparison, don't do any initial scrambling
flag := InitialiseProspector(G : UseAccelerator := true, PRScramble := 1);
assert flag;

// These elements are moderately rare
test := func<g | IsIrreducible(CharacteristicPolynomial(g))>;
flag, g1, w1 := Prospector(G, test : MaxTries := p^2);
assert flag;

// Length of the SLP
print #w1;

// As a comparison, use standard product replacement
R := RandomProcessWithWords(G : Scramble := 1);

repeat
    g2, w2 := Random(R);
until test(g2);

// A slightly longer SLP
print #w2;
