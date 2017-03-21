// Let's try using the Prospector in a big permutation group
n := 1000;
G := Sym(n);

// The initialisation is cheap
time flag := InitialiseProspector(G);
assert flag;

// Compare against standard product replacement
R := RandomProcessWithWords(G : WordGroup := WordGroup(G));

// We want to find n-cycles
test := func<g | Order(g) eq n>;

// First try to find an n-cycle with the Prospector
flag, g1, w1 := Prospector(G, test : MaxTries := n^2);
assert flag;

// We did indeed obtain an n-cycle
print Order(g1) eq n;

// with quite short SLP
print #w1;

// Now try standard product replacement
repeat
    g2, w2 := Random(R);
until test(g2);

// This obtains a much longer SLP
print #w2;
