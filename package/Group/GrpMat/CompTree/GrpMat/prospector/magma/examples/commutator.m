// Use Prospector to find random elements of a normal subgroup
d := 5;
p := 11;
e := 3;
q := p^e;

// Try a cyclic extension of SL
H1 := SL(d, q);
H2 := sub<Generic(H1) | Random(Generic(H1))>;
assert H2.1 notin H1;
G := DirectProduct(H1, H2);
W := WordGroup(G);

// Compute some commutators
gens := [(G.i, G.j) : i in [1 .. NumberOfGenerators(G)],
    j in [1 .. NumberOfGenerators(G)] | j gt i];
slps := [(W.i, W.j) : i in [1 .. NumberOfGenerators(W)],
    j in [1 .. NumberOfGenerators(W)] | j gt i];

// The normal closure of H is G' = H1
H := sub<G | gens>;

// Prospector needs SLPs of generators of H in G
H_slps := [slps[Index(gens, g)] : g in UserGenerators(H)];

// Prospector will find random elements of normal closure of H in G
flag := InitialiseProspector(H : SuperGroup := G, SLPsInSuper := H_slps);
assert flag;

// Try to find p-elements
test := func<g | IsDivisibleBy(Order(g), p)>;
flag, g1, w1 := Prospector(H, test : MaxTries := q^2);
assert flag;

// Length of the SLP
print #w1;

// As a comparison, use standard product replacement
K, K_slps := DerivedGroupMonteCarlo(G);
R := RandomProcessWithWords(K);

repeat
    g2, w2 := Random(R);
until test(g2);

// Map into the same word group to compare SLP length
print #Evaluate(w2, K_slps);
