// let's try a small field
q := 2^9;
G := Sz(q);

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// first we must recognise the group
time flag, iso, inv, g2slp, slp2g := RecogniseSz(G);

// try creating some Sylow subgroups
p := Random([x[1] : x in Factorization(q - 1)]);
print p;
time R := SuzukiSylow(G, p);
time S := SuzukiSylow(G, p);

// that was easy, as is conjugating them
time g, slp := SuzukiSylowConjugacy(G, R, S, p);
time print R^g eq S;

// in this case we also automatically get an SLP of the conjugating element
print slp2g(slp) eq g;

// those Sylow subgroups are cyclic, and we know the order
print #R, NumberOfGenerators(R);

// creating Sylow 2-subgroups is harder, since there are lots of generators
time R := SuzukiSylow(G, 2);
time S := SuzukiSylow(G, 2);
print NumberOfGenerators(R), #R;

// but conjugation is easy
time g, slp := SuzukiSylowConjugacy(G, R, S, 2);

// verifying the conjugating element can be hard
time print R^g eq S;
