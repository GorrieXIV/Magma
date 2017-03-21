// let's try a small field
m := 1;
F := GF(3, 2 * m + 1);
q := #F;
print q;
G := Ree(F);

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// First we must recognise the group
time flag, iso, inv, g2slp, slp2g := RecogniseRee(G);

// what about creating Sylow subgroups?
p := Random([x[1] : x in Factorization(q - 1) | x[1] gt 2]);
print p;
time R := ReeSylow(G, p);
time S := ReeSylow(G, p);

// that was easy, as is conjugating them
time g, slp := ReeSylowConjugacy(G, R, S, p);
time print R^g eq S;

// in this case we also automatically get an SLP of the conjugating element
print slp2g(slp) eq g;

// those Sylow subgroups are cyclic, and we know the order
print #R, NumberOfGenerators(R);

// creating Sylow 3-subgroups is harder, since there are lots of generators
time R := ReeSylow(G, 3);
time S := ReeSylow(G, 3);
print NumberOfGenerators(R), #R;

// but conjugation is easy
time g, slp := ReeSylowConjugacy(G, R, S, 3);

// verifying the conjugating element can be expensive
time print R^g eq S;

// Sylow 2-subgroups are small
time R := ReeSylow(G, 2);
print NumberOfGenerators(R), #R;

// but slightly harder to conjugate
time S := ReeSylow(G, 2);
time g, slp := ReeSylowConjugacy(G, R, S, 2);
time print R^g eq S;
