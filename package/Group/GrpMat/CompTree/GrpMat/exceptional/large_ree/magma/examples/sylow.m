// let's try a small field
F := GF(2, 5);
G := LargeRee(F);
q := #F;
print q;

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// first we must recognise the group
time flag, iso, inv, g2slp, slp2g := RecogniseLargeRee(G);

// try creating some Sylow subgroups
p := Random({x[1] : x in Factorization(q^2 - q + 1)} diff
    {x[1] : x in Factorization(q + 1)});
print p;
time R := LargeReeSylow(G, p);

// those Sylow subgroups are cyclic, and we know the order
print #R, NumberOfGenerators(R);

// creating Sylow 2-subgroups is harder, since there are lots of generators
time R := LargeReeSylow(G, 2);

// other examples of Sylow subgroups
p := Random([x[1] : x in Factorization(q - 1)]);
print p;
time R := LargeReeSylow(G, p);

// these are not cyclic and have order p^2
print NumberOfGenerators(R), #R;
