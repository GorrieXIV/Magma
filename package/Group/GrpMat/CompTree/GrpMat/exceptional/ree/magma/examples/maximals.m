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

// first we must recognise the group
time flag, iso, inv, g2slp, slp2g := RecogniseRee(G);

// try finding the maximal subgroups
time l, slps := ReeMaximalSubgroups(G);

// should have a parabolic, an involution centraliser, three Frobenius groups
print #l;

// we can conjugate all except Frobenius groups
// but verifying the conjugating element can be expensive
r := Random(G`RandomProcess);
time g, slp := ReeMaximalSubgroupsConjugacy(G, l[1], l[1]^r);
time print l[1]^g eq l[1]^r;

time g, slp := ReeMaximalSubgroupsConjugacy(G, l[2], l[2]^r);
print l[2]^g eq l[2]^r;
