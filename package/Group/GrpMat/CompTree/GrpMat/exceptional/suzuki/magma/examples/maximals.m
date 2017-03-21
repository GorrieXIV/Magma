// let's try a small field
m := 4;
F := GF(2, 2 * m + 1);
q := #F;
print q;
G := Sz(F);

// let's try a conjugate
G ^:= Random(Generic(G));

// also move to another generating set
G := DerivedGroupMonteCarlo(G);
print NumberOfGenerators(G);

// first we must recognise the group
time flag, iso, inv, g2slp, slp2g := RecogniseSz(G);

// try finding the maximal subgroups
time l, slps := SuzukiMaximalSubgroups(G);

// should have a parabolic, a torus normaliser, two Frobenius groups
// and one smaller Sz
print #l;

// we can conjugate all maximals around
r := Random(G`RandomProcess);
for H in l do
    time g, slp := SuzukiMaximalSubgroupsConjugacy(G, H, H^r);
    time print H^g eq H^r;
end for;
