// Test Prospector on Sym(n)
Attach("main.m");
SetVerbose("PRProspection", 3);

n := 500;
nElements := 100;
H := SymmetricGroup(n);

// Find random generators of Sym(n)
repeat
    G := sub<H | RandomPermutation(n), RandomPermutation(n),
	RandomPermutation(n)>;
until IsSymmetric(G);
    
slots := 10;
scrambles := 0;
nReturns := 10;
alpha := 0.1;

printf "Using MAGMA standard generators of %m\n", H;
printf "PR Slots = %o, PR Scrambles = %o\n", slots, scrambles;

print "Init ordinary PR";
R := RandomProcessWithWords(G : WordGroup := WordGroup(G), Slots := slots,
    Scramble := scrambles);

print "Init Prospector";
flag := InitPermGroupProspector(G : PRSlots := slots,
    PRScramble := scrambles, nReturnsToGoodVertex := nReturns,
    UseAccelerator := true);
	
for m in [n] do
    printf "Looking for perms that have a cycle of length %o\n", m;
    
    // Probability about 1/m to find a good element
    PropertyTester := func<g |
	exists{x : x in CycleStructure(g) | x[1] eq m}>;
    
    TestProspector(G, R, PropertyTester, m, nElements, alpha);
end for;
