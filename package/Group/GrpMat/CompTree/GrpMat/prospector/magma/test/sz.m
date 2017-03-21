// Test Prospector using Sz(2^(2m+1))
Attach("main.m");
SetVerbose("PRProspection", 3);

startM := 1;
stopM := 10;
nElements := 100;

slots := 10;
scrambles := 50;
alpha := 0.05;
reals := RealField();

for m in [startM .. stopM] do
    q := 2^(2 * m + 1);
    H := Sz(q);
    G := H;
    
    printf "Using MAGMA standard generators of %m\n", H;
    printf "PR Slots = %o, PR Scrambles = %o\n", slots, scrambles;
    
    print "Init ordinary PR";
    R := RandomProcessWithWords(G : WordGroup := WordGroup(G),
	Slots := slots, Scramble := scrambles);
    
    print "Init Prospector";
    flag := InitMatGroupProspector(G : PRSlots := slots,
	PRScramble := scrambles);
    
    print "Looking for elements of even order, expected # selections:", q;
    PropertyTester := func<g | IsEven(Order(g))>;
    
    TestProspector(G, R, PropertyTester, q, nElements, alpha);
end for;
