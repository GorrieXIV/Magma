// Test Prospector on SL(d, p^r)
Attach("main.m");
SetVerbose("PRProspection", 3);

d := 10;
n := 10;
r := 10;
p := NthPrime(n);
nElements := 100;

H := SL(d, p^r);
F := CoefficientRing(H);
MA := MatrixAlgebra(F, d);

// Find random elements that generate SL
repeat
    repeat
	x := ScaleMatrix(MA ! RandomInvertibleMatrix(F, d));
    until x cmpne false;
    repeat
	y := ScaleMatrix(MA ! RandomInvertibleMatrix(F, d));
    until y cmpne false;
    
    assert x in H and y in H;
    G := sub<H | x, y>;
until IsLinearGroup(G);

// Prospector parameters
// No initial scrambling
slots := 10;
scrambles := 0;
alpha := 0.05;

printf "Using MAGMA standard generators of %m\n", H;
printf "PR Slots = %o, PR Scrambles = %o\n", slots, scrambles;

print "Init ordinary PR";
R := RandomProcessWithWords(G : WordGroup := WordGroup(G), Slots := slots,
    Scramble := scrambles);

print "Init Prospector";
flag := InitMatGroupProspector(G : PRSlots := slots,
    PRScramble := scrambles);

for m in [d] do
    
    printf "Looking for matrices whose char poly has a factor of degree %o\n",
	m;
    
    // Probability about 1/m to find a good element
    PropertyTester := func<g | exists{x : x in
	FactoredCharacteristicPolynomial(g) | Degree(x[1]) eq m}>;
    
    TestProspector(G, R, PropertyTester, m, nElements, alpha);
end for;
