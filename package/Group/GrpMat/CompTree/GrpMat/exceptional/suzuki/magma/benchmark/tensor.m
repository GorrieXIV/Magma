//
// Benchmark of tensor decomposition code of Suzuki package. 

ClearVerbose();

// Low and high values of n used in the test, where the dimension of the
// representations are 4^n
//startN := 3;
//stopN  := 3;

// Number of tensor decompositions for each field size, degree and twist
//nTests := 10;
nTests := StringToInteger(nTests);

times := [];

function testSzCopy(G, q)
    
    G := DerivedGroupMonteCarlo(RandomConjugate(G));
    G`RandomProcess := RandomProcessWithWords(G :
	WordGroup := WordGroup(G), Scramble := 1);
    
    SetAssertions(false);
    testTime := Cputime();
    _, cbm := SuzukiTensorDecompose(G : CheckInput := false,
	Randomiser := G`RandomProcess, FieldSize := q);
    testTime := Cputime(testTime);
    SetAssertions(true);

    return testTime;
end function;

reals := RealField();

// Check specified field sizes
m := StringToInteger(m);
F := GF(2, 2 * m + 1 : Optimize := false);
q := #F;
print "Checking field size", q;

fieldTime := Cputime();
for i in [1 .. 1000000] do
    _ := Random(F) * Random(F);
end for;
fieldTime := Cputime(fieldTime);

n := StringToInteger(n);

degree := 4^n;
print "Checking degree", degree;

// Get all possible twists
twists := CartesianPower([0 .. 2 * m], n);
assert #twists eq (2 * m + 1)^n;
    
testTimes := [];

// Check each twist
for tuple in twists do
    if forall{i : i in [1 .. #tuple - 1] |
	tuple[i] lt tuple[i + 1]} and tuple[1] eq 0 then
	
	G := SuzukiIrreducibleRepresentation(F,
	    [tuple[i] : i in [1 .. #tuple]]);
	assert IsAbsolutelyIrreducible(G);
	assert Degree(G) eq degree;
	assert CoefficientRing(G) eq F;
	    
	print "Checking twist:", tuple;
	flag, GG := IsOverSmallerField(G);
	if flag then
	    print "over smaller field", #CoefficientRing(GG);
	    G := GG;
	end if;
	    
	for i in [1 .. nTests] do
	    curTestTime := testSzCopy(G, q);
	    Append(~testTimes, curTestTime);
	end for;
    end if;
end for;

printf "%o %o %o %o\n", char, m, n, 
    reals ! ((&+testTimes) / (#testTimes * fieldTime));


