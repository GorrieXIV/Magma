// Test black box standard generator algorithm for Sz

ClearVerbose();
load "../suzuki.m";

nTests := 100;
nMemberships := 100;

function testGroup(G, F)

    G`RandomProcess :=
	RandomProcessWithWords(G : WordGroup := WordGroup(G),
	Scramble := 1);

    group_time := 0;
    membership_time := 0;
    
    for i in [1 .. nTests] do
	SetAssertions(false);
	t := Cputime();

	gens, slps := SzBlackBoxGenerators(G, F :
	    Randomiser := G`RandomProcess);
	
	group_time +:= Cputime(t);
	SetAssertions(true);
	//assert IsSatisfied(BraySzRelations(F), gens);
    end for;
    
    for i in [1 .. nMemberships] do
	SetAssertions(false);
	g := Random(G`RandomProcess);
	t := Cputime();
	
	flag, slp := SzBlackBoxMembership(G, g);
	membership_time +:= Cputime(t);
	
	SetAssertions(true);
	assert flag;
	//assert Evaluate(slp, UserGenerators(G)) eq g;
    end for;
    
    return group_time / nTests, membership_time / nMemberships;
end function;

reals := RealField();
m := StringToInteger(m);
n := StringToInteger(n);

F := GF(2, 2 * m + 1 : Optimize := true);
q := #F;
print "Checking field size", q;

// Check specified degrees
//for n in [startN .. Min([stopN, m])] do
degree := 4^n;
print "Checking degree", degree;

// Get all possible twists
twists := CartesianPower([0 .. 2 * m], n);
assert #twists eq (2 * m + 1)^n;

testTimes := [];

gens_time := 0;
membership_time := 0;

// Check each twist
for tuple in twists do
    if forall{i : i in [1 .. #tuple - 1] |
	tuple[i] lt tuple[i + 1]} then
	
	G := SuzukiIrreducibleRepresentation(F,
	    [tuple[i] : i in [1 .. #tuple]]);
	//assert IsAbsolutelyIrreducible(G);
	assert Degree(G) eq degree;
	assert CoefficientRing(G) eq F;
	
	print "Checking twist:", tuple;
	flag, GG := IsOverSmallerField(G);
	if flag then
	    print "over smaller field", #CoefficientRing(GG);
	    G := GG;
	end if;
	
	gens_time_twist, membership_time_twist :=
	    testGroup(DerivedGroupMonteCarlo(RandomConjugate(G)), F);
	
	gens_time +:= gens_time_twist;
	membership_time +:= membership_time_twist;
    end if;
end for;

printf "%o %o %o %o %o\n", char, q, n, gens_time, membership_time;
