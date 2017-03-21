// Test black box standard generator algorithm for Sz

SetVerbose("SuzukiCrossChar", 5);

nofTests := 100;
nofMemberships := 100;

startM := 1;
stopM := 10;

function testGroup(G, F)
    assert assigned G`RandomProcess;

    group_time := 0;
    membership_time := 0;
    
    for i in [1 .. nofTests] do
	t := Cputime();
	gens, slps := SzBlackBoxGenerators(G, F :
	    Randomiser := G`RandomProcess);
	group_time +:= Cputime(t);
    end for;
    
    for i in [1 .. nofMemberships] do
	g := Random(G`RandomProcess);

	t := Cputime();
	flag, slp := SzBlackBoxMembership(G, g);
	membership_time +:= Cputime(t);
	assert flag;
	
	//assert Evaluate(slp, UserGenerators(G)) eq g;
    end for;

    return group_time / nofTests, membership_time / nofMemberships;
end function;

for m in [startM .. stopM] do
    F := GF(2, 2 * m + 1 : Optimize := false);
    q := #F;
    
    print "Field", F;
    G := DerivedGroupMonteCarlo(RandomConjugate(Sz(F)));
    G`RandomProcess :=
	RandomProcessWithWords(G : WordGroup := WordGroup(G),
	Scramble := 1);
    
    group_time, membership_time := testGroup(G, F);
    
    printf "Time: %o %o %o\n",
	q, group_time, membership_time;
end for;
