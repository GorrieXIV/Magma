// Test black box standard generator algorithm for Sz

SetVerbose("SuzukiCrossChar", 5);

nofTests := 100;
nofMemberships := 100;

input := [<"Sz8", GF(8),
    ["Sz8G1-f125r65bB0.M", "Sz8G1-f125r65cB0.M", "Sz8G1-f5r14bB0.M",
    "Sz8G1-f5r195B0.M", "Sz8G1-Zr64B0.m",
    "Sz8G1-Zr91B0.m"],
    ["Sz8G1-Ar14aB0.m", "Sz8G1-Ar14bB0.m", "Sz8G1-Zr105B0.m",
    "Sz8G1-Ar65aB0.m", "Sz8G1-Ar65bB0.m", "Sz8G1-Ar65cB0.m"],
    ["Sz8G1-p520B0.M"]>, <"Sz32", GF(32), [],
    ["Sz32G1-Cr124aB0.m", "Sz32G1-Cr124bB0.m"], []>];

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

for tuple in input do

    // Get reps of Sz
    A := ATLASGroup(tuple[1]);

    // Groups stored in Magma
    groups := [MatrixGroup(rep) : rep in MatRepKeys(A)];

    // Char 0 matrix groups
    files := tuple[4];
    strings := [Read(name) : name in files];
    lists := [eval(str) : str in strings];
    groups cat:= [MatrixGroup<deg,
	MinimalCyclotomicField(&cat l[1] cat &cat l[2]) |
	Matrix(deg, deg, l[1]), Matrix(deg, deg, l[2])> where deg is #l[1]
	: l in lists];

    // Char p matrix groups
    files := tuple[3];
    strings := [Read(name) : name in files];
    groups cat:= [eval(str) : str in strings];
    
    print "Test Sz on matrix groups for field size", #tuple[2];
    for GG in groups do
	if IsFinite(CoefficientRing(GG)) then
	    G := DerivedGroupMonteCarlo(RandomConjugate(GG));
	else
	    G := DerivedGroupMonteCarlo(GG);
	end if;
	
	G`RandomProcess :=
	    RandomProcessWithWords(G : WordGroup := WordGroup(G),
	    Scramble := 1);

	group_time, membership_time := testGroup(G, tuple[2]);
	
	printf "Time: %o : %o : %o : %o\n\n",
	    Degree(G), CoefficientRing(G), group_time, membership_time;
    end for;

    
    // Groups stored in Magma
    groups := [PermutationGroup(rep) : rep in PermRepKeys(A)];

    // Additional perm groups
    files := tuple[5];
    strings := [Read(name) : name in files];
    groups cat:= [eval(str) : str in strings];
    
    print "Test Sz on perm groups";
    for GG in groups do
	G := DerivedGroupMonteCarlo(RandomConjugate(GG));
	G`RandomProcess :=
	    RandomProcessWithWords(G : WordGroup := WordGroup(G),
	    Scramble := 1);

	group_time, membership_time := testGroup(G, tuple[2]);
	
	printf "Time: %o : %o : %o\n\n", Degree(G), group_time,
	    membership_time;
    end for;
end for;
