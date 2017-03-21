// Tests of Classical groups package

SetVerbose("ClassicalRecognition", 0);
SetVerbose("User1", 0);
SetVerbose("User2", 0);
SetVerbose("User3", 0);
SetVerbose("User4", 0);
SetVerbose("User5", 0);
SetAssertions(true);

// Number of conjugates per group to test
nConjugates := 1;

// Number of rewrites per group
nRewrites := 10;

// Test variables
GroupInfo := recformat<
    creator : Intrinsic, // group creator function
    dims : SeqEnum, // matrix dims 
    primes : SeqEnum, // field chars
    degs : SeqEnum>; // field degrees

// Classical types to test
types := [
    "linear",
    "symplectic",
    "unitary",
    "orthogonalcircle",
    "orthogonalplus",
    "orthogonalminus"];

// Fill test data for each classical type
groups := AssociativeArray();

groups["linear"] := rec<GroupInfo |
    creator := SL,
    dims := [2 .. 6],
    primes := PrimesInInterval(2, 17),
    degs := [1 .. 5]>;

groups["symplectic"] := rec<GroupInfo |
    creator := Sp,
    dims := [2 .. 6 by 2],
    primes := PrimesInInterval(3, 17),
    degs := [1 .. 5]>;

groups["unitary"] := rec<GroupInfo |
    creator := SU,
    dims := [2 .. 6],
    primes := PrimesInInterval(3, 17),
    degs := [2 .. 6 by 2]>;

groups["orthogonalcircle"] := rec<GroupInfo |
    creator := Omega,
    dims := [3 .. 5 by 2],
    primes := PrimesInInterval(3, 17),
    degs := [1 .. 5]>;

groups["orthogonalplus"] := rec<GroupInfo |
    creator := OmegaPlus,
    dims := [2 .. 6 by 2],
    primes := PrimesInInterval(3, 17),
    degs := [1 .. 5]>;

groups["orthogonalminus"] := rec<GroupInfo |
    creator := OmegaMinus,
    dims := [2 .. 6 by 2],
    primes := PrimesInInterval(3, 17),
    degs := [1 .. 5]>;

procedure ErrorOutput(err, G, type, d, p, e)
    print "Error in Classical recognition!";
    printf "Parameters type = %o, d = %o, p = %o, e = %o\n", type, d, p, e;
    print "Error message:", err`Object;
    print err`Position;
    //print err`Traceback;
    print "Bad group";
    print G : Magma;
end procedure;

procedure testGroup(G)
    flag := ClassicalConstructiveRecognition(G);
    assert flag;
    assert assigned G`RandomProcess;

    for i in [1 .. nRewrites] do
	g := Random(G`RandomProcess);
	
	flag, slp := ClassicalElementToWord(G, g);
	assert flag;
	
	slpUser := Evaluate(slp, G`ClassicalRecognitionData`slps);
	assert Evaluate(slpUser, UserGenerators(G)) eq g;
    end for;
end procedure;

//SetProfile(true);
//ProfileReset();

for type in (types) do
    print "Testing type", type;
    for d in groups[type]`dims do
	print "Testing d =", d;
	for p in groups[type]`primes do
	    for e in groups[type]`degs do
		print "Testing q =", p^e;
		for i in [1 .. nConjugates] do

		    G := RandomConjugate(groups[type]`creator(d, GF(p, e)));

		    try
			testGroup(G);
		    catch er
			ErrorOutput(er,	G, type, d, p, e);
		    end try;
		end for;
	    end for;
	end for;
    end for;
end for;

//graph := ProfileGraph();
//SetProfile(false);
//ProfilePrintByTotalTime(graph);
//ProfileHTMLOutput(graph, "classical");
