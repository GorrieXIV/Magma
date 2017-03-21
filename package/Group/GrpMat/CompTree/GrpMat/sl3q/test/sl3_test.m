SetLogFile("sl3_test_new.out" : Overwrite := true);
SetVerbose("sl3q", 0);

SetSeed(1);

load "construct-examples.m";
load "../../../test/suites/testgroup.m";

procedure TestSL3(H, F)
    G := RandomConjugate(H);
    print "Testing group";
    try
	flag, iso, inv, g2slp := RecogniseSL3(G, F : Verify := true);
	assert flag;
	rate := G`SL3Data`TotalTime gt 0 select G`SL3Data`SL2Time / G`SL3Data`TotalTime else 0;	   
        printf "%o%% in SL2 oracle\n", 100 * rate;
    catch err
        ErrorOutput(err, "RecogniseSL3", G);
    end try;
    
    try
	R := RandomProcess(G);
	elts := [];
	slps := [];
	for i in [1 .. 10] do
	    g := Random(R);
	    flag, slp := SL3ElementToWord(G, g);
	    assert flag;
	    Append(~elts, g);
	    Append(~slps, slp);
	end for;
	assert Evaluate(slps, UserGenerators(G)) eq elts;
	assert flag;
    catch err
        ErrorOutput(err, "SL3ElementToWord", G);
    end try;
end procedure;

startPrimeNr := 2;
maxPrimeNr := 11;
startExponent := 1;
maxExponent := 10;

for prime in [startPrimeNr .. maxPrimeNr] do
    p := NthPrime(prime);
    for e in [startExponent .. maxExponent] do		
	F := GF(p, e);
	q := #F;
	if q lt 2^20 then
	    printf "Testing SL3 reps for p = %o, e = %o\n", p, e;
	    S := SL(3, F);
	
            print "Test standard copy";
	    TestSL3(S, F);
	
            print "Test exterior power";
            G := MyExteriorPower(S, 2);
	    TestSL3(G, F);

            print "Test adjoint";
	    G := MyAdjointRepresentation(S);
	    TestSL3(G, F);
	
	    for t in [1 .. e - 1] do
		printf "Test reps for t = %o\n", t;
		G := MySymmetricPower(S, t);
		TestSL3(G, F);

		G := MyDeltaRepresentation(S, t);
		TestSL3(G, F);
		
		G := MyOtherRepresentation(S, t);
		TestSL3(G, F);
	    end for;
	
            print "Test groups from ConstructReps";
	    reps := ConstructReps(S);
	    printf "Number of groups: %o\n", #reps;
            for G in reps do
		TestSL3(G, F);
	    end for;
	end if;
    end for;
end for;
