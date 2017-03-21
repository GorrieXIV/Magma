// Test Prospector on Sym(n) with bad generators
SetVerbose("PRProspection", 3);

startN := 2;
stopN := 100;
nTests := 100;

scrambles := 0;
nReturns := 10;
alpha := 0.05;

reals := RealField();
mixTimes := [];
output := Open("R/mixing.cox.nonacc.data", "w");
fprintf output, "%4o %4o\n", "n", "mix";

for n in [startN .. stopN] do
    H := SymmetricGroup(n);
    
    nMix := [reals | ];
    for i in [1 .. nTests] do
	// Use Coxeter generators
	gens := GeneratingTranspositions(n);
	G := sub<H | gens>;
	
	flag := InitialiseProspector(G : 
	    PRScramble := scrambles, nReturnsToGoodVertex := nReturns,
	    UseAccelerator := false, UseProspector := false,
	    BiasUnusedGenerators := true,
	    SamplerSignificanceLevel := alpha,
	    SeekerSignificanceLevel := alpha);
	assert flag;
	    
	// Probability about 1/n to find a good element
	PropertyTester := func<g |
	    exists{x : x in CycleStructure(g) | x[1] eq n}>;
	    
	PRTries := 0;
	repeat
	    flag, g, slp, nTries :=
		Prospector(G, PropertyTester : MaxTries := n^2);
	    PRTries +:= nTries;
	until flag;
	
	Append(~nMix, PRTries);
    end for;
    
    Append(~mixTimes, &+nMix / nTests);
    fprintf output, "%4o %4o\n", n, mixTimes[#mixTimes];
    printf "%4o %4o\n", n, mixTimes[#mixTimes];
end for;

print mixTimes;
delete output;
