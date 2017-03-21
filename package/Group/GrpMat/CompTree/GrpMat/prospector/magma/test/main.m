intrinsic TestProspector(G :: Grp, R :: GrpRandProc, PropertyTester ::
    UserProgram, m :: RngIntElt, nElements :: RngIntElt,
    alpha :: FldReElt)
    { Main test routine for the Product Replacement Prospector. Find nElements
    elements of the required kind. Compare number of required selections with
    the expected number, which is assumed to be about m.
    }

    reals := RealField();
    
    PRElements := {};
    ProspectorElements := {};
    nElts := nElements;
    PREltTries := [reals | ];
    ProspectEltTries := [reals | ];
    PRLengths := [reals | ];
    ProspectLengths := [reals | ];

    // Use Prospector and normal PR to find nElts elements
    // Save lengths of SLPs
    while nElts gt 0 do
	PRTries := 0;
	repeat
	    h, w := Random(R);
	    PRTries +:= 1;
	until PropertyTester(h);
	
	ProspectTries := 0;
	repeat
	    flag, g, slp, nTries :=
		Prospector(G, PropertyTester : MaxTries := m^2);
	    ProspectTries +:= nTries;
	until flag;
	
	Include(~PRElements, h);
	Include(~ProspectorElements, h);
	
	Append(~PREltTries, PRTries);
	Append(~ProspectEltTries, ProspectTries);

	Append(~PRLengths, #w);
	Append(~ProspectLengths, #slp);
	
	print #w, #slp, PRTries, ProspectTries;
	nElts -:= 1;
    end while;
    
    for i in [1 .. #G`ProspectorData`SamplingData`TestData] do
	printf "Test %o ok after %o and %o steps\n", i,
	    G`ProspectorData`SamplingData`TestData[i]`SamplerOKPos,
	    G`ProspectorData`SamplingData`TestData[i]`SeekerOKPos;
    end for;
    
    print "PR average SLP length:", Round(&+PRLengths / #PRLengths);
    print "Prospector average SLP length:",
	Round(&+ProspectLengths / #ProspectLengths);

    print "PR average number of choices:", Round(&+PREltTries / #PREltTries);
    print "Prospector average number of choices:",
	Round(&+ProspectEltTries / #ProspectEltTries);
    
    // Chi square tests to see if number of selections differ
    // significantly from the expected values
    
    f := #ProspectEltTries - 1;
    threshold := Probit(1 - alpha);
    
    n := &+ProspectEltTries;
    chi := reals ! &+[(ProspectEltTries[i] - n / m)^2 / (n * m) :
	i in [1 .. #ProspectEltTries]];
    
    value := (Root(chi / f, 3) - (1 - 2 / (9 * f))) / Sqrt(2 / (9 * f));
    printf "Ordinary PR wrong nof choices: %o\n", value gt threshold;
    
    n := &+ PREltTries;
    chi := reals ! &+[(PREltTries[i] - n / m)^2 / (n * m) :
	i in [1 .. #PREltTries]];
    
    value := (Root(chi / f, 3) - (1 - 2 / (9 * f))) / Sqrt(2 / (9 * f));
    printf "Prospector wrong nof choices: %o\n", value gt threshold;
end intrinsic;
