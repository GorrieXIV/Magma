// Test Prospector on various sporadic groups
Attach("magma/test/main.m");
SetVerbose("PRProspection", 3);
sporadic_str := Read("data/atlas.out");
sporadics := eval sporadic_str;

nElements := 10;
slots := 10;
scrambles := 0;
maxSelections := 1000;
minSelections := 200;
maxPermDegree := 10000; 
maxMatDegree := 100;
alpha := 0.05;

printf "PR Slots = %o, PR Scrambles = %o\n", slots, scrambles;

for sporadic in sporadics do
    name := sporadic[1];
    data := sporadic[2];
    
    goodElements := [i : i in [1 .. #data] |
	data[i][2] le maxSelections and data[i][2] ge minSelections];
    
    for i in goodElements do
	order := data[i][1];
	selections := Integers() ! data[i][2];
	
	PropertyTester := func<g | Order(g) eq order>;
	
	A := ATLASGroup(name);
	reps := PermRepKeys(A);
	
	for rep in reps do
	    H := PermutationGroup(rep);
	    G := H;
	    n := Degree(H);
	    
	    if n le maxPermDegree then
		printf "Using perm rep of %m of degree %o\n", A, n;
		printf "Looking for elements of order %o\n", order;
		printf "Expected number of selections %o\n", selections;
		
		print "Init ordinary PR";
		R := RandomProcessWithWords(G : WordGroup := WordGroup(G),
		    Slots := slots,
		    Scramble := scrambles);
		
		print "Init Prospector";
		flag := InitPermGroupProspector(G : PRSlots := slots,
		    PRScramble := scrambles);
		
		TestProspector(G, R, PropertyTester, selections,
		    nElements, alpha);
	    end if;
	end for;
	
	reps := MatRepKeys(A);
	
	for rep in reps do
	    G := MatrixGroup(rep);
	    n := Degree(G);

	    if n le maxMatDegree then
		printf "Using matrix rep of %m of degree %o\n", A, n;
		printf "Field size %o\n", #CoefficientRing(G);
		printf "Looking for elements of order %o\n", order;
		printf "Expected number of selections %o\n", selections;
		
		print "Init ordinary PR";
		R := RandomProcessWithWords(G : WordGroup := WordGroup(G),
		    Slots := slots,
		    Scramble := scrambles);
		
		print "Init Prospector";
		flag := InitMatGroupProspector(G : PRSlots := slots,
		    PRScramble := scrambles);
		
		TestProspector(G, R, PropertyTester, selections,
		    nElements, alpha);
	    end if;
	end for;
    end for;
end for;
