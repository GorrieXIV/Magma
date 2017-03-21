freeze;

//$Id:: centraliser.m 3135 2015-08-09 05:15:13Z eobr007                    $:

import "basics.m" : MatSLP;

declare verbose Centraliser, 2;

MyCentraliserOfInvolution := function (G, g, wg:
    Central := false, Proof := false, NumberRandom := 100,
    CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 20>,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))

    local centraliser, element, commutator, q, r, residue, slpMap,
	word, nGens;

    if Central then fct := CentralOrder; else fct := Order; end if;

    R := Randomiser;

    centraliser := sub<Generic(G) | g>;
    slpMap := [wg];

    vprint Centraliser, 1: "Starting Bray algorithm";
    repeat
        NumberRandom -:= 1;
	element, word := Random(R);
	assert Parent(word) cmpeq Parent(wg);
	commutator := rec<MatSLP | mat := (g, element), slp := (wg, word)>;
	// compute order 
	if Type (g) eq GrpMatElt then     
           o := fct(commutator`mat : Proof := Proof);
           q, r := Quotrem(o, 2);
	else 
           q, r := Quotrem(fct(commutator`mat), 2);
        end if;
	
	if r eq 1 then
	    vprint Centraliser, 2: "Odd case";
	    residue := rec<MatSLP | mat := element * commutator`mat^q,
		slp := word * commutator`slp^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) |
		[centraliser.i : i in [1 .. nGens]], residue`mat>;

	    // Only add SLP if generator was not obviously redundant
	    if NumberOfGenerators(centraliser) gt nGens then
		Append(~slpMap, residue`slp);
	    end if;

	    assert #slpMap eq NumberOfGenerators(centraliser);
	else
	    vprint Centraliser, 2: "Even case";
	    residue := rec<MatSLP | mat := commutator`mat^q,
		slp := commutator`slp^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) | [centraliser.i :
		i in [1 .. nGens]], residue`mat>;

	    // Only add SLP if generator was not obviously redundant
	    if NumberOfGenerators(centraliser) gt nGens then
		Append(~slpMap, residue`slp);
	    end if;
	    
	    residue := rec<MatSLP | mat := (g, element^(-1))^q,
		slp := (wg, word^(-1))^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) | [centraliser.i :
		i in [1 .. nGens]], residue`mat>;

	    // Only add SLP if generator was not obviously redundant
	    if NumberOfGenerators(centraliser) gt nGens then
		Append(~slpMap, residue`slp);
	    end if;

	    assert #slpMap eq NumberOfGenerators(centraliser);
	end if;

	vprint Centraliser, 2: "Check centraliser completion";
    until CompletionCheck(G, centraliser, g, slpMap) or NumberRandom eq 0;
    
    vprint Centraliser, 1: "Bray algorithm finished";
    assert #slpMap eq NumberOfGenerators(centraliser);

    return centraliser, slpMap;
end function;

intrinsic CentraliserOfInvolution (G :: GrpMat, g :: GrpMatElt, wg :: 
    GrpSLPElt : Central := false, NumberRandom := 100,
    CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 20>,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> GrpMat, SeqEnum
    {g is an involution in G, and wg is an SLP for g. 
    Return the centraliser C of g in G, and SLPs of the generators of C.
    Randomiser is the random process used to construct the 
    elements and the SLP for g must lie in the word group of this process. 

    The algorithm used is that of John Bray.  Since it is Monte Carlo, 
    it may return only a subgroup of the centraliser. 

    If Central then construct the projective centraliser of  g.
    The function CompletionCheck is used to determine when we have 
    constructed the centraliser.  It takes arguments G, C, g 
    and SLPs for generators of C as input, and 
    returns true or false.  By default, the algorithm completes when the 
    centraliser has 20 generators or considered NumberRandom elements.}
    
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(g) eq 2: "<g> must be an involution";

    return MyCentraliserOfInvolution (G, g, wg: Central := Central, 
       NumberRandom := NumberRandom, CompletionCheck := CompletionCheck, 
       Randomiser := Randomiser);
end intrinsic;

intrinsic CentraliserOfInvolution (G :: GrpPerm, g :: GrpPermElt, 
    wg :: GrpSLPElt: Central := false, NumberRandom := 100, 
    CompletionCheck := func<G, C, g, l | NumberOfGenerators(C) ge 20>,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
    -> GrpPerm, SeqEnum
    {g is an involution in G, and wg is an SLP for g. 
    Return the centraliser C of g in G, and SLPs of the generators of C.
    Randomiser is the random process used to construct 
    the elements and the SLP for g must lie in the word group of 
    this process. 
    The algorithm used is that of John Bray.  Since it is Monte Carlo, 
    it may return only a subgroup of the centraliser. 
    If Central then construct the projective centraliser of  g.
    The function CompletionCheck is used to determine when we have 
    constructed the involution centraliser. 
    It takes arguments G, C, g 
    and SLPs for generators of C as input, and returns true or false.
    By default, the algorithm completes when the centraliser has 20
    generators or considered NumberRandom elements.
    }

    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(g) eq 2: "<g> must be an involution";
    return MyCentraliserOfInvolution (G, g, wg: Central := Central, 
       NumberRandom := NumberRandom, CompletionCheck := CompletionCheck, 
       Randomiser := Randomiser);
end intrinsic;

MyCentraliserWithoutWords := function (G, g:
   Central := false, Proof := false, NumberRandom := 100,
   CompletionCheck := func<G, C, g | NumberOfGenerators(C) ge 20>,
   Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))

    local centraliser, element, commutator, q, r, residue, slpMap,
	word, nGens;

    if Central then fct := CentralOrder; else fct := Order; end if;

    R := RandomProcess (G);
    centraliser := sub<Generic(G) | g>;

    vprint Centraliser, 1: "Starting Bray algorithm";
    repeat
        NumberRandom -:= 1;
	element := Random(R);
	commutator := rec<MatSLP | mat := (g, element)>;
	if Type (g) eq GrpMatElt then     
           o := fct(commutator`mat : Proof := Proof);
           q, r := Quotrem(o, 2);
	else 
           q, r := Quotrem(fct(commutator`mat), 2);
        end if;
	
	if r eq 1 then
	    vprint Centraliser, 2: "Odd case";
	    residue := rec<MatSLP | mat := element * commutator`mat^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) |
		[centraliser.i : i in [1 .. nGens]], residue`mat>;
	else
	    vprint Centraliser, 2: "Even case";
	    residue := rec<MatSLP | mat := commutator`mat^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) | [centraliser.i :
		i in [1 .. nGens]], residue`mat>;

	    residue := rec<MatSLP | mat := (g, element^(-1))^q>;
	    nGens := NumberOfGenerators(centraliser);

	    // Add generator to centraliser
	    centraliser := sub<Generic(G) | [centraliser.i :
		i in [1 .. nGens]], residue`mat>;
	end if;
	
	vprint Centraliser, 2: "Check centraliser completion";
    until CompletionCheck(G, centraliser, g) or NumberRandom eq 0;
    vprint Centraliser, 1: "Bray algorithm finished";

    return centraliser;

end function;

intrinsic CentraliserOfInvolution (G :: GrpMat, g :: GrpMatElt:
  Central := false, NumberRandom := 100, 
  CompletionCheck := func<G, C, g | NumberOfGenerators(C) ge 20>, 
  Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G))) -> GrpMat
    {g is an involution in G. Return the centraliser C of g in G.
    The algorithm used is that of John Bray.  
    Since it is Monte Carlo, it may return only a subgroup of the centraliser. 
    If Central then construct the projective centraliser of  g.
    The function CompletionCheck is used to determine when we have 
    constructed the centraliser. It takes arguments G, C and g
    as input and returns true or false.
    By default, the algorithm completes when the centraliser has 20 
    generators or considered NumberRandom elements.
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(g) eq 2: "<g> must be an involution";
    return MyCentraliserWithoutWords (G, g: Central := Central,
	NumberRandom := NumberRandom, CompletionCheck := CompletionCheck,
	Randomiser := Randomiser);
end intrinsic;

intrinsic CentraliserOfInvolution (G :: GrpPerm, g :: GrpPermElt:
 Central := false, NumberRandom := 100, 
 CompletionCheck := func<G, C, g | NumberOfGenerators(C) ge 20>,
 Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G))) -> GrpPerm
    {g is an involution in G. Return the centraliser C of g in G.
    The algorithm used is that of John Bray.  Since it is Monte Carlo, 
    it may return only a subgroup of the centraliser. 
    If Central then construct the projective centraliser of  g.
    The function CompletionCheck is used to determine when we have 
    constructed the centraliser. It takes arguments G, C and g
    as input and returns true or false.
    By default, the algorithm completes when the 
    centraliser has 20 generators or considered NumberRandom elements.
    }
    if Central then fct := CentralOrder; else fct := Order; end if;
    require fct(g) eq 2: "<g> must be an involution";
    return MyCentraliserWithoutWords (G, g: Central := Central,
       NumberRandom := NumberRandom, CompletionCheck := CompletionCheck,
       Randomiser := Randomiser);
end intrinsic;

function BrayAlgorithm(G, g, slp :
    completionCheck := func<G, U, g, l | NumberOfGenerators(G) ge 20>,
	Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)))
	return CentraliserOfInvolution(G, g, slp :
	CompletionCheck := func<G, C, g, l | completionCheck(C, G, g, l)>,
	Randomiser := Randomiser);
end function;
