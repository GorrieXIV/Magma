freeze;

// Find comp factors of G and see if <family, rank, q> exists
// If one such matrix group factor is found, return effective iso
function CTRecogniserMultiple(G, names)
    tree := CompositionTree(G);
    _, toFactor, fromFactor, _, _, leaves := CompositionTreeSeries(G);

    // Find standard copy among comp factors
    for i in [1 .. #fromFactor] do
	if assigned leaves[i]`LeafData`Family and
	    assigned leaves[i]`LeafData`LieRank and
	    assigned leaves[i]`LeafData`DefiningField then

	    for name in names do
		if Retrieve(leaves[i]`LeafData`Family) cmpeq name[1] and
		    leaves[i]`LeafData`LieRank eq name[2] and
		    Retrieve(leaves[i]`LeafData`DefiningField) cmpeq
		    name[3] then

		    S := Domain(fromFactor[i]);
		    if Category(S) eq GrpMat then
			return true, toFactor[i], fromFactor[i], leaves[i];
		    end if;
		end if;
	    end for;
	end if;
    end for;

    return false, _, _;
end function;

function CTRecogniser(G, family, rank, q)
    return CTRecogniserMultiple(G, [<family, rank, q>]);
end function;

// Use comp tree to recognise a copy of SL(d,q)
function CTRecogniseSL(G, d, q)
    priorities := [19 .. 1 by -1];

    // In grey box context we can do less reductions
    if Category(G) eq GrpMat and
	IsDivisibleBy(q, Characteristic(CoefficientRing(G))) then
	for i in [10 .. 14] do
	    priorities[i] := 0;
	end for;

	mandarins := 10;

	// SL2 requires even less reductions
	if d eq 2 then
	    for i in [15 .. 17] do
		priorities[i] := 0;
	    end for;
	end if;
    else
	mandarins := 100;
    end if;

    // EOB -- may sometimes want ExhibitSummands set to false because of cost 
    tree := CompositionTree(G : Priorities := priorities,
			    MandarinBatchSize := mandarins, Verify := false, 
			    ExhibitSummands := true);

    /*
    if d eq 2 then
	names := [<"A", 1, q>, <"B", 1, q>];
	flag, qq := IsSquare(q);
	if flag then
	    Append(~names, <"2D", 2, qq>);
	end if;

	if q eq 3 then
	    Append(~names, <17, 3, 4>);
	elif q eq 4 then
	    names cat:= [<"A", 1, 5>, <17, 5, 0>];
	elif q eq 5 then
	    names cat:= [<"A", 1, 4>, <17, 5, 0>];
	elif q eq 7 then
	    Append(~names, <"A", 2, 2>);
	elif q eq 9 then
	    Append(~names, <17, 6, 0>);
	end if;
    elif d eq 3 then
	names := [<"A", 2, q>];
	
	if q eq 2 then
	    Append(~names, <"A", 1, 7>);
	end if;
    elif d eq 4 then
	names := [<"A", 3, q>, <"D", 3, q>];
    else
    */	

    names := [<"A", d - 1, q>];
    //end if;
    
    return CTRecogniserMultiple(G, names);
end function;

function CTRecogniseSL2(G, q)    
    return CTRecogniseSL(G, 2, q);
end function;

function CTRecogniseSL3(G, q)
    return CTRecogniseSL(G, 3, q);
end function;

function SL2pElement(G, q)
    // Find maps to standard SL2
    flag, toS, fromS := CTRecogniseSL2(G, q);
    assert flag;
    
    // S is SL2 standard copy
    S := Domain(fromS);

    // Construct p-element
    F := CoefficientRing(S);
    g := elt<Generic(S) | 1, 0, PrimitiveElement(F), 1>;
    
    // Map p-element to input copy
    pElt := Function(fromS)(g);
    flag, slp := CompositionTreeElementToWord(G, pElt);
    assert flag;
		
    coerce := CompositionTreeNiceToUser(G);
    return pElt, coerce(slp);
end function;
