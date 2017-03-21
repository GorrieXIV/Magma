freeze;

//$Id:: formula.m 1605 2008-12-15 09:05:48Z jbaa004                        $:

import "basics.m" : MatSLP;

function TheFormula(a, h) 
    local n, b;

    n := Order(a`mat : Proof := false);
    assert IsOdd(n);
    
    b := rec<MatSLP | mat := a`mat^h`mat * a`mat, slp := a`slp^h`slp * a`slp>;
    return rec<MatSLP | mat := b`mat^((n - 1) div 2) * h`mat^(-1),
	slp := b`slp^((n - 1) div 2) * h`slp^(-1)>;
end function;

function FindCentraliser(G, a, slpCoercion :
    nGens := 5, Randomiser := RandomProcessWithWords(G : WordGroup :=
    WordGroup(G)))
    /* Situation as with FindComplement. Find centraliser of a \in H \leq G
    where a has order n. This uses TheFormula.

    Randomiser, slpCoercion and nGens are described in FindComplement
    (as RandomiserG and GslpCoercion).
    */
    local R, h, slp_h, gens, slpList;
    
    gens := [];
    slpList := [];
      
    // Find centraliser of element inside G
    repeat
	h, slp_h := Random(Randomiser);
	h := rec<MatSLP | mat := h, slp := slpCoercion(slp_h)>;
	
	repeat
	    h := TheFormula(a, h);
	    h`mat ^:= -1;
	    h`slp ^:= -1;	
	    
	    // Element should centralise a
	until a`mat^h`mat eq a`mat;
	
	Append(~gens, h`mat);
	Append(~slpList, h`slp);	
    until #gens eq nGens;

    return sub<Generic(G) | gens>, slpList;
end function;

function FindComplement(G, H, 
    GslpCoercion, HslpCoercion, n :
    nGens := 5, kernelGens := {}, cyclicElt := "unknown",
    RandomiserG := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    RandomiserH := RandomProcessWithWords(H : WordGroup := WordGroup(H)),
    ExtendedComplement := false) 
    
    /*
    The Formula:
    
    H leq G with H = [2^m] : n, and G = H : S for some group S. Returns
    generators of S, as well as a list of SLPs of the generators, in the
    generators of G.

    Random elements from H, G are chosen using RandomiserH and RandomiserG,
    respectively. HslpCoercion and GslpCoercion must be maps from the word
    groups of these random processes to the same word group. The returned
    SLPs have this word group as parent.

    nGens is the number of generators computed for n : S. If cyclicElt is
    a MatSLP record, it must be an element of H of order n. If kernelGens are
    assigned, they must be generators of [2^m] and cyclicElt must act fixed
    point freely on them by conjugation.

    If ExtendedComplement is true, then n : S is returned rather than S.
    */
    local a, slp_a, C, slpC, S, slpS, slpList;

    // Take element of order n
    if Category(cyclicElt) eq Rec then
	a := cyclicElt;
	assert Order(a`mat : Proof := false) eq n;
	assert forall{x : x in kernelGens | x`mat^a`mat ne x`mat};
    else
	repeat
	    flag, a, slp_a := RandomElementOfOrder(H, n :
		Randomiser := RandomiserH);
	    assert flag;
	    
	    a := rec<MatSLP | mat := a, slp := HslpCoercion(slp_a)>;
	until forall{x : x in kernelGens | x`mat^a`mat ne x`mat};
    end if;
    
    // Find generators for n : S
    C, slpC := FindCentraliser(G, a, GslpCoercion : nGens := nGens,
	Randomiser := RandomiserG);

    if ExtendedComplement then
	return C, slpC;
    end if;

    // Remove cyclic group by finding derived group = S
    S, slpS := DerivedGroupMonteCarlo(C);
    slpList := Evaluate(slpS, slpC);

    return S, slpList;
end function;
