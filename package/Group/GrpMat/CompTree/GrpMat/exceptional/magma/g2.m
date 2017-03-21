/******************************************************************************
 *
 *    g2.m      Wilson/Bray trick for finding SL2 and SL3/SU3 in G2
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-11-03
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: g2.m 1605 2008-12-15 09:05:48Z jbaa004                         $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose Exceptional, 10;

// Structure for storing a matrix and its SLP
EltSLP := recformat<elt : GrpElt, slp : GrpSLPElt>;

import "../../util/order.m" : IsProbablySL2;
import "../../util/comptree.m" : SL2pElement;

forward G2SL2Copy, G2Maximal, getSL3Conjugator, G2pElement;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

intrinsic testG2Trick(p :: RngIntElt, e :: RngIntElt) -> BoolElt
    { }

    F := GF(p, e);
    G := RandomConjugate(G2(F));
    G`RandomProcess := RandomProcessWithWords(G : WordGroup := WordGroup(G));
    
    for i in [1 .. 10] do
	H, H_slps, x, g := G2SL2Copy(G, #F);
	flag := true;
	//flag, U, U_slps := G2Maximal(G, H, H_slps, x, g);
	//print flag;
	
	if flag then
	    break;
	end if;
    end for;
    assert flag;

    g, slp := G2pElement(G, H, H_slps);
    print Order(g);
    assert flag;
    assert Evaluate(slp, UserGenerators(G)) eq g;
    assert Order(g) mod p eq 0;

    RandomSchreier(H);
    cc := ConjugacyClasses(H);
    print [x : x in cc | x[1] eq 2];
    /*
    RandomSchreier(H);
    RandomSchreier(U);
    print CompositionFactors(H);
    print CompositionFactors(U);
    */
    
    print #F mod 3;
    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

/* Get generators for H \leq G s.t. H \cong SL(2,q).
   This trick is due to Rob Wilson and works if char is not 3.
   This is a "black box with order oracle" method.
   H is a long root SL2 since it lies inside an SL3
   */
function G2SL2Copy(G, q)     
    r := q mod 3;
    assert assigned G`RandomProcess;
    
    if r eq 0 then
	error "Char 3 not supported";
    else
	if r eq 1 then
	    power := q^2 + q + 1;
	elif r eq 2 then
	    power := q^2 - q + 1;
	end if;

	// Find element in correct conjugacy class that powers up to an
	// element of order 3
	vprint Exceptional, 3 : "Get element of pseudo order 3";
	repeat
	    flag, x, slp_x := RandomElementOfOrder(G, power :
		Randomiser := G`RandomProcess);
	until flag;
    end if;
    
    vprint Exceptional, 3 : "Fix element order";
    l, r := Quotrem(Order(x), 3);
    assert r eq 0;
    a := rec<EltSLP | elt := x^l, slp := slp_x^l>;
    assert Order(a`elt) eq 3;
    
    vprint Exceptional, 3 : "Get random conjugates";
	
    // Take random conjugates until we get an SL2
    repeat
	g, w := Random(G`RandomProcess);
	b := rec<EltSLP | elt := a`elt^g, slp := a`slp^w>;

	H := sub<Generic(G) | a`elt, b`elt>;
	H_slps := [a`slp, b`slp];
	vprint Exceptional : "Checking for SL2";

    until IsProbablySL2(H : ErrorProb := 2^(-100), q := q);

    return H, H_slps, rec<EltSLP | elt := x, slp := slp_x>,
	rec<EltSLP | elt := g, slp := w>;
end function;

// G is G2(q), H is SL2 inside G found with function above
// x and g are elements returned by SL2 finder above
// Find SL3.2 or SU3.2 in G, containing H
// If q mod 3 = 1, then find SL3.2, if q mod 3 = 2 then find SU3.2
function G2Maximal(G, H, H_slps, x, g)

    tree := CompositionTree(H);
    _, toFactor, fromFactor, _, _, leaves := CompositionTreeSeries(H);

    flag := false;
    for i in [1 .. #toFactor] do
	if assigned leaves[i]`LeafData`Family and
	    assigned leaves[i]`LeafData`LieRank and
	    Retrieve(leaves[i]`LeafData`Family) cmpeq "A" and
	    leaves[i]`LeafData`LieRank eq 1 then
	    
	    S := Codomain(toFactor[i]);
	    if Category(S) eq GrpMat and Degree(S) eq 2 then
		// S is SL2 standard copy
	    
		flag, conj := getSL3Conjugator(H, H_slps, 
		    toFactor[i], fromFactor[i]);
		if not flag then
		    return false, _, _;
		end if;
		
		flag, slp := CompositionTreeElementToWord(H, conj);
		assert flag;
		
		coerce := CompositionTreeNiceToUser(H);
		gen := rec<EltSLP | elt := g`elt * conj,
		    slp := g`slp * Evaluate(coerce(slp), H_slps)>;
		assert H.1^gen`elt eq H.1^(-1);
		break;
	    end if;
	end if;
    end for;

    // H is not SL2
    if not flag then
	return false, _, _;
    end if;
    
    // Generators for SL3.2 or SU3.2
    return true, sub<Generic(G) | x`elt, gen`elt>, [x`slp, gen`slp];
end function;
    
// G = G2(q), q = p^e
// Find an element of order p by using above black box trick to find an SL2
// This produces a long root p-element
function G2pElement(G, q)
    // Find an SL2
    H, H_slps := G2SL2Copy(G, q);

    elt, slp := SL2pElement(H, q);
    return elt, Evaluate(slp, H_slps);
end function;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Trick due to John Bray, finds extra elements that generate an SL3 or SU3
// containing H \cong SL2 inside G2
function getSL3Conjugator(H, H_slps, largeToSmall, smallToLarge)
    vprint Exceptional, 3 : "SL2 found, mapping to small dim";
    assert NumberOfGenerators(H) eq 2;
    i1 := Function(largeToSmall)(H.1);
    i2 := Function(largeToSmall)(H.2);
    
    S := Codomain(largeToSmall);
    flag, conj := IsSimilar(i1^(-1), i2);
    if flag then
	vprint Exceptional, 3 : "Similar elements, scaling conjugator";
	flag, conj := ScaleMatrix(conj);
	
	if flag then
	    conj := Generic(S) ! conj;
	    assert i2^conj eq i1^(-1) and IsOne(Determinant(conj));
	    
	    vprint Exceptional, 3 : "Mapping conjugator to large dim";
	    return true, Function(smallToLarge)(conj);
	end if;
    end if;
    
    return false, _;
end function;
