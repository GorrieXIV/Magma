/******************************************************************************
 *
 *    elements.m Element conjugacy for small Ree groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2007-05-08
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: elements.m 1605 2008-12-15 09:05:48Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeElements, 10;

import "standard.m" : getReeInfSylowGen, standardGeneratorsNaturalRep;
import "maximals.m" : ReeMaximalsInfo;

forward stdCopyClasses, stdCopyRepresentative;

ReeConjugacyClassInfo := recformat<
    classes : SeqEnum,
    representatives : SetIndx,
    torusBases : SeqEnum,
    torusNormalisers : SeqEnum>;

declare attributes GrpMat : ReeConjugacyClassData;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeConjugacyClasses(G :: GrpMat) -> []
    { G is isomorphic to Ree(q) and RecogniseRee(G) has returned true. 
      Returns of list of conjugacy class representatives of G. }

    if not assigned G`ReeReductionData then
	error "G must be a recognised Ree group";
    end if;

    if assigned G`ReeConjugacyClassData then
	return G`ReeConjugacyClassData`classes;
    end if;

    assert assigned G`ReeReductionData`stdCopy;
    if not assigned G`ReeReductionData`stdCopy`ReeConjugacyClassData then
	G`ReeReductionData`stdCopy`ReeConjugacyClassData :=
	    stdCopyClasses(G`ReeReductionData`stdCopy);
    end if;

    if not ReeStandardRecogniser(G) then
	classes := [<x[1], x[2], G`ReeReductionData`inv(x[3])> : x in
	    G`ReeReductionData`stdCopy`ReeConjugacyClassData`classes];
	
	G`ReeConjugacyClassData := rec<ReeConjugacyClassInfo |
	    classes := classes>;
    end if;
    
    return G`ReeConjugacyClassData`classes;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function stdCopyClasses(G)

    assert assigned G`RandomProcess;
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 3^(m + 1);

    gens := standardGeneratorsNaturalRep(F);
    
    if not assigned G`ReeMaximals then
	vprint ReeElements, 1:
	    "Construct maximals subgroups of standard copy";
	
	maximals, slps := ReeStandardMaximalSubgroups(G);
	G`ReeMaximals :=
	    rec<ReeMaximalsInfo |
	    maximals := maximals,
	    slps := slps>;
    end if;
    maximals := G`ReeMaximals`maximals;
    
    // Generators of cyclic subgroups to search in
    torus_gens := [gens[2]];
    //k, s := Valuation(Order(torus_gens[#torus_gens] : Proof := false), 2);
    //torus_gens[#torus_gens] ^:= 2^k;
    //assert Order(torus_gens[#torus_gens] : Proof := false) eq s;
    
    for i in [0 .. 2] do
	Append(~torus_gens, (maximals[#maximals - i].1,
	    maximals[#maximals - i].2));

	//k, s := Valuation(Order(torus_gens[#torus_gens] : Proof := false), 2);
	//torus_gens[#torus_gens] ^:= 2^k;
	//assert Order(torus_gens[#torus_gens] : Proof := false) eq s;
    end for;
    
    // Also need normalising elements
    torus_normalisers := [gens[1]];
    for i in [0 .. 2] do
	Append(~torus_normalisers, maximals[#maximals - i].1 *
	    maximals[#maximals - i].2);
    end for;
    
    // Lowest order should come first
    Sort(~torus_gens, func<x, y | Order(x) - Order(y)>, ~perm);
    
    // Sort normalisers accordingly
    torus_normalisers := PermuteSequence(torus_normalisers, perm);

    g := getReeInfSylowGen(F, 1, 0, 0);
    smallRee := sub<Generic(G) | g * gens[1], gens[2]^((q - 1) div 2)>;
    flag, small_ree := IsOverSmallerField(smallRee);
    assert flag;
    cbm := SmallerFieldBasis(smallRee);
    
    smallClasses := [x : x in ConjugacyClasses(small_ree) | x[1] ne 7];
    reeExt, inc := ExtendField(Generic(small_ree), F);
    reeInc := hom<small_ree -> smallRee | x :-> inc(x)^(cbm^(-1))>;
    
    uni_big_class_sizes := [1, #G div (q * (q^2 - 1)),
	#G div q^3, #G div (2 * q^2), #G div (2 * q^2), 
	#G div (2 * q), #G div (2 * q), #G div (3 * q), 
	#G div (3 * q), #G div (3 * q)];
    
    // Avoid 7-elements, since we don't know their class size
    classes := [<smallClasses[i][1],
	uni_big_class_sizes[i],
	Function(reeInc)(smallClasses[i][3])> : i in [1 .. #smallClasses]];
    
    // Numbers and sizes of semisimple classes
    orders := [q - t + 1, (q + 1) div 2, q - 1, q + t + 1];
    Sort(~orders, ~perm);
    
    num_classes := PermuteSequence([(q - t) div 6, (q - 3) div 6,
	(q - 3) div 2, (q + t) div 6], perm);
    
    cent_sizes := PermuteSequence([q - t + 1, q + 1, q - 1, q + t + 1],
	perm);
    
    // Search for torus representatives
    for i in [1 .. #torus_gens] do
	traces := {};
	torus_reps := [];
	g := torus_gens[i];
	
	// Check elements in the cyclic group until we have found enough
	for j in [1 .. Order(torus_gens[i]) - 1] do
	    if Order(g) gt 2 then
		trace := Trace(g);
		
		if trace notin traces then
		    Include(~traces, trace);
		    Append(~torus_reps, g);
		end if;
		
		if #traces eq num_classes[i] then
		    break;
		end if;
	    end if;
	    
	    // Check next element
	    g *:= torus_gens[i];
	end for;
	
	classes cat:= [<Order(x), #G div cent_sizes[i], x> : x in torus_reps];
    end for;

    // Sort representatives on element order
    Sort(~classes, func<x, y | x[1] - y[1]>);
    
    return rec<ReeConjugacyClassInfo |
	classes := classes,
	representatives := {@ x[3] : x in classes @},
	torusBases := torus_gens,
	torusNormalisers := torus_normalisers>;
end function;
