/******************************************************************************
 *
 *    crosschar.m Ree cross char constructive recognition
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2005-08-11
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: crosschar.m 1605 2008-12-15 09:05:48Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeCrossChar, 10;

import "ree.m": ReeReductionFormat, ReeReductionMaps;
import "../../../util/basics.m" : MatSLP;

forward ReeStandardGeneratorsBlackBox;

declare attributes GrpMat : ReeStandardGenerators;

ReeStandardGensFormat := recformat<h : Rec, x : Rec, z : Rec>;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeCrossCharacteristicReduction(G :: GrpMat : CheckInput :=
    true, FieldSize := 0, Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) -> Map
    { G is isomorphic to Ree(q) but is over a field of characteristic not 3.
    Return isomorphism to Ree(q). }
    local H, recognition, field, q, permHomo1, permGroup1, permHomo2,
	permGroup2, permIso, status, iso, GG, inv, bool, prime, degree,
	ruleMap1, ruleMap2;

    if CheckInput then
	recognition, q := ReeGeneralRecogniser(G);
	if not recognition then
	    error "Ree CrossChar: G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error "Ree CrossChar: Field must have size > 3";
	end if;

	// Check that field size is valid
	flag, degree := IsPowerOf(FieldSize, 3);
	if not (flag and IsOdd(degree)) then
	    error "Ree CrossChar: Field must be an odd power of 3";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    F := GF(q);
    H := Ree(F);

    // Find standard generators in input copy
    gens, slps := ReeStandardGenerators(G, F);
    GS := sub<Generic(G) | gens>;
    phi := InverseWordMap(GS);
    homo := hom<G -> H | x :-> Evaluate(phi(x), UserGenerators(H))>;
    
    // Find standard copy
    ree := sub<Generic(H) | [Function(homo)(x) : x in UserGenerators(G)]>;

    assert ReeStandardRecogniser(ree);
    iso := hom<G -> ree | x :-> Function(homo)(x)>;
    inv := hom<ree -> G | x :-> Evaluate(slp, gens)
    where slp is ReeStandardConstructiveMembership(H, x :
	Randomiser := H`RandomProcess, CheckInput := false)>;
    
    if not assigned G`ReeReductionData then
	G`ReeReductionData := rec<ReeReductionFormat |
	    maps := rec<ReeReductionMaps | crosschar := iso>>;
    else
	G`ReeReductionData`maps`crosschar := iso;
    end if;
    
    return iso;
end intrinsic;

intrinsic ReeStandardGenerators(G :: GrpMat, F :: FldFin) -> [], []
    { G is isomorphic to Ree(F). Find g_1,g_2,g_3 in G that corresponds to the
    generators returned by the Ree intrinsic. }
    
    q := #F;
    H := Ree(F);

    vprint ReeCrossChar, 1 : "Entering Ree standard generators algorithm";
    
    // Find permutation representations and obtain stabilisers for free 
    _, PH, SS, SS_w := ReePermutationRepresentation(H);
    vprint ReeCrossChar, 1 : "Found standard perm rep";
    assert SS.1 eq PH.2 and SS.2 eq PH.3;

    _, PG := PermutationRepresentation(G);
    W := WordGroup(PG);
    R := RandomProcessWithWords(PG : WordGroup := W);

    flag, g, g_w := RandomElementOfOrder(PG, q - 1 : Randomiser := R);
    assert flag;
    repeat
	flag, h, h_w := RandomElementOfOrder(PG, q - 1 : Randomiser := R);
	assert flag;

	S := sub<PG | g, h>;
	S_w := [g_w, h_w];
    until #Fix(S) eq 1;

    vprint ReeCrossChar, 1 : "Found other perm rep";    
    
    assert #Fix(S) eq 1;
    assert Order(S.1) eq q - 1;
    assert Evaluate(S_w, UserGenerators(PG)) eq UserGenerators(S);
    assert Evaluate(SS_w, UserGenerators(PH)) eq UserGenerators(SS);
    
    S_w := Evaluate(S_w, UserGenerators(W));
    
    WS := WordGroup(S);
    SR := RandomProcessWithWords(S : WordGroup := WS);

    // Generators of stabiliser
    h := rec<MatSLP | mat := S.1, slp := S_w[1]>;
    repeat
	g1, g1_w := Random(SR);
	g2, g2_w := Random(SR);

	g_slps := Evaluate([g1_w, g2_w], S_w);
	
	x := rec<MatSLP | mat := (g1, g2), slp := (g_slps[1], g_slps[2])>;
    until Order(x`mat) eq 9;

    vprint ReeCrossChar, 2 : "Found x";
    
    // Base for change in x
    xx2 := rec<MatSLP | mat := x`mat^3, slp := x`slp^3>;
    repeat
	g1, g1_w := Random(SR);
	g2, g2_w := Random(SR);

	g_slps := Evaluate([g1_w, g2_w], S_w);
	
	xx1 := rec<MatSLP | mat := (x`mat^g1, x`mat^g2),
	    slp := (x`slp^g_slps[1], x`slp^g_slps[2])>;
    until xx1`mat^x`mat ne xx1`mat;

    vprint ReeCrossChar, 1 : "Searching for stabiliser gens";
    
    for i in [1 .. q - 1] do
	for j in [1 .. q - 1] do
	    found := false;
	    
	    // Base for change in h
	    hh := rec<MatSLP | mat := Identity(PG), slp := Identity(W)>;
	    
	    // Some small power of h or its inverse works
	    for k in [1 .. q - 1] do
		hh`mat *:= h`mat;
		hh`slp *:= h`slp;
		
		// Possible pairs of standard generators
		gens := [<hh, rec<MatSLP | mat := x`mat * xx1`mat * xx2`mat,
		    slp := x`slp * xx1`slp * xx2`slp>>,
		    <hh, rec<MatSLP | mat := x`mat * xx1`mat^(-1) * xx2`mat,
		    slp := x`slp * xx1`slp^(-1) * xx2`slp>>];
		    
		// See if these pairs work
		for gen in gens  do
		    vprint ReeCrossChar, 3 : "Test homomorphism",
			i, j, k, q - 1;
		    if IsHomomorphism(SS, S, [g`mat : g in gen]) then
			h := rec<MatSLP | mat := gen[1]`mat,
			    slp := gen[1]`slp>;
			x := rec<MatSLP | mat := gen[2]`mat,
			    slp := gen[2]`slp>;
			found := true;
			vprint ReeCrossChar, 1 : "Homomorphism ok!";
			break;
		    end if;
		end for;

		if found then
		    break;
		end if;
	    end for;
	    
	    if found then
		break;
	    end if;
	end for;

	if found then
	    break;
	end if;
    end for;
    assert found;

    vprint ReeCrossChar, 1 : "Found stabiliser gens";
    
    if not found then
	error "No stabiliser generators found";
    end if;

    //assert IsHomomorphism(SS, PG, [h`mat, x`mat]);
    assert Evaluate([h`slp, x`slp], UserGenerators(PG)) eq [h`mat, x`mat];

    // Now find anti-diag involution
    z := rec<MatSLP | mat := h`mat^((q - 1) div 2),
	slp := h`slp^((q - 1) div 2)>;
    assert Order(z`mat) eq 2;

    vprint ReeCrossChar, 1 : "Find initial involution";

    // Conjugate involution until it is outside stabiliser
    repeat
	g, w := Random(R);
	    
	z`mat ^:= g;
	z`slp ^:= w;
    until IsEmpty(Fix(S) meet Fix(z`mat));

    vprint ReeCrossChar, 2 : "Found initial z";
    
    // Conjugate involution to interchange points of h
    P := Rep(Fix(S));
    Q := Rep(Fix(h`mat) diff {P});
    repeat
	k, k_w := Random(SR);
    until (P^z`mat)^k eq Q;

    vprint ReeCrossChar, 2 : "Found conjugating k";
    
    z`mat ^:= k;
    z`slp ^:= Evaluate(Evaluate(k_w, S_w), UserGenerators(W));
    assert P^z`mat eq Q;

    vprint ReeCrossChar, 1 : "Find correct involution";

    // If T is the correct involution, then T also interchanges P and Q
    // Hence Tz fixes P and Q and therefore lies in <h>
    // Hence we can find T
    while not IsHomomorphism(PH, PG, [z`mat, h`mat, x`mat]) do
	z`mat *:= h`mat;
	z`slp *:= h`slp;
    end while;
    
    vprint ReeCrossChar, 1 : "Involution found!";

    //assert IsHomomorphism(PH, PG, [z`mat, h`mat, x`mat]);
    assert Evaluate([z`slp, h`slp, x`slp], UserGenerators(PG)) eq
	[z`mat, h`mat, x`mat];

    vprint ReeCrossChar, 1 : "Evaluating on input matrices";

    // Obtain matrix generators
    gens := Evaluate([z`slp, h`slp, x`slp], UserGenerators(G));
    
    vprint ReeCrossChar, 1 : "Standard generators found";
    return gens, [z`slp, h`slp, x`slp];
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/
