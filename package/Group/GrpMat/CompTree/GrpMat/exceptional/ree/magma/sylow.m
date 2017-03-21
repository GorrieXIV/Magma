/******************************************************************************
 *
 *    sylow.m  Ree group package Sylow subgroup code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-06-13
 *
 *    Version   : $Revision:: 1619                                           $:
 *    Date      : $Date:: 2008-12-16 19:46:55 +1100 (Tue, 16 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: sylow.m 1619 2008-12-16 08:46:55Z jbaa004                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "membership.m" : getInfMapping, getZeroMapping, getReeRecognitionData;
import "standard.m" : getReeOrder, exceptionalOuterAutomorphism,
    isOrbitPoint, getOrbitPoint, getReeDiagonalElt,
    standardGeneratorsNaturalRep;
import "stab.m" : getDiagonalMapping;
import "../../../util/basics.m" : MatSLP, getMapFunction, DiagonaliseMatrix;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/centraliser.m" : BrayAlgorithm;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/section.m" : MeatAxeMaps;

forward sylow3Conjugation, sylow2Conjugation, cyclicSylowConjugation,
    hardSylowConjugation;

declare verbose ReeSylow, 10;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeSylow(G :: GrpMat, p :: RngIntElt) -> GrpMat, SeqEnum
    { G is isomorphic to Ree(q), RecogniseRee(G) has returned true,
    p is a prime. Returns a random Sylow p-subgroup S of G.

    Also returns list of SLPs of the generators of S, in generators of G.
    If p does not divide |G|, then the trivial subgroup is returned. }
    local S, field, m, t, q, invol, slp, CS, smallInvol, largeInvol,
	CS_involSLP, CS_invol, W, completion, g, w, R, CSS, CSS_slps,
	gens, slpList, multiple, order, found, divisor, point, conjugator, GS;
    
    if not (assigned G`ReeReductionData and IsPrime(p)) then
	error "Ree Sylow: G must be a recognised Ree and p a prime";
    end if;

    assert assigned G`RandomProcess;
    
    // Work in standard copy
    S := G`ReeReductionData`stdCopy;
    
    field := CoefficientRing(S);
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    q := #field;

    if not IsDivisibleBy(#S, p) then
	return sub<G | >;
    end if;

    if p eq 2 then
	assert assigned S`RandomProcess;

	// Sylow 2-subgroup is elementary abelian of order 8
	// So find 3 involutions that all commute

	// First involution is arbitrary
	invol, slp := RandomInvolution(S : MaxTries := q,
	    Randomiser := S`RandomProcess);
	dim7Cent := ReeInvolutionCentraliser(S, invol, slp :
	    Randomiser := S`RandomProcess, CheckInput := false);

	// Second involution is from involution centraliser in Ree
	smallInvol := elt<GL(2, field) | 0, 1, -1, 0>;
	
	// Map to 3-dim PSL
	largeInvol :=
	    dim7Cent`ReeInvolCentraliserData`smallToLarge(smallInvol);
	flag, dim7_involSLP :=
	    SL2ElementToWord(dim7Cent`ReeInvolCentraliserData`SmallSL2,
	    largeInvol);
	assert flag;

	// Map to 7-dim PSL
	dim7_invol := dim7Cent`ReeInvolCentraliserData`SLPEval(dim7_involSLP);
	W := Parent(dim7_involSLP);
	assert NumberOfGenerators(W) eq
	    NumberOfGenerators(dim7Cent`ReeInvolCentraliserData`LargeSL2);
	
	assert IsIdentity(dim7_invol^2);
	assert invol^dim7_invol eq invol;	
	
	// Third involution from involution centraliser in PSL of second invol
	// Naive completion check for Bray algorithm
	completion := function(H, U, i, l)
	    H`RandomProcess :=
	    RandomProcessWithWords(H : WordGroup := WordGroup(H));
	g, w := RandomInvolution(H : MaxTries := q,
	    Randomiser := H`RandomProcess);
	if g ne i and invol^g eq invol then
	    return true;
	else
	    return false;
	end if;
    end function;

    R := RandomProcessWithWords(dim7Cent`ReeInvolCentraliserData`LargeSL2 :
	WordGroup := W);
    dim7_PSL_cent, dim7_PSL_cent_slps :=
	BrayAlgorithm(dim7Cent`ReeInvolCentraliserData`LargeSL2,
	dim7_invol, dim7_involSLP : completionCheck := completion,
	Randomiser := R);
    assert assigned dim7_PSL_cent`RandomProcess;

    // Find third involution in centraliser of second
    repeat
	g, w := RandomInvolution(dim7_PSL_cent : MaxTries := q,
	    Randomiser := dim7_PSL_cent`RandomProcess);
    until g ne dim7_invol;
        
    assert invol^g eq invol;
    assert Evaluate(w, UserGenerators(dim7_PSL_cent)) eq g;
    
    // Get w in generators of 7-dim PSL
    w := Evaluate(w, dim7_PSL_cent_slps);
    assert Evaluate(w,
	UserGenerators(dim7Cent`ReeInvolCentraliserData`LargeSL2)) eq g;
    
    // Get w in generators of Ree involution centraliser
    w := Evaluate(w, dim7Cent`ReeInvolCentraliserData`SL2SLPs);
    dim7_involSLP :=
	dim7Cent`ReeInvolCentraliserData`SLPCoercion(dim7_involSLP);

    // Generators of Sylow subgroup as words in Ree generators
    W := Domain(G`ReeReductionData`slpCoercion);
    gens := [invol, dim7_invol, g];
    slpList := [W ! slp, W ! dim7_involSLP, W ! w];
    
    // Return Sylow subgroup
    GS := sub<Generic(G) | [G`ReeReductionData`slpHomo(w) : w in slpList]>;
    GS`Order := 8;
    return GS, slpList;
    
    elif p eq 3 then
	assert assigned S`ReeRecognitionData;

	// Sylow 3-subgroup is elementary abelian of q^3 and is O_3 of
	// the point stabiliser
	
	// Take arbitrary point and conjugate it to zero point
	point := ReeFindOrbitPoint(S : Randomiser := S`RandomProcess,
	    CheckInput := false, wordGroup := WordGroup(G));
	conjugator := getInfMapping(S, point);

	// Conjugate SLPs of generators
	slpList := [g`slp^(conjugator`slp^(-1)) :
	    g in S`ReeRecognitionData`upperGens`subDiagonals[1]`generators];
	
	// Return Sylow subgroup
	GS := sub<Generic(G) | G`ReeReductionData`slpHomo(slpList)>;
	GS`Order := q^3;
	return GS, slpList;
    else

	// Other Sylow subgroups are cyclic
	n := rep{n : n in [q - 1, q + 3 * t + 1, q - 3 * t + 1, (q + 1) div 4]
	    | IsDivisibleBy(n, p)};

	// Find order of cyclic Sylow subgroup
	k, divisor := Valuation(n, p);
	order := p^k;
		
	// Find cyclic Sylow subgroup generator
	W := Domain(G`ReeReductionData`slpCoercion);
	flag, g, slp := RandomElementOfOrder(S, n :
	    Randomiser := S`RandomProcess, MaxTries := q^2);
	assert flag;
	
	// Return Sylow subgroup
	GS := sub<Generic(G) | G`ReeReductionData`slpHomo(W ! slp^divisor)>;
	assert Order(GS.1 : Proof := false) eq order;
	
	GS`Order := order;
	return GS, [W ! slp^divisor];
    end if;
end intrinsic;

intrinsic ReeSylowConjugacy(G :: GrpMat, R :: GrpMat, S :: GrpMat,
    p :: RngIntElt) -> GrpMatElt, GrpSLPElt
    { G is isomorphic to Ree(q), RecogniseRee(G) has returned true,
    p is a prime. R and S are Sylow p-subgroups of G.
    
    Returns g in G such that R^g = S. Also returns g as SLP in generators of G.

    Only implemented cases are p = 2,3 or p divides q - 1.
    If p does not divide |G|, then the identity element is returned.
    }
    local H, field, m, t, q, V, RH, SH, conjugator, P, Q, generator, values,
	a, b, conj1, conj2, points, slp, slp1, slp2;
    
    if not (assigned G`ReeReductionData and IsPrime(p)) then
	error "Ree Sylow conjugation:",
	    "G must be a recognised Ree and p a prime";
    end if;
    if not forall{H : H in [R, S] | forall{x : x in Generators(H) |
	IsDivisibleBy(Order(x : Proof := false), p)}} then
	error "Sz Ree conj: R, S must be p-groups";
    end if;
    if p eq 3 then
	if not (forall{H : H in [R, S] |
	    exists{i : i in [1 .. NumberOfGenerators(H)] |
	    Order(H.i : Proof := false) eq 9}}) then
	    error "Ree Sylow conjutation:",
		"Sylow 3-subgroups are generated by elements of order 9";
	end if;
    end if;

    assert assigned G`RandomProcess;

    // Work in standard copy
    vprint ReeSylow, 3 : "Get standard copy";
    H := G`ReeReductionData`stdCopy;
    assert assigned H`ReeRecognitionData;
    
    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    q := #field;
    V := VectorSpace(field, 7);

    if not IsDivisibleBy(#H, p) then
	return Identity(G), Identity(G`ReeReductionData`slpGroup);
    end if;
    
    vprint ReeSylow, 3 : "Get image of first Sylow";
    RH := sub<Generic(H) | [Function(G`ReeReductionData`iso)(g) :
	g in UserGenerators(R)]>;
    
    vprint ReeSylow, 3 : "Get image of second Sylow";
    SH := sub<Generic(H) | [Function(G`ReeReductionData`iso)(g) :
	g in UserGenerators(S)]>;

    if p eq 2 then
	conjugator, slp := sylow2Conjugation(H, RH, SH, WordGroup(G));	
    elif p eq 3 then
	conjugator, slp := sylow3Conjugation(H, RH, SH);	
    elif IsDivisibleBy(q - 1, p) then
	conjugator, slp := cyclicSylowConjugation(H, RH, SH);
    else
	error "Conjugation not implemented";
    end if;

    // Map back to input copy
    assert IsCoercible(Domain(G`ReeReductionData`slpHomo), slp);
    conjugator := G`ReeReductionData`slpHomo(slp);
        
    return conjugator, slp;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function sylow2Conjugation(H, RH, SH, W)
    local field, q, gensRH, gensSH, involsR, involsS, conjugators,
	otherInvols, C1, completion, C2, R, conj, slp;
    
    field := CoefficientRing(H);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);

    // Check input 
    gensRH := UserGenerators(RH);
    gensSH := UserGenerators(SH);
    assert #gensRH ge 3 and exists{<a,b,c> : a in gensRH, b in gensRH,
	c in gensRH | IsIdentity(a^2) and IsIdentity(b^2) and IsIdentity(c^2)
	and a^b eq a and a^c eq a and b^c eq a};
    assert #gensSH ge 3 and exists{<a,b,c> : a in gensSH, b in gensSH,
	c in gensSH | IsIdentity(a^2) and IsIdentity(b^2) and IsIdentity(c^2)
	and a^b eq a and a^c eq a and b^c eq a};

    // Find the involutions to conjugate
    involsR := rep{[a,b,c] : a in gensRH, b in gensRH,
	c in gensRH | IsIdentity(a^2) and IsIdentity(b^2) and IsIdentity(c^2)
	and a^b eq a and a^c eq a and b^c eq b and #{a, b, c} eq 3};
    involsS := rep{[a,b,c] : a in gensSH, b in gensSH,
	c in gensSH | IsIdentity(a^2) and IsIdentity(b^2) and IsIdentity(c^2)
	and a^b eq a and a^c eq a and b^c eq b and #{a, b, c} eq 3};
    
    conjugators := [];    
    vprint ReeSylow, 3 : "First conjugation";
    
    // Conjugate first involutions
    // Don't care about SLPs
    conj := DihedralTrick(rec<MatSLP | mat := involsR[1], slp := Identity(W)>, 
	rec<MatSLP | mat := involsS[1], slp := Identity(W)>,
	H`RandomProcess : MaxTries := q^2);
    Append(~conjugators, conj`mat);

    // Find centraliser of first involution
    involCent := ReeInvolutionCentraliser(H, involsS[1], Identity(W) :
	Randomiser := H`RandomProcess, CheckInput := false);
    R := RandomProcessWithWords(involCent : WordGroup := WordGroup(involCent));

    vprint ReeSylow, 3 : "Second conjugation";

    // involCent is 2 x L_2(q)
    // Make sure that the other involutions lie in the L_2(q), to make
    // the dihedral trick work

    newInvolsR := [Generic(H) | involsR[1]^conj`mat];
    newInvolsS := [Generic(H) | involsS[1]];

    // Replace involutions
    for i in [2 .. 3] do
	repeat
	    // Random element of odd order from PSL
	    repeat
		g := NormalSubgroupRandomElement(involCent,
		    involCent`ReeInvolCentraliserData`LargeSL2);
	    until IsOdd(Order(g : Proof := false));

	    // We have two cases and hence get a Las Vegas algorithm
	    if IsOdd(Order(involsR[i]^conj`mat * g : Proof := false)) then
		Append(~newInvolsR, involsR[i]^conj`mat);
		break;
	    end if;

	    if IsOdd(Order((involsR[1] * involsR[i])^conj`mat * g :
		Proof := false)) then
		Append(~newInvolsR, (involsR[1] * involsR[i])^conj`mat);
		break;
	    end if;
	until false;
    end for;

    // Replace involutions
    for i in [2 .. 3] do
	repeat
	    // Random element of odd order from PSL
	    repeat
		g := NormalSubgroupRandomElement(involCent,
		    involCent`ReeInvolCentraliserData`LargeSL2);
	    until IsOdd(Order(g : Proof := false));
	    
	    // We have two cases and hence get a Las Vegas algorithm
	    if IsOdd(Order(involsS[i] * g : Proof := false)) then
		Append(~newInvolsS, involsS[i]);
		break;
	    end if;

	    if IsOdd(Order(involsS[1] * involsS[i] * g :
		Proof := false)) then
		Append(~newInvolsS, involsS[1] * involsS[i]);
		break;
	    end if;
	until false;
    end for;
    
    assert newInvolsS[1]^(newInvolsR[2]) eq newInvolsS[1];
    assert newInvolsS[1]^newInvolsS[2] eq newInvolsS[1];
    
    // Conjugate second involutions in stabiliser of first
    // Don't care about SLPs
    conj := DihedralTrick(rec<MatSLP | mat := newInvolsR[2],
	slp := Identity(WordGroup(involCent))>,
	rec<MatSLP | mat := newInvolsS[2], slp :=
	Identity(WordGroup(involCent))>, R : MaxTries := q^2);
    
    Append(~conjugators, conj`mat);

    // Trick due to Mark Stather performs final conjugation
    _, r := Valuation(Order(newInvolsR[3]^conj`mat * newInvolsS[3] :
	Proof := false), 2);
    if r gt 1 then
	r := (r - 1) div 2;
	
	Append(~conjugators, (newInvolsS[3] * newInvolsR[3]^conj`mat)^r);
    end if;
    
    // Get total conjugator
    conj := &* conjugators;
    assert ReeStandardMembership(conj);

    // Express element as SLP
    flag, slp := ReeStandardConstructiveMembership(H, conj :
	Randomiser := H`RandomProcess, CheckInput := false);
    assert flag;

    assert RH^conj eq SH;
    return conj, slp;
end function;

function sylow3Conjugation(H, RH, SH)
    local generator, values, P, Q, a, b, conjugator, slp;

    field := CoefficientRing(H);
    
    points := [];
    for G in [RH, SH] do
	M := GModule(G);
	V := VectorSpace(H);
	
	series := CompositionSeries(M);
	assert exists{N : N in series | Dimension(N) eq 1};
	N := rep{N : N in series | Dimension(N) eq 1};
	
	inc := Morphism(N, M);
	P := V ! inc(N.1);
	assert isOrbitPoint(P);

	Append(~points, P);
    end for;

    // Determine which normalising function we can use
    if exists(k){i : i in [1 .. #points] |
	points[i] eq V ! [1, 0, 0, 0, 0, 0, 0]} then
	// Here we cannot normalise to Zero while fixing Inf

	Q := Rep(Remove(points, k));
	if Q eq V ! [0, 0, 0, 0, 0, 0, 1] then
	    // Here we cannot normalise to Inf while fixing Zero
	    // In this case we know exactly what conjugating matrix to use
	    conjugator := Generic(H) ! -PermutationMatrix(field,
		Reverse([1 .. Degree(H)]));
	    
	    flag, slp := ReeElementToWord(H, conjugator);
	    assert flag;
	    
	    return conjugator, slp;
	end if;

	mapper := getInfMapping;
    else
	mapper := getZeroMapping;
    end if;

    vprint ReeSylow, 3 : "Conjugate to lower triangular form";
    conjs := [mapper(H, P) : P in points];
    
    // Mapping elements will also conjugate Sylow subgroups
    conjugator := conjs[1]`mat * conjs[2]`mat^(-1);
    slp := conjs[1]`slp * conjs[2]`slp^(-1);

    assert ReeStandardMembership(conjugator);
    return conjugator, slp;
end function;

function cyclicSylowConjugation(H, RH, SH)
    local generator, P, Q, a, b, conj1, slp1, conj2, slp2;

    conjs := [];
    V := VectorSpace(H);
    for G in [RH, SH] do
	M := GModule(G);
	factors := CompositionFactors(M);
	assert #factors eq 7 and forall{x : x in factors | Dimension(x) eq 1};

	// Find two ovoids point preserved by subgroup
	homos := {GHom(x, M) : x in factors};
	submods := {Image(homo.1) : homo in homos};	
	points := {@ P : N in submods | isOrbitPoint(P)
	    where P is V ! inc(N.1) where inc is Morphism(N, M) @};
	assert #points eq 2;

	// Get element that conjugates R to H
	// ie map fixed pair of points to infinity and zero points
	a := getInfMapping(H, points[1]);
	b := getZeroMapping(H, points[2] * a`mat);
	conj := a`mat * b`mat;
	slp := a`slp * b`slp;
	
	Append(~conjs, rec<MatSLP | mat := conj, slp := slp>);
    end for;
    
    // Get element that conjugates R to S
    conjugator := conjs[1]`mat * conjs[2]`mat^(-1);
    slp := conjs[1]`slp * conjs[2]`slp^(-1);

    assert ReeStandardMembership(conjugator);
    return conjugator, slp;
end function;
