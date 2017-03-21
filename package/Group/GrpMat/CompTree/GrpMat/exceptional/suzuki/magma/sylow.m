/******************************************************************************
 *
 *    sylow.m   Suzuki group package Sylow subgroup code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm and Mark Stather
 *    Dev start : 2005-05-10
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: sylow.m 1605 2008-12-15 09:05:48Z jbaa004                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiSylow, 10;

import "membership.m" : getSuzukiRecognitionData, getInfMappingMatrix,
    getZeroMappingMatrix;
import "standard.m" : diagramAutomorphism, getSuzukiOrder, isOvoidPoint;

import "../../../util/basics.m" : getMapFunction, MatSLP;

forward hardSylowConjugation, sylow2Conjugation, cyclicSylowConjugation;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiSylow(G :: GrpMat, p :: RngIntElt) -> GrpMat, SeqEnum
    { G is isomorphic to Sz(q), RecogniseSz(G) has returned true, p is a prime.
    Returns a random Sylow p-subgroup S of G.

    Also returns list of SLPs of the generators of S, in generators of G.
    If p does not divide |G|, then the trivial subgroup is returned. }
    local S, field, m, r, q, point, conjugator, slpMap, gens, order,
	divisor, multiple, g, slp, GS;
    
    if not (assigned G`SuzukiReductionData and IsPrime(p)) then
	error "Sz Sylow: G must be a recognised Sz and p a prime";
    end if;

    assert assigned G`RandomProcess;
    
    // Work in standard copy
    S := G`SuzukiReductionData`stdCopy;
    W := Domain(G`SuzukiReductionData`slpCoercion);
    
    field := CoefficientRing(S);
    m := (Degree(field) - 1) div 2;
    r := 2^m;
    q := #field;

    if not IsDivisibleBy(#S, p) then
	return sub<G | >;
    end if;
    
    if p eq 2 then
	assert assigned S`SuzukiRecognitionData;

	// Take arbitrary point and conjugate it to zero point
	point := SuzukiFindOvoidPoints(S : CheckInput := false,
	    W := WordGroup(G), Randomiser := S`RandomProcess);
	conjugator := getInfMappingMatrix(S, point);

	// Get generators of Sylow subgroup
	slpMap := [W ! g[1]^(conjugator[1]^(-1)) :
	    g in S`SuzukiRecognitionData`upperGens`subDiagonal`generators];

	GS := sub<Generic(G) | G`SuzukiReductionData`slpHomo(slpMap)>;
	GS`Order := q^2;
	return GS, slpMap;
    else

	n := rep{n : n in [q - 1, q + 2 * r + 1, q - 2 * r + 1]
	    | IsDivisibleBy(n, p)};

	// Find order of cyclic Sylow subgroup
	k, divisor := Valuation(n, p);
	order := p^k;

	// Find cyclic Sylow subgroup generator
	assert assigned S`RandomProcess;
	flag, g, slp := RandomElementOfOrder(S, n :
	    MaxTries := q^2, Randomiser := S`RandomProcess);
	assert flag;
	
	// Return Sylow subgroup
	GS := sub<Generic(G) | G`SuzukiReductionData`slpHomo(W ! slp^divisor)>;
	assert Order(GS.1 : Proof := false) eq order;
	
	GS`Order := order;
	return GS, [W ! slp^divisor];
    end if;
end intrinsic;

intrinsic SuzukiSylowConjugacy(G :: GrpMat, R :: GrpMat, S :: GrpMat,
    p :: RngIntElt) -> GrpMatElt, GrpSLPElt
    { G is isomorphic to Sz(q), RecogniseSz(G) has returned true, p is a prime.
    R and S are Sylow p-subgroups of G.

    Returns g in G such that R^g = S. Also returns g as SLP in
    generators of G. }
    local H, field, m, t, q, V, RH, SH, generator, values, P, Q, a, b,
	conjugator, slp, conj1, conj2, slp1, slp2, points;
    
    if not (assigned G`SuzukiReductionData and IsPrime(p)) then
	error "Sz Sylow conjugation: G must be a recognised Sz and p a prime";
    end if;
    if not forall{H : H in [R, S] | forall{x : x in Generators(H) |
	IsDivisibleBy(Order(x : Proof := false), p)}} then
	error "Sz Sylow conjugation: R, S must be p-groups";
    end if;
    if p eq 2 then
	if not (forall{H : H in [R, S] |
	    exists{i : i in [1 .. NumberOfGenerators(H)] |
	    Order(H.i : Proof := false) eq 4}}) then
	    error "Sz Sylow conjugation:",
		"Sylow 2-subgroups are generated by elements of order 4";
	end if;
    end if;
    
    assert assigned G`RandomProcess;

    
    // Work in standard copy
    vprint SuzukiSylow, 3 : "Get standard copy";
    H := G`SuzukiReductionData`stdCopy;
    assert assigned H`SuzukiRecognitionData;
    
    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    q := #field;
    V := VectorSpace(field, 4);

    if not IsDivisibleBy(#H, p) then
	return Identity(G), Identity(G`SuzukiReductionData`slpGroup);
    end if;
    
    vprint SuzukiSylow, 3 : "Get image of first Sylow";
    RH := sub<Generic(H) | [Function(G`SuzukiReductionData`iso)(g) :
	g in UserGenerators(R)]>;
    
    vprint SuzukiSylow, 3 : "Get image of second Sylow";
    SH := sub<Generic(H) | [Function(G`SuzukiReductionData`iso)(g) :
	g in UserGenerators(S)]>;

    vprint SuzukiSylow, 6 : "Conjugate Sylows for p = ", p;
    vprint SuzukiSylow, 6 : Factorization(q - 1), Factorization(q + t + 1),
	Factorization(q - t + 1);
    
    if p eq 2 then
	// R, S are conjugate to lower triangular Sylow 2-subgroup
	// find point they fix, use trick to find conjugating element
	
	vprint SuzukiSylow, 3 : "p = 2";

	conjugator, slp := sylow2Conjugation(H, RH, SH);	
    elif IsDivisibleBy(q - 1, p) then
	// R, S each fixes a distinct pair of points

	conjugator, slp := cyclicSylowConjugation(H, RH, SH);
    else
	conjugator, slp := hardSylowConjugation(H, RH, SH);	
    end if;

    vprint SuzukiSylow, 3 : "Move back to input copy";
    
    // Map back to input copy
    assert IsCoercible(Domain(G`SuzukiReductionData`slpHomo), slp);
    conjugator := G`SuzukiReductionData`slpHomo(slp);
    
    return conjugator, slp;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function sylow2Conjugation(H, RH, SH)
    local generator, values, P, Q, a, b, conjugator, slp;

    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    q := #field;

    points := [];
    V := VectorSpace(H);
    for G in [RH, SH] do
	M := GModule(G);
	
	series := CompositionSeries(M);
	assert exists{N : N in series | Dimension(N) eq 1};
	N := rep{N : N in series | Dimension(N) eq 1};
	
	inc := Morphism(N, M);
	P := V ! inc(N.1);
	assert isOvoidPoint(P);

	Append(~points, P);
    end for;

    // Determine which normalising function we can use
    if exists(k){i : i in [1 .. #points] | points[i] eq V ! [0, 0, 0, 1]} then
	// Here we cannot normalise to Zero while fixing Inf

	Q := Rep(Remove(points, k));
	if Q eq V ! [1, 0, 0, 0] then
	    // Here we cannot normalise to Inf while fixing Zero
	    // In this case we know exactly what conjugating matrix to use
	    conjugator := Generic(H) ! PermutationMatrix(field,
		Reverse([1 .. Degree(H)]));
	    	    
	    flag, slp := SzElementToWord(H, conjugator);
	    assert flag;
	    
	    return conjugator, slp;
	end if;

	mapper := getInfMappingMatrix;
    else
	mapper := getZeroMappingMatrix;
    end if;

    vprint SuzukiSylow, 3 : "Conjugate to lower triangular form";
    conjs := [mapper(H, P) : P in points];

    // Mapping elements will also conjugate Sylow subgroups
    conjugator := conjs[1][2] * conjs[2][2]^(-1);
    slp := conjs[1][1] * conjs[2][1]^(-1);

    assert SuzukiStandardMembership(conjugator);
    return conjugator, slp;
end function;

function cyclicSylowConjugation(H, RH, SH)
    local generator, points, a, b, conj1, slp1, conj2, slp2, conjugator, slp;
    
    field := CoefficientRing(H);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    q := #field;

    conjs := [];
    V := VectorSpace(H);
    for G in [RH, SH] do
	M := GModule(G);
	factors := CompositionFactors(M);
	assert #factors eq 4 and forall{x : x in factors | Dimension(x) eq 1};

	// Find two ovoids point preserved by subgroup
	homos := {GHom(x, M) : x in factors};
	submods := {Image(homo.1) : homo in homos};	
	points := {@ P : N in submods | isOvoidPoint(P)
	    where P is V ! inc(N.1) where inc is Morphism(N, M) @};
	assert #points eq 2;

	// Can't map zero point to infinity
	if points[1] eq Vector(field, [1, 0, 0, 0]) then
	    points := Reverse(IndexedSetToSequence(points));
	end if;

	// Can't map infinity point to zero
	if points[2] eq Vector(field, [0, 0, 0, 1]) then
	    points := Reverse(IndexedSetToSequence(points));
	end if;

	// Get element that conjugates R to H
	// ie map fixed pair of points to infinity and zero points
	a := getInfMappingMatrix(H, points[1]);
	b := getZeroMappingMatrix(H, points[2] * a[2]);
	conj := a[2] * b[2];
	slp := a[1] * b[1];
	
	Append(~conjs, rec<MatSLP | mat := conj, slp := slp>);
    end for;
        
    // Get element that conjugates R to S
    conjugator := conjs[1]`mat * conjs[2]`mat^(-1);
    slp := conjs[1]`slp * conjs[2]`slp^(-1);
    assert SuzukiStandardMembership(conjugator);

    return conjugator, slp;
end function;

// Trick due to Bill Kantor
// Given two matrices acting irreducibly, find a power of one of them that is
// similar to the other. This is done without actually finding the power
// itself, ie the correct positive integer.
function fixCyclicGenerators(g, h)

    F := CoefficientRing(g);
    f_1 := MinimalPolynomial(g);
    assert IsIrreducible(f_1);

    // alpha is expressed as a polynomial in a root of f_1
    flag, alpha := HasRoot(MinimalPolynomial(h), ext<F | f_1>);
    assert flag;

    // This polynomial gives the correct power of g
    MA := MatrixAlgebra(F, Degree(g));
    return Generic(Parent(g)) ! Evaluate(Polynomial(MA,
	ElementToSequence(alpha, F)), MA ! g);
end function;

function hardSylowConjugation(H, RH, SH)
    local n, genS, genR, flag, g1, g2, J, t1, A, D, C, conj, f1, t2, alpha, w,
	k, j, ints, i, conjugator, slp, theta1, theta2, field, q;
    
    // hard case, need discrete log in GF(q^4)
    // This solution in this case is mostly due to Mark Stather,
    // and the underlying idea is from Scott Murray

    field := CoefficientRing(H);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    n := Degree(H);

    ordersSH := [Order(x : Proof := false) : x in UserGenerators(SH)];
    ordersRH := [Order(x : Proof := false) : x in UserGenerators(RH)];
    assert forall{x : x in ordersSH | IsDivisibleBy(q + t + 1, x)} or
	forall{x : x in ordersSH | IsDivisibleBy(q - t + 1, x)};
    assert forall{x : x in ordersRH | IsDivisibleBy(q + t + 1, x)} or
	forall{x : x in ordersRH | IsDivisibleBy(q - t + 1, x)};

    _, k := Max(ordersSH);
    genSH := SH.k;
    _, k := Max(ordersRH);
    genRH := RH.k;
	
    if not IsSimilar(genSH, genRH) then	
	genS := genSH;
	genR := fixCyclicGenerators(genRH, genSH);
	assert Order(genR : Proof := false) eq ordersRH[k];
    else
	genS := genSH;
	genR := genRH;
    end if;
    
    flag, g1 := IsSimilar(genS, genR);
    assert flag;
    
    g1 := Generic(H) ! g1;
    assert genR^g1 eq genS;
    
    // Standard symplectic form
    J := PermutationMatrix(field, Reverse([1 .. n]));
    assert J eq form where _, form is SymplecticForm(H);
    t1 := J * Transpose(g1^(-1)) * J^(-1) * g1^(-1);
    
    // Check that R.1 and S.1 are conjugate in GL
    A := MatrixAlgebra(field, n);
    D := Centralizer(A, sub<A | A ! genR>);
    assert A ! t1 in D;
    
    C := AutomorphismGroup(GModule([genR]));
    assert IsCyclic(C);
    
    // Construct isomorphism from C to GF(q^n)
    // theta1 is the iso and theta2 is the inverse
    CC, f1 := AbsoluteRepresentation(C);
    _, f2 := WriteOverSmallerField(Generic(CC), field);
    flag, conj := IsSimilar(C.1, Function(f2)(f1(C.1)));
    assert flag;
    f2 := func<g | (Generic(H) ! Function(f2)(g))^(Generic(H) ! conj)>;
    theta1 := func<g | f1(g)[1, 1]>;
    theta2 := func<g | f2(Matrix([[g]]))>;
    
    // Find conjugating element in Sp
    flag, g2 := NormEquation(GF(q^n), GF(q^2) ! theta1(t1));
    assert flag;
    g2 := theta2(g2);
    assert genR^(g2 * g1) eq genS;
    assert g2 * g1 * J * Transpose(g2 * g1) eq J;
    
    // Find element of order q^2 + 1 in GF(q^n)
    alpha := PrimitiveElement(GF(q^n));
    w := alpha^(q^2 - 1);
    assert Order(w) eq q^2 + 1;
    
    // Use discrete log in GF(q^n) to find conjugating element in Sz
    t2 := g2 * g1 * diagramAutomorphism(g2 * g1)^(-1);
    
    k := Log(w, theta1(diagramAutomorphism(theta2(w))));
    j := Log(w, theta1(t2));
    ints := Integers(q^2 + 1);
    i := Integers() ! Solution(ints ! (k - 1), ints ! j);
    
    conjugator := theta2(w^i) * g2 * g1;
    assert genR^conjugator eq genS;

    assert SuzukiStandardMembership(conjugator);
    flag, slp := SuzukiStandardConstructiveMembership(H, conjugator :
	Randomiser := H`RandomProcess, CheckInput := false);
    
    return conjugator, slp;
end function;
