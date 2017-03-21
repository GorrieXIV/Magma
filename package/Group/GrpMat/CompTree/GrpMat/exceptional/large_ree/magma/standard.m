/******************************************************************************
 *
 *    standard.m Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2006-06-04
 *
 *    Version   : $Revision:: 1648                                           $:
 *    Date      : $Date:: 2009-02-07 11:36:00 +1100 (Sat, 07 Feb 2009)       $:
 *    Last edit : $Author:: eobr007                                          $:
 *
 *    $Id:: standard.m 1648 2009-02-07 00:36:00Z eobr007                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose LargeReeStandard, 10;

forward getIrreducibleModuleFactors, getLargeReeOrder,
    OrderLargeReeDiagonal, getLargeReeDiagonal, checkAlbertAlgebra,
    normaliseQuadForm, getLargeReeQuadForm, getLargeReeDiagonalAlt,
    getReeRobTorus, LargeReeStandardCopy, getReeRobTorusElt,
    getRobF4Torus, twistingMap, getQuadraticForm;

import "ree.m" : LargeReeTrivialRecognitionChecks;
import "../../../util/basics.m" : MatSLP, DiagonaliseMatrix;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeRee(F :: FldFin) -> GrpMat
    { |F| = 2^(2m + 1) with m > 0. Return LargeRee(F) on its standard
    generators. }

    if not (Characteristic(F) eq 2 and #F gt 2 and IsOdd(Degree(F))) then
	error "F must have size an odd power of 2";
    end if;
    
    G := LargeReeStandardCopy(F);
    G`Order := getLargeReeOrder(#F);
    return G;
end intrinsic;

intrinsic LargeReeGroup(F :: FldFin) -> GrpMat
    { |F| = 2^(2m + 1) with m > 0. Return LargeRee(F) on its standard
    generators. }

    return LargeRee(F);
end intrinsic;
/*
intrinsic LargeRee(m :: RngIntElt) -> GrpMat
    { m is a positive integer. Return LargeRee(2^(2m + 1)) on its
    standard generators. }
    local F;

    F := GF(2, 2 * m + 1);
    return LargeRee(F);
end intrinsic;
*/
intrinsic LargeRee(q :: RngIntElt) -> GrpMat
    { q = 2^(2m + 1) with m > 0. Return LargeRee(q) on its
    standard generators. }
    local field, flag, p, k;

    p := 2;
    flag, k := IsPowerOf(q, p);
    if not (flag and IsOdd(k) and k gt 1) then
	error "Field size must be an odd power of 2";
    end if;
    
    field := GF(p, k);
    return LargeRee(field);
end intrinsic;

intrinsic LargeReeGroup(q :: RngIntElt) -> GrpMat
    { q = 2^(2m + 1) with m > 0. Return LargeRee(q) on its
    standard generators. }

    return LargeRee(q);
end intrinsic;

intrinsic LargeRee(V :: ModTupRng) -> GrpMat
    { Given a 26-dimensional vector space V over the finite field GF(q), where
    q = 2^(2m + 1) with m > 0, return LargeRee(V) on its standard generators. }
    local field;

    field := CoefficientRing(V);    
    return LargeRee(field);
end intrinsic;

intrinsic LargeReeGroup(V :: ModTupRng) -> GrpMat
    { Given a 26-dimensional vector space V over the finite field GF(q), where
    q = 2^(2m + 1) with m > 0, return LargeRee(V) on its standard generators. }
    local field;

    return LargeRee(V);
end intrinsic;

intrinsic LargeReeIrreducibleRepresentation(F :: FldFin,
    twists :: SeqEnum[SeqEnum[RngIntElt]] : CheckInput := true) -> GrpMat
    { F has size q = 2^(2 * m + 1), m > 0, and twists is a sequence of 
    distinct pairs of integers [i, j], where i is in [26, 246, 4096] and j is
    in the range [0 .. 2m].

    Return an absolutely irreducible representation of BigRee(q),
    a tensor product of twisted powers of the basic representations of
    dimensions 26, 246 and 4096, where the twists
    are given by the input sequence. }
    local H, G, factors, dims;
    
    if CheckInput then
	if not LargeReeTrivialRecognitionChecks(F) then
	    error "|F| must be an odd power of 2, at least 8.";
	end if;
	if not #SequenceToSet(twists) eq #twists then
	    error "<twists> must consist of distinct integers";
	end if;
	
	m := (Degree(F) - 1) div 2;
	if not forall{i : i in twists | i ge 0 and i le 2 * m} then
	    error "Elements of <twists> must be in the range [0 .. 2m]";
	end if;
    end if;
    
    factors := getIrreducibleModuleFactors(F);
    dims := {@ 26, 246, 4096 @};
    G := LargeRee(F);
    M := TrivialModule(G, F);
    
    // Accumulate twisted versions of the group
    for j in [1 .. #twists] do
	N := FrobeniusImage(factors[Index(dims, twists[j][1])],
	    G, twists[j][2]);
	M := TensorProduct(M, N);
    end for;
    
    return ActionGroup(M);
end intrinsic;

intrinsic LargeReeDiagonalisation(g :: GrpMatElt) -> GrpMatElt, GrpMatElt
    { Diagonalise g of split torus type in LargeRee(q). Return diagonal matrix
    and change of basis matrix. }
    local m, d, k, G;

    G := Generic(Parent(g));
    m := (Degree(CoefficientRing(g)) - 1) div 2;
    t := 2^(m + 1);
    
    // Diagonalise and order eigenvalues properly
    d, k := DiagonaliseMatrix(g : OrderEigenvalues :=
	func<x | OrderLargeReeDiagonal(x, t)>);
    assert LargeReeStandardMembership(G ! d);
    return G ! d, G ! k;
end intrinsic;

intrinsic LargeReeInvolutionClass(g :: GrpMatElt :
    CheckInput := true) -> MonStgElt
    { Return the conjugacy class (2A or 2B) of the involution g
    in a conjugate of LargeRee(q). }
    local factors, mult, F;

    if CheckInput then
	if not (IsIdentity(g^2) and not IsIdentity(g) and
	    Degree(g) eq 26) then
	    error "g must be a Big Ree involution";
	end if;
    end if;

    F := CoefficientRing(g);
    vprint LargeReeStandard, 8 : "Get primary invariant factors of", g;
    t := Cputime();
    factors := {* x[2] : x in PrimaryInvariantFactors(g) *};
    vprint LargeReeStandard, 8 : "Done", Cputime(t);

    mult := Multiplicity(factors, 1);
    assert mult in {2, 6};
    
    if mult eq 2 then
	return "2B";
    else
	return "2A";
    end if;
end intrinsic;

intrinsic IsValidLargeReeOrder(q :: RngIntElt, o :: RngIntElt) -> BoolElt
    { Returns true if LargeRee(q) has an element of order o, false otherwise. }

    // See Deng & Shi,
    // "The Characterization of Ree Groups 2F_4(q) by Their Element Orders"
    // J. Algebra 217, 180-187, 1999
    orders := {1, 2, 4, 8, 12, 16, 2 * (q + 1), 4 * (q - 1),
	4 * (q + Sqrt(2 * q) + 1), 4 * (q - Sqrt(2 * q) + 1),
	q^2 - 1, q^2 + 1, q^2 - q + 1,
	(q - 1) * (q + Sqrt(2 * q) + 1), (q - 1) * (q - Sqrt(2 * q) + 1),
	q^2 + Sqrt(2 * q) * q + q + Sqrt(2 * q) + 1,
	q^2 - Sqrt(2 * q) * q + q - Sqrt(2 * q) + 1};

    if exists{k : k in orders | IsDivisibleBy(k, o)} then
	return true;
    else
	return false;
    end if;
end intrinsic;

intrinsic LargeReeStandardMembership(g :: GrpMatElt) -> BoolElt
    { Non-explicit membership test for LargeRee(q) }

    F := CoefficientRing(g);
    if not (LargeReeTrivialRecognitionChecks(F) and Degree(g) eq 26) then
	return false;
    end if;

    if not IsOne(Determinant(g)) then
	return false;
    end if;

    // Check that we preserve correct bilinear form
    form := PermutationMatrix(F, Reverse([1 .. Degree(g)]));
    if g * form * Transpose(g) ne form then
	return false;
    end if;
   
    // Check that we preserve correct quadratic form
    form := getQuadraticForm(F);
    if normaliseQuadForm(g * form * Transpose(g)) ne form then
	return false;
    end if;

    // Check that we preserve correct Jordan algebra
    if not checkAlbertAlgebra(g) then
	return false;
    end if;

    // Check that we preserve automorphism
    return twistingMap(g) eq g;
end intrinsic;

intrinsic LargeReeStandardRecogniser(G :: GrpMat) -> BoolElt
    { G \leq GL(26, q). Determine (non-constructively) if G = LargeRee(q). }
    local field;

    field := CoefficientRing(G);
    if not LargeReeTrivialRecognitionChecks(field) or Degree(G) ne 26 then
	return false;
    end if;

    if not forall{g : g in Generators(G) | LargeReeStandardMembership(g)} then
	return false;
    end if;

    // Dispose of proper subgroups. They are either Ree groups over subfields
    // or reducible
    if not IsAbsolutelyIrreducible(G) or IsOverSmallerField(G) then
	return false;
    end if;

    return true;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Return quadratic form preserved by standard copy
function getQuadraticForm(F)
    return Matrix(SparseMatrix(F, 26, 26, [1, 26, 1, 1, 25, 1, 1, 24, 1, 1, 23,
	1, 1, 22, 1, 1, 21, 1, 1, 20, 1, 1, 19, 1, 1, 18, 1, 1, 17, 1,
	2, 11, 1, 16, 1, 1, 15, 1, 1, 14, 1, 0, 0, 1, 16, 1, 0, 0, 0, 0, 0, 0,
	0, 0, 0, 0]));
end function;
    
// Convert quadratic form to an upper triangular matrix
function normaliseQuadForm(form)
    n := NumberOfRows(form);
    assert NumberOfColumns(form) eq n;
    newForm := ZeroMatrix(CoefficientRing(form), n, n);
    
    for i in [1 .. n] do
	for j in [i .. n] do
	    if not i eq j then
		newForm[i][j] := form[i][j] + form[j][i];
	    else
		newForm[i][j] := form[i][j];
	    end if;
	end for;
    end for;
    
    return newForm;
end function;

// The exceptional Jordan algebra (Albert algebra) preserved by
// our Big Ree standard copy
function getAlbertAlgebra(F)

    albertTable := [
	<1,16,1,1>,  <1,18,2,1>,  <1,19,3,1>,  <1,20,4,1>,  <1,21,5,1>,
	<1,22,6,1>,  <1,23,7,1>,  <1,24,8,1>,  <1,25,9,1>,  <1,26,11,1>,
	<2,9,1,1>,   <2,11,2,1>,  <2,14,3,1>,  <2,15,4,1>,  <2,17,6,1>,
	<2,21,10,1>, <2,23,12,1>, <2,24,13,1>, <2,25,16,1>, <2,26,18,1>,
	<3,8,1,1>,   <3,11,3,1>,  <3,13,2,1>,  <3,15,5,1>,  <3,16,3,1>,
	<3,17,7,1>,  <3,20,10,1>, <3,22,12,1>, <3,24,11,1>, <3,24,16,1>,
	<3,25,14,1>, <3,26,19,1>, <4,7,1,1>,   <4,11,4,1>,  <4,12,2,1>,
	<4,14,5,1>,  <4,16,4,1>,  <4,17,8,1>,  <4,19,10,1>, <4,22,13,1>,
	<4,23,11,1>, <4,23,16,1>, <4,25,15,1>, <4,26,20,1>, <5,6,1,1>,
	<5,11,5,1>,  <5,12,3,1>,  <5,13,4,1>,  <5,17,9,1>,  <5,18,10,1>,
	<5,22,16,1>, <5,23,14,1>, <5,24,15,1>, <5,26,21,1>, <6,5,1,1>,
	<6,10,2,1>,  <6,11,6,1>,  <6,14,7,1>,  <6,15,8,1>,  <6,16,6,1>,
	<6,19,12,1>, <6,20,13,1>, <6,21,11,1>, <6,21,16,1>, <6,25,17,1>,
	<6,26,22,1>, <7,4,1,1>,   <7,10,3,1>,  <7,11,7,1>,  <7,13,6,1>,
	<7,15,9,1>,  <7,18,12,1>, <7,20,16,1>, <7,21,14,1>, <7,24,17,1>,
	<7,26,23,1>, <8,3,1,1>,   <8,10,4,1>,  <8,11,8,1>,  <8,12,6,1>,
	<8,14,9,1>,  <8,18,13,1>, <8,19,16,1>, <8,21,15,1>, <8,23,17,1>,
	<8,26,24,1>, <9,2,1,1>,   <9,10,5,1>,  <9,11,9,1>,  <9,12,7,1>,
	<9,13,8,1>,  <9,16,9,1>,  <9,18,11,1>, <9,18,16,1>, <9,19,14,1>,
	<9,20,15,1>, <9,22,17,1>, <9,26,25,1>, <10,6,2,1>,  <10,7,3,1>,
	<10,8,4,1>,  <10,9,5,1>,  <10,16,10,1>,<10,17,11,1>,<10,22,18,1>,
	<10,23,19,1>,<10,24,20,1>,<10,25,21,1>,<11,2,2,1>,  <11,3,3,1>,
	<11,4,4,1>,  <11,5,5,1>,  <11,6,6,1>,  <11,7,7,1>,  <11,8,8,1>,
	<11,9,9,1>,  <11,18,18,1>,<11,19,19,1>,<11,20,20,1>,<11,21,21,1>,
	<11,22,22,1>,<11,23,23,1>,<11,24,24,1>,<11,25,25,1>,<12,4,2,1>,
	<12,5,3,1>,  <12,8,6,1>,  <12,9,7,1>,  <12,15,11,1>,<12,16,12,1>,
	<12,20,18,1>,<12,21,19,1>,<12,24,22,1>,<12,25,23,1>,<13,3,2,1>,
	<13,5,4,1>,  <13,7,6,1>,  <13,9,8,1>,  <13,14,11,1>,<13,16,13,1>,
	<13,19,18,1>,<13,21,20,1>,<13,23,22,1>,<13,25,24,1>,<14,2,3,1>,
	<14,4,5,1>,  <14,6,7,1>,  <14,8,9,1>,  <14,13,11,1>,<14,16,14,1>,
	<14,18,19,1>,<14,20,21,1>,<14,22,23,1>,<14,24,25,1>,<15,2,4,1>,
	<15,3,5,1>,  <15,6,8,1>,  <15,7,9,1>,  <15,12,11,1>,<15,16,15,1>,
	<15,18,20,1>,<15,19,21,1>,<15,22,24,1>,<15,23,25,1>,<16,1,1,1>,
	<16,3,3,1>,  <16,4,4,1>,  <16,6,6,1>,  <16,9,9,1>,  <16,10,10,1>,
	<16,12,12,1>,<16,13,13,1>,<16,14,14,1>,<16,15,15,1>,<16,17,17,1>,
	<16,18,18,1>,<16,21,21,1>,<16,23,23,1>,<16,24,24,1>,<16,26,26,1>,
	<17,2,6,1>,  <17,3,7,1>,  <17,4,8,1>,  <17,5,9,1>,  <17,10,11,1>,
	<17,16,17,1>,<17,18,22,1>,<17,19,23,1>,<17,20,24,1>,<17,21,25,1>,
	<18,1,2,1>,  <18,5,10,1>, <18,7,12,1>, <18,8,13,1>, <18,9,11,1>,
	<18,9,16,1>, <18,11,18,1>,<18,14,19,1>,<18,15,20,1>,<18,16,18,1>,
	<18,17,22,1>,<18,25,26,1>,<19,1,3,1>,  <19,4,10,1>, <19,6,12,1>,
	<19,8,16,1>, <19,9,14,1>, <19,11,19,1>,<19,13,18,1>,<19,15,21,1>,
	<19,17,23,1>,<19,24,26,1>,<20,1,4,1>,  <20,3,10,1>, <20,6,13,1>,
	<20,7,16,1>, <20,9,15,1>, <20,11,20,1>,<20,12,18,1>,<20,14,21,1>,
	<20,17,24,1>,<20,23,26,1>,<21,1,5,1>,  <21,2,10,1>, <21,6,11,1>,
	<21,6,16,1>, <21,7,14,1>, <21,8,15,1>, <21,11,21,1>,<21,12,19,1>,
	<21,13,20,1>,<21,16,21,1>,<21,17,25,1>,<21,22,26,1>,<22,1,6,1>,
	<22,3,12,1>, <22,4,13,1>, <22,5,16,1>, <22,9,17,1>, <22,10,18,1>,
	<22,11,22,1>,<22,14,23,1>,<22,15,24,1>,<22,21,26,1>,<23,1,7,1>,
	<23,2,12,1>, <23,4,11,1>, <23,4,16,1>, <23,5,14,1>, <23,8,17,1>,
	<23,10,19,1>,<23,11,23,1>,<23,13,22,1>,<23,15,25,1>,<23,16,23,1>,
	<23,20,26,1>,<24,1,8,1>,  <24,2,13,1>, <24,3,11,1>, <24,3,16,1>,
	<24,5,15,1>, <24,7,17,1>, <24,10,20,1>,<24,11,24,1>,<24,12,22,1>,
	<24,14,25,1>,<24,16,24,1>,<24,19,26,1>,<25,1,9,1>,  <25,2,16,1>,
	<25,3,14,1>, <25,4,15,1>, <25,6,17,1>, <25,10,21,1>,<25,11,25,1>,
	<25,12,23,1>,<25,13,24,1>,<25,18,26,1>,<26,1,11,1>, <26,2,18,1>,
	<26,3,19,1>, <26,4,20,1>, <26,5,21,1>, <26,6,22,1>, <26,7,23,1>,
	<26,8,24,1>, <26,9,25,1>, <26,16,26,1>];
    
    J := Algebra<F, 26 | albertTable>;
    assert not IsAssociative(J);

    return J;
end function;

// Check that g preserves the Jordan algebra
function checkAlbertAlgebra(g)
    F := CoefficientRing(g);

    assert Degree(g) eq 26;

    O := getAlbertAlgebra(F);
    V := Module(O);

    // Convert between module and algebra elements
    o2v := hom<O -> V | [V.i : i in [1 .. Degree(O)]]>;
    v2o := hom<V -> O | [O.i : i in [1 .. Degree(O)]]>;

    // Check that our group preserves algebra multiplication
    for i in [1 .. Degree(O)] do
	for j in [1 .. Degree(O)] do	    
	    if v2o(o2v(O.i * O.j) * g) ne
		v2o(V.i * g) * v2o(V.j * g) then
		return false;
	    end if;
	end for;
    end for;

    return true;
end function;

// Order the split torus diagonal element so that it lies in our standard copy
function OrderLargeReeDiagonal(diagonal, t)
    diag := SequenceToMultiset(diagonal);
    if not exists(a){a : a in diagonal | diag eq
	SequenceToMultiset(getLargeReeDiagonal(a, t))} then
	error "Wrong Big Ree diagonal type";
    end if;

    // Make sure that eigenvalues are in correct order
    orderDiag := getLargeReeDiagonal(a, t);
    perm := {@ @};

    for x in diagonal do
	idx := 0;
	repeat
	    idx := Index(orderDiag, x, idx + 1);
	until idx notin perm;
	
	Include(~perm, idx);
    end for;
    
    assert IndexedSetToSet(perm) eq {1 .. 26};
    
    return IndexedSetToSequence(perm);
end function;

// A split torus element of 2F4 in dimension 26, in 2 variables
// Returned as a sequence
function getLargeReeDiagonalAlt(lambda, mu)
    return getReeRobTorusElt(lambda, mu);
end function;

// A split torus element of 2F4 in dimension 26, in 1 variable
// Returned as a matrix
function getLargeReeDiagonalElt(a, m)
    local G, t;

    t := 2^(m + 1);
    G := GL(26, GF(2, 2 * m + 1));

    return G ! DiagonalMatrix(getLargeReeDiagonal(a, t));
end function;

// A split torus element of 2F4 in dimension 26, in 1 variable
// Returned as a sequence
function getLargeReeDiagonal(a, t)
    return getLargeReeDiagonalAlt(a, a^t);
end function;

// An general torus element of F4 in dimension 26
// Returned as a sequence
function getRobF4Torus(a, b, c, d)
    return [a, b, a * d  / c, c, a * d / b, b / d, a / c, c / d, a / b, d,
	1, b / c, (b * c) / (a * d), (a * d) / (b * c), c / b, 1, 1 / d,
	b / a, d / c, c / a, d / b, b / (a * d), 1 / c, c / (a * d),
	1 / b, 1 / a];
end function;

// A split torus element of 2F4 in dimension 26, in 2 variables
// Returned as a sequence
function getReeRobTorusElt(lambda, mu)
    F := Parent(lambda);
    return getRobF4Torus(F ! 1, lambda, lambda / mu, F ! 1);
end function;

// An general torus element of 2F4 in dimension 26
// Returned as a matrix
function getReeRobTorus(F, a, b)

    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    
    return GL(26, F) ! DiagonalMatrix(F,
	getRobF4Torus(a, b, a * b^(1 - t), a^(t - 1)));
end function;

intrinsic GeneralReeTorusElement (m:: RngIntElt, a, b) -> GrpMatElt 
{ return general torus element of 2F4 in dimension 26}
  F := GF (2^(2 * m + 1));
  return getReeRobTorus(F, a, b);
end intrinsic; 

// Return the 3 basic absolutely irreducible tensor indecomposable modules
// for Big Ree.
// This won't run unless your machine has a _lot_ of RAM!
function getIrreducibleModuleFactors(field)
    local H1, H2, H3;

    vprint LargeReeStandard, 2 : "Get 26-dimensional representation";
    H1 := GModule(LargeRee(field));
    
    vprint LargeReeStandard, 2 : "Get 246-dimensional representation";
    H2 := rep{x : x in CompositionFactors(ExteriorSquare(H1)) |
	Dimension(x) eq 246};

    vprint LargeReeStandard, 2 : "Get 4096-dimensional representation";
    H3 := rep{x : x in CompositionFactors(TensorProduct(H1, H2)) |
	Dimension(x) eq 4096};

    vprint LargeReeStandard, 2 : "Got all basic irreducible representation";
    return [H1, H2, H3];
end function;

// Assumes q is an odd power of 2
function getLargeReeOrder(q)
    return q^12 * (q^6 + 1) * (q^4 - 1) * (q^3 + 1) * (q - 1);
end function;

// Obtain various elements that help us generate Big Ree and its maximal
// subgroups.
// See "Elementary constructions of the Ree groups", Robert A. Wilson, preprint
// http://www.maths.qmul.ac.uk/~raw/
function getLargeReeRobStandardGenerators(F)

    V := VectorSpace(F, 26);
    H := Hom(V, V);
    q := #F;
    p := Characteristic(F);
    U := GL(Degree(V), F);
    S := SymmetricGroup(Degree(V));
    
    // Torus generators
    alpha := PrimitiveElement(F);    
    torus1 := getReeRobTorus(F, alpha, F ! 1);
    torus2 := getReeRobTorus(F, F ! 1, alpha);

    // Involutions from Weyl group
    rho := U ! PermutationMatrix(F, S ! (15, 12)(14, 13)(2, 5)(7, 8)(19, 20)
	(22, 25)(3, 4)(6, 9)(18, 21)(24, 23));
    sigma := U ! PermutationMatrix(F, S ! (11, 16)(1, 2)(8, 13)(14, 19)
	(25, 26)(7, 10)(5, 12)(15, 22)(17, 20)(4, 6)(9, 18)(21, 23));

    // rho of Sz type
    // sigma of SL2 type
    assert LargeReeInvolutionClass(rho) ne LargeReeInvolutionClass(sigma);

    // Other involutions, also non-conjugate
    z := U ! (H ! hom<V -> V | [V.i : i in [1 .. 15]] cat
    [V.16 + V.1, V.17 + V.1, V.18 + V.2, V.19 + V.3, V.20 + V.4, V.21 + V.5,
	V.22 + V.2 + V.6, V.23 + V.3 + V.7, V.24 + V.4 + V.8, V.25 + V.5 + V.9,
	V.26 + V.1 + V.10 + V.11]>);

    t := U ! (H ! hom<V -> V | [V.1, V.2 + V.1, V.3, V.4, V.5, V.6 + V.4,
    V.7 + V.5, V.8, V.9, V.10 + V.5, V.11 + V.9, V.12 + V.10 + V.5 + V.7,
	V.13 + V.8, V.14, V.15, V.16 + V.9, V.17 + V.15,
	V.18 + V.9 + V.11 + V.16, 
	V.19 + V.14, V.20 + V.15, V.21, V.22 + V.17 + V.20 + V.15,
	V.23 + V.21, V.24, V.25, V.26 + V.25]>);

    assert LargeReeInvolutionClass(t) ne LargeReeInvolutionClass(z);

    // Square root of z
    x_1 := LowerTriangularMatrix(F, [1, 1, 1, 1, 1, 1, 1, 0, 1, 1]);
    x_2 := LowerTriangularMatrix(F, [1, 0, 1, 0, 1, 1, 1, 1, 1, 1,
	1, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1]);
    x_3 := Matrix(F, [[1]]);
    
    x := U ! DiagonalJoin(<x_3, x_1, x_1, x_3, x_2, x_3, x_1, x_1, x_3>);

    return [torus1, torus2, rho, sigma, z, t, x];
end function;

intrinsic StandardGeneratorsForLargeRee (m :: RngIntElt) -> []
{return list of standard generators for 2F4(q) where q = 2^(2m + 1) }
  return getLargeReeRobStandardGenerators (GF(2^(2*m + 1)));
end intrinsic; 

function twistingMap(g)

    F := CoefficientRing(g);
    m := (Degree(F) - 1) div 2;
    V := VectorSpace(Parent(g));
    E := VectorSpace(F, Binomial(Dimension(V), 2));
    
    EE := VectorSpace(F, Dimension(E) - Degree(g));
    HomE := Hom(E, E);
    HomEE := Hom(EE, EE);
    HomV := Hom(V, V);

    // Coordinates for change of basis matrices in Hom-spaces
    cbm1_coords := [27, 353, 679, 1005, 1331, 1657, 1983, 2309, 2635, 2961,
	3287, 3613, 3939, 4265, 4551, 4594, 4599, 4605, 4617, 4916, 5242, 5568,
	5894, 6220, 6546, 6872, 7198, 7524, 7850, 8176, 8502, 8828, 9154, 9480,
	9806, 10132, 10458, 10784, 11110, 11436, 11762, 12088, 12414, 12740,
	13066, 13327, 13402, 13410, 13443, 13472, 13653, 13719, 13728, 13744,
	13769, 13809, 13979, 14045, 14062, 14080, 14095, 14150, 14305, 14396, 
	14406, 14421, 14493, 14692, 15018, 15344, 15670, 15996, 16256, 16331,
	16339, 16372, 16383, 16462, 16647, 16973, 17232, 17325, 17335, 17350,
	17361, 17502, 17558, 17701, 17712, 17727, 17744, 17949, 18275, 18601,
	18927, 19253, 19579, 19905, 20231, 20484, 20573, 20598, 20609, 20707,
	20882, 21135, 21278, 21289, 21339, 21358, 21533, 21859, 22185, 22511,
	22837, 23163, 23489, 23815, 24061, 24159, 24174, 24185, 24304, 24466,
	24712, 24854, 24880, 24915, 24955, 25117, 25443, 25769, 26095, 26421,
	26747, 27073, 27399, 27725, 28051, 28377, 28613, 28767, 28799, 28836,
	28879, 29028, 29264, 29364, 29391, 29416, 29431, 29466, 29528, 29551,
	29679, 30005, 30331, 30657, 30983, 31309, 31635, 31961, 32287, 32613,
	32840, 33008, 33025, 33083, 33105, 33264, 33590, 33916, 34242, 34568,
	34894, 35220, 35546, 35872, 36198, 36524, 36850, 37176, 37502, 37828,
	38154, 38480, 38806, 39132, 39458, 39784, 40110, 40436, 40762, 41088,
	41414, 41740, 42066, 42266, 42470, 42489, 42510, 42532, 42717, 43043,
	43369, 43695, 44021, 44347, 44673, 44999, 45325, 45651, 45977, 46303,
	46629, 46817, 46966, 46981, 46998, 47016, 47035, 47056, 47078, 47280,
	47468, 47608, 47621, 47636, 47671, 47752, 47931, 48257, 48444, 48598,
	48629, 48666, 48728, 48770, 48940, 48955, 49013, 49054, 49233, 49421,
	49627, 49644, 49665, 49706, 49884, 50210, 50536, 50862, 51188, 51514,
	51840, 52166, 52492, 52818, 53144, 53470, 53796, 54122, 54297, 54463,
	54478, 54483, 54561, 54580, 54773, 54948, 55150, 55167, 55172, 55213,
	55232, 55424, 55750, 56076, 56402, 56728, 57054, 57380, 57706, 58032,
	58358, 58684, 59010, 59336, 59662, 59988, 60314, 60640, 60799, 61001,
	61039, 61044, 61064, 61083, 61291, 61617, 61943, 62269, 62595, 62921,
	63247, 63573, 63899, 64225, 64551, 64877, 65203, 65529, 65855, 66181,
	66507, 66833, 66975, 67196, 67217, 67242, 67259, 67484, 67810, 68136,
	68462, 68788, 69114, 69440, 69766, 70092, 70418, 70744, 71070, 71396,
	71722, 72048, 72374, 72700, 73026, 73352, 73678, 74004, 74330, 74656,
	74776, 75001, 75022, 75044, 75061, 75307, 75633, 75959, 76285, 76611, 
	76937, 77263, 77589, 77915, 78241, 78567, 78893, 79219, 79545, 79871,
	80197, 80523, 80849, 81175, 81501, 81827, 82153, 82479, 82805, 83131,
	83457, 83783, 84109, 84435, 84761, 85087, 85413, 85739, 86065, 86391,
	86717, 87043, 87369, 87695, 88021, 88347, 88673, 88999, 89325, 89651,
	89977, 90303, 90629, 90955, 91281, 91607, 91933, 92259, 92585, 92911,
	93237, 93563, 93889, 94215, 94541, 94867, 95193, 95519, 95845, 96171,
	96497, 96823, 97149, 97475, 97801, 98127, 98453, 98779, 99105, 99431,
	99757, 100083, 100409, 100735, 101061, 101387, 101713, 102039, 102365,
	102691, 103017, 103343, 103669, 103995, 104321, 104647, 104973,
	105299, 105625];

    cbm2_coords := [27, 327, 627, 927, 1227, 1496, 1528, 1551, 1826, 2126,
	2426, 2726, 3026, 3326, 3590, 3627, 3656, 3890, 3931, 3963, 4224, 4524,
	4824, 5124, 5386, 5432, 5466, 5723, 6023, 6323, 6623, 6923, 7181, 7227,
	7269, 7522, 7780, 7827, 7891, 8121, 8421, 8721, 9021, 9321, 9621, 9921,
	10221, 10521, 10821, 11121, 11421, 11721, 12021, 12321, 12621, 12921,
	13221, 13521, 13821, 14121, 14421, 14721, 15021, 15321, 15621, 15921, 
	16221, 16452, 16574, 16585, 16820, 17120, 17420, 17720, 18020, 18320,
	18620, 18920, 19144, 19266, 19292, 19444, 19567, 19627, 19818, 20118,
	20418, 20718, 21018, 21318, 21618, 21918, 22218, 22435, 22568, 22599,
	22735, 22869, 22935, 23116, 23416, 23716, 24016, 24316, 24616, 24916,
	25216, 25516, 25726, 25873, 25889, 26026, 26174, 26190, 26245, 26265,
	26288, 26326, 26474, 26545, 26626, 26791, 26866, 27012, 27312, 27612,
	27912, 28212, 28512, 28812, 29112, 29412, 29712, 30012, 30312, 30612,
	30912, 31212, 31512, 31812, 32112, 32412, 32712, 33012, 33312, 33612,
	33912, 34102, 34281, 34298, 34318, 34338, 34361, 34402, 34582, 34599,
	34702, 34882, 34919, 35002, 35200, 35240, 35302, 35520, 35540, 35707,
	36007, 36307, 36607, 36907, 37207, 37507, 37807, 38107, 38407, 38707,
	39007, 39307, 39607, 39907, 40207, 40507, 40807, 41107, 41407, 41707,
	42007, 42307, 42607, 42907, 43207, 43507, 43807, 44107, 44407, 44707,
	45007, 45307, 45607, 45907, 46207, 46507, 46807, 47107, 47407, 47707,
	48007, 48307, 48607, 48907, 49207, 49356, 49523, 49619, 49806, 50106,
	50406, 50706, 51006, 51306, 51606, 51906, 52206, 52506, 52806, 53106,
	53406, 53706, 54006, 54306, 54606, 54906, 55206, 55506, 55806, 56106,
	56406, 56706, 57006, 57306, 57606, 57906, 58206, 58506, 58806, 59106,
	59406, 59706, 60006, 60306, 60606, 60719, 60923, 60983, 61019, 61243,
	61283, 61504, 61804, 62104, 62404, 62704, 63004, 63304, 63604, 63904,
	64204, 64504, 64804, 65104, 65404, 65704, 66004, 66304, 66604, 66904,
	67204, 67299, 67544, 67563, 67803, 68103, 68403, 68703, 69003, 69303,
	69603, 69903, 70203, 70503, 70803, 71103, 71403, 71703, 72003, 72303,
	72603, 72903, 73203, 73503, 73803, 73878, 74123, 74142, 74402, 74477,
	74723, 74742, 75001, 75301, 75601, 75901, 76201, 76501, 76801, 77101,
	77401, 77701, 78001, 78301, 78601, 78901, 79201, 79501, 79801, 80101,
	80401, 80701, 81001, 81301, 81601, 81901, 82201, 82501, 82801, 83101,
	83401, 83701, 84001, 84301, 84601, 84901, 85201, 85501, 85801, 86101,
	86401, 86701, 87001, 87301, 87601, 87901, 88201, 88501, 88801, 89101, 
	89401];

    cbm3_coords := [1, 28, 55, 82, 109, 140, 162, 189, 220, 242, 273, 295, 328,
	352, 379, 401, 434, 461, 488, 515, 537, 568, 595, 622, 649, 676];

    cbm1 := &+[HomE.i : i in cbm1_coords];
    cbm2 := &+[HomEE.i : i in cbm2_coords];
    cbm3 := &+[HomV.i : i in cbm3_coords];

    // Quotient with the natural module
    g_star := SubmatrixRange(cbm1^(-1) * ExteriorSquare(g) * cbm1,
	Degree(g) + 1, Degree(g) + 1, Dimension(E), Dimension(E));

    // Take image in the twisted submodule
    g_star := Submatrix(cbm2^(-1) * g_star * cbm2, 1, 1, Degree(g), Degree(g));

    // Change basis and twist
    return FrobeniusImage(cbm3^(-1) * g_star * cbm3, m);
end function;

intrinsic calculateBigReeTwistingMapCBMs(m :: RngIntElt) -> .
    { Calculate the necessary change of basis matrices for the twisting map.
    Print out as indices of positive coordinates in corresponding Hom-spaces. }

    G := LargeRee(m);
    F := CoefficientRing(G);

    M := GModule(G);
    EG := ExteriorSquare(M);
    H := ActionGroup(EG);
    E := GModule(H);

    // Obtain first change of basis
    N := rep{x : x in Submodules(E) | Dimension(x) eq 26};
    cbm1 := ChangeOfBasisMatrix(H, N);

    // Quotient out with the 26-dim module at the bottom
    ENG := quo<E | N>;
    gens := [cbm1 * ExteriorSquare(g) * cbm1^(-1) : g in UserGenerators(G)];
    assert [Submatrix(g, 1, 1, 26, 26) : g in gens] eq
	ActionGenerators(N);
    gensENG := [Submatrix(g, 27, 27, Dimension(ENG), Dimension(ENG)) :
	g in gens];
    assert gensENG eq ActionGenerators(ENG);

    // Obtain matrix as Hom-space indices, as a more efficient representation
    H1 := Hom(E, E);
    coords1 := Coordinates(H1, H1 ! cbm1^(-1));
    assert forall{i : i in [1 .. #coords1] | coords1[i] in {0, 1}};
    print [i : i in [1 .. #coords1] | coords1[i] eq 1];

    // Obtain second change of basis
    HN := ActionGroup(ENG);
    EN := GModule(HN);
    NN := rep{x : x in Submodules(EN) | Dimension(x) eq 26};
    cbm2 := ChangeOfBasisMatrix(HN, NN);
    gensNN := [Submatrix(cbm2 * g * cbm2^(-1), 1, 1, 26, 26) : g in gensENG];
    assert gensNN eq ActionGenerators(NN);
    
    // Obtain matrix as Hom-space indices, as a more efficient representation
    H2 := Hom(EN, EN);
    coords2 := Coordinates(H2, H2 ! cbm2^(-1));
    assert forall{i : i in [1 .. #coords2] | coords2[i] in {0, 1}};
    print [i : i in [1 .. #coords2] | coords2[i] eq 1];

    // Obtain final change of basis
    NN_star := FrobeniusImage(NN, G, m);
    flag, cbm3 := IsIsomorphic(NN_star, M);
    assert flag;

    // Various sanity checks
    assert ActionGenerators(NN_star^cbm3) eq ActionGenerators(M);
    G_star := ActionGroup(NN_star);
    assert UserGenerators(G_star) eq ActionGenerators(NN_star);
    conj3 := Generic(G) ! cbm3;
    assert ActionGenerators(M) eq UserGenerators(G);
    assert Generators(ActionGroup(NN_star^cbm3)) eq Generators(G);
    assert Generators(G) eq Generators(G_star^conj3);

    // Obtain matrix as Hom-space indices, as a more efficient representation
    H3 := Hom(M, M);
    coords3 := Coordinates(H3, H3 ! cbm3);
    assert forall{i : i in [1 .. #coords3] | coords3[i] in {0, 1}};
    print [i : i in [1 .. #coords3] | coords3[i] eq 1];        
end intrinsic;

intrinsic calculateAlbertAlgebra(m :: RngIntElt) -> .
    { Calculate and print Albert algebra multiplication table of standard
    Big Ree copy. }

    G := LargeRee(m);
    F := CoefficientRing(G);
    M := GModule(G);
    MM := TensorProduct(M, M);

    // Albert algebra is given by a generator of the following Hom-space
    A := GHom(MM, M);
    homo := A.1;
    assert Dimension(A) eq 1;
    V := VectorSpace(G);

    // Construct algebra multiplication table
    multTable := [];
    for i in [1 .. Dimension(V)] do
	
	tbl := [];
	for j in [1 .. Dimension(V)] do
	    Append(~tbl, Coordinates(V,
		V ! homo(MM ! TensorProduct(V.i, V.j))));
	end for;
	Append(~multTable, tbl);
    end for;

    // Print multiplication table
    AA := Algebra<F, Degree(G) | multTable>;
    for i in [1 .. Dimension(AA)] do
	for j in [1 .. Dimension(AA)] do
	    for l in [1 .. #multTable[i][j]] do
		if multTable[i][j][l] ne 0 then
		    printf "<%o,%o,%o,%o>\n", i, j,l, multTable[i][j][l];
		end if;
	    end for;
	end for;
    end for;
end intrinsic;

// Construct our standard Big Ree copy
// See "Elementary constructions of the Ree groups", Robert A. Wilson, preprint
// http://www.maths.qmul.ac.uk/~raw/
function LargeReeStandardCopy(F)
    local G, gens;
    
    if not LargeReeTrivialRecognitionChecks(F) then
	error "Field size must be an odd power of 2";
    end if;

    // Use Rob's generators
    gens := getLargeReeRobStandardGenerators(F);
    assert #gens eq 7;
        
    return sub<GL(26, F) | gens[2], gens[3] * gens[4] * gens[7]>;
end function;
