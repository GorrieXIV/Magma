/******************************************************************************
 *
 *    standard.m Standard copy code for Suzuki groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-03-24
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: standard.m 1605 2008-12-15 09:05:48Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiStandard, 10;

forward getSuzukiSylowGen, diagramAutomorphism, getSuzukiOrder,
    orderSuzukiEigenvalues;

import "conjugate.m" : conjugateToTriangular;
import "trick.m": getStabiliser;
import "suzuki.m" : checkSuzukiProperSubgroups;
import "../../../util/basics.m" : MatSLP, DiagonaliseMatrix;

// Status values from standard recogniton
STANDARD_SUZUKIGROUP  := 1;
STANDARD_WRONG_INPUT  := 2;
STANDARD_NOT_SUBGROUP := 3;
STANDARD_PROPER_SUB   := 4;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiStandardGeneratorsNaturalRep(m :: RngIntElt) -> []
    { Return Magma standard generators for Sz(2^(2 * m + 1)). }
    local field, q, t, S, T, M, omega, lambda, G, X, power;
    
    field := GF(2, 2 * m + 1);
    q := #field;
    t := 2^(m + 1);
    G := GL(4, field);
    
    omega := PrimitiveElement(field);
    assert MinimalPolynomial(omega) eq DefiningPolynomial(field);
    lambda := omega^(1 - 2^m);

    // Element of order 4
    S := getSuzukiSylowGen(field, 1, 0);

    // Diagonal element
    M := G ! DiagonalMatrix([lambda^(t + 1), lambda, lambda^(-1),
	lambda^(-t - 1)]);
    M1 := G ! DiagonalMatrix([omega^(t + 1), omega, omega^(-1),
	omega^(-t - 1)]);
    assert M eq M1^(1 - 2^m);
    
    // Diagonal element
    M2 := G ! DiagonalMatrix([omega^(2^m + 1), omega^(2^m), omega^(-2^m),
	omega^(-2^m - 1)]);
    //assert M2^(1-t) eq M;
    //assert M^(-2^m) eq M2;
    assert M1^(2^m) eq M2;
    
    // Anti-diagonal involution
    T := G ! PermutationMatrix(field, Reverse([1 .. 4]));
    
    power := q div 2;
    X1 := [T, M, S^(M1^power)];
    X2 := [T, M1, S];
    X3 := [S^(-1), M2, T];
        
    assert X1 eq UserGenerators(Sz(field));
    
    return X1, X2, X3;
end intrinsic;

intrinsic SuzukiStandardMembership(g :: GrpMatElt) -> BoolElt
    { g \in GL(4, q). Determine (non-constructively) if g \in Sz(q). }
    local symplecticMatrix;
    
    // Check that input is sensible
    if not (Degree(g) eq 4 and Category(F) eq FldFin and
	Characteristic(F) eq 2 and IsOdd(Degree(F)) and Degree(F) gt 1)
	where F is CoefficientRing(g) then
	return false;
    end if;

    // Check that g is in SL(4, q)
    if Determinant(g) ne 1 then
	return false;
    end if;

    symplecticMatrix := Generic(Parent(g)) !
	PermutationMatrix(CoefficientRing(g), Reverse([1 .. 4]));

    // Check that g is in the Symplectic Group, Sp(4, q)
    if g * symplecticMatrix * Transpose(g) ne symplecticMatrix then
	return false;
    end if;
    
    return g eq diagramAutomorphism(g);
end intrinsic;

intrinsic SuzukiFindOvoidPoints(G :: GrpMat : CheckInput := true,
    W := WordGroup(G), Randomiser :=
    RandomProcessWithWords(G : WordGroup := W)) -> ModTupFldElt, ModTupFldElt
    { G \leq GL(4, q) and G is a conjugate to Sz(q). Returns two random
    points in the ovoid corresponding to G. }
    local field, q, m, t, R, g, eigenvectors;

    if CheckInput then
	if not SuzukiConjugateRecogniser(G) then
	    error "G must be a conjugate of Sz(q)";
	end if;
    end if;
    
    field := CoefficientRing(G);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    
    flag, g := RandomElementOfOrder(G, q - 1 : Randomiser := Randomiser,
	MaxTries := q^2);
    assert flag;
    
    // Two of the eigenvectors are points in the ovoid. If we order the
    // eigenvalues properly, they are the first and last eigenvectors.
    _, eigenvectors := SuzukiCyclicEigenvalues(g);
    return eigenvectors[1], eigenvectors[4];
end intrinsic;

intrinsic SuzukiStandardRecogniser(G :: GrpMat) -> BoolElt, RngIntElt
    { G \leq GL(4, q). Determine (non-constructively) if G = Sz(q).

    Also return status code of recognition. }
    local q, generators;
    
    // Check that input is sensible
    if not (Degree(G) eq 4 and Category(F) eq FldFin and
	Characteristic(F) eq 2 and IsOdd(Degree(F)) and Degree(F) gt 1)
	where F is CoefficientRing(G) then
	return false, STANDARD_WRONG_INPUT;
    end if;

    q := #CoefficientRing(G);
    generators := Generators(G);
    
    // Check that all generators are in Sz
    if not forall{gen : gen in generators | SuzukiStandardMembership(gen)} then
	return false, STANDARD_NOT_SUBGROUP;
    end if;

    // Check if G is inside a proper subgroup of Sz(q)
    if checkSuzukiProperSubgroups(G) then
	return true, STANDARD_SUZUKIGROUP;
    else
	return false, STANDARD_PROPER_SUB;
    end if;
end intrinsic;

intrinsic SuzukiCyclicEigenvalues(g :: GrpMatElt) -> [], []
    { g \in Sz(q) with order q - 1. Return eigenvalues and eigenvectors of g
    in correct order. }
    local eigenvalues, lambda, q, t, m, field, eigenvectors;
    
    field := CoefficientRing(g);
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    q := #field;

    assert IsDivisibleBy(q - 1, Order(g : Proof := false));

    diag, conj := DiagonaliseMatrix(g : OrderEigenvalues :=
	func<x | orderSuzukiEigenvalues(x, m)>);
    assert SuzukiStandardMembership(Generic(Parent(g)) ! diag);
    
    // Get eigenvalues in correct order
    eigenvalues := Diagonal(diag);
    eigenvectors := [Rep(Basis(Eigenspace(g, e))) : e in eigenvalues];

    return eigenvalues, eigenvectors;
end intrinsic;

intrinsic SuzukiNonSplit6Dim(F :: FldFin : CheckInput := true) -> GrpMat
    { F has order an odd power of 2, at least 8. Return standard copy of unique
    6-dimensional non-split representation of Sz(F). }
    local G, gens, m, q, r, t, h, z, x;
    
    if CheckInput then
	if not (Characteristic(F) eq 2 and IsOdd(Degree(F)) and #F gt 2) then
	    error "#F > 2 must be an odd power of 2";
	end if;
    end if;

    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    r := 2^m;
    w := PrimitiveElement(F);

    // Get 6-dim standard generators

    // Diagonal matrix
    h := DiagonalMatrix([1, w * w^r, w^r, w^(-r), w^(-1) * w^(-r), 1]);
    
    // Anti-diagonal involution
    z := DiagonalJoin(<Matrix(F, 1, 1, [1]),
	PermutationMatrix(F, Reverse([1 .. 4])),
	Matrix(F, 1, 1, [1])>);
    
    // Sylow subgroup generator
    x := LowerTriangularMatrix(F, [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1,
	0, 0, 1, 0, 0, 1]);

    G := sub<GL(6, F) | z, h, x>;
    G`Order := getSuzukiOrder(q);

    return G;
end intrinsic;

intrinsic SuzukiNonSplit6Dim(q :: RngIntElt : CheckInput := true) -> GrpMat
    { q > 2 is an odd power of 2. Return standard copy of unique 6-dimensional
    non-split representation of Sz(q) }
    local flag, p, k;

    if CheckInput then
	flag, p, k := IsPrimePower(q);
	if not (flag and p eq 2 and IsOdd(k) and k gt 1) then
	    error "q > 2 must be an odd power of 2";
	end if;
    end if;

    return SuzukiNonSplit6Dim(GF(q));
end intrinsic;

intrinsic isValidSuzukiOrder(q :: RngIntElt, o :: RngIntElt) -> BoolElt
    { Returns true if Sz(q) has an element of order o, false otherwise. }

    // See Shi Wujie, "A Characterization of Suzuki's simple group"
    // Proc. Amer. Math. Soc. 114 (3), 589-591, 1992
    orders := {1, 2, 4, (q - 1), (q - Sqrt(2 * q) + 1), (q + Sqrt(2 * q) + 1)};
	
    if exists{k : k in orders | IsDivisibleBy(k, o)} then
	return true;
    else
	return false;
    end if;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function orderSuzukiEigenvalues(eigs, m)
    t := 2^(m + 1);

    perm := [];
    eigenvalues := SequenceToSet(eigs);
    lambda := rep{e : e in eigenvalues |
	{e^(t + 1), e^(-1), e^(-t - 1), e} eq eigenvalues};

    orderDiag := [e^(t + 1), e, e^(-1), e^(-t - 1)] where e is lambda;
    perm := [Index(orderDiag, x) : x in eigs];
    assert SequenceToSet(perm) eq {1 .. 4};
    return perm;
end function;

function isOvoidPoint(P)

    V := Parent(P);
    F := CoefficientRing(V);
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    
    if IsZero(P[4]) then
	return P eq V ! [1, 0, 0, 0];
    else
	PP := P / P[4];
	return PP[1] eq PP[2] * PP[3] + PP[3]^(t + 2) + PP[2]^t;
    end if;
end function;

// Get S(a, b) in Huppert notation
function getSuzukiSylowGen(field, a, b)
    local m, t;
    
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    
    return GL(4, field) ! LowerTriangularMatrix([1, a, 1, b, a^t, 1,
	a^(t + 2) + a * b + b^t, b + a^(t + 1), a, 1]);
end function;

function getSuzukiOrder(q)
    // q is assumed to be an odd power of 2
    return q^2 * (q^2 + 1) * (q - 1);
end function;

// Compute the image of g \in Sp(4, q) under the diagram automorphism
// g is a fixed point if and only if g \in Sz(q)
// The idea behind this is due to Robert Wilson
function diagramAutomorphism(g)
    local gl, V, basis, VV, sym_tensors, exterior, proj1, proj2, basis_map,
	star_map, v, star_basis, V_star, complement, field;

    field := CoefficientRing(g);
    assert Degree(g) eq 4 and Category(field) eq FldFin and
	Characteristic(field) eq 2 and IsOdd(Degree(field));
    m := (Degree(field) - 1) div 2;
    gl := Generic(Parent(g));
    symplecticMatrix := gl ! PermutationMatrix(field, Reverse([1 .. 4]));

    // Standard vector space with symplectic basis
    V := VectorSpace(CoefficientRing(g), 4, symplecticMatrix);
    basis := Basis(V);
    VV := TensorProduct(V, V);

    // Exterior square is quotient by the symmetric tensors
    sym_tensors := sub<VV | {TensorProduct(u, v) + TensorProduct(v, u) :
	u in basis, v in basis} join {TensorProduct(u, u) : u in basis}>;
    exterior, proj1 := quo<VV | sym_tensors>;
    assert Dimension(exterior) eq 6;
    
    // indices for e1, e2, f1, f2 of the symplectic basis
    basis_map := [1, 2, 4, 3];

    // Maps of basis vectors
    star_map := [];
    star_map[basis_map[1]] := [basis[basis_map[1]], basis[basis_map[2]]];
    star_map[basis_map[2]] := [basis[basis_map[1]], basis[basis_map[4]]];
    star_map[basis_map[3]] := [basis[basis_map[3]], basis[basis_map[4]]];
    star_map[basis_map[4]] := [basis[basis_map[2]], basis[basis_map[3]]];

    // v is fixed by Sp
    v := proj1(TensorProduct(basis[basis_map[1]], basis[basis_map[3]]) +
	TensorProduct(basis[basis_map[2]], basis[basis_map[4]]));
    assert v in exterior;
    assert proj1(TensorProduct(basis[basis_map[1]] * g,
	basis[basis_map[3]] * g) + TensorProduct(basis[basis_map[2]] * g,
	basis[basis_map[4]] * g)) eq v;

    // Create images of basis vectors of 4-dim space
    star_basis := [proj1(TensorProduct(e[1], e[2])) : e in star_map];
    
    // The other 4-dimensional space is quotient by v
    complement := sub<exterior | Append(star_basis, v)>;
    V_star, proj2 := complement / sub<complement | v>;
    assert Dimension(V_star) eq 4;
    
    // The diagram automorphism consists of a change of basis and then a twist
    h := gl ! &cat[ElementToSequence(proj2(u * ExteriorSquare(g)))
	: u in star_basis];
    
    return FrobeniusImage(h, m);
end function;
