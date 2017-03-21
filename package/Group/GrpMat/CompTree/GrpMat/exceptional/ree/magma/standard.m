/******************************************************************************
 *
 *    standard.m Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-05-08
 *
 *    Version   : $Revision:: 2447                                           $:
 *    Date      : $Date:: 2013-12-30 06:29:40 +1100 (Mon, 30 Dec 2013)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: standard.m 2447 2013-12-29 19:29:40Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

forward exceptionalOuterAutomorphism, OrderReeDiagonal,
    OrderReeDiagonal2, isOrbitPoint,
    getOrbitPoint, getReeMagmaCBM, getReeDiagonalElt, getReeDiagonal,
    getReeInfSylowGen, getReeMagmaForm, checkG2membership, getReeOrder,
    checkG2Algebra, checkOctonionAlgebra, checkTwistedMiddleAlgebra,
    findHardMaximals, standardGeneratorsNaturalRep, getReeInfSylowGenMatrix,
    solveEquations, getRobReeCopy;

import "ree.m": ReeTrivialRecognitionChecks;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/basics.m" : MatSLP, DiagonaliseMatrix;

declare verbose ReeStandard, 10;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*
intrinsic testReeRob(m :: RngIntElt) -> BoolElt
    { }

    F := GF(3, 2 * m + 1);
    B := getRobReeCopy(F);
    print B;
    iso, x := ReeConjugacy(B);
    print x;
    return true;
end intrinsic;
*/

intrinsic testReeMap(m :: RngIntElt) -> BoolElt
    { }

    F := GF(3, 2 * m + 1);
    q := #F;
    G := Ree(F);
    flag := RecogniseRee(G);

    W := WordGroup(G);
    //H := G`ReeReductionData`stdCopy;
    j, w := RandomInvolution(G);
    j := G.2^13;
    w := W.2^13;
    C := ReeInvolutionCentraliser(G, j, w);

    V := VectorSpace(F, 3);
    im := {};
    
    for a in F do
	for b in F do
	    for c in F do
		P := getOrbitPoint(F, a, b, c : Infinity := false);
		
		PV := sub<V | C`ReeInvolCentraliserData`PointProj(P)>;
		//print PV, PV.1;
		if Dimension(PV) gt 0 then
		    Include(~im, PV);
		end if;
	    end for;
	end for;
    end for;

    /*
    P := getOrbitPoint(F, 0, 0, 0 : Infinity := true);
    PV := sub<V | C`ReeInvolCentraliserData`PointProj(P)>;
    assert Dimension(PV) gt 0;
    Include(~im, PV);
    */
    
    assert #im eq q^2;

    //print {x.1 : x in im};
    print #{x.1 : x in im | (x.1)[1] eq 1 and (x.1)[2]^2 ne (x.1)[3] and IsSquare((x.1)[2]^2 - (x.1)[3])}, q * (q + 1) div 2, q^2 - q, (q^2 - q) div 2;
    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeStandardMembership(g :: GrpMatElt) -> BoolElt
    { g \in GL(7, q). Determine (non-constructively) if g \in Ree(q). }
    local field, form, m;

    field := CoefficientRing(g);
    m := (Degree(field) - 1) div 2;
    
    // Check that input is sensible
    if not (Degree(g) eq 7 and ReeTrivialRecognitionChecks(field) and
	IsOne(Determinant(g))) then
	return false;
    end if;
    
    form := getReeMagmaForm(field);
    
    // Check membership in standard SO(7, q)
    if g * form * Transpose(g) ne form then
	return false;
    end if;
    
    // Check membership in standard G_2(q)
    if not checkOctonionAlgebra(g) then
	return false;
    end if;
        
    // Check membership in Ree(q)
    if exceptionalOuterAutomorphism(g) ne g then
	return false;
    else
	return true;
    end if;
end intrinsic;

intrinsic ReeStandardRecogniser(G :: GrpMat) -> BoolElt
    { G \leq GL(7, q). Determine (non-constructively) if G = Ree(q). }
    local field;

    field := CoefficientRing(G);
    if not ReeTrivialRecognitionChecks(field) or Degree(G) ne 7 then
	return false;
    end if;

    if not forall{g : g in Generators(G) | ReeStandardMembership(g)} then
	return false;
    end if;

    // Dispose of proper subgroups. They are either Ree groups over subfields
    // or reducible
    if not IsAbsolutelyIrreducible(G) or IsOverSmallerField(G) then
	return false;
    end if;

    return true;
end intrinsic;

intrinsic ReeFindOrbitPoint(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G))
    -> ModTupFldElt, ModTupFldElt
    { G \leq GL(7, q) and G is a conjugate to Ree(q). Returns two random
    points in the set on which G acts doubly transitively. }
    local element, field;

    if CheckInput then
	if not (Degree(G) eq 7 and ReeGeneralRecogniser(G)) then
	    error "G must be a conjugate of Ree(q)";
	end if;
    end if;
    
    field := CoefficientRing(G);
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // An element of order q - 1 has distinct eigenvalues
    flag, element := RandomElementOfOrder(G, #field - 1 :
	Randomiser := G`RandomProcess, MaxTries := #field^2);
    assert flag;
    
    return ReeFixedPoints(element : CheckInput := false);
end intrinsic;

intrinsic ReeDiagonalisation(g :: GrpMatElt) -> GrpMatElt, GrpMatElt
    { g in G, with G a conjugate of Ree(q), has order dividing q - 1.
    Diagonalise g in Ree(q). }
    local m, d, k, G;

    G := Generic(Parent(g));
    m := (Degree(CoefficientRing(g)) - 1) div 2;

    // Diagonalise and order eigenvalues properly
    d, k := DiagonaliseMatrix(g : OrderEigenvalues :=
	func<x | OrderReeDiagonal(x, m)>);
    assert ReeStandardMembership(G ! d);
    assert (G ! d)^(G ! k) eq g;
    
    return G ! d, G ! k;
end intrinsic;

intrinsic ReeFixedPoints(g :: GrpMatElt : CheckInput := true)
    -> ModTupFldElt, ModTupFldElt
    { g in G, with G a conjugate of Ree(q), has order dividing q - 1.
    Return the two points in the set on which G acts doubly transitively that
    are fixed by g. }
    local V, q, field, d, k, rows;
    
    field := CoefficientRing(g);
    q := #field;

    if CheckInput then
	if not (Degree(g) eq 7 and ReeGeneralRecogniser(Parent(g))) then
	    error "g must lie in a Ree conjugate";
	end if;

	if not IsDivisibleBy(q - 1, Order(g : Proof := false)) then
	    error "g must have order dividing q - 1";
	end if;
    end if;

    V := VectorSpace(field, Degree(g));
    d, k := ReeDiagonalisation(g);
    assert ReeStandardMembership(d);
    rows := RowSequence(k);
    assert #rows eq Degree(g);
    
    // The first and last eigenspaces are points
    return V ! rows[1], V ! rows[#rows];
end intrinsic;

intrinsic ReeStandardCopy(F :: FldFin) -> GrpMat
    { Return Ree(F) on its standard generators. }
    local ree, factors;
    
    if not ReeTrivialRecognitionChecks(F) then
	error "|F| must have size an odd power of 3";
    end if;
        
    // Set order properly
    ree := sub<GL(7, F) | standardGeneratorsNaturalRep(F)>;
    order := getReeOrder(#F);
    ree`Order := order;
    
    return ree;
end intrinsic;

intrinsic ReeStandardCopy(m :: RngIntElt) -> GrpMat
    { Return Ree(3^(2m + 1)) on its standard generators }
    return ReeStandardCopy(GF(3, 2 * m + 1));
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function standardGeneratorsNaturalRep(F)
    local tau, h, sylowGen;
    
    // 'Transpose' matrix
    tau := GL(7, F) ! -PermutationMatrix(F, Reverse([1 .. 7]));

    // Diagonal element
    h := getReeDiagonalElt(F, PrimitiveElement(F));

    // Upper triangular Sylow subgroup generator
    sylowGen := getReeInfSylowGen(F, 1, 0, 0);

    return [tau, h, sylowGen];
end function;

function getReeOrder(q)
    local factors, m, t;

    return q^3 * (q^3 + 1) * (q - 1);
end function;

// Given a sequence of values on a Ree diagonal, order them properly so that
// the diagonal is in the standard Ree copy
function OrderReeDiagonal(diagonal, m)
    local y, diag, t;

    t := 3^m;
    diag := SequenceToSet(diagonal);
    if not exists(y){z : x in diag | diag eq
	{ z^t, z^(1 - t), z^(2 * t - 1), 1, z^(1 - 2 * t), z^(t - 1),
    z^(-t) } where z is x^(3 * t)} then
	error "Not a Ree diagonal";
    end if;

    // Make sure that eigenvalues are in correct order
    orderDiag := getReeDiagonal(m, y);
    perm := [Index(orderDiag, x) : x in diagonal];
    assert SequenceToSet(perm) eq {1 .. 7};
    return perm;
end function;


// g should be in G_2. Check if it is a fixed point of the automorphism
// that defines 2G_2 = Ree
function exceptionalOuterAutomorphism(g)
    local cbm1, cbm2, cbm3, m, h, hh, field;

    field := CoefficientRing(g);
    m := (Degree(field) - 1) div 2;

    cbm1 := Matrix(field, [
	[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 1, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]]);
    
    cbm2 := Matrix(field, [
	[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
	[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
	[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0],
	[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
	[0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]]);

    cbm3 := Matrix(field, [
	[1, 0, 0, 0, 0, 0, 0],
	[0, 1, 0, 0, 0, 0, 0],
	[0, 0, 2, 0, 0, 0, 0],
	[0, 0, 0, 2, 0, 0, 0],
	[0, 0, 0, 0, 2, 0, 0],
	[0, 0, 0, 0, 0, 1, 0],
	[0, 0, 0, 0, 0, 0, 1]]);

    // Take quotient and subspaces of exterior square and finally a twist
    h := Submatrix(cbm1^(-1) * ExteriorSquare(g) * cbm1, 8, 8, 14, 14);
    hh := Submatrix(cbm2^(-1) * h * cbm2, 1, 1, 7, 7);
    return FrobeniusImage(cbm3^(-1) * hh * cbm3, m);
end function;

function getReeInfSylowGenMatrix(field, t, u, v)
    local m, theta;
    
    m := (Degree(field) - 1) div 2;
    theta := 3^m;
	
    return UpperTriangularMatrix([1,t^theta,-u^theta,(t*u)^theta-v^theta,
	-u-t^(3*theta+1)-(t*v)^theta,
	-v-(u*v)^theta-t^(3*theta+2)-t^theta*u^(2*theta),
	t^theta*v-u^(theta+1)+t^(4*theta+2)-v^(2*theta)-
	t^(3*theta+1)*u^theta-(t*u*v)^theta,
	1,t,u^theta+t^(theta+1),
	-t^(2*theta+1)-v^theta,-u^(2*theta)+t^(theta+1)*u^theta+t*v^theta,
	v+t*u-t^(2*theta+1)*u^theta-(u*v)^theta-t^(3*theta+2)-
	t^(theta+1)*v^theta,
	1,t^theta,-t^(2*theta),v^theta+(t*u)^theta,
	u+t^(3*theta+1)-(t*v)^theta-t^(2*theta)*u^theta,
	1,t^theta,u^theta,(t*u)^theta-v^theta,
	1,-t,u^theta+t^(theta+1),
	1,-t^theta,
	1]);
end function;

// Compute an element of the Sylow 3-subgroup that fixes infinity
// This matrix is upper triangular
function getReeInfSylowGen(field, t, u, v)
    return GL(7, field) ! getReeInfSylowGenMatrix(field, t, u, v);
end function;

// Compute an element of the Sylow 3-subgroup that fixes zero
// This matrix is lower triangular
function getReeZeroSylowGen(field, t, u, v)
    local MA, tau, element;

    // Get "transposing" matrix
    MA := MatrixAlgebra(field, 7);
    tau := GL(7, field) ! -&+[MatrixUnit(MA, i, 8 - i) : i in [1 .. 7]];
    
    return getReeInfSylowGen(field, t, u, v)^tau;
end function;

// Compute a diagonal element of Ree
function getReeDiagonalElt(field, y)
    local m;

    m := (Degree(field) - 1) div 2;
    return GL(7, field) ! DiagonalMatrix(getReeDiagonal(m, y));
end function;

// Get a Ree diagonal as a sequence
function getReeDiagonal(m, y)
    local t;
    
    t := 3^m;
    return [y^t, y^(1 - t), y^(2 * t - 1), 1,
	y^(1 - 2 * t), y^(t - 1), y^(-t)];
end function;

// Get the symmetric bilinear form preserved by the Magma copy of the Ree group
function getReeMagmaForm(field)
    local form;

    // The form preserved by the Magma copy
    form := elt<GL(7, field) |
	0, 0, 0, 0, 0, 0, 1,
	0, 0, 0, 0, 0, 2, 0,
	0, 0, 0, 0, 1, 0, 0,
	0, 0, 0, 1, 0, 0, 0,
	0, 0, 1, 0, 0, 0, 0,
	0, 2, 0, 0, 0, 0, 0,
	1, 0, 0, 0, 0, 0, 0>;

    // The form preserved by our copy
    form := elt<GL(7, field) |
	0, 0, 0, 0, 0, 0, 1,
	0, 0, 0, 0, 0, 1, 0,
	0, 0, 0, 0, 1, 0, 0,
	0, 0, 0, 2, 0, 0, 0,
	0, 0, 1, 0, 0, 0, 0,
	0, 1, 0, 0, 0, 0, 0,
	1, 0, 0, 0, 0, 0, 0>;

    return form;
end function;

// Check if point is in the standard Ree orbit
function isOrbitPoint(point)
    local pnt, V, field, m, t;
    
    field := CoefficientRing(point);
    m := (Degree(field) - 1) div 2;
    t := 3^m;

    // The point must be normalised to fit the pattern
    pnt := Normalise(point);

    // Check if we have the infinity point
    if pnt eq getOrbitPoint(field, 0, 0, 0 : Infinity := true) then
	return true;
    end if;
    if pnt[1] ne 1 then
	return false;
    end if;

    // The point is determined by 3 parameters
    alpha := pnt[2]^(3 * t);
    beta := (-pnt[3])^(3 * t);
    gamma := (-pnt[4] + (alpha * beta)^t)^(3 * t);

    if pnt eq getOrbitPoint(field, alpha, beta, gamma)  then
	return true;
    else
	return false;
    end if;
end function;

function orbitPoint(V, theta, t, u, v : Infinity := true)
    if Infinity then
	return elt<V | 0, 0, 0, 0, 0, 0, 1>;
    else
	return elt<V | 1, t^theta, -u^theta, (t * u)^theta - v^theta,
	    -u - t^(3 * theta + 1) - (t * v)^theta,
	    -v - (u * v)^theta - t^(3 * theta + 2) - t^theta * u^(2 * theta),
	    t^theta * v - u^(theta + 1) + t^(4 * theta + 2) - v^(2 * theta) -
	    t^(3 * theta + 1) * u^theta - (t * u * v)^theta>;
    end if;
end function;

// Get a point in standard Ree orbit
function getOrbitPoint(field, t, u, v : Infinity := false)
    local V, m, theta;
    
    V := VectorSpace(field, 7);
    m := (Degree(field) - 1) div 2;
    theta := 3^m;

    return orbitPoint(V, theta, t, u, v : Infinity := Infinity);
end function;

// Given the 3 first values of a Ree diagonal (some may be 0), try to
// determine the whole diagonal
function getReeDiagonalBase(t, values)
    local alpha;

    assert #values eq 3;
    if not IsZero(values[3]) then
	return true, [values[3]^(3 + 6 * t), values[3]^(3 + 6 * t)];
    elif not IsZero(values[2]) then
	alpha := values[2]^(3 * t + 3);
	flag, alpha := IsSquare(alpha);
	if flag then
	    return true, [alpha, -alpha];
	else
	    return false, _;
	end if;
    elif not IsZero(values[1]) then
	return true, [values[1]^(3 * t), values[1]^(3 * t)];
    end if;

    return false, _;
end function;

function getOctonions(F)

    // The octonion algebra multplication corresponding to our Ree group
    // This is the octonion algebra without the identity
    octonionMult := [
	<1, 4, 1, 1>, <1, 5, 2, -1>, <1, 6, 3, 1>, <1, 7, 4, 1>,
	<2, 3, 1, -1>, <2, 4, 2, -1>, <2, 6, 4, -1>, <2, 7, 5, 1>,
	<3, 2, 1, 1>, <3, 4, 3, -1>, <3, 5, 4, -1>, <3, 7, 6, -1>,
	<4, 1, 1, -1>, <4, 2, 2, 1>, <4, 3, 3, 1>, <4, 5, 5, -1>,
	<4, 6, 6, -1>, <4, 7, 7, 1>, 
	<5, 1, 2, 1>, <5, 3, 4, 1>, <5, 4, 5, 1>, <5, 6, 7, -1>,
	<6, 1, 3, -1>, <6, 2, 4, 1>, <6, 4, 6, 1>, <6, 5, 7, 1>,
	<7, 1, 4, -1>, <7, 2, 5, -1>, <7, 3, 6, 1>, <7, 4, 7, -1>];
    
    O := Algebra<F, 7 | octonionMult>;
    assert not IsAssociative(O);
    return O;
end function;

function checkOctonionAlgebra(g)
    F := CoefficientRing(g);

    assert Degree(g) eq 7;

    O := getOctonions(F);
    V := Module(O);
    o2v := hom<O -> V | [V.i : i in [1 .. Degree(O)]]>;
    v2o := hom<V -> O | [O.i : i in [1 .. Degree(O)]]>;

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

// Generators defined in MR2653247
// http://dx.doi.org/10.1017/S001309150800028X
function getReeRobStandardGenerators(F)

    m := (Degree(F) - 1) div 2;
    t := 3^(m + 1);

    V := VectorSpace(F, 7);
    H := Hom(V, V);
    U := GL(7, F);
    lambda := PrimitiveElement(F);
    torusGen := U ! DiagonalMatrix([lambda, lambda^(t - 1), lambda^(-t
	+ 2), 1, lambda^(t - 2), lambda^(-t + 1), lambda^(-1)]);

    torusNormaliser := U ! (H ! hom<V -> V | V.7, V.6, V.5, -V.4, V.3,
    V.2, V.1>);

    // Automorphisms s1, s2, s3 in Rob's paper
    borelAutos := [U | H ! hom<V -> V | [V.1, V.2, V.3, V.4 - V.1, V.5 + V.2,
    V.6 - V.3 - V.1, V.7 + V.4 + V.2 + V.1]>,
	H ! hom<V -> V | [V.1, V.2, V.3 - V.1, V.4 + V.2, V.5 + V.1,
    V.6 - V.4 + V.2, V.7 + V.5 - V.3 + V.1]>,
	H ! hom<V -> V | [V.1, V.2 - V.1, V.3 + V.2 - V.1, V.4 - V.3, 
	V.5 + V.4 + V.3 + V.1, V.6 - V.5 - V.4 - V.3 + V.1, 
        V.7 + V.6 - V.3 + V.2 - V.1]>];

    // Diagonal involution
    diagInvol := U ! DiagonalMatrix([-1, 1, -1, 1, -1, 1, -1]);

    assert torusNormaliser^diagInvol eq torusNormaliser;
    assert borelAutos[2]^diagInvol eq borelAutos[2];
    assert (borelAutos[3], borelAutos[2]) eq borelAutos[1];

    return [torusGen, torusNormaliser, diagInvol] cat borelAutos;
end function;

// Generators defined in MR2653666
// http://dx.doi.org/10.1007/s00013-010-0130-4
function getReeRobNewStandardGenerators(F)

    m := (Degree(F) - 1) div 2;
    t := 3^(m + 1);

    V := VectorSpace(F, 7);
    H := Hom(V, V);
    U := GL(7, F);
    lambda := PrimitiveElement(F);
    torusGen := U ! DiagonalMatrix([lambda^(-t - 2), lambda^(-t - 1), lambda^(-1), 1, lambda, lambda^(t + 1), lambda^(t + 2)]);

    torusNormaliser := U ! (H ! hom<V -> V | V.7, V.6, V.5, -V.4, V.3, V.2, V.1>);

    borelAutos := [
		   U ! LowerTriangularMatrix([1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 
					      0, -1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 
					      1, -1, 0, -1, 0, 0, 1]),
		   U ! LowerTriangularMatrix([1, 0, 1, -1, 0, 1, 0, 1, 0, 1, 
					      1, 0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 
					      1, 0, -1, 0, 1, 0, 1]),
		   U ! LowerTriangularMatrix([1, 1, 1, -1, -1, 1, 0, 0, 1, 1, 
					      1, 0, 1, -1, 1, -1, 0, 1, -1, 1, 
					      1, -1, -1, -1, 0, 0, -1, 1])];
    // Diagonal involution
    diagInvol := U ! DiagonalMatrix([-1, 1, -1, 1, -1, 1, -1]);

    assert torusNormaliser^diagInvol eq torusNormaliser;
    assert borelAutos[2]^diagInvol eq borelAutos[2];
    return [torusGen, torusNormaliser, diagInvol] cat borelAutos;
end function;

// Generators defined in Rob's book, "Finite simple groups"
function getReeRobBookStandardGenerators(F)

    m := (Degree(F) - 1) div 2;
    t := 3^(m + 1);

    V := VectorSpace(F, 7);
    H := Hom(V, V);
    U := GL(7, F);
    lambda := PrimitiveElement(F);
    torusGen := U ! DiagonalMatrix([lambda, lambda^(t - 1), lambda^(-t
	+ 2), 1, lambda^(t - 2), lambda^(-t + 1), lambda^(-1)]);

    torusNormaliser := U ! (H ! hom<V -> V | V.7, V.6, V.5, -V.4, V.3,
    V.2, V.1>);
    
    // basis change from i-basis to v-basis
    basisChange := hom<V -> V | [
	V.4 + V.6 + V.7, 
	V.2 + V.3 + V.5, 
	-V.1 - V.4 + V.7,
        V.3 - V.2,
        -V.1 + V.4 - V.7,
        -V.2 - V.3 + V.5,
	-V.4 + V.6 - V.7]>;
    
    borelAutos := [U ! LowerTriangularMatrix([1, 0, 1, 1, 0, 1, 0, 1, 0, 1, -2,
					      0, 0, 0, 1, 0, 1, 0, -1, 0, 1, 1,
					      0, 1, 0, -1, 0, 1]),
		   U ! LowerTriangularMatrix([1, -1, 1, 1, -1, 1, 0, 0, 1, 1, 
					      -1, 0, 1, -1, 1, 1, 0, 1, -1, 1, 
					      1, -1, 1, 1, 0, 0, 1, 1])];
    // Diagonal involution
    diagInvol := U ! DiagonalMatrix([-1, 1, -1, 1, -1, 1, -1]);

    assert torusNormaliser^diagInvol eq torusNormaliser;
    assert borelAutos[1]^diagInvol eq borelAutos[1];

    return [torusGen, torusNormaliser, diagInvol] cat borelAutos, U ! (H ! basisChange);
end function;

function getRobReeCopy(F)
    U := GL(7, F);
    /*    
    gens := getReeRobNewStandardGenerators(F);
    G := sub<U | gens[1], gens[2], gens[6]>;
    print G;
    H := sub<U | gens[2], gens[3]>;
    N := Normaliser(G, H);
    print N;
    //T := CompositionTree(G);
    //DisplayCompTreeNodes(H);
    return G;
    */
/*
    flag, form := SymmetricBilinearForm(G);
    assert flag;
    print form;

    gens := getReeRobStandardGenerators(F);
    G := sub<U | gens[1], gens[2], gens[6]>;
    print G;
    */
    //flag, form := SymmetricBilinearForm(G);
    //assert flag;
    //print form;
    
    gens, x := getReeRobBookStandardGenerators(F);

    G := sub<U | gens[1], gens[2], gens[5]>;
    //print G;
    //flag, form := SymmetricBilinearForm(G);
    //assert flag;
    //print form;
    //H1 := G^x;
    //flag, form := SymmetricBilinearForm(H1);
    //assert flag;
    //print form;

    return G;
end function;

