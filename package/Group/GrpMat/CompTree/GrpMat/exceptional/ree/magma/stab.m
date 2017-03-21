/******************************************************************************
 *
 *    stab.m    Ree group package point stabiliser code
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-05-22
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: stab.m 1605 2008-12-15 09:05:48Z jbaa004                       $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeTrick, 10;

import "standard.m": getReeDiagonalElt, getReeDiagonalBase;
import "involution.m": isCentraliserComplete;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/basics.m" : MatSLP;

forward getMappingElement, getSL3Element, getZeroMapping,
    checkPointOrbit, getSL2TriangularMapping;

// Flags from getMappingElement
MAPPING_OK      := 0;
MAPPING_NEW_DST := 1;
MAPPING_NEW_INV := 2;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeStabiliser(G :: GrpMat, P :: ModTupFldElt :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> []
    { Find stabiliser in G = Ree(q) of P (1-dim space)}
    local involution, word, mapping, slp, Q, total_log_time, log_time,
	total_slp_time, slp_time;

    if CheckInput then
	if not ReeStandardRecogniser(G) then
	    error "Ree stabiliser: G is not the Ree group";
	end if;
    end if;
    
    field := CoefficientRing(G);
    q := #field;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    vprint ReeTrick, 3: "Get involution centraliser";
    
    // Find initial involution centraliser
    stabiliser := {};
    element, slp := RandomInvolution(G : Randomiser := Randomiser,
	MaxTries := q);
    H := ReeInvolutionCentraliser(G, element, slp :
	Randomiser := Randomiser, CheckInput := false);

    // Repeat until stabiliser contains an element of order 9 and an element
    // of order q-1
    total_log_time := 0;
    total_slp_time := 0;
    total_sl2_time := H`ReeInvolCentraliserData`sl2Time;
    repeat
	// Take another random point
	g, word := Random(G`RandomProcess);
	Q := P * g;
	
	if Q eq P then
	    Include(~stabiliser, <g, word>);
	else
	    vprint ReeTrick, 4: "Get mapping element";
	    
	    // Find mapping element between our points
	    flag, element, slp, log_time, slp_time, sl2_time :=
		getMappingElement(H, P, Q);
	    total_slp_time +:= slp_time;
	    total_sl2_time +:= sl2_time;
	    total_log_time +:= log_time;
	    
	    if flag eq MAPPING_OK then
		// Construct stabilising element 
		element := g * element^(-1);
		slp := (H`ReeInvolCentraliserData`slpGroup ! word) * slp^(-1);

		vprint ReeTrick, 4: "Mapping element found, get commutators";
		
		// Add element to stabiliser, and compute commutators to get
		// element of order 9
		Include(~stabiliser, <element, slp>);
		elements := {<(element, e[1]), (slp, e[2])> :
		    e in stabiliser};
		stabiliser join:= elements;
		
	    elif flag eq MAPPING_NEW_INV then
		vprint ReeTrick, 4: "Get involution centraliser conjugate";
		
		// The involution centraliser was badly chosen
		// Possibly just take a random conjugate
		element, slp := Random(G`RandomProcess);
		HH := sub<Generic(G) | [x^element : x in UserGenerators(H)]>;

		slpMap := [x^slp : x in H`ReeInvolCentraliserData`genSLPs];
		repeat
		    flag := isCentraliserComplete(HH, G,
			H`ReeInvolCentraliserData`involution^element, slpMap);
		until flag;
		
		HH`ReeInvolCentraliserData`genSLPs := slpMap;
		HH`ReeInvolCentraliserData`involution :=
		    H`ReeInvolCentraliserData`involution^element;
		H := HH;

		total_sl2_time +:= H`ReeInvolCentraliserData`sl2Time;
	    else
		// Q was badly chosen, just take another random point
		continue;
	    end if;
	end if;
    until exists(g){x : x in stabiliser | Order(x[1] : Proof := false) eq 9}
	and exists(h){x : x in stabiliser |
	Order(x[1] : Proof := false) eq q - 1};
    
    assert Normalise(P * g[1]) eq Normalise(P) and
	Normalise(P * h[1]) eq Normalise(P);
    assert Evaluate([g[2], h[2]], UserGenerators(G)) eq [g[1], h[1]];
    
    vprint ReeTrick, 3: "Stabiliser found";
    
    // The stabiliser is generated by an element of order 9 and an element of
    // order q - 1
    return [rec<MatSLP | mat := g[1], slp := g[2]>,
	rec<MatSLP | mat := h[1], slp := h[2]>],
	total_log_time, total_slp_time, total_sl2_time;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Construct symmetric square of given 2x2 matrix
function getSL3Element(sl3, sl2elt)
    local element, sl2Element, MA;
    
    sl2Element := sl2elt;
    assert IsOne(Determinant(sl2Element));
    
    MA := MatrixAlgebra(CoefficientRing(sl2Element), Degree(sl2Element));
    return Generic(sl3) ! SymmetricSquare(MA ! (sl2Element))
	where cb is sl3`SL2Basis[3];
end function;

// Construct upper triangular 3-dim SL2 element that maps src to dst
function getSL2TriangularMapping(sl3, src, dst)
    local a, b, c, d, P, roots, eqn, elts, C, mapping;

    field := CoefficientRing(sl3);
    P<alpha> := PolynomialAlgebra(field);

    vprint ReeTrick, 8: "Construct polynomial equation";
    
    eqn := (x[1]^2*alpha^4*y[2]^2-3*x[1]*alpha^2*y[2]*y[1]*x[2]+
	2*y[1]^2*x[2]^2+x[3]*x[1]*y[1]^2)*y[1]*y[2]-
	y[3]*x[1]^2*alpha^4*y[2]*y[1]^2
	where x is src where y is dst;

    if IsZero(eqn) then
	vprint ReeTrick, 8: "Zero polynomial";
	return false, _;
    end if;
    
    vprint ReeTrick, 8: "Find roots";
    roots := {@ s[1] : s in Roots(eqn) | not IsZero(s[1]) @};
    if IsEmpty(roots) then
	vprint ReeTrick, 8: "No roots";
	return false, _;
    end if;

    assert #roots eq 2;
    elts := {@ @};
    for a in roots do
	c := -(x[1]*a^2*y[2]-y[1]*x[2]) * (y[1] * x[1] * a)^(-1)
	    where x is src where y is dst;

	C := -(x[1]*a*c-x[2]) * y[2]^(-1)
	    where x is src where y is dst;

	// Construct 2-dim SL2 element
	d := a^(-1);
	b := 0;
	h := elt<GL(2, field) | a, c, b, d>;
	Include(~elts, h);
	assert IsOne(Determinant(h));

	// Get corresponding 3-dim element
	mapping := getSL3Element(sl3, h);
	assert IsOne(Determinant(mapping));
    end for;
    
    vprint ReeTrick, 8: "Found triangular mappings";
    return true, elts;
end function;

// Check if 3-dim point in the symmetric square lies in the orbit of xy, ie
// in the orbit of (0 : 1 : 0)
function checkPointOrbit(point)
    local P, form, field, cbm, coeffs;

    field := CoefficientRing(point);
    P<x, y> := PolynomialAlgebra(field, 2);

    // Create quadratic form from point and see if it is non-zero
    form := x^2 * point[1] + y^2 * point[3] + x * y * point[2];
    if TotalDegree(form) lt 2 then
	return false, _, _;
    end if;

    // The form is in the correct orbit if it represents zero, ie has a
    // non-zero root, which is easy to check when we have diagonalised the form
    form, cbm := DiagonalForm(form);
    coeffs := Coefficients(form);
    if #coeffs eq 2 and IsSquare(-coeffs[1] * coeffs[2]^(-1)) then
	return true, coeffs, cbm;
    else
	return false, _, _;
    end if;
end function;

// Construct a 3x3 element (not necessarily in the given 3-dim copy of SL2)
// that takes point to (0 : 1 : 0) 
function getZeroMapping(sl3, point)
    local diagForm, diagCBM, diagPoint, gamma, cbm, field;

    field := CoefficientRing(point);

    // See if we have the correct point already
    if Normalise(point) eq Vector(field, [0, 1, 0]) then
	return Identity(GL(2, field));
    end if;

    // Get change of basis to diagonalised form
    flag, diagPoint, diagCBM := checkPointOrbit(point);
    assert flag;
    
    // Change of basis to [0, 1, 0] from diagonalised form
    gamma := Sqrt(-diagPoint[1] * diagPoint[2]^(-1));
    cbm := elt<GL(2, field) | gamma, 1, gamma, -1>^(-1);

    // Complete change of basis
    return (GL(2, field) ! Transpose(diagCBM)) * cbm;
end function;

// Get a diagonal 7x7 matrix in the Ree group that maps src to dst
function getDiagonalMapping(src, dst)
    local C, field, alpha, m, t, diag, flag;

    field := CoefficientRing(src);
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    
    assert Degree(src) eq Degree(dst) and Degree(src) eq 7;

    
    // Mapping is not possible if points are bad
    //if (IsZero(src[4]) or IsZero(dst[4])) then
	//return false, _, _, _;
    //end if;
    if not forall{i : i in [1 .. 7] | (IsZero(src[i]) and IsZero(dst[i])) or
	(not IsZero(src[i]) and not IsZero(dst[i]))} then
	return false, _, _, _;
    end if;

    // The 4th diagonal element is always 1 in the Ree group, which enables us
    // to determine the projective constant
    C := src[4] * dst[4]^(-1);

    // Determine the necessary diagonal elements
    values := [];
    for i in [1 .. 3] do
	Append(~values, IsZero(src[i]) select field ! 0
	    else C * dst[i] * src[i]^(-1));
    end for;

    // Determine the other diagonal elements
    flag, alphas := getReeDiagonalBase(t, values);
    if flag then
	diags := [getReeDiagonalElt(field, alphas[1]),
	    getReeDiagonalElt(field, alphas[2])];
	return true, diags[1], C, diags[2];
    end if;

    return false, _, _, _;   
end function;

// Get a 7x7 matrix whose projection in sl3 that takes src to dst
// This does not necessarily take the corresponding 7-dim points to each other
function getIntermediateMapping(sl3, src, dst, cb, slpHomo)
    local flag, elts, slp, g, point, h, evalTime, sl2Time;

    vprint ReeTrick, 8: "Get triangular 2-dim mapping matrix";

    // Get element in natural representation whose symmetric square is the
    // mapping element that we want
    flag, elts := getSL2TriangularMapping(sl3, src, dst);
    if not flag then
	return false, _, _, _, _;
    end if;
    
    vprint ReeTrick, 8: "Get SLP of corresponding 3-dim element";

    // Get corresponding 3x3 matrix and write it as a word
    h := getSL3Element(sl3, Rep(elts));
    sl2Time := Cputime();
    flag, slp := SL2ElementToWord(sl3, h^(cb^(-1)));
    sl2Time := Cputime(sl2Time);
    assert flag;
    
    vprint ReeTrick, 8: "Evaluate SLP to 7-dim element";
    vprint ReeTrick, 8: "SLP Length", #slp;
    
    // Get 7x7 matrix
    evalTime := Cputime();
    g := slpHomo(slp);
    evalTime := Cputime(evalTime);
    
    return true, g, slp, evalTime, sl2Time;
end function;

// Get 7x7 elements whose projections to 3-dim SL2 stabilises point
function getPointStabiliser(sl3, point, cb, slpHomo)
    local cbm, field, stab, flag, slp, fldElt, residue, evalTime, sl2Time;
    
    vprint ReeTrick, 8: "Get CBM to [0, 1, 0]";

    // Change of basis from [0, 1, 0] to point
    cbm := getZeroMapping(sl3, point)^(-1);
    field := CoefficientRing(sl3);
    
    vprint ReeTrick, 8: "Get stabilising element of [0, 1, 0]";

    // Get representative elements of stabiliser of [0, 1, 0]
    fldElt := PrimitiveElement(field);
    stab := (GL(2, field) ! DiagonalMatrix([fldElt, fldElt^(-1)]));

    vprint ReeTrick, 8: "Get SLP of 3-dim element";
    
    // Write stabilising elements of point as words in sl3
    sl2Time := Cputime();
    flag, slp := SL2ElementToWord(sl3, getSL3Element(sl3, stab^cbm)^cb);
    sl2Time := Cputime(sl2Time);
    assert flag;
    
    // Get corresponding 7x7 elements
    vprint ReeTrick, 8: "Evaluate SLP to 7-dim element";
    vprint ReeTrick, 8: "SLP Length", #slp;
    evalTime := Cputime();
    residue := slpHomo(slp);
    evalTime := Cputime(evalTime);
    
    return rec<MatSLP | mat := residue, slp := slp>, evalTime, sl2Time;
end function;

// G is an involution centraliser in the Ree group
// Find element that maps source to dest
function getMappingElement(G, source, dest)
    local P, field, poly, src, dst, proj, q, cb, sl3, slpHomo,
	logTime, slpTime, totalSLPTime, sl2Time, totalSL2Time;

    assert assigned G`ReeInvolCentraliserData;
    field := CoefficientRing(G);
    q := #field;
    sl3 := G`ReeInvolCentraliserData`SmallSL2;

    // Change of basis that makes sl3 a visible symmetric square of the
    // natural representation
    cb := sl3`SL2Basis[4]^(-1) * G`ReeInvolCentraliserData`conj;

    // Evaluates SLPs in sl3 on generators of 7x7 SL2
    slpHomo := G`ReeInvolCentraliserData`SLPEval;
    proj := G`ReeInvolCentraliserData`PointProj;

    // Map points to 3-dim
    vprint ReeTrick, 8: "Getting points and forms in symmetric square";
    src := proj(source) * cb;
    dst := proj(dest) * cb;
    
    // Both points must be in the correct orbit
    if not checkPointOrbit(src) then
	vprint ReeTrick, 8: "Source point in wrong orbit";
	return MAPPING_NEW_INV, Identity(G), Identity(Domain(slpHomo)),
	    0, 0, 0;
    end if;
    if not checkPointOrbit(dst) then
	vprint ReeTrick, 8: "Destination point in wrong orbit";
	return MAPPING_NEW_DST, Identity(G), Identity(Domain(slpHomo)),
	    0, 0, 0;
    end if;
    
    vprint ReeTrick, 8: "Getting intermediate mapping";

    totalSLPTime := 0;
    totalSL2Time := 0;
    
    // Find element that maps 3-dim points to each other
    // both src and dst in orbit of [0, 1, 0]
    flag, g, slp, slpTime, sl2Time :=
	getIntermediateMapping(sl3, src, dst, cb, slpHomo);
    
    if not flag then
	vprint ReeTrick, 8: "No intermediate mapping";
	return MAPPING_NEW_INV, Identity(G),
	    Identity(Domain(slpHomo)), 0, totalSLPTime, totalSL2Time;
    end if;

    totalSLPTime +:= slpTime;
    totalSL2Time +:= sl2Time;

    // Map back to 7-dim to get intermediate point
    point := proj(source * g) * cb;
    
    assert G`ReeInvolCentraliserData`involution^g
	eq G`ReeInvolCentraliserData`involution;
    assert checkPointOrbit(point);
    assert Normalise(point) eq Normalise(dst);

    // Get stabiliser of 3-dim destination point
    // map element to 7-dim to get something that can make our intermediate
    // point to the destination
    vprint ReeTrick, 8: "Getting stabilising element of intermediate point";   
    residue, slpTime, sl2Time :=
	getPointStabiliser(sl3, point, cb^(-1), slpHomo);
    totalSLPTime +:= slpTime;
    totalSL2Time +:= sl2Time;

    order := Order(residue`mat : Proof := false);
    assert IsDivisibleBy(q - 1, order);
	
    vprint ReeTrick, 4: "Residue with order", order;
    assert order eq (q - 1) div 2;
    
    // Add centralised involution to get order q - 1
    mapper := residue`mat * G`ReeInvolCentraliserData`involution;
    mapslp := G`ReeInvolCentraliserData`SLPCoercion(residue`slp) *
	G`ReeInvolCentraliserData`slpGroup !
	G`ReeInvolCentraliserData`genSLPs[1];
    assert Order(mapper : Proof := false) eq q - 1;

    // Diagonalise element and change points accordingly
    diag, conj := ReeDiagonalisation(mapper);
    x := source * (g * conj^(-1));
    y := dest * conj^(-1);

    // Some power of our element maps to the two points to each other
    assert IsOne(diag[4, 4]);
    flag, diagMap, C := getDiagonalMapping(x, y);
    assert flag and x * diagMap eq C * y;

    // Find power using discrete log
    vprint ReeTrick, 8: "Found mapping! Calling discrete log";
    logTime := Cputime();
    j := Log(diag[1, 1], diagMap[1, 1]);
    logTime := Cputime(logTime);

    assert source * (g * mapper^j) eq C * dest;
    assert Normalise(source * (g * mapper^j)) eq Normalise(dest);
    
    vprint ReeTrick, 8: "Discrete log done";
    
    return MAPPING_OK, g * mapper^j,
	G`ReeInvolCentraliserData`SLPCoercion(slp) * mapslp^j,
	logTime, totalSLPTime, totalSL2Time;
end function;
