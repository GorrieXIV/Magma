/******************************************************************************
 *
 *    trick.m   Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-06-26
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: trick.m 1605 2008-12-15 09:05:48Z jbaa004                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose LargeReeTrick, 10;

import "standard.m": getLargeReeDiagonalElt,
    getLargeReeDiagonalAlt, getLargeReeRobStandardGenerators;
import "../../../util/basics.m" : MatSLP;

forward getInterpolationValues, solveEquations, interpolate, EvenOrderTrick;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeSzInvolution(G :: GrpMat : CheckInput := true,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    wordGroup := WordGroup(G))
    -> GrpMatElt, GrpSLPElt
    { Find involution in G = 2F_4(q) (or a conjugate) of Sz type}
    local invol, g, slp, foundInvol, l, r, elements;
    
    if CheckInput then
	if not (LargeReeGeneralRecogniser(G) and Degree(G) eq 26) then
	    error "G is not a Large Ree group in natural representation";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    // If we have already found a parabolic, we have an involution
    if assigned G`LargeReeSzParabolicData then
	assert assigned G`RandomProcess;

	// Take a random conjugate of the involution
	g, w := Random(G`RandomProcess);
	return G`LargeReeSzParabolicData`group.1^g,
	    G`LargeReeSzParabolicData`slps[1]^w;
    end if;
	
    // If we already have recognised this group, use the isomorphism
    if assigned G`LargeReeReductionData and
	assigned G`LargeReeReductionData`stdCopy then
	assert assigned G`RandomProcess;
    
	// Work in standard copy
	S := G`LargeReeReductionData`stdCopy;

	gens := getLargeReeRobStandardGenerators(CoefficientRing(S));
	invol := Function(G`LargeReeReductionData`inv)(gens[5]);
	flag, slp := LargeReeStandardConstructiveMembership(S, gens[5] :
	    Randomiser := S`RandomProcess, wordGroup := WordGroup(G),
	    CheckInput := false);
	assert flag;
	
	return invol, slp;
    end if;
	
    foundInvol := false;
    repeat
	// Find a batch of elements of even order
	elements := EvenOrderElement(G : Randomiser := G`RandomProcess,
	    CheckInput := false,
	    Element := rec<MatSLP | mat := Identity(G),
	    slp := Identity(wordGroup)>);

	for element in elements do
	    g := element[1];
	    slp := element[2];
	    l, r := Quotrem(Order(g : Proof := false), 2);
	    assert r eq 0;

	    // Obtain involution
	    g ^:= l;
	    slp ^:= l;

	    // Check involution class
	    if LargeReeInvolutionClass(g) eq "2A" then
		invol := g;
		foundInvol := true;
		break;
	    end if;
	end for;
    until foundInvol;

    return invol, slp;
end intrinsic;

intrinsic EvenOrderElement(G :: GrpMat : CheckInput := true, Element :=
    rec<MatSLP | mat := Identity(G), slp := Identity(WordGroup(G))>,
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    MaxTries := 1000)
    -> {}, RngIntElt, RngIntElt
    { Find element of even order in G = 2F_4(q) }
	local order, diagonaliser, total_time, g, slp, field, q, m, t,
	d, conj;
    
    if CheckInput then
	if not LargeReeGeneralRecogniser(G) then
	    error "G is not a Big Ree group";
	end if;
    end if;

    field := CoefficientRing(G);
    q := #field;
    m := (Degree(CoefficientRing(G)) - 1) div 2;
    t := 2^(m + 1);
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    if Characteristic(field) gt 2 or IsEven(Degree(field)) or
	Degree(G) gt 26 then

	vprint LargeReeTrick, 1 :
	    "Find Big Ree Sz even order element by random search";

	// Use random search to find even order element
	total_time := Cputime();
	repeat
	    g, slp := Random(G`RandomProcess);
	    s, r := Quotrem(Order(g * Element`mat : Proof := false), 2);
	until r eq 0;
	
	return {<g, slp>}, Cputime(total_time), 0;
    end if;
    
    vprint LargeReeTrick, 1 : "Use trick to find even order element";

    order := (q + t + 1);
    diagonaliser := func<lambda, mu |
	DiagonalMatrix(getLargeReeDiagonalAlt(lambda, mu))>;
    
    vprint LargeReeTrick, 2 : "Find special torus element";

    // Get random cyclic group in correct conjugacy class
    flag, g, slp := RandomElementOfOrder(G, (q - 1) * order :
	Randomiser := G`RandomProcess);
    assert flag;
    
    g ^:= order;
    slp ^:= order;
    
    vprint LargeReeTrick, 2 : "Diagonalise special torus element";

    // Diagonalise and order eigenvalues properly
    d, conj := LargeReeDiagonalisation(g);
    assert d^conj eq g;
    
    vprint LargeReeTrick, 2 : "Execute trick";

    // Find k and b s.t. g^k * b * Element`mat has even order
    return EvenOrderTrick(G, g, d, conj, slp, Element, diagonaliser, MaxTries);
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function initialiseTrick(G, g, slp, diagonaliser)
    local field, P, R, base, terms;
    
    field := CoefficientRing(G);
    
    // Create diagonal matrix with indeterminates
    P<lambda, mu> := PolynomialAlgebra(field, 2);
    R := FieldOfFractions(P);

    // Base of cyclic group
    base := rec<MatSLP | mat := g, slp := slp>;
    
    // Create monomials for interpolation
    terms := [];
    for i in [-10 .. 10] do
	for j in [-6 .. 6] do
	    Append(~terms, (R ! lambda)^i * (R ! mu)^j);
	end for;
    end for;

    return R, base, terms;
end function;

procedure TrickInCoset(G, b, w, base, d, element, R, conj, terms, diagonaliser,
    ~elements, ~total_log_time)
	local field, q, m, t, P, B, coeffs, polys, polys2, var_change,
	good_coeffs, eqns, diag, k;
	
    field := CoefficientRing(R);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    P := IntegerRing(R);
    
    assert Parent(w) cmpeq Parent(element`slp);
    element`mat := b * element`mat;
    element`slp := w * element`slp;
	
    vprint LargeReeTrick, 4: "Find char poly using interpolation";
    B := conj * element`mat * conj^(-1);
	
    // Get characteristic polynomial
    polys<alpha> := PolynomialAlgebra(R);

    // Change variables instead of taking derivatives
    // We want all first k derivatives to be zero, since we want root of
    // multiplicity k, and this is equivalent to that the k lowest
    // coefficients of the new polynomial vanish
    polys2<beta> := PolynomialAlgebra(R);
    var_change := hom<polys -> polys2 | beta + 1>;

    // Get zeros of coefficient polynomials
    // We want zero of multiplicity 6
    coeffs := Coefficients(var_change(polys ! interpolate(field,
	terms, B, diagonaliser)));	
    good_coeffs := [Denominator(coeffs[i]) : i in [1 .. 6]
	| not IsZero(coeffs[i])];

    vprint LargeReeTrick, 4: "Number of good coeffs:", #good_coeffs;
    if #good_coeffs eq 0 then
	return;
    end if;

    // Obtain polynomial equations
    eqns := [P ! (coeffs[i] * (&*good_coeffs)) : i in [1 .. 6]];

    vprint LargeReeTrick, 4: "Solve coefficient equations";
    roots := solveEquations(P, t, eqns);
    vprint LargeReeTrick, 4: "Roots:", roots;
    
    for root in roots do
	// Obtain element in cyclic group
	diag := Generic(G) ! diagonaliser(root, root^t);

	// Order of coset element
	order := Order(diag^conj * element`mat : Proof := false);
	vprint LargeReeTrick, 4: "Order:", order;
	
	if not IsOne(root) and IsEven(order) then
	    vprint LargeReeTrick, 3: "Candidate found!", root;
	    vprint LargeReeTrick, 2: "Candidate order",  order;

	    // Express diagonal element in generator
	    vprint LargeReeTrick, 2: "Apply discrete log";
	    log_time := Cputime();
	    k := Log(d[2, 2], root);
	    log_time := Cputime(log_time);
	    total_log_time +:= log_time;

	    // If cyclic generator has order less than q-1, we might get k=0
	    if k gt 0 then
		vprint LargeReeTrick, 2: "Discrete log done", k;
		assert diag^conj eq base`mat^k;
		assert order eq Order(base`mat^k * element`mat :
		    Proof := false);
		
		Include(~elements, <base`mat^k * element`mat,
		    base`slp^k * element`slp>);
	    end if;
	end if;
    end for;
end procedure;
    
// Find element of even order in G = 2F_4(q)
function EvenOrderTrick(G, g, d, conj, slp, element, diagonaliser, maxTries)
    local field, q, m, t, A, R, terms, b, w, total_time, log_time, base,
	total_log_time, tries, elements;
    
    field := CoefficientRing(G);
    q := #field;
    m := (Degree(CoefficientRing(G)) - 1) div 2;
    t := 2^(m + 1);

    assert assigned G`RandomProcess;
    
    vprint LargeReeTrick, 1: "Entering Large Ree Trick";
    total_time := Cputime();
    total_log_time := 0;
    
    // Initialise trick and obtain monomials for interpolation
    R, base, terms := initialiseTrick(G, g, slp, diagonaliser);
    
    // Number of iterations
    tries := 0;
    repeat
	b, w := Random(G`RandomProcess);
	elements := {};

	// Perform the trick in the given coset 
	TrickInCoset(G, b, w, base, d, element, R, conj, terms, diagonaliser,
	    ~elements, ~total_log_time);

	tries +:= 1;
    until not IsEmpty(elements) or tries ge maxTries;
    
    total_time := Cputime(total_time);
    vprint LargeReeTrick, 1: "Leaving Large Ree Trick";
    return elements, total_time, total_log_time;
end function;

// Calculate the char poly of a matrix A(u,v)B using interpolation.
// terms are the monomials used in the char poly
// diagonaliser returns a diagonal matrix given two field elements
function interpolate(field, terms, B, diagonaliser)
    local interpolation_points, interpolation_values, x, y,
	interpolation_matrix, sols, nulls, values, coeffs;

    interpolation_points := [];
    interpolation_values := [];
    nonZeroField, inc := MultiplicativeGroup(field);
    
    vprint LargeReeTrick, 8: "Nof terms:", #terms;
    for i in [1 .. #terms] do
	x := inc(Random(nonZeroField));
	y := inc(Random(nonZeroField));

	// Get explicit field coefficients
	Append(~interpolation_points,
	    [Evaluate(term, [x, y]) : term in terms]);
	
	vprint LargeReeTrick, 8: "Get interpolation values", i;
	Append(~interpolation_values, getInterpolationValues(x, y, B,
	    diagonaliser));
    end for;

    // Setup structure for linear equation solver
    interpolation_matrix := Transpose(Matrix(Codomain(inc),
	interpolation_points));
    values := [Vector(Codomain(inc), row) :
	row in RowSequence(Transpose(Matrix(interpolation_values)))];

    // Perform interpolation, ie solve a linear system for each value in values
    sols, nulls := Solution(interpolation_matrix, values);
    assert #sols eq 27;
    
    // Get coefficients of characteristic polynomial
    coeffs := [&+[sol[i] * terms[i] : i in [1 .. Degree(sol)]] : sol in sols];
    return coeffs;
end function;

function getInterpolationValues(lambda, mu, b, diagonaliser)
    local A, MA, coeffs;

    MA := MatrixAlgebra(CoefficientRing(b), Degree(b));

    // Diagonal matrix
    A := MA ! diagonaliser(lambda, mu);

    // Matrix in coset
    M := A * (MA ! b);

    // Get characteristic polynomial
    coeffs := Coefficients(CharacteristicPolynomial(M));

    // Pad coefficients if necessary
    while #coeffs lt Degree(b) + 1 do
	Append(~coeffs, 0);
    end while;

    return coeffs;
end function;

// Solve equations in 2 variables
function solveEquations(P, t, eqns)
    local id, roots, equations, sols, polys, roots2, poly, lambda, mu;

    field := CoefficientRing(P);
    m := (Degree(field) - 1) div 2;
    lambda := P.1;
    mu := P.2;

    vprint LargeReeTrick, 7: "Equations:", eqns, #eqns;
    eqns := &join{@ {@ e @} : e in eqns | not IsZero(e) @};

    vprint LargeReeTrick, 7: "Equations:", eqns, #eqns;
    vprint LargeReeTrick, 4: "Factorise equations";
    divider := GCD(eqns);
    equations := {@ eqn div divider : eqn in eqns @};
    
    vprint LargeReeTrick, 7: "Equations:", equations, #equations;
    vprint LargeReeTrick, 4: "Compute resultants";

    // Calculate resultants and thus remove mu
    resultants := &cat[[UnivariatePolynomial(Resultant(equations[i],
	equations[j], mu)) : i in [j + 1 .. #equations]] :
	j in [1 .. #equations - 1]];
    
    vprint LargeReeTrick, 7: "Resultants:", resultants;
    vprint LargeReeTrick, 4: "Find resultant roots for lambda";

    // Get possible values for lambda
    roots := &join{{r[1] : r in Roots(p) | not IsZero(r[1])} :
	p in resultants | not IsZero(p)};

    vprint LargeReeTrick, 7: "Lambda roots:", roots;
    
    sols := {};
    for r in roots do
	vprint LargeReeTrick, 4: "Evaluate equations at", r;
	
	// Get polynomials in mu only
	polys := [UnivariatePolynomial(Evaluate(eqns[i], lambda, r))
	    : i in [1 .. #eqns]];

	vprint LargeReeTrick, 7: "Polys:", polys;
	vprint LargeReeTrick, 4: "Find roots for mu";
	
	// Get possible values for mu
	roots2 := &join{{s[1] : s in Roots(p) | r^t eq s[1]} :
	    p in polys | not IsZero(p)};
	
	if not IsEmpty(roots2) then
	    Include(~sols, r);
	end if;
    end for;
    
    return sols;
end function;
