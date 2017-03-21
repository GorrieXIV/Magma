/******************************************************************************
 *
 *    trick.m   New trick for finding stabiliser element in Sz(q)
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-03-31
 *
 *    Version   : $Revision:: 3160                                           $:
 *    Date      : $Date:: 2015-11-02 09:56:37 +1100 (Mon, 02 Nov 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: trick.m 3160 2015-11-01 22:56:37Z jbaa004                      $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiNewTrick, 10;

SuzukiCentraliserInfo :=
    recformat<q : RngIntElt, conjugator : Rec, involution : Rec>;
declare attributes GrpMat : SuzukiCentraliserData;

import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/centraliser.m" : BrayAlgorithm;
import "../../../util/basics.m" : MatSLP;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Diagonalise an element of order q-1 in standard Suzuki group
function diagonaliseSuzukiCyclicGroup(g, m)
    local G, eigenvalues, t, q, lambda;

    F := GF(2, 2 * m + 1);
    q := #F;
    t := 2^(m + 1);
    G := GL(4, F);

    eigenvalues, eigenvectors := SuzukiCyclicEigenvalues(g);
    lambda := eigenvalues[2];
    
    // 4 x 4 conjugating matrix with eigenvectors
    x := G ! &cat[ElementToSequence(f) : f in eigenvectors];

    // 4 x 4 diagonal matrix with eigenvalues
    d := G ! DiagonalMatrix(F, 4, eigenvalues);
    assert d^x eq g;

    return d, x, lambda;
end function;

// Find element of order q-1 and diagonalise it
function findCyclicGroup(R, m)
    local a, lambda, eigenvalues, x, d, t, F, word,  G, q;

    t := 2^(m + 1);
    q := 2^(2 * m + 1);
    
    repeat
	a, word := Random(R);
    until Order(a : Proof := false) eq q - 1;
    
    d, x, lambda := diagonaliseSuzukiCyclicGroup(a, m);
    return a, word, d, x, lambda;
end function;

// Solve bivariate equations using resultants
function solveEquations(P, t, equations)
    local id, roots, sols, polys, roots2, poly, lambda, mu;

    // The two variables
    lambda := P.1;
    mu := P.2;

    vprint SuzukiNewTrick, 7: "Equations:", equations;

    // Calculate resultants and thus remove mu
    resultants := &cat[[UnivariatePolynomial(Resultant(equations[i],
	equations[j], mu)) : i in [j + 1 .. #equations]] :
	j in [1 .. #equations]];
    
    vprint SuzukiNewTrick, 7: "Resultants:", resultants;

    // Get possible values for lambda
    roots := &join{{r[1] : r in Roots(p) | r[1] notin {0, 1}} :
	p in resultants | not IsZero(p)};

    // print "lambda", roots;
    
    sols := {};
    for r in roots do
	// Get polynomials in mu only
	polys := [UnivariatePolynomial(Evaluate(equations[i], lambda, r))
	    : i in [1 .. #equations]];

	// print "mu", [Roots(p) : p in polys];
	
	// Get possible values for mu
	roots2 := &join{{s[1] : s in Roots(p) | r^t eq s[1]} :
	    p in polys | not IsZero(p)};
	
	for s in roots2 do
	    Include(~sols, <r, s>);
	end for;
    end for;
    
    return sols;
end function;

// Completion check for the Bray algorithm, which also finds the elements
// that we are looking for.
function centraliserCompletionCheck(G, U, involution, slpMap)
    local y, slp_y, g, field, elements, q, r, s;

    // Take elements of even order in involution centraliser
    elements := [i : i in [1 .. NumberOfGenerators(G)] |
	G.i ne involution and Order(G.i) in {2, 4}];

    if #elements gt 0 then
	// Take arbitrary element
	k := Rep(elements);
	y := G.k;
	slp_y := slpMap[k];

	// Get corresponding involution
	if Order(y) eq 4 then
	    y ^:= 2;
	    slp_y ^:= 2;
	end if;
	
	assert assigned U`RandomProcess;
	field := CoefficientRing(G);

	// Find external involution 
	y := rec<MatSLP | mat := y, slp := slp_y>;
	z := y;
	repeat
	    g, w := Random(U`RandomProcess);
	    z`mat ^:= g;
	    z`slp ^:= w;
	until IsOdd(Order(involution * z`mat : Proof := false)) and
	    IsOdd(Order(z`mat * y`mat : Proof := false));

	c := rec<MatSLP | mat := involution, slp := slpMap[1]>;

	// Find q-1 element
	vprint SuzukiNewTrick, 2 : "Apply dihedral trick";
	g1 := DihedralTrick(c, z, U`RandomProcess);
	g2 := DihedralTrick(z, y, U`RandomProcess);
	g := rec<MatSLP | mat := g1`mat * g2`mat, slp := g1`slp * g2`slp>;

	// Check that we got an element of order q-1
	vprint SuzukiNewTrick, 2 : "Dihedral trick order", Order(g`mat);
	s, r := Quotrem(Order(g`mat), U`SuzukiCentraliserData`q - 1);
	
	if r eq 0 then
	    //g`mat ^:= s;
	    //g`slp ^:= s;
	    
	    if involution^(g`mat) eq y`mat then
		G`SuzukiCentraliserData :=
		    rec<SuzukiCentraliserInfo | conjugator := g,
		    involution := z>;
		return true;
	    end if;
	end if;
    end if;

    return false;
end function;

// New trick to find an element of order 4, which avoids the magic polynomials
// and the need to consider double cosets.

function getOrder4Element(G : UseDiscreteLog := true)
    R := G`RandomProcess;
    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    words := [];
    t := 2^(m + 1);

    // Find random element of order q - 1 and diagonalise it
    a, words[2], d, eigenvectors, b := findCyclicGroup(R, m);

    // Find element of order 4 in coset of diagonal matrices
    PP<lambda, mu> := PolynomialAlgebra(field, 2);
    MA := MatrixAlgebra(FieldOfFractions(PP), Degree(G));
    A := MA ! DiagonalMatrix([lambda * mu, lambda, 1 / lambda,
	1 / (lambda * mu)]);

    repeat
	// Get random matrix
	h, words[1] := Random(R);
	B := MA ! (eigenvectors * h * eigenvectors^(-1));

	H := G^(eigenvectors^(-1));
	flag, form := SymplecticForm(H);
	assert flag;
	
	// Setup the two equations for an element of order 4. It should have
	// the eigenvalue 1 and trace 0
	f := Determinant(A * B - One(MA));
	g := Trace(A * B);
	gg := A * B * form * Transpose(A * B) - form;
	
	// Get field values which determine elements
	vprint SuzukiNewTrick, 2 : "Solve equations for even order element";
	roots := {r[1] : r in solveEquations(PP, t, [Numerator(f),
	    Numerator(g)])};// cat [Numerator(x) : x in ElementToSequence(gg)])};
	
	// Get corresponding elements in correct coset as words in generators
	x := Identity(G);
	for r in roots do

	    // Get diagonal matrix for this solution
	    diag := Generic(G) !
		DiagonalMatrix([r^(t + 1), r, r^(-1), r^(-t - 1)]);

	    // Move back to original coset
	    x := diag^eigenvectors * h;
	    
	    if Order(x) eq 4 then
		vprint SuzukiNewTrick, 3 : "Candidate found!";

		if UseDiscreteLog then
		    vprint SuzukiNewTrick, 3 : "Apply discrete log";
		    k := Log(b, r);
		    slp_x := words[2]^k * words[1];
		    vprint SuzukiNewTrick, 3 : "Discrete log done";
		else
		    slp_x := Identity(Parent(words[1]));
		end if;
		break;
	    end if;
	end for;
    until Order(x) eq 4;

    return x, slp_x;
end function;

// Main function of the new trick. Finds generators for a stabiliser of a point
// and also the extra involution that generates the whole of Sz.
// Note that these generators do not in general give an isomorphism to the
// standard copy.

function getStabiliser(G : UseDiscreteLog := true, FieldSize := 0)
    local x, invol, slp, slp_x, centraliser, slpMap, g, q, field;
    
    assert assigned G`RandomProcess;
    field := CoefficientRing(G);

    // Find element of order 4
    // Use new trick if we are in the natural representation and random search
    // otherwise.
    if Degree(G) eq 4 and Characteristic(field) eq 2 and
	IsOdd(Degree(field)) and Degree(field) gt 1 then
	x, slp_x := getOrder4Element(G : UseDiscreteLog := UseDiscreteLog);
	q := #field;
    else
	q := FieldSize;
	flag, x, slp_x := RandomElementOfOrder(G, 4 :
	    Randomiser := G`RandomProcess, MaxTries := q^2);
	assert flag;
    end if;

    // Find centraliser of corresponding involution and find the generators
    // inside this centraliser
    vprint SuzukiNewTrick, 2 : "Getting involution centraliser";
    invol := x^2;
    slp := slp_x^2;
    G`SuzukiCentraliserData := rec<SuzukiCentraliserInfo | q := q>;
    centraliser, slpMap := BrayAlgorithm(G, invol, slp :
	Randomiser := G`RandomProcess,
	completionCheck := centraliserCompletionCheck);

    g := centraliser`SuzukiCentraliserData`conjugator;
    z := centraliser`SuzukiCentraliserData`involution;

    assert Evaluate(slp_x, UserGenerators(G)) eq x;
    assert Evaluate(g`slp, UserGenerators(G)) eq g`mat;
    
    vprint SuzukiNewTrick, 2 : "Stabiliser found";
    return [<slp_x, x>, <g`slp, g`mat>, <z`slp, z`mat>];
end function;
