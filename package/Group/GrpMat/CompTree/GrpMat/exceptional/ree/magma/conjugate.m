/******************************************************************************
 *
 *    conjugate.m    Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-06-04
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: conjugate.m 1605 2008-12-15 09:05:48Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeConjugate, 10;

import "standard.m": getReeDiagonalElt, isOrbitPoint, getReeMagmaForm,
    checkG2membership, exceptionalOuterAutomorphism;
import "ree.m": ReeTrivialRecognitionChecks, ReeReductionFormat,
    ReeReductionMaps;

forward conjugateToTriangular, diagonalConjugate;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeConjugacy(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, wordGroup := WordGroup(G)) -> Map, GrpMatElt
    {G \leq GL(7, q) is a conjugate of Ree(q).

    Return an explicit isomorphism to the standard copy H = G^x,
    as well as such an element x. }
    local P, Q, h, stab, u1, u2, H1, H2, H, field;

    if CheckInput then
	if not (Degree(G) eq 7 and ReeGeneralRecogniser(G)) then
	    error "Ree conjugation: G must be a Ree conjugate";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    field := CoefficientRing(G);
    repeat
	repeat
	    // Find two stabilisers
	    P, Q := ReeFindOrbitPoint(G : CheckInput := false,
		Randomiser := Randomiser, wordGroup := wordGroup);

	    stabs := [];
	    Append(~stabs, ReeStabiliser(G, P : CheckInput := false,
		Randomiser := Randomiser, wordGroup := wordGroup));
	    Append(~stabs, ReeStabiliser(G, Q : CheckInput := false,
		Randomiser := Randomiser, wordGroup := wordGroup));
	    
	    // Get stabilisers
	    stabGroups := [];
	    for stab in stabs do
		Append(~stabGroups, sub<Generic(G) | [g`mat : g in stab]>);
	    end for;

	    // Find change of basis matrix h such that G^h_P and
	    // G^h_Q consists of upper and lower triangular matrices,
	    // respectively
	    h := conjugateToTriangular(G, stabGroups[1], stabGroups[2]);
	    H := G^h;
	    H`RandomProcess := RandomProcessWithWords(H :
		WordGroup := WordGroup(H));
	    
	    // Get form fixed by conjugate
	    flag, form := SymmetricBilinearForm(H);
	    assert flag;
	    
	    // Form is determined up to a constant, and we need middle element
	    // to be a non-square
	    if not IsSquare(-form[4, 4]) then
		alpha := Random(field);
		form *:= -alpha^2;
	    end if;
	    assert IsSquare(-form[4, 4]);

	    // Find diagonal matrix that conjugates the form to the
	    // standard form,
	    // and also conjugates us to the standard Ree group
	    flag, diags := diagonalConjugate(H, form);
	until flag;

	// If we're very unlucky, the conjugating matrix might not work
	// since we don't check that it works for every ovoid point
    until exists(diag){d : d in diags | ReeStandardRecogniser(H^d)};

    ree := H^diag;
    
    // Construct explicit isomorphism to standard copy
    homo := hom<G -> Generic(ree) | x :-> x^(h * diag)>;
    iso := hom<G -> ree | x :-> Function(homo)(x)>;

    if not assigned G`ReeReductionData then
	G`ReeReductionData := rec<ReeReductionFormat |
	    maps := rec<ReeReductionMaps | conjugation := iso>,
	    conjugator := h * diag>;
    else
	G`ReeReductionData`conjugator := h * diag;
	if not assigned G`ReeReductionData`maps then
	    G`ReeReductionData`maps :=
		rec<ReeReductionMaps | conjugation := iso>;
	else
	    G`ReeReductionData`maps`conjugation := iso;
	end if;
    end if;
    
    return iso, h * diag;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function diagonalConjugate(G, form)
    local K, p, P, d, poly, field, t, m, q, polys;

    field := CoefficientRing(G);
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    assert assigned G`RandomProcess;

    // Given form is the standard form up to a diagonal matrix
    stdform := getReeMagmaForm(field);
    a := form[1, 7];
    b := form[2, 6];
    c := form[3, 5];
    P<alpha, beta> := PolynomialAlgebra(field, 2);

    // Try to find mapping using both square roots
    for s in [Sqrt(-form[4, 4]), -Sqrt(-form[4, 4])] do
	// Get pairs of points
	points := [];
	for i in [1 .. 2] do
	    p, q := ReeFindOrbitPoint(G : Randomiser := G`RandomProcess,
		CheckInput := false);
	    Append(~points, [p, q]);
	end for;

	// Construct equations using the points
	polys := [];
	for pair in points do
	    
	    polys := Append(polys, [(-p[2]^(3*t+2)*(q[4]*s)^(3*t)*alpha^3*beta^2*p[3]+p[2]^(3*t)*(q[4]*s)^(3*t)*alpha*p[5]*c-p[2]^(3*t+1)*(q[4]*s)^(3*t)*alpha^2*beta*p[4]*s-q[5]*c*q[2]^(3*t)*(p[4]*s)^(3*t)*alpha-q[5]*c*q[2]^(3*t)*p[2]*alpha^2*beta^2*p[3]^2+q[5]*c*q[2]^(3*t)*p[6]*b+q[5]*c*q[2]^(3*t)*beta*p[3]*alpha*p[4]*s+beta*alpha^2*q[2]^(3*t+1)*q[4]*s*(p[4]*s)^(3*t)+beta^3*alpha^3*q[2]^(3*t+1)*q[4]*s*p[2]*p[3]^2-beta*alpha*q[2]^(3*t+1)*q[4]*s*p[6]*b-beta^2*alpha^2*q[2]^(3*t+1)*q[4]*s^2*p[3]*p[4]+beta^2*alpha^3*q[2]^(3*t+2)*q[3]*(p[4]*s)^(3*t)+beta^4*alpha^4*q[2]^(3*t+2)*q[3]*p[2]*p[3]^2-beta^2*alpha^2*q[2]^(3*t+2)*q[3]*p[6]*b-beta^3*alpha^3*q[2]^(3*t+2)*q[3]*p[3]*p[4]*s+p[2]^(3*t+2)*beta^3*q[3]*alpha^3*q[4]*s*p[3]-p[2]^(3*t)*beta*q[3]*alpha*q[4]*s*p[5]*c+p[2]^(3*t+1)*beta^2*q[3]*alpha^2*q[4]*s^2*p[4]-p[2]^(3*t+2)*alpha^4*q[2]*beta^4*q[3]^2*p[3]+p[2]^(3*t)*alpha^2*q[2]*beta^2*q[3]^2*p[5]*c-p[2]^(3*t+1)*alpha^3*q[2]*beta^3*q[3]^2*p[4]*s+p[2]^(3*t+2)*q[6]*b*alpha^2*beta^2*p[3]-p[2]^(3*t)*q[6]*b*p[5]*c+p[2]^(3*t+1)*q[6]*b*alpha*beta*p[4]*s),
		(q[2]^(3*t+1)*q[5]*c*p[2]*alpha^2*beta^2*p[3]^2-p[2]^(3*t)*alpha*q[2]*(q[4]*s)^(3*t)*p[5]*c-2*p[2]^(3*t+1)*alpha^3*q[2]^2*beta^3*q[3]^2*p[4]*s+alpha*q[2]^(3*t+2)*beta*q[4]*s*p[6]*b-p[2]^(3*t)*q[7]*a*p[5]*c-alpha^3*q[2]^(3*t+2)*beta^3*q[4]*s*p[2]*p[3]^2+beta^3*alpha^3*q[2]^(3*t+3)*q[3]*p[3]*p[4]*s-q[2]^(3*t+1)*q[5]*c*p[6]*b-p[2]^(3*t)*q[3]*q[5]*c^2*p[5]+p[2]^(3*t+1)*q[7]*a*alpha*beta*p[4]*s+p[2]^(3*t+1)*alpha^2*q[2]*(q[4]*s)^(3*t)*beta*p[4]*s-2*p[2]^(3*t+2)*alpha^4*q[2]^2*beta^4*q[3]^2*p[3]+2*p[2]^(3*t)*alpha^2*q[2]^2*beta^2*q[3]^2*p[5]*c+beta^2*alpha^2*q[2]^(3*t+3)*q[3]*p[6]*b+q[2]^(3*t+1)*q[5]*c*(p[4]*s)^(3*t)*alpha-q[2]^(3*t+1)*q[5]*c*beta*p[3]*alpha*p[4]*s-p[2]^(3*t)*q[4]^2*s^2*p[5]*c+alpha^2*q[2]^(3*t+2)*beta^2*q[4]*s^2*p[3]*p[4]+p[2]^(3*t+1)*q[4]^2*s^3*alpha*beta*p[4]+p[2]^(3*t+1)*q[3]*q[5]*c*alpha*beta*p[4]*s+p[2]^(3*t+2)*q[7]*a*alpha^2*beta^2*p[3]-p[2]^(3*t+1)*beta^2*q[3]*alpha^2*q[2]*q[4]*s^2*p[4]-alpha^2*q[2]^(3*t+2)*beta*q[4]*s*(p[4]*s)^(3*t)+p[2]^(3*t+2)*alpha^3*q[2]*(q[4]*s)^(3*t)*beta^2*p[3]-beta^2*alpha^3*q[2]^(3*t+3)*q[3]*(p[4]*s)^(3*t)-beta^4*alpha^4*q[2]^(3*t+3)*q[3]*p[2]*p[3]^2+p[2]^(3*t+2)*q[3]*q[5]*c*alpha^2*beta^2*p[3]+p[2]^(3*t+2)*q[4]^2*s^2*alpha^2*beta^2*p[3]-p[2]^(3*t+2)*beta^3*q[3]*alpha^3*q[2]*q[4]*s*p[3]+p[2]^(3*t)*beta*q[3]*alpha*q[2]*q[4]*s*p[5]*c)]) where p is pair[1] where q is pair[2];
	end for;

	// Check that we have non-zero equations
	if exists{i : i in [1 .. #polys] | forall{x : x in polys[i] |
	    IsZero(x)}} then
	    continue;
	end if;
	eqns := [rep{p : p in polys[i] | not IsZero(p)} : i in [1 .. #polys]];
	
	// Get polynomial in alpha only
	resultant := UnivariatePolynomial(Resultant(eqns[1], eqns[2], beta));
	if IsZero(resultant) then
	    continue;
	end if;

	// Get possible values for alpha
	alpha_roots := {r[1] : r in Roots(resultant) | not IsZero(r[1])};
	if IsEmpty(alpha_roots) then
	    continue;
	end if;
    
	for x in alpha_roots do
	    // Substitute alpha to get polynomial in beta only
	    unipolys := [UnivariatePolynomial(Evaluate(eqns[i], alpha, x)) :
		i in [1 .. #eqns]];

	    // Get possible values for beta
	    beta_roots := {};
	    for p in {x : x in unipolys | not IsZero(x)} do
		beta_roots join:= {r[1] : r in Roots(p) | not IsZero(r[1])};
	    end for;
	    
	    if IsEmpty(beta_roots) then
		continue;
	    end if;

	    // Get possible diagonal matrices
	    diags := [];
	    for y in beta_roots do
		diag := Generic(G) ! DiagonalMatrix([1, x, y, s, c * y^(-1),
		    b * x^(-1), a]);
		
		// Check that we have a valid conjugating matrix
		if diag * stdform * Transpose(diag) eq form and
		    forall{x : x in points | isOrbitPoint(x[1] * diag) and
		    isOrbitPoint(x[2] * diag)} then
		    Append(~diags, diag);
		end if;
	    end for;
	    if #diags gt 0 then
		return true, diags;
	    end if;
	end for;
    end for;
    
    return false, _;
end function;

// G should be a conjugate of Ree, and H1, H2 stabilisers of some points
// Find a matrix that conjugates G to H such that H1 and H2 consist of
// lower and upper triangular matrices, respectively.
function conjugateToTriangular(G, H1, H2)
    local V, compSeries, flags, spaces, conjugator;

    assert Degree(G) eq 7;
    V := VectorSpace(CoefficientRing(G), Degree(G));

    // Compute composition series using MeatAxe
    compSeries := [CompositionSeries(GModule(H1)),
	CompositionSeries(GModule(H2))];

    // Compute flags of fixed subspaces
    flags :=
	[[sub<V | [V ! ElementToSequence(gen * Morphism(c1[i], c1[#c1])) :
	gen in Generators(c1[i])]> : i in [1 .. Degree(G)]],
	[sub<V | [V ! ElementToSequence(gen * Morphism(c2[i], c2[#c2])) :
	gen in Generators(c2[i])]> : i in [1 .. Degree(G)]]]
	where c1 is compSeries[1] where c2 is compSeries[2];

    // Get one-dimensional subspaces
    spaces := [flags[1][i] meet flags[2][#flags[2] - i + 1] : i in [1 .. 4]]
	cat Reverse([flags[2][i] meet flags[1][#flags[1] - i + 1] :
	i in [1 .. 3]]);
    assert forall{space : space in spaces | Dimension(space) eq 1};

    // Compute conjugating element that turns stabilisers into triangular form
    conjugator := Generic(G) ! &cat[ElementToSequence(Random(Basis(spaces[i])))
	: i in [1 .. #spaces]];
    return conjugator^(-1);
end function;

