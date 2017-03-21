/******************************************************************************
 *
 *    conjugate.m Solves the conjugation problem for Sz
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm
 *    Dev start : 2004-12-10
 *
 *    Version   : $Revision:: 3160                                           $:
 *    Date      : $Date:: 2015-11-02 09:56:37 +1100 (Mon, 02 Nov 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: conjugate.m 3160 2015-11-01 22:56:37Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;

/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiConjugate, 10;

import "suzuki.m" : recognitionErrors, SuzukiReductionMaps,
    SuzukiReductionFormat, checkSuzukiProperSubgroups;
import "standard.m" : diagramAutomorphism, getSuzukiOrder, isOvoidPoint;
import "../../../util/basics.m" : MatSLP;
import "membership.m" : getSuzukiRecognitionDataCore;
import "trick.m" : getStabiliser;

forward conjugateToTriangular, conjugateToSz, conjugateIntoSp;

// Status values from conjugate recognition
CONJ_SUZUKIGROUP    := 5; 
CONJ_WRONG_INPUT    := 6; 
CONJ_NOT_SYMPLECTIC := 7; 
CONJ_NOT_SUBGROUP   := 8; 
CONJ_PROPER_SUB     := 9; 

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

function findStabilisedPoint(S, V)
    M := GModule(S);
    series := CompositionSeries(M);
    points := [L : L in series | Dimension(L) eq 1];
    assert #points eq 1;
    P := V ! (points[1].1 * Morphism(points[1], M));

    return Normalise(P);
end function;

function findStabiliser(G)
    gens := getStabiliser(G);
    S := sub<Generic(G) | gens[1][2], gens[2][2]>;
    return S, gens;
end function;

intrinsic SuzukiConjugacy(G :: GrpMat[FldFin] : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, W := WordGroup(G)) -> Map, GrpMatElt
    {G \leq GL(4, q) is a conjugate of Sz(q).

    Return an explicit isomorphism to the standard copy H = G^x,
    as well as such an element x. }
    local P, Q, h, u1, u2, H1, H2, H, gl, field, V, form, formSz, conjugator,
	iso, status, bool, image;
    
    if CheckInput then
	bool := SuzukiConjugateRecogniser(G);
	if not bool then
	    error "Sz conjugation: G is not a conjugate of Sz";
	end if;
    end if;
    
    field := CoefficientRing(G);
    V := VectorSpace(G);
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    vprint SuzukiConjugate, 3 : "Find stabilisers";

    H1, gens1 := findStabiliser(G);
    P := findStabilisedPoint(H1, V);

    repeat
	H2, gens2 := findStabiliser(G);
	Q := findStabilisedPoint(H2, V);
    until P ne Q;
    
    vprint SuzukiConjugate, 3 : "Simultaneously triangulate stabilisers";

    // Find change of basis matrix h such that G^h_P and G^h_Q consist of
    // upper and lower triangular matrices, respectively
    h := conjugateToTriangular(G, H1, H2);
    H := G^h;
    H`RandomProcess := RandomProcessWithWords(H : WordGroup := WordGroup(H));

    inf := Normalise(P * h);
    zero := Normalise(Q * h);
    assert isOvoidPoint(inf);
    assert isOvoidPoint(zero);
    
    // Now H is conjugate to Sz by a diagonal matrix
    // This matrix can be found by conjugating the form fixed by H into the
    // form fixed by the standard Sz
    
    // Find form fixed by H = G^h
    flag, form := SymplecticForm(H);
    assert flag;
    gl := Generic(G);
    form := gl ! form;

    vprint SuzukiConjugate, 3 : "Compute final diagonal conjugator";

    // Find diagonal conjugating matrix that makes G^h preserve correct form
    conjugator := conjugateToSz(H, (V ! Q) * h, form);
    image := H^conjugator;
    assert SuzukiStandardRecogniser(image);

    // Construct isomorphism from G to standard Sz
    homo := hom<G -> Generic(image) | x :-> x^(h * conjugator)>;
    iso := hom<G -> image | x :-> Generic(image) ! Function(homo)(x)>;

    if not assigned G`SuzukiReductionData then
	G`SuzukiReductionData := rec<SuzukiReductionFormat |
	    conjugator := h * conjugator,
	    maps := rec<SuzukiReductionMaps | conjugation := iso>>;
    else
	G`SuzukiReductionData`conjugator := h * conjugator;
	if not assigned G`SuzukiReductionData`maps then
	    G`SuzukiReductionData`maps :=
		rec<SuzukiReductionMaps | conjugation := iso>;
	end if;
    end if;
    
    vprint SuzukiConjugate, 3 : "Setup constructive membership data";
    // Make stabilisers upper and lower triangular
    for i in [1 .. 2] do
	gens1[i][2] ^:= (h * conjugator);
	gens2[i][2] ^:= (h * conjugator);
    end for;

    G`SuzukiRecognitionData :=
	getSuzukiRecognitionDataCore(G, gens1, gens2, W);
    
    vprint SuzukiConjugate, 3 : "Conjugation problem solved";

    return iso, h * conjugator;
end intrinsic;


intrinsic SuzukiConjugateRecogniser(G :: GrpMat) -> BoolElt, RngIntElt
    { G \leq GL(4, q). Determine (non-constructively) if G is a conjugate of
    the standard copy of Sz(q). }
    local form, field, GG, H, q;

    vprint SuzukiConjugate, 8: "Checking input";
    
    // Check that input is sensible
    if not (Degree(G) eq 4 and Category(F) eq FldFin and
	Characteristic(F) eq 2 and IsOdd(Degree(F)) and Degree(F) gt 1)
	where F is CoefficientRing(G) then
	return false, CONJ_WRONG_INPUT;
    end if;
    
    vprint SuzukiConjugate, 8: "Checking preserved form";

    // Check that G is conjugate to a subgroup of Sp(4, q), ie check that it
    // preserves a symplectic form
    flag, form := SymplecticForm(G);
    if not flag then
	return false, CONJ_NOT_SYMPLECTIC;
    end if;
    
    field := CoefficientRing(G);
    q := #field;
    
    vprint SuzukiConjugate, 8: "Conjugating form";

    // Make sure G preserves standard form
    conj := TransformForm(form, "symplectic");
    H := G^conj;

    // Determine if G is a subgroup of Sz(q)
    GG := sub<Generic(H) | [diagramAutomorphism(H.i) :
	i in [1 .. NumberOfGenerators(H)]]>;
    if not IsIsomorphic(GModule(H), GModule(GG)) then
	return false, CONJ_NOT_SUBGROUP;
    end if;

    // Determine if G is a proper subgroup of Sz(q)
    if checkSuzukiProperSubgroups(G) then
	return true, CONJ_SUZUKIGROUP;
    else
	return false, CONJ_PROPER_SUB;
    end if;    
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// G should be a conjugate of Sz, and H1, H2 stabilisers of some points
// Find a matrix that conjugates G to H such that H1 and H2 consist of
// lower and upper triangular matrices, respectively.
function conjugateToTriangular(G, H1, H2)
    local V, compSeries, flags, spaces, conjugator;

    assert Degree(G) eq 4;
    V := VectorSpace(CoefficientRing(G), Degree(G));

    // Compute composition series using MeatAxe
    compSeries := [CompositionSeries(GModule(H1)),
	CompositionSeries(GModule(H2))];
    
    // Compute flags of fixed subspaces
    flags :=
	[[sub<V | [V ! ElementToSequence(gen * Morphism(c1[i], c1[4])) :
	gen in Generators(c1[i])]> : i in [1 .. 4]],
	[sub<V | [V ! ElementToSequence(gen * Morphism(c2[i], c2[4])) :
	gen in Generators(c2[i])]> : i in [1 .. 4]]]
	where c1 is compSeries[1] where c2 is compSeries[2];
    
    // Get one-dimensional subspaces
    spaces := [flags[1][1], flags[1][2] meet flags[2][3],
	flags[1][3] meet flags[2][2], flags[2][1]];
    assert forall{space : space in spaces | Dimension(space) eq 1};

    // Compute conjugating element that turns stabilisers into triangular form
    conjugator := GL(Degree(G), CoefficientRing(G)) !
	&cat[ElementToSequence(Basis(spaces[i])[1]) : i in [1 .. #spaces]];
    return conjugator^(-1);
end function;

// G is conjugate to Sz by a diagonal matrix
// point is in the ovoid of G
// form is the symplectic form preserved by G
// Returns a conjugating element that takes G to Sz
function conjugateToSz(G, point, form)
    local field, q, m, t, c, polys, roots, s, conjugator, gl, formSz, iters;
    
    field := CoefficientRing(point);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    c := [form[1, 4], form[2, 3]];
    gl := GL(4, field);

    // Check that the given form is correct
    assert form[1, 4] eq form[4, 1] and form[2, 3] eq form[3, 2];

    // The form preserved by the standard Sz
    formSz := gl ! PermutationMatrix(field, Reverse([1 .. 4]));

    // Count iterations for benchmark purposes
    iters := 0;
    repeat
	repeat
	    // Find two points with last coordinate non-zero
	    // This happens with high proability
	    points := [];
	    for i in [1 .. 2] do
		repeat
		    points[i] := point * Random(G`RandomProcess);
		until not IsZero(points[i][4]);
		points[i] *:= points[i][4]^(-1);
	    end for;
	    
	    // Create system of linear equations
	    coeffs := Matrix([[points[1][2]^t, points[2][2]^t],
		[points[1][3]^(t + 2), points[2][3]^(t + 2)]]);
	    consts := Vector([p[1] * c[1] - p[2] * p[3] * c[2] : p in points]);

	    // Solve system
	    roots := Solution(coeffs, consts);
	    
	    // All roots must be non-zero
	    iters +:= 1;
	until forall{r : r in ElementToSequence(roots) | not IsZero(r)};
	
	// Compute the conjugating diagonal matrix
	s := 2^m;
	conjugator := gl ! diagonal
	    where diagonal is DiagonalMatrix([c[1], Sqrt(roots[1]^t),
	    roots[2] * roots[2]^(-s), 1]);
	
	vprint SuzukiConjugate, 5: conjugator * formSz * Transpose(conjugator),
	    form;

	// If we're very unlucky, the conjugating matrix might not work
	// since we don't check that it works for every ovoid point
    until conjugator * formSz * Transpose(conjugator) eq form and
	SuzukiStandardRecogniser(G^conjugator);
    
    vprint SuzukiConjugate, 3: "Iterations:", iters;
    return conjugator;
end function;

