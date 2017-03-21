/******************************************************************************
 *
 *    conjugate.m    Large Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2006-04-06
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

declare verbose LargeReeConjugacy, 10;

import "involution.m" : getMaximal;
import "ree.m" : LargeReeEquality, getLargeReeCorrectForm,
    LargeReeReductionMaps, LargeReeReductionFormat,
    LargeReeSzWreath2Info, LargeReeSzParabolicInfo;
import "standard.m" : normaliseQuadForm;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/formula.m" : FindCentraliser, FindComplement;

import "../../../util/basics.m" : getMapFunction, MatSLP, EvaluateMatTup;

forward getComplement, findSzCrossSz, fixSzCrossSz, findSzWreath2,
    conjugationCommonSzWreath2;

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic LargeReeConjugacy(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true) -> Map, GrpMatElt
    {G \leq GL(26, q) is a conjugate of LargeRee(q).

    Return an explicit isomorphism to the standard copy H = G^x,
    as well as such an element x. }
    local F, p, q, m, S, G1, G2, S1, S2, conj, homo, iso,
	M1, M2, flag, conj1, conj2;

    if CheckInput then
	if not (LargeReeGeneralRecogniser(G) and Degree(G) eq 26) then
	    error "G must be a Big Ree group in natural representation";
	end if;
    end if;
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    vprint LargeReeConjugacy, 1 : "Entering Big Ree conjugation";

    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    S := LargeRee(F);
    
    S`RandomProcess := RandomProcessWithWords(S :
	WordGroup := WordGroup(S), Scramble := 1);

    vprint LargeReeConjugacy, 2 : "Find Sz \wr 2 in standard copy";

    // Get Sz \wr 2 and Sz x Sz in standard copy
    findSzWreath2(S);

    vprint LargeReeConjugacy, 2 : "Get standard generators for Sz x Sz";

    // Find standard gens for each Sz factor
    S1, S2 := fixSzCrossSz(S, <S`LargeReeSzWreath2Data`sz1,
	S`LargeReeSzWreath2Data`sz1small>, <S`LargeReeSzWreath2Data`sz2,
	S`LargeReeSzWreath2Data`sz2small>);
    
    vprint LargeReeConjugacy, 2 : "Find Sz \wr 2 in input copy";

    // Get Sz \wr 2 and Sz x Sz in input copy
    findSzWreath2(G);
    
    vprint LargeReeConjugacy, 2 : "Get standard generators for Sz x Sz";

    // Find standard gens for each Sz factor
    G1, G2 := fixSzCrossSz(G, <G`LargeReeSzWreath2Data`sz1,
	G`LargeReeSzWreath2Data`sz1small>, <G`LargeReeSzWreath2Data`sz2,
	G`LargeReeSzWreath2Data`sz2small>);
        
    SS := sub<Generic(G) | UserGenerators(S1) cat UserGenerators(S2)>;

    // Obtain Sz x Sz on two standard generating sets
    M1 := GModule(SS);
    M2 := GModule(SS, UserGenerators(G1) cat UserGenerators(G2));

    homos := GHom(M1, M2);
    vprint LargeReeConjugacy, 2 :
	"Find isomorphism between modules for Sz x Sz", Dimension(homos);

    // Find conjugating element between Sz x Sz
    flag, cbm := IsIsomorphic(M1, M2);
    assert flag;
    
    conj1 := Generic(G) ! cbm^(-1);    
    vprint LargeReeConjugacy, 2 :
	"Conjugate by element in automorphism group of Sz \wr 2";
    
    // Find final conjugating element in endomorphism algebra of module of GS2
    conj2 := conjugationCommonSzWreath2(G^conj1, S, SS);
    
    conj := conj1 * conj2;
    ree := G^conj;
    
    // Construct explicit isomorphism to standard copy
    homo := hom<G -> Generic(ree) | x :-> x^conj>;
    iso := hom<G -> ree | x :-> Function(homo)(x)>;

    if not assigned G`LargeReeReductionData then
	G`LargeReeReductionData := rec<LargeReeReductionFormat |
	    maps := rec<LargeReeReductionMaps | conjugation := iso>,
	    conjugator := conj>;
    else
	G`LargeReeReductionData`conjugator := conj;
	if not assigned G`LargeReeReductionData`maps then
	    G`LargeReeReductionData`maps :=
		rec<LargeReeReductionMaps | conjugation := iso>;
	else
	    G`LargeReeReductionData`maps`conjugation := iso;
	end if;
    end if;
    
    vprint LargeReeConjugacy, 1 : "Leaving Big Ree conjugation";
    return iso, conj;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// sub1 and sub2 are tuples of 26-dim and 4-dim Sz inside G = LargeRee
function fixSzCrossSz(G, sub1, sub2)
    local F, H, stdGens, S, S4, stdGens_slp, H4, flag, slp;
    
    F := CoefficientRing(G);
    H := Sz(F);

    stdGens := [* *];
    
    for tuple in [sub1, sub2] do
	// 26-dim Sz
	S := tuple[1];

	// 4-dim Sz
	S4 := tuple[2];

	// These Suzuki's are already recognised
	assert assigned S4`SuzukiReductionData;
	vprint LargeReeConjugacy, 3 : "Get standard generator SLPs";

	stdGens_slp := [];
	H4 := S4`SuzukiReductionData`stdCopy;

	// Obtain SLPs of 4-dim standard generators
	for g in UserGenerators(H) do
	    flag, slp := SuzukiStandardConstructiveMembership(H4, g);
	    assert flag;
	    Append(~stdGens_slp, WordGroup(S4) ! slp);
	end for;

	// Obtain standard generators in 26-dim
	vprint LargeReeConjugacy, 3 : "Get standard generators";
	Append(~stdGens, Evaluate(stdGens_slp, UserGenerators(S)));
    end for;
	
    return sub<Generic(G) | stdGens[1]>, sub<Generic(G) | stdGens[2]>;
end function;

// Use The Formula to find a copy of Sz x (q-1) inside Sz parabolic
function getComplement(parabolic, parabolicSLPs, kernelGens, normaliser,
    wordGroup : nGens := 5)
	local q, o2, formula_group, formula_slps, reeSLPCoercion, slpCoercion;
    
    q := #CoefficientRing(parabolic);

    // Get generators of [q^10]
    vprint LargeReeInvolution, 2: "Get subgroup generators";
    o2 := sub<Generic(parabolic) | [g`mat : g in kernelGens]>;

    // Obtain [q^10] : (q-1)
    formula_group := sub<Generic(parabolic) | [g`mat : g in kernelGens],
	normaliser`mat>;
    formula_slps := Append([g`slp : g in kernelGens], normaliser`slp);

    // Now find complement of formula_group inside parabolic
    // This complement is Sz x (q-1)
    
    // Need random processes
    formula_group`RandomProcess :=
	RandomProcessWithWords(formula_group : WordGroup :=
	WordGroup(formula_group));
    
    vprint LargeReeInvolution, 2: "Construct SLP homs";
    reeSLPCoercion := hom<WordGroup(parabolic) -> wordGroup |
    Append(parabolicSLPs, normaliser`slp)>;
    slpCoercion := hom<WordGroup(formula_group) -> wordGroup | formula_slps>;

    // Use The Formula
    return FindComplement(parabolic, formula_group, reeSLPCoercion,
	slpCoercion, q - 1 : nGens := nGens, kernelGens := kernelGens,
	cyclicElt := normaliser, ExtendedComplement := true,
	RandomiserG := parabolic`RandomProcess,
	RandomiserH := formula_group`RandomProcess);
end function;

// Use The Formula to find Sz x (q-1) inside an Sz parabolic
// HG should be a recognised Sz involution centraliser
function findSzInParabolic(HG, wordGroup, q)

    // Initialise parabolic record
    parabolicData := rec<LargeReeSzParabolicInfo |
	group := HG,
	slps := HG`LargeReeInvolCentraliserData`genSLPs,
	o2Base := HG`LargeReeInvolCentraliserData`kernelGens,
	parabolic := sub<Generic(HG) |
	HG, HG`LargeReeInvolCentraliserData`normaliser`mat>,
	parabolicSLPs := Append(HG`LargeReeInvolCentraliserData`genSLPs,
	HG`LargeReeInvolCentraliserData`normaliser`slp)>;
    
    parabolicData`parabolic`RandomProcess :=
	RandomProcessWithWords(parabolicData`parabolic :
	WordGroup := WordGroup(parabolicData`parabolic));

    // Get Sz x (q-1)
    CG, compSLPsG := getComplement(parabolicData`parabolic,
	parabolicData`parabolicSLPs,
	parabolicData`o2Base,
	HG`LargeReeInvolCentraliserData`normaliser, wordGroup);

    // Get Sz
    CS, slpList := DerivedGroupMonteCarlo(CG);
    CS_slps := Evaluate(slpList, compSLPsG);
    
    assert forall{x : x in Generators(CS) |
	x^HG`LargeReeInvolCentraliserData`normaliser`mat eq x};
    
    // Split up Sz to get 4-dim natural
    MCS := GModule(CS);
    SM4 := rep{f[1] : f in ConstituentsWithMultiplicities(MCS) |
	Dimension(f[1]) eq 4 and f[2] eq 4};
    CS4 := ActionGroup(SM4);

    // Recognise Sz
    flag := RecogniseSz(CS4 : Verify := false, FieldSize := q);
    assert flag;

    // Add parabolic data
    parabolicData`szCyclic := CG;
    parabolicData`szCyclicSLPs := compSLPsG;
    parabolicData`sz := CS;
    parabolicData`szSLPs := CS_slps;
    parabolicData`smallSZ := CS4;
    parabolicData`slpMap :=hom<WordGroup(CS4) -> CS | UserGenerators(CS)>;
    parabolicData`slpCoercion := hom<WordGroup(CS4) -> wordGroup | CS_slps>;   
    return parabolicData;
end function;

// Use a subtle application of The Formula to conjugate a to b
// G is [q^10] : (q - 1) and a,b are of order (dividing) q-1
// G lies in the centraliser of invol
function TheFormulaMapping(G, a, b, invol)
    local d_a, d_b, j, c, h, n;
    
    // Both should have the same order, dividing q-1
    n := Order(a`mat);
    assert Order(b`mat) eq n;

    // Need to make the elements equal up to inverse modulo [q^10]
    d_a := LargeReeDiagonalisation(a`mat);
    d_b := LargeReeDiagonalisation(b`mat);
    j := Log(d_a[2, 2], d_b[2, 2]);

    if j lt 0 then
	return false, _;
    end if;
    
    // Sanity check
    assert invol`mat^(a`mat^j * b`mat^(-1)) eq invol`mat or
	invol`mat^(a`mat^j * b`mat) eq invol`mat;

    // Invert one element to obtain correct version
    if invol`mat^(a`mat^j * b`mat^(-1)) ne invol`mat then
	b`mat ^:= -1;
	b`slp ^:= -1;
    end if;
    
    assert invol`mat^(a`mat^j * b`mat^(-1)) eq invol`mat;
    assert IsDivisibleBy(4, Order(a`mat^j * b`mat^(-1)));
    assert GCD(j, n) eq 1;    
    assert Order(a`mat^j) eq n;

    // Need to take the power from discrete log in order for elements to be
    // conjugate
    c := rec<MatSLP | mat := a`mat^j, slp := a`slp^j>;

    // Initialise conjugator
    h := rec<MatSLP | mat := Identity(G), slp := Identity(Parent(a`slp))>;

    // Iteratively conjugate 
    // After each step, c conjugates a -> b modulo the Frattini subgroup of
    // the group in previous step
    // The group in the first step is O_2(G)
    i := 0;
    repeat
	// This is "The Formula"
	g := rec<MatSLP | mat := c`mat * (b`mat * c`mat)^((n - 1) div 2),
	    slp := c`slp * (b`slp * c`slp)^((n - 1) div 2)>;

	// Next starting element
	c := rec<MatSLP | mat := c`mat^g`mat, slp := c`slp^g`slp>;
	
	// Update conjugator
	h := rec<MatSLP | mat := h`mat * g`mat, slp := h`slp * g`slp>;
	i +:= 1;
    until c`mat eq b`mat;

    vprint LargeReeConjugacy, 5 : "Nr elementary abelian layers", i;
    return true, rec<MatSLP | mat := h`mat^(-1), slp := h`slp^(-1)>;
end function;

// Finds a copy of Sz \wr 2 inside G = LargeRee
//
// First find an Sz involution, and its centraliser and corresponding parabolic
// Then pick out the Sz from the parabolic using The Formula
// Finally use another Formula trick to conjugate the Sz to another Sz, while
// staying inside an Sz x Sz, hence obtaining the wreathing 2
procedure findSzWreath2(G)
    
    q := #CoefficientRing(G);
    F := CoefficientRing(G);

    assert assigned G`RandomProcess; 
	
    vprint LargeReeConjugacy, 5 : "Find Sz involution";
    invol, slp := LargeReeSzInvolution(G : Randomiser := G`RandomProcess,
	CheckInput := false);

    vprint LargeReeConjugacy, 5 : "Find involution centraliser";
    involCent := LargeReeInvolutionCentraliser(G, invol, slp :
	CheckInput := false, Randomiser := G`RandomProcess);

    // Now we have also found a parabolic
    // Use The Formula to find an Sz inside
    // Also recognise Sz and store parabolic data for later use
    G`LargeReeSzParabolicData := findSzInParabolic(involCent, WordGroup(G), q);
    G`LargeReeSzParabolicData`parabolic`Order := q^10 * #Sz(q) * (q - 1);

    repeat
	// Find stabiliser of a point inside 4-dim Sz in parabolic
	SZ_point := SuzukiFindOvoidPoints(G`LargeReeSzParabolicData`smallSZ :
	    CheckInput := false,
	    Randomiser := G`LargeReeSzParabolicData`smallSZ`RandomProcess);
	SZ_stab_dim4 := SuzukiStabiliser(G`LargeReeSzParabolicData`smallSZ,
	    SZ_point : CheckInput := false,
	    Randomiser := G`LargeReeSzParabolicData`smallSZ`RandomProcess);
	
	// Map 4-dim stabiliser to 26-dim Sz
	// Also coerce SLPs to Big Ree slp group
	W_SZ_dim4 := WordGroup(G`LargeReeSzParabolicData`smallSZ);
	W := WordGroup(G);
	SZ_stab_dim4_slps := [W_SZ_dim4 ! w[1] : w in SZ_stab_dim4];
	SZ_stab_gens := Evaluate(SZ_stab_dim4_slps,
	    UserGenerators(G`LargeReeSzParabolicData`sz));
	SZ_stabSLPs := Evaluate(SZ_stab_dim4_slps,
	    G`LargeReeSzParabolicData`szSLPs);
	
	vprint LargeReeConjugacy, 5 : "Find involution in Sz parabolic";
	
	assert Evaluate(SZ_stabSLPs, UserGenerators(G)) eq SZ_stab_gens;
	assert Order(SZ_stab_gens[1] : Proof := false) eq 4 and
	    Order(SZ_stab_gens[2] : Proof := false) eq q - 1;
	
	involSZ := SZ_stab_gens[1]^2;
	involSZ_slp := SZ_stabSLPs[1]^2;
	
	// Now we have the following two involutions
	x1 := rec<MatSLP | mat := invol, slp := slp>;
	x2 := rec<MatSLP | mat := involSZ, slp := involSZ_slp>;
	
	// We also have the following q-1 elements
	y1 := involCent`LargeReeInvolCentraliserData`normaliser;
	y2 := rec<MatSLP | mat := SZ_stab_gens[2], slp := SZ_stabSLPs[2]>;
	
	// We conjugate (x1, y1) -> (x2, y3) using dihedral trick
	xi := DihedralTrick(x1, x2, G`RandomProcess : MaxTries := q);
	y3 := rec<MatSLP | mat := y1`mat^xi`mat, slp := y1`slp^xi`slp>;
	
	// Then we want to conjugate (x2, y3) -> (x2, y2)
	// use Formula to do this
	
	assert Evaluate([x1`slp, x2`slp, y1`slp, y2`slp, y3`slp],
	    UserGenerators(G)) eq [x1`mat, x2`mat, y1`mat, y2`mat, y3`mat];
	
	// Neither y2 nor y3 centralises x2, but they centraliser x1
	assert x2`mat^y2`mat ne x2`mat and x2`mat^y3`mat ne x2`mat;
	
	// Conjugate y3 to y2, while fixing x2
	vprint LargeReeConjugacy, 5 : "Conjugate q-1's using The Formula";
	flag, gamma := TheFormulaMapping(G, y2, y3, x2);
    until flag;
    
    assert x2`mat^gamma`mat eq x2`mat;

    // Now we have conjugated (x1, y1) -> (x2, y2)
    // and hence also the Sz's that contain them
    conj := rec<MatSLP | mat := xi`mat * gamma`mat,
	slp := xi`slp * gamma`slp>;
    assert Evaluate(conj`slp, UserGenerators(G)) eq conj`mat;

    // This is our Sz \wr 2
    SZ_2 := sub<Generic(G) | UserGenerators(G`LargeReeSzParabolicData`sz),
	conj`mat>;
    SZ_2_slps := Append(G`LargeReeSzParabolicData`szSLPs, conj`slp);

    // Get other Sz which commutes with first
    SZ_conj := sub<Generic(G) | [x^(conj`mat^(-1)) :
	x in UserGenerators(G`LargeReeSzParabolicData`sz)]>;
    SZ_conj_slps := [x^(conj`slp^(-1)) :
	x in G`LargeReeSzParabolicData`szSLPs];  
    assert forall{<x, y> : x in UserGenerators(G`LargeReeSzParabolicData`sz),
	y in UserGenerators(SZ_conj) | x^y eq x};

    // The first Sz is already recognised
    // Now recognise other Sz
    
    // Split up Sz module to obtain natural module
    M_SZ := GModule(SZ_conj);
    SZ_natural := rep{f[1] : f in ConstituentsWithMultiplicities(M_SZ) |
	Dimension(f[1]) eq 4 and f[2] eq 4};
    SZ_dim4 := ActionGroup(SZ_natural);

    vprint LargeReeConjugacy, 5 : "Recognise Sz";
    flag := RecogniseSz(SZ_dim4 : Verify := false, FieldSize := q);
    assert flag;
    
    SZ_2`Order := (#Sz(q))^2 * 2;
    vprint LargeReeConjugacy, 5 : "Found Sz \wr 2";
    
    G`LargeReeSzWreath2Data := rec<LargeReeSzWreath2Info | 
	group := SZ_2, slps := SZ_2_slps,
	sz1 := G`LargeReeSzParabolicData`sz, sz2 := SZ_conj,
	sz1small := G`LargeReeSzParabolicData`smallSZ, sz2small := SZ_dim4,
	sz1slps := G`LargeReeSzParabolicData`szSLPs, sz2slps := SZ_conj_slps,
	conj := conj,
	slpMap1 := hom<WordGroup(G`LargeReeSzParabolicData`smallSZ) ->
    G`LargeReeSzParabolicData`sz |
	UserGenerators(G`LargeReeSzParabolicData`sz)>,
	slpMap2 := hom<WordGroup(SZ_dim4) -> SZ_conj |
    UserGenerators(SZ_conj)>,
	slpCoercion1 := hom<WordGroup(G`LargeReeSzParabolicData`smallSZ) ->
    WordGroup(G) | G`LargeReeSzParabolicData`szSLPs>,
	slpCoercion2 := hom<WordGroup(SZ_dim4) -> WordGroup(G) | SZ_conj_slps>
    >;
end procedure;

// G and S are Big Ree groups with intersection containing Sz x Sz
// Find conjugating element from G to S by solving equations coming from
// the preserved quadratic forms
function conjugationCommonSzWreath2(G, S, SZ)
    local F, M, E, form, quad, stdForm, stdQuad, P, R, MR, VP, MA, constTerm,
	coeffs, eqnVector, eqns, polys, variety, conj, GG, eqnSpace;
    
    F := CoefficientRing(G);
    M := GModule(SZ);
    E := EndomorphismAlgebra(M);
    assert Dimension(E) eq 3;

    // Obtain bilinear and quadratic forms of input and standard copy
    flag, form := SymmetricBilinearForm(G);
    assert flag;
    flag, quad := QuadraticForm(G);
    assert flag;
    flag, stdForm := SymmetricBilinearForm(S);
    assert flag;
    flag, stdQuad := QuadraticForm(S);
    assert flag;
    
    P := PolynomialAlgebra(F, Dimension(E));
    MR := MatrixAlgebra(P, Degree(G));
    VP := KMatrixSpace(F, Rank(P) + 1, Rank(P) + 1);
    MA := MatrixAlgebra(F, Rank(P) + 1);

    // Get constant term of polynomial
    constTerm := hom<P -> F | [0 : i in [1 .. Rank(P)]]>;

    // Convert 2-degree polynomial to matrix space element
    // similar to SymmetricBilinearForm(RngMPolElt)
    coeffs := hom<P -> VP | x :->
    &+[Coefficient(Coefficient(x, i, 1), j, 1) *
	MatrixUnit(MA, i, j) : i in [1 .. Rank(P)],
	j in [1 .. Rank(P)] | j gt i] +
	&+[Coefficient(x, i, 2) * MatrixUnit(MA, i, i) : i in [1 .. Rank(P)]] +
	constTerm(x) * MatrixUnit(MA, Rank(P) + 1, Rank(P) + 1)>;

    // Convert matrix space element back to polynomial
    eqnVector := hom<VP -> P | b :-> &+[b[i, j] * P.i * P.j :
    i in [1 .. Rank(P)], j in [1 .. Rank(P)] | j ge i] +
	b[Rank(P) + 1, Rank(P) + 1]>;
    
    // This matrix conjugates G to S, for some values of P.i
    // We want to find these values
    A := &+[P.i * (MR ! E.i) : i in [1 .. Dimension(E)]];

    // Obtain equations for P.i from the quadratic forms
    // Every entry of A gives one equation
    eqns := {P | };
    eqns := SequenceToSet(ElementToSequence(A * (MR ! stdForm) * Transpose(A) -
	(MR ! form))) join
	SequenceToSet(ElementToSequence(normaliseQuadForm(A * (MR ! stdQuad) *
	Transpose(A) - (MR ! quad))));
    
    // Remove trivial equation
    Exclude(~eqns, P ! 0);

    vprint LargeReeConjugacy, 3 : "Number of equations", #eqns;
    assert forall{e : e in eqns | TotalDegree(e) eq 2};

    // Get vector space of equations
    eqnSpace := sub<VP | coeffs(eqns)>;
        
    vprint LargeReeConjugacy, 3 : "Equation space dimension",
	Dimension(eqnSpace);

    // Take only the equations corresponding to a basis
    // Solve the equations
    polys := ideal<P | eqnVector(Basis(eqnSpace))>;
    variety := Variety(polys);
    vprint LargeReeConjugacy, 3 : "Number of solutions", #variety;
    assert #variety le 2;
    
    goodSols := {@ Generic(G) ! B :
	coeffs in variety | not IsZero(Determinant(B))
	where B is EvaluateMatTup(A, coeffs) @};
    vprint LargeReeConjugacy, 3 : "Nof non-singular solutions", #goodSols;

    if LargeReeStandardRecogniser(G^goodSols[1]) then
	return goodSols[1];
    else
	return goodSols[2];
    end if;
end function;
