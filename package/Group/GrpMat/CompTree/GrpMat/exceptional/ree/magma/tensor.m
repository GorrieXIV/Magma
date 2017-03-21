/******************************************************************************
 *
 *    tensor.m  Ree group package
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm
 *    Dev start : 2005-05-29
 *
 *    Version   : $Revision:: 3068                                           $:
 *    Date      : $Date:: 2015-03-01 12:09:26 +1100 (Sun, 01 Mar 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: tensor.m 3068 2015-03-01 01:09:26Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose ReeTensor, 10;

forward getPointDim, StoreDetails, getTensorBasis, getPointValues,
    tensorDecomposeBackup, tensorDecomposeCheckTwists,
    tensorDecomposeRandomHom,
    getIrreducibleModuleFactors, getEigenvalues, tensorDecomposeSubmodules;

import "../../../Smash/functions.m" :
    SetTensorBasis, SetTensorFactors, SetTensorProductFlag;
import "../../../Tensor/is-tensor.m" : ConstructTensorFactors;
import "../../../Tensor/find-point.m" : GeneralFindPoint;
import "../../../util/order.m" : RandomInvolution;
import "../../../util/tensor.m" : ScaledTensorFactors;
import "../../../util/section.m" : MeatAxeMaps;
import "../../../util/basics.m" : getMapFunction, MatSLP;

import "standard.m": getReeDiagonal;
import "ree.m": ReeReductionFormat, ReeReductionMaps,
    ReeTrivialRecognitionChecks;

// Prefix on error strings
ErrorHeader := "Ree tensor decompose:";

/*****************************************************************************/
/* TEST AND BENCHMARK FUNCTIONS                                              */
/*****************************************************************************/

function getRepresentation(G, twists)
    A := GModule(G);
    F := CoefficientRing(G);
    M := TrivialModule(G, F);
    
    // Accumulate twisted versions of the group
    for j in [1 .. #twists] do
	N := FrobeniusImage(A, G, twists[j]);
	M := TensorProduct(M, N);
    end for;

    return ActionGroup(M);
end function;

function goodTwist(m, twists)
    for i in [1 .. #twists] do
	flag := true;
	for j in [1 .. #twists] do
	    if IsDivisibleBy(twists[i] + m + 1 - twists[j], 2 * m + 1) then
		flag := false;
	    end if;
	end for;
	if flag then
	    return i;
	end if;
    end for;
    return 0;
end function;

function calculateEigenvalue(lambda, twists, tuple)
    return lambda^&+[3^twists[i] * tuple[i][1] : i in [1 .. #twists]];
end function;

procedure testEigenvalues(F, m, twists)
    lambda := PrimitiveElement(F);
    t := 3^m;
    n := #twists;
    d := 7^n;
    base := [<0, "0">, <t, "t">, <-t, "-t">, <t - 1, "t-1">, <1 - t, "1-t">, 
	     <2 * t - 1, "2t-1">, <1 - 2 * t, "1-2t">];
    powers := CartesianPower(base, n);
    eigs := {@ @};
    eigMulti := {* *};
    eigPowers := [];
    //numMatches := 0;
    for p in powers do 
	e := calculateEigenvalue(lambda, twists, p);
	Include(~eigMulti, e);
	newPowers := <x[2] : x in p>;
	if e in eigs then
	    idx := Index(eigs, e);
	    Append(~eigPowers[idx], newPowers);
	    //printf "%o matches %o\n", newPowers, oldPowers;
	    //numMatches +:= 1;
	else
	    Include(~eigs, e);
	    Append(~eigPowers, [newPowers]);
	end if;
    end for;
    //print eigMulti;
    print Multiplicities(eigMulti);
    print eigPowers;
    //printf "Num matches %o\n", numMatches;
end procedure;

procedure testTwist(F, m, twists, constructRep)
   q := #F;
   G := RandomConjugate(constructRep(twists));
   R := RandomProcessWithWords(G : Scramble := 1);
   flag, g := RandomElementOfOrder(G, q - 1 : Randomiser := R);
   assert flag;
   
   eigs := {* e[1]^^e[2] : e in Eigenvalues(g) *};
   good := goodTwist(m, twists);
   assert good gt 0;
   testEigenvalues(F, m, twists);

   printf "%o %o %o %o %o %o\n%o\n%o\n", m, 2 * m, Degree(G), q, 
	  #MultisetToSet(eigs),
	  good, 
	  <x : x in twists>, Multiplicities(eigs);
end procedure;

procedure testTwists(n, m, twists, testFun)
    if #twists eq n then
	testFun(twists);
    else	
        for k in [(twists[#twists] + 1) .. (2 * m - (n - #twists - 1))] do
	    testTwists(n, m, Append(twists, k), testFun);
	end for;
    end if;
end procedure;

intrinsic TestReeTensor() -> BoolElt
{ }

    for n in [1 .. 1] do	
	for m in [n + 1 .. 2 * n] do	    
	    F := GF(3, 2 * m + 1);
	    S := Ree(F);
	    twists := [0];
	    testFun := procedure(twists)
	        testTwist(F, m, twists, func<t | getRepresentation(S, t)>);
	    end procedure;
	    testTwists(n + 1, m, twists, testFun);
	end for;
    end for;

    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic ReeIrreducibleRepresentation(F :: FldFin,
    twists :: SeqEnum[SeqEnum[RngIntElt]] : CheckInput := true) -> GrpMat
    { F has size q = 3^(2 * m + 1), m > 0, and twists is a sequence of n
    distinct pairs of integers [i, j] where i is 7 or 27 and j is in the range
    [0 .. 2m].

    Return an absolutely irreducible representation of Ree(q),
    a tensor product of n twisted powers of the representation of dimension 7
    or 27, where the twists and dimensions are given by the input sequence. }
    local H, G, factors, dims;

    dims := {@ 7, 27 @};

    if CheckInput then
	if not (Characteristic(F) eq 3 and IsOdd(Degree(F)) and #F gt 3) then
	    error "|F| must be an odd power of 3, at least 27.";
	end if;
	if not #{x[2] : x in twists} eq #twists then
	    error "<twists> must consist of distinct twisting powers";
	end if;
	
	if not forall{i : i in twists | i[2] ge 0 and i[2] lt Degree(F) and
	    i[1] in dims} then
	    error "Elements of <twists> must be [i, j] where i is in [7, 27]",
		"and j is in the range [0 .. 2m]";
	end if;
    end if;
    
    factors := getIrreducibleModuleFactors(F);
    assert forall{i : i in [1 .. #factors] | Dimension(factors[i]) eq dims[i]};
    G := Ree(F);
    M := TrivialModule(G, F);
    
    // Accumulate twisted versions of the group
    for j in [1 .. #twists] do
	N := FrobeniusImage(factors[Index(dims, twists[j][1])],
	    G, twists[j][2]);
	M := TensorProduct(M, N);
    end for;

    return ActionGroup(M);
end intrinsic;

intrinsic ReeTensorDecompose(G :: GrpMat :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, FieldSize := 0, wordGroup := WordGroup(G)) ->
    Map, GrpMatElt
    { G \leq GL(d, q) is isomorphic to Ree(q), with d > 7. Return an
    isomorphism to a conjugate Ree(q). }
    local G_orig, fieldExt, q, recognition, m, t, field;
    
    if CheckInput then
	flag, q := ReeRecognition(G);
	if not flag then
	    error ErrorHeader, "G is not Ree";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 3) then
	    error ErrorHeader, "Field size must be greater than 3";
	end if;
	
	if not (bool and prime eq 3 and IsOdd(degree) and
	    IsDivisibleBy(FieldSize, #CoefficientRing(G))
	    where bool, prime, degree is IsPrimePower(FieldSize)) then
	    error ErrorHeader, "Field size must be an odd power of 3",
		"at least 27, and divisible by field size of G";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    G_orig := G;

    vprint ReeTensor, 3: "Extend field if necessary";

    if q gt #CoefficientRing(G) then
	// Extend to correct field
	extField := GF(q);
	Embed(CoefficientRing(G), extField);
	H, inc := ExtendField(Generic(G), extField);
	
	// Embed group in larger field
	G := sub<H | [inc(g) : g in UserGenerators(G)]>;
	fieldExt := hom<G_orig -> G | x :-> inc(x)>;
	
	G`RandomProcess :=
	    RandomProcessWithWords(G : WordGroup := WordGroup(G));
    else
	fieldExt := hom<G_orig -> G_orig | x :-> x>;
    end if;

    vprint ReeTensor, 3: "Get tensor basis";
    if getPointDim(Degree(G)) eq 7 then
	flag, cb := getTensorBasis(G);
    else
	if IsPowerOf(Degree(G), 27) then
	    vprint ReeTensor, 4: "Use hom-space method";
	    flag, cb := tensorDecomposeRandomHom(G, wordGroup);
	else
	    vprint ReeTensor, 4: "Use involution centraliser method";
	    flag, cb := tensorDecomposeSubmodules(G, wordGroup);
	end if;
    end if;
	    
    if not flag then
	vprint ReeTensor, 3: "Main approach failed. Using backup strategy";
	flag, cb := tensorDecomposeBackup(G);
    end if;
    
    if not flag then
	error ErrorHeader, "Tensor decomposition failed";
    end if;
    
    vprint ReeTensor, 3: "Getting scaled tensor factors";
    factor1, factor2 := ScaledTensorFactors(G, cb);
    factors := [factor1, factor2];
    
    decomposer := cb[1];
    smallDim := cb[2];
    
    // Get (2)7-dim tensor factor and make sure it has determinant 1
    assert #factors eq 2;
    assert exists{f : f in factors | Degree(f) eq smallDim};
    factor := Degree(factors[1]) eq smallDim select 1 else 2;
    otherFactor := factor eq 1 select 2 else 1;

    vprint ReeTensor, 3: "Constructing isomorphism";
	
    // Create homomorphism to (conjugate of) natural representation
    homo := hom<G_orig -> Generic(factors[factor]) |
    x :-> scaled where _, scaled is
	ScaleMatrix(Generic(factors[factor]) ! subMatrix[factor])
	where bool, subMatrix is
	IsProportional(Function(fieldExt)(x)^decomposer, smallDim)>;

    // Find generators for natural representation copy
    genImages := [Function(homo)(G_orig.i) :
	i in [1 .. NumberOfGenerators(G_orig)]];

    // Find (2)7-dim copy and explicit isomorphism
    ree := sub<Generic(factors[factor]) | genImages>;
    iso := hom<G_orig -> ree | x :-> Generic(ree) ! Function(homo)(x)>;
    
    G_orig`ReeReductionData := rec<ReeReductionFormat |
	maps := rec<ReeReductionMaps | tensor := iso>,
	tensorCBM := decomposer>;
    
    vprint ReeTensor, 1: "Tensor decomposition successful";
    return iso, decomposer;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Try to find a tensor basis (ie find a point) using the eigenvalue approach
// The conjecture is that this always works and is polynomial time except
// for some tensor products involving the 27-dim representation
function getTensorBasis(G)
    local field, m, t, g, eigenvalues, pointCandidates, CB, Status, point,
	pointDim, values;
    
    field := CoefficientRing(G);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 3^m;
    
    vprint ReeTensor, 5: "Finding random element";
    assert assigned G`RandomProcess;
    
    flag, g := RandomElementOfOrder(G, q - 1 : MaxTries := q,
	Randomiser := G`RandomProcess);
    assert flag;
    
    // No need to use multisets, since only interested in eigenspacecs
    eigenvalues := { e[1] : e in Eigenvalues(g) };
    pointCandidates := [* *];

    vprint ReeTensor, 5: "Finding possible points";
    
    pointDim, n := getPointDim(Degree(G));
    if pointDim eq 7 then
	vprint ReeTensor, 5: "No symmetric square present";
    else
	vprint ReeTensor, 5: "Some tensor factor is a symmetric square";
    end if;
    
    vprint ReeTensor, 5: "Nof factors", n;
    
    for e in eigenvalues do
	for pointDim in {7, 27} do
	    values := getPointValues(m, e^(3 * t), pointDim);

	    if values subset eigenvalues then
		vprint ReeTensor, 7: "Found valid subset";
		point := &+[Eigenspace(g, d) : d in values];
		
		vprint ReeTensor, 8: "Point dim", Dimension(point), pointDim;
		if Dimension(point) eq pointDim then
		    vprint ReeTensor, 7: "Found good candidate";
		    Append(~pointCandidates, <point, Dimension(point)>);
		end if;
	    end if;
	end for;
    end for;
    
    vprint ReeTensor, 9 : "Candidates", pointCandidates;
    
    for p in pointCandidates do
	// Send point/line to tensor decomposition
	CB := "unknown";
	Status := false;
	point := p[1];
	vprint ReeTensor, 4 : "Testing point", Dimension(point);
	GeneralFindPoint(G, ~point, p[2], ~Status, ~CB);
	if Status then
	    StoreDetails(G, CB);
	    return true, CB;
	end if;
    end for;
    
    return false, _;
end function;

function getPointValues(m, value, dim)
    local diag;
    
    diag := getReeDiagonal(m, value);
    if dim eq 7 then
	return SequenceToSet(diag);
    else
	eigs := { diag[i] * diag[j] : i in [1 .. #diag],
	    j in [1 .. #diag] | j ge i };
	return eigs;
    end if;
end function;
    
// Store information about tensor decomposition
procedure StoreDetails(G, Result)
    local CB, U, W, scalar, M1, M2;
    
    CB := Result[1];
    SetTensorProductFlag(G, true);
    SetTensorBasis(G, CB);
    U, W := ConstructTensorFactors(G, Result);
    assert Degree(W) in {7, 27} or Degree(U) in {7, 27};

    if Degree(W) eq 7 then
	SetTensorFactors(G, [U, W]);
    else
	SetTensorFactors(G, [W, U]);
    end if;
end procedure;

// Given dimension of module, return the dimension of a point: 7 if only
// 7-dim modules are involved and 27 otherwise. Also return number of
// tensor factors.
function getPointDim(dim)
    local factors, nofFactors, syms, naturals;
    
    factors := Factorization(dim);

    assert forall{x : x in factors | x[1] eq 3 or x[1] eq 7};
    naturals := IsDivisibleBy(dim, 7) select
	rep{x[2] : x in factors | x[1] eq 7} else 0;
    syms := IsDivisibleBy(dim, 3) select
	rep{x[2] div 3 : x in factors | x[1] eq 3} else 0;
    nofFactors := syms + naturals;
    
    if syms eq 0 then
	return 7, nofFactors;
    else
	return 27, nofFactors;
    end if;

end function;

// Special case of tensor decomposition, using permutation techniques
// and checks all possible twists
function tensorDecomposeCheckTwists(G)
    local field, H, permGroup1, permGroup2, permHomo1, permHomo2, status,
	iso, iso1, iso2, mod1, mod2, HH, GG, m, baseDegree, decomposeLen, g, q;

    field := CoefficientRing(G);
    q := #field;
    m := (Degree(field) - 1) div 2;
    assert assigned G`RandomProcess;
    
    H := Ree(field);

    // Get explicit isomorphism between input group and standard Ree
    
    vprint ReeTensor, 4: "Finding permutation representation 1";
    permHomo1, permGroup1 := ReePermutationRepresentation(G :
	CheckInput := false, Randomiser := G`RandomProcess, FieldSize := q);

    vprint ReeTensor, 4: "Finding permutation representation 2";
    permHomo2, permGroup2 := ReePermutationRepresentation(H :
	CheckInput := false, FieldSize := q);

    vprint ReeTensor, 4: "Finding permutation representations iso";
    status, iso := IsIsomorphic(permGroup2, permGroup1);
    assert status;
    iso2 := permHomo2 * iso * permHomo1^(-1);
    
    // Generate all possible twists
    vprint ReeTensor, 4: "Getting all possible twists";
    baseDegree := Degree(H);
    decomposeLen := Floor(Log(baseDegree, Degree(G)));

    // Include symmetric powers 1 and 2
    twists := CartesianPower(CartesianProduct([7, 27], [0 .. 2 * m]),
	decomposeLen);
    assert #twists eq (2 * m + 1)^(2 * decomposeLen);

    // Switch generators of G, so that they come in the right order
    GG := sub<GL(Degree(G), field) | [iso2(H.i) :
	i in [1 .. NumberOfGenerators(H)]]>;
    mod1 := GModule(GG);
    
    // Check each twist until we find the correct one
    for tuple in twists do
	vprint ReeTensor, 4: "Checking twist:", tuple;

	// Convert to sequences
	twist := [[tuple[j][1], tuple[j][2]] : j in [1 .. #tuple]];
	
	// Construct twisted version of standard Ree
	HH := ReeIrreducibleRepresentation(H, twist : CheckInput := false);
	mod2 := GModule(HH);
	
	// Check if this is the correct twist
	status, g := IsIsomorphic(mod1, mod2);
	if status then
	    StoreDetails(G, <GL(Degree(GG), field) ! g, Degree(H)>);
	    return true, <GL(Degree(GG), field) ! g, Degree(H)>;
	end if;
    end for;

    return false, _;
end function;

// Backup approach which tries to construct a point by looking at submodules
// of an involution centraliser. This seems to work in all cases when both
// a 7-dim and a 27-dim is involved, but not when only 27-dims are involved.
function tensorDecomposeSubmodules(G, wordGroup)

    V := VectorSpace(G);
    F := CoefficientRing(G);
    q := #F;
    
    assert assigned G`RandomProcess;
    vprint ReeTensor, 4: "Find involution";
    invol, slp := RandomInvolution(G : MaxTries := q,
	Randomiser := G`RandomProcess);

    vprint ReeTensor, 4: "Get involution centraliser";

    assert Degree(invol) eq Degree(G);
    assert not IsZero(Determinant(invol));
    H := ReeInvolutionCentraliser(G, invol, slp :
	Randomiser := G`RandomProcess, CheckInput := false);

    vprint ReeTensor, 4: "Found involution centraliser"; 
    MH := GModule(H);
    factors := CompositionFactors(MH);

    vprint ReeTensor, 4: "Found composition factors";

    // The centraliser won't have any 7-dim composition factors, since the
    // natural rep splits up as 3+4
    // First approach is to find a 27-dim among the composition factors
    // If this fails we try to add 3's and 4's to obtain a 7
    
    // Try to fin 27-dim
    dim27 := {x : x in factors | Dimension(x) eq 27};
    hom27 := {GHom(x, MH) : x in dim27};

    vprint ReeTensor, 6: "Checking 27-dim factors", hom27;
    submods := {};

    // Check only those 27's that are isomorphic to _unique_ submodules
    for homo in {x : x in hom27 | Dimension(x) eq 1} do
	N := Image(homo.1);

	// Add preimage of 27 in input module
	inc := Morphism(N, MH);
	if Dimension(N) eq 27 then
	    Include(~submods, sub<V | [V ! ElementToSequence(inc(v)) :
		v in Basis(N)]>);
	end if;
    end for;

    vprint ReeTensor, 4: "Found candidates", #submods;

    // See if some of the 27's are also points
    for p in submods do
	// Send point/line to tensor decomposition
	CB := "unknown";
	Status := false;
	point := p;
	
	vprint ReeTensor, 4 : "Testing point", Dimension(p);
	GeneralFindPoint(G, ~point, Dimension(p), ~Status, ~CB);
	if Status then
	    StoreDetails(G, CB);
	    return true, CB;
	end if;
    end for;

    vprint ReeTensor, 4: "Finding 3's and 4's";
    
    // Try to get at 7-dim space by adding a 3-dim and a 4-dim
    dim3 := {x : x in factors | Dimension(x) eq 3};
    dim4 := {x : x in factors | Dimension(x) eq 4};
    hom3 := {GHom(x, MH) : x in dim3};
    hom4 := {GHom(x, MH) : x in dim4};
    
    // Check only those factors that are isomorphic to _unique_ submodules
    // This seems always to work
    submods := {};
    for a in {x : x in hom3 | Dimension(x) eq 1} do
	for b in {x : x in hom4 | Dimension(x) eq 1} do

	    // Add preimages of 3's and 4's
	    vprint ReeTensor, 4: "Sum 3's and 4's";
	    N := Image(a.1) + Image(b.1);
	    
	    vprint ReeTensor, 4: "Find embedding", Dimension(N);
	    inc := Morphism(N, MH);

	    // Store candidate
	    if Dimension(N) eq 7 then
		vprint ReeTensor, 4: "Found candidate";
		Include(~submods, sub<V | [V ! ElementToSequence(inc(m)) :
		    m in Basis(N)]>);
	    end if;
	end for;
    end for;

    vprint ReeTensor, 4: "Found candidates", #submods;
    
    // See if any 7's are points
    for p in submods do
	// Send point/line to tensor decomposition
	CB := "unknown";
	Status := false;
	point := p;
	
	vprint ReeTensor, 4 : "Testing point", Dimension(p);
	GeneralFindPoint(G, ~point, Dimension(p), ~Status, ~CB);
	if Status then
	    StoreDetails(G, CB);
	    return true, CB;
	end if;
    end for;

    return false, _;
end function;

function findPSL2StdGens(G)

    F := CoefficientRing(G);
    q := #F;
    
    // Split up module and find a suitable non-trivial factor
    meatAxeData := MeatAxeMaps(G);
    goodFactors := [<i, Degree(H)> : i in [1 .. #meatAxeData] |
	Degree(H) gt 1 and IsAbsolutelyIrreducible(H) and
	not IsOverSmallerField(H) where H is meatAxeData[i]`image];
    assert #goodFactors ge 1;
    k := goodFactors[1][1];
    
    // Take smallest factor for efficieny
    Sort(~goodFactors, func<x, y | x[2] - y[2]>);
    H := meatAxeData[k]`image;

    // Recognise small PSL2
    flag, iso, inv := RecogniseSL2(H, q);
    assert flag;

    // Obtains SLPs in small PSL2
    W := WordGroup(H);
    g2slp := hom<H -> W | x :-> slp cmpeq false select false
    else W ! Evaluate(slp, [W.i : i in [1 .. NumberOfGenerators(W)]])
	where _, slp is SL2ElementToWord(H, x)>;

    // Maps small to big PSL2
    slpHomo := hom<H -> G | x :-> slp cmpeq false
    select false else meatAxeData[k]`slpMap(slp)
	where slp is Function(g2slp)(x)>;

    // Map standard generators from natural PSL2 up to big PSL2
    return [getMapFunction(inv * slpHomo)(g) :
	g in UserGenerators(Domain(inv))];
end function;

/* This approach is for decomposing a module of dimension 27^n
 * Here we find an involution centraliser C1 in the input copy
 * Then obtain a 27-dim rep of Ree, and find an involution C2 inside it
 * We constructively recognise the PSL(2,q) inside C1 and C2
 * Hence we standard generators of PSL(2,q) in two dimensions, and hence two
 * isomorphic modules M1 and M2 for PSL(2, q) correponding to C1 and C2
 *
 * The Hom-space of M2 has dim 5, and there exists a twist M2' of M2 such that
 * the Hom-space from M2' to M1 has dim 5.
 * The image of any invertible element from this Hom-space is a 27-dim subspace
 * of the input representation, and must be a point, by construction.
 */
 function tensorDecomposeRandomHom(G, wordGroup)
    V := VectorSpace(G);
    field := CoefficientRing(G);
    q := #field;
    
    assert assigned G`RandomProcess;
    vprint ReeTensor, 4: "Find involution in input copy";
    invol, slp := RandomInvolution(G : MaxTries := q,
	Randomiser := G`RandomProcess,
	Element := rec<MatSLP | mat := Identity(G),
	slp := Identity(wordGroup)>);

    assert Degree(invol) eq Degree(G);
    assert not IsZero(Determinant(invol));

    vprint ReeTensor, 4: "Get involution centraliser in input copy";
    centBig := ReeInvolutionCentraliser(G, invol, slp :
	Randomiser := G`RandomProcess, CheckInput := false);
    vprint ReeTensor, 4: "Found involution centraliser";
    
    G27 := ReeIrreducibleRepresentation(field, [[27, 0]]);
    G27`RandomProcess := RandomProcessWithWords(G27 :
	WordGroup := WordGroup(G27), Scramble := 1);
    
    vprint ReeTensor, 4: "Find involution in 27-dim copy";
    invol27, slp27 := RandomInvolution(G27 : MaxTries := q,
	Randomiser := G27`RandomProcess,
	Element := rec<MatSLP | mat := Identity(G27),
	slp := Identity(WordGroup(G27))>);
    
    assert Degree(invol27) eq Degree(G27);
    assert not IsZero(Determinant(invol27));

    vprint ReeTensor, 4: "Get involution centraliser in 27-dim copy";
    cent27 := ReeInvolutionCentraliser(G27, invol27, slp27 :
	Randomiser := G27`RandomProcess, CheckInput := false);    
    vprint ReeTensor, 4: "Found involution centraliser";

    // Move down to PSL2 from centraliser
    PSL_big := DerivedGroupMonteCarlo(centBig);
    PSL_small := DerivedGroupMonteCarlo(cent27);
    
    gensBig := findPSL2StdGens(PSL_big);
    gensSmall := findPSL2StdGens(PSL_small);
    vprint ReeTensor, 4: "Found standard gens";
    
    M1 := GModule(PSL_big, gensBig);
    M2 := GModule(PSL_big, gensSmall);

    // Check all twists, at least one will work
    for i in [0 .. Degree(field)] do
	M2 := FrobeniusImage(M2, PSL_big, i);
	
	homs := GHom(M2, M1);
	vprint ReeTensor, 4: "Found Hom space", Dimension(homs);
	
	if Dimension(homs) eq 5 then
	    break;
	end if;
    end for;
    assert Dimension(homs) eq 5;

    // Now there must be some homomorphism whose image is a point
    repeat
	// The homomorphism will be invertible with high probability
	repeat
	    homo := Random(homs);
	until Dimension(Kernel(homo)) eq 0;
	
	p := Image(homo);
	vprint ReeTensor, 4: "Found hom image", Dimension(p);
	assert Dimension(p) eq 27;
	
	// Send point/line to tensor decomposition
	CB := "unknown";
	Status := false;
	point := p;
	vprint ReeTensor, 4 : "Testing point", Dimension(p);
	GeneralFindPoint(G, ~point, Dimension(p), ~Status, ~CB);
	if Status then
	    StoreDetails(G, CB);
	    return true, CB;
	end if;
    until false;
end function;

// Backup strategy when eigenvalue approach fails
function tensorDecomposeBackup(G)
    local cb, status, deg, f1, f2;
    	
    vprint ReeTensor, 4: "Use permutation techniques";
    status, cb := tensorDecomposeCheckTwists(G);
    if status then
	return status, cb;
    end if;
    
    vprint ReeTensor, 4: "Use general method";
    if GetVerbose("ReeTensor") gt 0 then
	SetVerbose("Tensor", 1);
    end if;
    status := IsTensor(G);
    SetVerbose("Tensor", 0);
    f1, f2 := TensorFactors(G);
    deg := Min([Degree(x) : x in [f1, f2]]);
    if status cmpeq true then
	return <TensorBasis(G), deg>;
    end if;

    return false, _;
end function;

// Construct the basic irreducible modules of Ree, of dimensions 7 and 27
function getIrreducibleModuleFactors(field)
    local G, H, M, S, N;

    G := Ree(field);
    M := GModule(G);
    S := SymmetricSquare(M);
    
    // Get irreducible 27-dim submodule of symmetric square
    N := rep{x : x in Submodules(S) | Dimension(x) eq 27};    
    return [M, N];
end function;
