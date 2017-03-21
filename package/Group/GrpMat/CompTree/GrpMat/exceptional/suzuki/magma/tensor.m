/******************************************************************************
 *
 *    tensor.m  Finding tensor decompositions of Sz(q)
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik Bäärnhielm
 *    Dev start : 2005-01-24
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: tensor.m 1605 2008-12-15 09:05:48Z jbaa004                     $:
 *
 *****************************************************************************/

freeze;

/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiTensor, 10;

import "../../../Smash/functions.m" :
    SetTensorBasis, SetTensorFactors, SetTensorProductFlag;
import "../../../Tensor/is-tensor.m" : ConstructTensorFactors;
import "../../../Tensor/find-point.m" : GeneralFindPoint;

forward twistedTensorProduct, tensorDecompose,
    tensorDecomposeBackup, getEigenvalues, findBaseValues;
import "suzuki.m" : SuzukiReductionMaps, SuzukiReductionFormat,
    SuzukiTensorData;
import "../../../util/tensor.m" : ScaledTensorFactors;
import "../../../util/basics.m" : MatSLP;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SuzukiTensorDecompose(G :: GrpMat :
    Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    CheckInput := true, FieldSize := 0) -> Map, GrpMatElt
    { G \leq GL(d, q) is isomorphic to Sz(q), with d > 4. Return an isomorphism
    to Sz(q). }
    local conjugator, decomposer, factors, homo1, homo2, genImages1,
	genImages2, q, flag, cb, G_orig, szFactor, otherFactor, fieldExt,
	sz1, sz2, iso1, iso2, m, n;

    if CheckInput then
	flag, q := SuzukiRecognition(G);
	if not flag then
	    error "Sz tensor decompose: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz tensor decompose: Field size must be greater than 2";
	end if;
	
	if not (bool and prime eq 2 and IsOdd(degree) and
	    IsDivisibleBy(FieldSize, #CoefficientRing(G))
	    where bool, prime, degree is IsPrimePower(FieldSize)) then
	    error "Sz tensor decompose: Field size must be an odd power of 2",
		"at least 8, and divisible by field size of G";
	else
	    q := FieldSize;
	end if;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    G_orig := G;

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
	fieldExt := hom<G -> G | x :-> x>;
    end if;
    
    field := CoefficientRing(G);
    assert q eq #field;
    m := (Degree(field) - 1) div 2;
    n := Floor(Log(4, Degree(G)));

    // According to our conjecture, the main tensor decomposition works if
    // m \geq n. Otherwise use permutation techniques.
    if m ge n then
	flag, cb := tensorDecompose(G);

	if not flag then
	    flag, cb := tensorDecomposeBackup(G);
	end if;
    else
	flag, cb := tensorDecomposeBackup(G);
    end if;
    
    if flag then
	smallDim := cb[2];
	decomposer := cb[1];

	// Get tensor factors of determinant 1
	factor1, factor2 := ScaledTensorFactors(G, cb);
	factors := [factor1, factor2];
	vprint SuzukiTensor, 10: factors;

	// Get 4-dim tensor factor and make sure it has determinant 1
	assert exists{f : f in factors | Degree(f) eq 4};
	
	factor := rep{i : i in [1 .. #factors] |
	    Degree(factors[i]) eq 4};
	otherFactor := factor eq 1 select 2 else 1;
	
	// Create homomorphism to (conjugate of) natural representation
	homo1 := hom<G_orig -> Generic(factors[factor]) |
	x :-> Generic(factors[factor]) ! scaled
	    where _, scaled is ScaleMatrix(subMatrix[factor])
	    where bool, subMatrix is
	    IsProportional(Function(fieldExt)(x)^decomposer, smallDim)>;

	homo2 := hom<G_orig -> Generic(factors[otherFactor]) |
	x :-> Generic(factors[otherFactor]) ! scaled
	    where _, scaled is ScaleMatrix(subMatrix[otherFactor])
	    where bool, subMatrix is
	    IsProportional(Function(fieldExt)(x)^decomposer, smallDim)>;

	// Images of input generators in natural representation
	genImages1 := [Function(homo1)(G_orig.i) :
	    i in [1 .. NumberOfGenerators(G_orig)]];	
	genImages2 := [Function(homo2)(G_orig.i) :
	    i in [1 .. NumberOfGenerators(G_orig)]];

	// Standard copy and explicit isomorphisms
	sz1 := sub<Generic(factors[factor]) | genImages1>;
	sz2 := sub<Generic(factors[otherFactor]) | genImages2>;
	iso1 := hom<G_orig -> sz1 | x :-> Generic(sz1) ! Function(homo1)(x)>;
	iso2 := hom<G_orig -> sz2 | x :-> Generic(sz2) ! Function(homo2)(x)>;
	
	G_orig`SuzukiReductionData := rec<SuzukiReductionFormat |
	    maps := rec<SuzukiReductionMaps | tensor := iso1>,
	    tensorCBM := decomposer>;

	vprint SuzukiTensor, 1: "Tensor decomposition successful";
	return iso1, decomposer, rec<SuzukiTensorData | maps := [iso1, iso2],
	    tensorCBM := decomposer>;
    else
	vprint SuzukiTensor, 1: "No tensor decomposition";
	error "Suzuki tensor decomposition failed!";
    end if;
end intrinsic;

intrinsic SuzukiIrreducibleRepresentation(F :: FldFin,
    twists :: SeqEnum[RngIntElt] : CheckInput := true,
    Gens := UserGenerators(Sz(F))) -> GrpMat
    { F has size q = 2^(2 * m + 1), m > 0, and twists is a sequence of n
    distinct integers in the range [0 .. 2m].

    Return an absolutely irreducible representation of Sz(q) of dimension 4^n,
    a tensor product of twisted powers of the standard copy, where the twists
    are given by the input sequence. }
    local H, G, factors, dims, m;
    
    if CheckInput then
	if not (Characteristic(F) eq 2 and IsOdd(Degree(F)) and #F gt 2) then
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

    G := sub<GL(4, F) | Gens>;
    factors := [GModule(G)];
    M := TrivialModule(G, F);
    
    // Accumulate twisted versions of the group
    for j in [1 .. #twists] do
	N := FrobeniusImage(factors[1], G, twists[j]);
	M := TensorProduct(M, N);
    end for;

    return ActionGroup(M);
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

// Store information about tensor decomposition
procedure StoreDetails(G, Result)
    local CB, U, W, scalar, M1, M2;
    
    CB := Result[1];
    SetTensorProductFlag(G, true);
    SetTensorBasis(G, CB);
    U, W := ConstructTensorFactors(G, Result);
    assert Degree(W) eq 4 or Degree(U) eq 4;
    if Degree(W) eq 4 then
	SetTensorFactors(G, [U, W]);
    else
	SetTensorFactors(G, [W, U]);
    end if;
end procedure;

// Special case of tensor decomposition, using permutation techniques
// and checks all possible twists
function tensorDecomposeCheckTwists(G)
    local field, H, permGroup1, permGroup2, permHomo1, permHomo2, status,
	iso, iso1, iso2, mod1, mod2, HH, GG, m, baseDegree, decomposeLen, g, q;

    field := CoefficientRing(G);
    q := #field;
    m := (Degree(field) - 1) div 2;
    assert assigned G`RandomProcess;
    
    vprint SuzukiTensor, 2: "Get standard generators in dim 4";

    // Construct standard copy
    _, _, stdgens := SuzukiStandardGeneratorsNaturalRep(m);
    H := sub<GL(4, field) | stdgens>;
        
    vprint SuzukiTensor, 2: "Get standard generators";
    
    // Find standard generators in input copy
    gens, slps := SzBlackBoxGenerators(G, field);

    // Switch generators of G, so that module isomorphism works
    GG := sub<Generic(G) | gens>;
    mod1 := GModule(GG);
        
    // Generate all possible twists
    vprint SuzukiTensor, 4: "Getting all possible twists";
    baseDegree := Degree(H);
    flag, decomposeLen := IsPowerOf(Degree(G), baseDegree);
    assert flag;
    
    twists := CartesianPower([0 .. 2 * m], decomposeLen);
    assert #twists eq (2 * m + 1)^(decomposeLen);
    
    // Check each twist until we find the correct one
    for tuple in twists do
	vprint SuzukiTensor, 6: "Checking twist:", tuple;
	
	// Construct twisted version of standard Sz
	HH := SuzukiIrreducibleRepresentation(field,
	    [tuple[i] : i in [1 .. #tuple]] : CheckInput := false,
	    Gens := UserGenerators(H));
	mod2 := GModule(HH);
	
	// Check if this is the correct twist
	status, g := IsIsomorphic(mod1, mod2);
	if status then
	    StoreDetails(G, <Generic(GG) ! g, Degree(H)>);
	    return true, <TensorBasis(G), Degree(H)>;
	end if;
    end for;

    return false, _;
end function;

// Backup strategy when eigenvalue approach fails
function tensorDecomposeBackup(G)
    local degreePower, status;
    
    degreePower := Floor(Log(4, Degree(G)));
    vprint SuzukiTensor, 4: "Use permutation techniques";
    flag, status := tensorDecomposeCheckTwists(G);
    if flag then
	return true, status;
    end if;
    
    vprint SuzukiTensor, 4: "Use general method";
    if GetVerbose("SuzukiTensor") gt 0 then
	SetVerbose("Tensor", 1);
    end if;
    status := IsTensor(G : Factors := [[4, 4^(degreePower - 1)],
	[4^(degreePower - 1), 4]]);
    SetVerbose("Tensor", 0);
    if status cmpeq true then
	return true, <TensorBasis(G), 4>;
    end if;

    vprint SuzukiTensor, 4: "Backup approaches failed";
    return false, _;
end function;

// Calculate all eigenvalues, given a sequence of base values
function getEigenvalues(baseValues, t)
    local candidates, lastValue, lastCandidates;
    
    candidates := {One(field)} where field is Parent(Rep(baseValues));

    // Add products of next value and all previous eigenvalues
    for value in baseValues do
	lastValue := value;
	lastCandidates := candidates;
	
	candidates := {* d * c : c in candidates, d in
	    {e, e^(-1), e^(t + 1), e^(-(t + 1))} *} where e is value;
    end for;
    
    return candidates, lastValue, lastCandidates;
end function;

// Heuristic for finding a short sequence of base values
function findBaseValues(eigenvalues, m, degreePower)
    local products, values, baseValues, values2, vals2,
	subs, cross, t;

    n := degreePower;
    t := 2^(m + 1);
    newBaseVals := {};
    eigProds := {@ Sqrt(e / f) : e in eigenvalues,
	f in eigenvalues | e ne f @};

    // Use initial heuristic for picking out base valuse
    // For most modules this is sufficient
    for i in [1 .. #eigProds] do
	x := eigProds[i];
	if forall{e : e in eigenvalues |
	    exists{y : y in {x, x^(-1), x^(t + 1), x^(-t-1)} | 
	    {f * x, f / x, f * x^(t + 1), f / x^(t + 1)} subset eigenvalues
	    where f is e / y}} and x notin newBaseVals then
	    Include(~newBaseVals, x);
	end if;
    end for;

    // We might have to try harder
    baseValues := newBaseVals;
    if #baseValues gt 2 * n then
	candidates := {@ @};
	for x in baseValues do
	    testCandidates := {x};
	    while #testCandidates lt n do
		if exists(y){y : y in baseValues, k in [1 .. 2 * m] |
		    y eq x^(2^k) and y notin testCandidates} then
		    Include(~testCandidates, y);
		else
		    break;
		end if;
	    end while;
	    if #testCandidates eq n then
		Include(~candidates, x);
	    end if;
	end for;
    else
	candidates := baseValues;
    end if;
    
    // Finally make sure that inverses are not included
    subs := {};
    for e in candidates do
	if e^(-1) notin subs then
	    Include(~subs, e);
	end if;
    end for;
    baseValues := subs;
    
    // Conjecture is that this produces a short sequence of base values
    vprint SuzukiTensor, 5 : "Post base vals:", #baseValues, n;    
    return baseValues;
end function;

// Tensor decomposition main function
function tensorDecompose(G)
    local g, eigenvalues, products, values, field, m, baseValues, q,
	degreePower, candidateValues, candidates, lastCandidate,
	lastCandidates, pointValues, pointSpace, CB, Status;
    
    field := CoefficientRing(G);
    q := #field;
    m := (Degree(field) - 1) div 2;
    t := 2^(m + 1);
    s := 2^m;
    degreePower := Floor(Log(4, Degree(G)));
    assert assigned G`RandomProcess;

    /* The approach is to construct a point or a line in the projective
     * geometry given by the tensor decomposition. We do this by using 
     * eigenspaces, and an element of order q - 1 has 4 eigenspaces of 
     * dimension 1 in the natural representation.
     */
     
     vprint SuzukiTensor, 5: "Finding element";
     flag, g := RandomElementOfOrder(G, q - 1 : MaxTries := q^2,
	 Randomiser := G`RandomProcess);
     assert flag;
    
     vprint SuzukiTensor, 5: "Checking eigenvalues";

     eigenvalues := {* e[1]^^e[2] : e in Eigenvalues(g) *};
     baseValues := findBaseValues(eigenvalues, m, degreePower);
     
     candidateValues := Subsets(baseValues, degreePower);
     vprint SuzukiTensor, 3: "Basevalues:", #baseValues,
	 "Candidates:", #candidateValues;
     
     for subs in candidateValues do
	 candidates, lastValue, lastCandidates :=
	     getEigenvalues(subs, t);
	      
	 // Check if we have found the right eigenvalues, ie the right
	 // base values
	 if candidates eq eigenvalues then
	     
	     // It is possible that certain base values can give us a
	     // line but not others, so we need to calculate the
	     // eigenvalues in different order
	     valueList := SetToSequence(subs);
	     for i in [1 .. #valueList] do
		      
		 // Calculate candidate line flat
		 pointValues :=
		     {lastValue * c : c in lastCandidates} join
		     {lastValue^(-1) * c : c in lastCandidates};
		 pointSpace := &+[Eigenspace(g, v) :
		     v in pointValues];
		 
		 // Check if we have actually found a line
		 if Dimension(pointSpace) eq
		     2 * 4^(degreePower - 1) then
		     break;
		 end if;
		 
		 vprint SuzukiTensor, 6: "Rotating base values";
		 
		 // Change order of base values
		 Rotate(~valueList, 1);
		 candidates, lastValue, lastCandidates :=
		     getEigenvalues(valueList, t);
	     end for;
	      
	     // If no point or line was found, revert to brute force
	     // tensor decomposition
	     if  Dimension(pointSpace) notin {2 * 4^(degreePower - 1),
		 4^(degreePower - 1)} then

		 vprint SuzukiTensor, 6: "Eigenvalue approach failed";
		 return false, "unknown", #baseValues;
	     end if;
	     
	     vprint SuzukiTensor, 6: "Point/line found!";
	     
	     // Send point/line to tensor decomposition
	     CB := "unknown";
	     Status := false;
	     GeneralFindPoint(G, ~pointSpace, 4^(degreePower - 1),
		 ~Status, ~CB);
	     assert Status;
	     StoreDetails(G, CB);
	     return true, CB, #baseValues;
	 end if;
     end for;
     return false, "unknown", #baseValues;
 end function;
