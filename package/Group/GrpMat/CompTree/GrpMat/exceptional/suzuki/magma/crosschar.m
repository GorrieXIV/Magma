/******************************************************************************
 *
 *    crosschar.m  Suzuki cross char constructive recognition
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2006-03-31
 *
 *    Version   : $Revision:: 3160                                           $:
 *    Date      : $Date:: 2015-11-02 09:56:37 +1100 (Mon, 02 Nov 2015)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: crosschar.m 3160 2015-11-01 22:56:37Z jbaa004                  $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiCrossChar, 10;

SzCrossCharInfo := recformat<
    defField : FldFin,
    conj : Rec,
    lambda : FldFinElt,
    lambdaLog : RngIntElt,
    stdGens : SeqEnum,
    stdSLPs : SeqEnum>;
    
declare attributes Grp : SzCrossCharData, RandomProcess;
declare attributes GrpMat : SzCrossCharData;

import "suzuki.m" : SuzukiReductionMaps, SuzukiReductionFormat, 
    BraySzRelations;
import "trick.m" : getStabiliser;
import "standard.m" : getSuzukiSylowGen, isOvoidPoint;
import "membership.m" : getInfMappingMatrix, getZeroMappingMatrix;
import "sylow.m" : cyclicSylowConjugation;

import "../../../util/basics.m" : MatSLP, DiagonaliseMatrix;;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/

function orderSuzukiEigenvalues(eigs, m)
    t := 2^(m + 1);

    perm := [];
    eigenvalues := SequenceToSet(eigs);
    lambda := rep{e : e in eigenvalues |
	{c^(2^m + 1), c^(-2^m), c^(-2^m - 1), c^(2^m)} eq eigenvalues
	where c is e^t};

    orderDiag := [e^(2^m + 1), e^(2^m), e^(-2^m), e^(-2^m - 1)]
	where e is lambda^t;
    perm := [Index(orderDiag, x) : x in eigs];
    assert SequenceToSet(perm) eq {1 .. 4};
    return perm;
end function;

intrinsic testSzBlackBox(m :: RngIntElt) -> BoolElt
    { }

    SetVerbose("SuzukiCrossChar", 5);

    F := GF(2, 2 * m + 1);
    q := #F;
    G := Sz(F);
    t := 2^(m + 1);
    
    
    c := PrimitiveElement(F);
    /*
    for i in [1 .. q - 1] do
	c := a^i;
	if Trace(c) eq 1 then
	    break;
	end if;
    end for;
    */
    
    
    x := getSuzukiSylowGen(F, 1, 1);

    // Diagonal element
    M2 := G ! DiagonalMatrix([c^(2^m + 1), c^(2^m), c^(-2^m),
	c^(-2^m - 1)]);

    // Anti-diagonal involution
    T := G ! PermutationMatrix(F, Reverse([1 .. 4]));

    gens := [x, M2, T];

    G := sub<Generic(G) | gens>;
    W := WordGroup(G);
    
    G`RandomProcess := RandomProcessWithWords(G : WordGroup := WordGroup(G));
    
    G`SzCrossCharData := rec<SzCrossCharInfo |
	defField := F,
	lambda := c,
	stdGens := UserGenerators(G),
	stdSLPs := UserGenerators(W)>;
    
    stdgens := UserGenerators(G);
    stdgens, slps := SzBlackBoxGenerators(G, F);
    
    assert IsSatisfied(BraySzRelations(F), stdgens);

    diag := DiagonaliseMatrix(stdgens[2] : OrderEigenvalues :=
	func<x | orderSuzukiEigenvalues(x, m)>);
    
    // Get eigenvalues in correct order
    
    eigs := Diagonal(diag);
    print eigs, Diagonal(M2);
    
    /*
    flag := RecogniseSz(G);

    c := G`SzCrossCharData`lambda;

    
    a := PrimitiveElement(F);
    print Log(a, c);
    // Diagonal element
    M2 := Generic(G) ! DiagonalMatrix([c^(2^m + 1), c^(2^m), c^(-2^m),
	c^(-2^m - 1)]);
    x := getSuzukiSylowGen(F, 1, 0);
    */
    /*
    R := sub<Generic(G) | x, M2>;
    S := sub<Generic(G) | stdgens[1], stdgens[2]>;

    conj := SuzukiMaximalSubgroupsConjugacy(G, S, R);
    */
    /*
    repr := SzClassRepresentative(G, stdgens[2]);
    print repr, M2, M2^(-1);
    print Log(c, repr[2, 2]^t);
    print MinimalPolynomial(c), MinimalPolynomial(repr[2, 2]^t);

    //print IsConjugate(G, stdgens[2], M2);
    flag, conj := SzIsConjugate(G, stdgens[2], M2);
    print flag;
    */
    
    /*
    print ((stdgens[1]^stdgens[2])^conj)[2, 1], (stdgens[1]^conj)[2, 1] * c,
	((stdgens[1]^stdgens[2])^conj)[3, 1],
	(stdgens[1]^conj)[3, 1] * c^(t + 1);
    read xx;
    */
    
    //G`SzCrossCharData`conj := rec<MatSLP | mat := conj, slp := Identity(W)>;

    for i in [1 .. 5] do
	g := Random(G`RandomProcess);
	/*
	if IsLowerTriangular(g * T) then
	    print T * g, g, g^T, g * T, Eigenvalues(g), Order(g);
	end if;
	*/
	flag, slp := SzBlackBoxMembership(G, g);
	assert flag;

	assert Evaluate(slp, UserGenerators(G)) eq g;
    end for;

    return true;
end intrinsic;

/*****************************************************************************/
/* MAIN INTRINSIC                                                            */
/*****************************************************************************/

intrinsic SuzukiOddCharacteristicReduction(G :: GrpMat : CheckInput :=
    true, Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    FieldSize := 0) -> Map
    { G is isomorphic to Sz(q) but is over a field of odd characteristic.
    Return isomorphism to Sz(q). }
    local flag, q, homo;

    if CheckInput then
	flag, q := SuzukiGeneralRecogniser(G);
	if not flag then
	    error "Sz CrossChar: G is not Sz";
	end if; 
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz CrossChar: Field size must be > 2";
	end if;
	if  not (flag and prime eq 2 and IsOdd(degree)
	    where flag, prime, degree is IsPrimePower(FieldSize)) then
	    error "Sz CrossChar: Field size must be an odd prime power";
	end if;

	q := FieldSize;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    homo := SuzukiSmallFieldReduction(G : CheckInput := false,
	FieldSize := q, Randomiser := G`RandomProcess);
    
    if not assigned G`SuzukiReductionData then
	G`SuzukiReductionData := rec<SuzukiReductionFormat |
	    maps := rec<SuzukiReductionMaps | crossChar := homo>>;
    else
	G`SuzukiReductionData`maps`crossChar := homo;
    end if;
    
    vprint SuzukiCrossChar, 5 : "Odd char reduction done";

    return homo;
end intrinsic;

intrinsic SuzukiSmallFieldReduction(G :: GrpMat : CheckInput :=
    true, Randomiser := RandomProcessWithWords(G : WordGroup := WordGroup(G)),
    FieldSize := 0) -> Map, Map
    { G is isomorphic to Sz(q) with q small (eg polynomial in the input).
    Return isomorphism to Sz(q). }
    local H, flag, field, q, iso, inv, prime, degree,
	ruleMap1, ruleMap2, sz, homo, f2, GP, f1, HP;

    if CheckInput then
	flag, q := SuzukiRecognition(G);
	if not flag then
	    error "Sz small field reduction: G is not Sz";
	end if;
    else
	if not (Category(FieldSize) eq RngIntElt and FieldSize gt 2) then
	    error "Sz small field reduction: Field size must be > 2";
	end if;
	if  not (flag and prime eq 2 and IsOdd(degree)
	    where flag, prime, degree is IsPrimePower(FieldSize)) then
	    error "Sz small field reduction:",
		"Field size must be an odd prime power";
	end if;

	q := FieldSize;
    end if;

    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;

    F := GF(q);
    m := (Degree(F) - 1) div 2;
    
    // Construct standard copy
    _, _, stdgens := SuzukiStandardGeneratorsNaturalRep(m);
    H := sub<GL(4, F) | stdgens>;
    H`RandomProcess := RandomProcessWithWords(H : WordGroup := WordGroup(H),
	Scramble := 1);
    
    // Find standard generators in input copy
    gens, slps := SzBlackBoxGenerators(G, F);
    GS := sub<Generic(G) | gens>;
    GS`SzCrossCharData := G`SzCrossCharData;
    GS`SzCrossCharData`stdSLPs := UserGenerators(WordGroup(GS));
    GS`RandomProcess := RandomProcessWithWords(GS : WordGroup := WordGroup(GS),
	Scramble := 1);
    //phi := InverseWordMap(GS);
    phi := function(g)
        flag, w := SzBlackBoxMembership(GS, g);
	assert flag;
	return w;
    end function;
    
    homo := hom<G -> H | x :-> Evaluate(phi(x), UserGenerators(H))>;
    
    // Find standard copy
    sz := sub<Generic(H) | [Function(homo)(x) : x in UserGenerators(G)]>;

    assert SuzukiStandardRecogniser(sz);
    iso := hom<G -> sz | x :-> Function(homo)(x)>;
    inv := hom<sz -> G | x :-> Evaluate(slp, gens)
    where slp is SuzukiStandardConstructiveMembership(H, x :
	Randomiser := H`RandomProcess, CheckInput := false)>;
    
    return iso, inv;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function BrayStabTrick(U, C, invol, slps)
    assert assigned U`RandomProcess;
    n := NumberOfGenerators(C);
    q := #U`SzCrossCharData`defField;
    
    if Order(C.n) eq 1 then 
       return false;
    end if;
       
    assert Order(C.n) in {2, 4};
    z := rec<MatSLP | mat := C.n, slp := slps[n]>;
    if Order(z`mat) eq 4 then
	z`mat ^:= 2;
	z`slp ^:= 2;
    end if;
    if z`mat eq invol then
	return false;
    end if;
    
    repeat
	g, w := Random(U`RandomProcess);
	c := rec<MatSLP | mat := z`mat^g, slp := z`slp^w>;
    until invol^c`mat ne invol and IsOdd(Order(invol * c`mat));

    s, r := Quotrem(Order(invol * c`mat), 2);
    assert r eq 1;
    conj := rec<MatSLP | mat := (g * (invol * c`mat)^s)^(-1),
	slp := (w * (slps[1] * c`slp)^s)^(-1)>;
    assert invol^conj`mat eq z`mat;
    
    C`SzCrossCharData := rec<SzCrossCharInfo | conj := conj>;
    return Order(conj`mat) eq q - 1;
end function;

intrinsic SzBlackBoxGenerators(G :: Grp, F :: FldFin : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G))) -> [], []
    { Find standard generators of G, which must be isomorphic to Sz(F) }
    
    if not assigned G`RandomProcess then
	G`RandomProcess := Randomiser;
    end if;
    
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    W := WordGroup(G`RandomProcess);
    vprint SuzukiCrossChar, 1 : "Entering Suzuki Black Box Standard Gens";
    
    repeat
	f, f_w := Random(G`RandomProcess);
    until Order(f) eq 4;

    vprint SuzukiCrossChar, 2 : "Found f";
    
    f := rec<MatSLP | mat := f, slp := f_w>;
    s := rec<MatSLP | mat := f`mat^2, slp := f`slp^2>;
    
    repeat
	g, w := Random(G`RandomProcess);
	
	T := rec<MatSLP | mat := s`mat^g, slp := s`slp^w>;
    until Order(s`mat * T`mat) notin {1, 2, 4};
    
    assert Order(T`mat) eq 2 and Order(s`mat) eq 2;

    vprint SuzukiCrossChar, 2 : "Found T";
    
    G`SzCrossCharData := rec<SzCrossCharInfo | defField := F>;
    C, C_w := CentraliserOfInvolution(G, s`mat, s`slp :
	CompletionCheck := BrayStabTrick);
    h := C`SzCrossCharData`conj;
    //assert Order(h`mat) eq q - 1;

    vprint SuzukiCrossChar, 2 : "Found h";
    
    for i in [1 .. q - 1] do
	if Order(s`mat^(h`mat^i) * T`mat) eq 5 then
	    s`mat ^:= h`mat^i;
	    s`slp ^:= h`slp^i;
	    f`mat ^:= h`mat^i;
	    f`slp ^:= h`slp^i;
	    break;
	end if;
    end for;
    
    assert Order(s`mat * T`mat) eq 5;
    vprint SuzukiCrossChar, 2 : "Fixed f and s";

    relations, stabRelations := BraySzRelations(F);

    c := PrimitiveElement(F);
    a := F ! 1;
    for i in [i : i in [1 .. q - 1] | GCD(i, q - 1) eq 1] do
	if Trace(c^(-i)) eq 1 then
	    a := c^i;
	    l := i;
	    break;
	end if;
    end for;	
    assert a ne 1 and Trace(a^(-1)) eq 1;
    //SetPrimitiveElement(F, a);

    vprint SuzukiCrossChar, 2 : "Found a", l;
    
    found := false;
    for jj in [1 .. q - 1] do
	j := Solution(jj, 1, q - 1);

	if j eq -1 then
	    continue;
	end if;
	coeffs := Coefficients(MinimalPolynomial(c^jj));
	
	assert #coeffs eq Degree(F) + 1;	    
	assert coeffs[1] eq 1 and coeffs[Degree(F) + 1] eq 1;
	
	g := &*[f`mat^(h`mat^i) :
	    i in Reverse([0 .. Degree(F)]) | coeffs[i + 1] ne 0];
	
	if Order(g) le 2 then
	    k := j;
	    found := true;
	    break;
	end if;
    end for;
    assert found;

    vprint SuzukiCrossChar, 2 : "Found k";
    hh := rec<MatSLP | mat := h`mat^k, slp := h`slp^k>;
    
    found := false;
    for i in [1 .. q - 1] do
	ff := rec<MatSLP | mat := f`mat * s`mat^(hh`mat^i),
	    slp := f`slp * s`slp^(hh`slp^i)>;
	if Order(ff`mat) eq 4 and (IsIdentity(T`mat * ff`mat * T`mat *
	    ff`mat^2 * T`mat * ff`mat^3) or IsIdentity(T`mat * ff`mat^3 *
	    T`mat * ff`mat^2 * T`mat * ff`mat)) then
	    
	    f := ff;
	    found := true;
	    break;
	end if;
    end for;
    assert found;
	
    vprint SuzukiCrossChar, 2 : "Fixed f";

    if IsIdentity(T`mat * f`mat^3 * T`mat * f`mat^2 * T`mat * f`mat) then
	f`mat ^:= -1;
	f`slp ^:= -1;
    end if;    
    
    // corresponds to T(a, gamma), some gamma
    x := rec<MatSLP | mat := f`mat^(hh`mat^l), slp := f`slp^(hh`slp^l)>;
    
    found := false;
    for i in [1 .. q - 1] do

	// corresponds T(a, beta), some beta
	y := rec<MatSLP | mat := x`mat * s`mat^(hh`mat^i),
	    slp := x`slp * s`slp^(hh`slp^i)>;
	
	// try this element
	if Order(y`mat * T`mat) eq 4 and
	    (y`mat^2 * T`mat)^y`mat in
	    {(y`mat^2 * T`mat)^q, (y`mat^2 * T`mat)^(-q)} then

	    if (y`mat^2 * T`mat)^y`mat eq (y`mat^2 * T`mat)^q then
		qq := q;
	    else
		qq := -q;
	    end if;
	    
	    found := true;
	    break;
	end if;
    end for;
    assert found;
    
    vprint SuzukiCrossChar, 2 : "Found y";
        
    // Find corresponding b
    b := a^(t + 1) * &+[a^(-2^i) : i in [1 .. m + 1]];
        
    found := false;
    for r in {b, b + a^(t + 1)} do
	t1 := getSuzukiSylowGen(F, a, r)^(-1);
	t2 := GL(4, F) ! PermutationMatrix(F, Reverse([1 .. 4]));
	assert Order(t1 * t2) eq 4;
	assert (t1^2 * t2)^t1 in {(t1^2 * t2)^q, (t1^2 * t2)^(-q)};

	if (t1^2 * t2)^t1 eq (t1^2 * t2)^qq then
	    bb := r;
	    found := true;
	    break;
	end if;
    end for;
    assert found;
    
    vprint SuzukiCrossChar, 2 : "Found b";
    
    // should correspond to T(a, 0)
    
    z := rec<MatSLP | mat := y`mat, slp := y`slp>;
    coords := ElementToSequence(bb^(t - 1));
    z`mat *:= (&*[f`mat^(hh`mat^(j - 1)) : j in [1 .. #coords] |
	not IsZero(coords[j])])^2;
    z`slp *:= (&*[f`slp^(hh`slp^(j - 1)) : j in [1 .. #coords] |
	not IsZero(coords[j])])^2;
            
    assert c^(-l) eq a^(-1);
    
    // should correspond to D(a^(1+t)≤)
    d := rec<MatSLP | mat := T`mat * z`mat * T`mat *
	(s`mat^(hh`mat^(-l)))^(-1) * T`mat * z`mat^(-1),
	slp := T`slp * z`slp * T`slp *
	(s`slp^(hh`slp^(-l)))^(-1) * T`slp * z`slp^(-1)>;
    
    vprint SuzukiCrossChar, 2 : "Found d";
    
    ll := Solution(l, 1, q - 1);
    assert ll ne -1;
    
    d`mat ^:= 2^(2 * m) * ll;
    d`slp ^:= 2^(2 * m) * ll;

    // now d should correspond to D(a)
    
    G`SzCrossCharData`stdGens := [f`mat, d`mat, T`mat];
    G`SzCrossCharData`stdSLPs := [f`slp, d`slp, T`slp];
    G`SzCrossCharData`lambda := c;
    G`SzCrossCharData`lambdaLog := 1;
    
    vprint SuzukiCrossChar, 1 : "Leaving Suzuki Black Box Standard Gens";
    return [f`mat, d`mat, T`mat], [f`slp, d`slp, T`slp];
end intrinsic;

function parabolicSLP(g, q, x, y)

    vprint SuzukiCrossChar, 2 : "Entering Suzuki Parabolic Membership";
    
    // Now g = T(a, b) D(w)
    exps := {i : i in [1 .. q - 1] | (x`mat^2)^(y`mat^i) eq
	(x`mat^2)^g`mat};

    if #exps ne 1 then
	return false, _;
    end if;

    k := Rep(exps);
    g`mat *:= y`mat^(-k);
    g`slp *:= y`slp^(-k);
    assert IsIdentity(g`mat^4);
    // Now g = T(a, b)

    if not IsIdentity(g`mat^2) then
	exps := {i : i in [1 .. q - 1] | IsIdentity((g`mat *
	    x`mat^(y`mat^i))^2)};

	if #exps ne 1 then
	    return false, _;
	end if;

	k := Rep(exps);
	g`mat *:= x`mat^(y`mat^k);
	g`slp *:= x`slp^(y`slp^k);
	assert IsIdentity(g`mat^2);
    end if;
    // Now g = T(0, c)
    
    if not IsIdentity(g`mat) then
	exps := {i : i in [1 .. q - 1] | IsIdentity(g`mat *
	    (x`mat^2)^(y`mat^i))};

	if #exps ne 1 then
	    return false, _;
	end if;

	k := Rep(exps);
	g`mat *:= (x`mat^2)^(y`mat^k);
	g`slp *:= (x`slp^2)^(y`slp^k);
	assert IsIdentity(g`mat);
    end if;
    
    vprint SuzukiCrossChar, 2 : "Leaving Suzuki Parabolic Membership";
    return true, g`slp^(-1);
end function;

intrinsic SzBlackBoxMembership(G :: Grp, h :: GrpElt) -> BoolElt, GrpSLPElt
    { }

    require assigned G`SzCrossCharData : "No standard generators known in G";

    assert assigned G`RandomProcess;

    F := G`SzCrossCharData`defField;
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    W := WordGroup(G`RandomProcess);
    V, inc := VectorSpace(F, PrimeField(F));
    
    vprint SuzukiCrossChar, 1 : "Entering Suzuki Black Box Membership";

    g := rec<MatSLP | mat := h, slp := Identity(W)>;
    assert W cmpeq Parent(G`SzCrossCharData`stdSLPs[1]);
    
    x := rec<MatSLP | mat := G`SzCrossCharData`stdGens[1],
	slp := G`SzCrossCharData`stdSLPs[1]>;
    y := rec<MatSLP | mat := G`SzCrossCharData`stdGens[2],
	slp := G`SzCrossCharData`stdSLPs[2]>;
    z := rec<MatSLP | mat := G`SzCrossCharData`stdGens[3],
	slp := G`SzCrossCharData`stdSLPs[3]>;
    w := G`SzCrossCharData`lambda;
    
    if IsIdentity((x`mat^2, g`mat)^2) then
	return parabolicSLP(g, q, x, y);
    end if;

    if IsIdentity((x`mat^2, g`mat * z`mat)^2) then
	return parabolicSLP(rec<MatSLP | mat := g`mat * z`mat,
	    slp := g`slp * z`slp>, q, x, y);
    end if;
    
    // zz = T(0,1)^z    
    order5 := {i : i in [1 .. q - 1] | IsIdentity(u^5) and not IsIdentity(u)
	where u is (x`mat^2 * ((x`mat^2)^g`mat)^(y`mat^i))};
    if #order5 ne 1 then
	return false, _;
    end if;

    n := Rep(order5);
    g`mat *:= y`mat^n;
    g`slp *:= y`slp^n;
    // Now T(0,1)^g = zz^T(a,b) some (a,b) \neq (0,0)

    order5 := {i : i in [1 .. q - 1] | IsIdentity(u^5) and not IsIdentity(u)
	where u is (((x`mat^2)^y`mat^i) * (x`mat^2)^(g`mat * z`mat))};
    if #order5 ne 1 then
	return false, _;
    end if;

    k := Rep(order5);
    c := w^(k * (1 + t));

    order5 := {i : i in [1 .. q - 1] | IsIdentity(u^5) and not IsIdentity(u)
	where u is ((x`mat^2)^(y`mat^k))^(z`mat) *
	((x`mat^2)^g`mat)^((x`mat^2)^(y`mat^i))};

    if #order5 gt 1 or not (IsIdentity(u^5) and not IsIdentity(u)
	where u is ((x`mat^2)^(y`mat^k))^(z`mat) * ((x`mat^2)^g`mat)) then
	return false, _;
    end if;
    
    if #order5 eq 0 then
	// d = 0
	a := 0;
    elif #order5 eq 1 then
	// d = w^(i * (1 + t))
	l := Rep(order5);
	a := w^l;
    else
	return false, _;
    end if;
    
    if a ne 0 then
	lambda := (a^(t+2) * c^(t div 2))^(-1);
	b1 := a^(t + 1) * &+[lambda^(2^i) : i in [0 .. m]];
	b2 := a^(t + 1) + b1;
	b_vals := {b1, b2};
    else
	b_vals := {Sqrt(1/c)};
    end if;

    //for b in b_vals do
    u := rec<MatSLP | mat := Identity(G), slp := Identity(W)>;
    if a ne 0 then
	u`mat *:= x`mat^(y`mat^l);
	u`slp *:= x`slp^(y`slp^l);
    end if;
    
    b := Rep(b_vals);
    if b ne 0 then	
	coords := ElementToSequence(b^(t - 1));
	u`mat *:= (&*[(x`mat)^(y`mat^(j - 1)) : j in [1 .. #coords] |
	    not IsZero(coords[j])])^2;
	u`slp *:= (&*[(x`slp)^(y`slp^(j - 1)) : j in [1 .. #coords] |
	    not IsZero(coords[j])])^2;
    end if;
/*
    print u`mat;
    
    u := rec<MatSLP | mat := Identity(G), slp := Identity(W)>;
    if a ne 0 then
	u`mat *:= x`mat^(y`mat^l);
	u`slp *:= x`slp^(y`slp^l);
    end if;
    
    b := Rep(b_vals);
    if b ne 0 then
	j := Log(w, b^(t - 1));
		
	u`mat *:= (x`mat^(y`mat^j))^2;
	u`slp *:= (x`slp^(y`slp^j))^2;
    end if;

    print u`mat;
*/  
    u_elts := [u, rec<MatSLP | mat := u`mat^(-1), slp := u`slp^(-1)>];
	
    for u in u_elts do
	// u = T(a, b)

	if (x`mat^2)^g`mat eq (x`mat^2)^(z`mat * u`mat) then
	    v := rec<MatSLP | mat := g`mat * u`mat^(-1) * z`mat,
		slp := g`slp * u`slp^(-1) * z`slp>;
	    
	    assert ((x`mat)^2)^v`mat eq (x`mat^2);

	    if IsIdentity((x`mat^2, v`mat)^2) then
		flag, slp := parabolicSLP(v, q, x, y);

		if flag then
		    return true, slp;
		end if;
	    end if;
	end if;
    end for;

    return false, _;
end intrinsic;
