/******************************************************************************
 *
 *    elements.m Element conjugacy for Suzuki groups
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B‰‰rnhielm
 *    Dev start : 2007-05-07
 *
 *    Version   : $Revision:: 1605                                           $:
 *    Date      : $Date:: 2008-12-15 20:05:48 +1100 (Mon, 15 Dec 2008)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: elements.m 1605 2008-12-15 09:05:48Z jbaa004                   $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

declare verbose SuzukiElements, 10;

import "maximals.m" : SuzukiMaximalsInfo;
import "membership.m" : getZeroMappingMatrix;
import "standard.m" : getSuzukiSylowGen, orderSuzukiEigenvalues;
import "sylow.m" : cyclicSylowConjugation, hardSylowConjugation;
import "../../../util/dihedral.m" : DihedralTrick;
import "../../../util/basics.m" : MatSLP, DiagonaliseMatrix;

forward stdCopyClasses, stdCopyRationalClasses, stdCopyRepresentative;

SuzukiConjugacyClassInfo := recformat<
    classes : SeqEnum,
    representatives : SetIndx,
    rationalClasses : SeqEnum,
    indicesGen : SeqEnum,
    torusBases : SeqEnum,
    torusNormalisers : SeqEnum>;

declare attributes GrpMat : SuzukiConjugacyClassData;

/*****************************************************************************/
/* TEST FUNCTIONS                                                            */
/*****************************************************************************/
    
/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic SzClassMap(G :: GrpMat) -> Map
    { G is isomorphic to Sz(q) and RecogniseSz has returned true. 
      Returns the class map for G. }

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    if not assigned G`SuzukiConjugacyClassData then
	_ := SzConjugacyClasses(G);
    end if;

    return map<G -> Integers() | x :->
    Index(G`SuzukiReductionData`stdCopy`
	SuzukiConjugacyClassData`representatives,
	stdCopyRepresentative(G`SuzukiReductionData`stdCopy,
	G`SuzukiReductionData`iso(x), WordGroup(G)))>;
end intrinsic;

intrinsic SzIsConjugate(G :: GrpMat, g :: GrpMatElt,
    h :: GrpMatElt) -> BoolElt, GrpMatElt
    { G is isomorphic to Sz(q), RecogniseSz(G) has returned true, 
      and g,h are in G. Determine if g is conjugate to h, and if so, return
      a conjugating element. }

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;
    
    rep1, conj1 := SzClassRepresentative(G, g);
    rep2, conj2 := SzClassRepresentative(G, h);

    if rep1 ne rep2 then
	return false, _;
    end if;
    
    assert g^(conj1 * conj2^(-1)) eq h;
    return true, conj1 * conj2^(-1);
end intrinsic;

intrinsic SzConjugacyClasses(G :: GrpMat) -> []
    { G is isomorphic to Sz(q) and RecogniseSz(G) has returned true. 
      Returns of list of conjugacy class representatives of G. }

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    if assigned G`SuzukiConjugacyClassData and
	assigned G`SuzukiConjugacyClassData`classes then
	return G`SuzukiConjugacyClassData`classes;
    end if;

    assert assigned G`SuzukiReductionData`stdCopy;
    if not assigned G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData then
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData :=
	    stdCopyClasses(G`SuzukiReductionData`stdCopy);
    end if;

    if not assigned
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`classes then
	info := stdCopyClasses(G`SuzukiReductionData`stdCopy);
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`classes :=
	    info`classes;
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`
	    representatives := info`representatives;
    end if;
    
    if not SuzukiStandardRecogniser(G) then
	classes := [<x[1], x[2], G`SuzukiReductionData`inv(x[3])> : x in
	    G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`classes];
	
	G`SuzukiConjugacyClassData := rec<SuzukiConjugacyClassInfo |
	    classes := classes>;
    end if;
    
    return G`SuzukiConjugacyClassData`classes;
end intrinsic;

intrinsic SzRationalConjugacyClasses(G :: GrpMat) -> [], []
    { G is isomorphic to Sz(q) and RecogniseSz(G) has returned true. 
      Returns of list of rational conjugacy class representatives of G. 
      Also returns a list of functions corresponding to the representatives,
      that return the powers of the representatives that give representatives
      of all conjugacy classes. }

    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    if assigned G`SuzukiConjugacyClassData and
	assigned G`SuzukiConjugacyClassData`rationalClasses then
	return G`SuzukiConjugacyClassData`rationalClasses,
	    G`SuzukiConjugacyClassData`indicesGen;
    end if;

    assert assigned G`SuzukiReductionData`stdCopy;
    if not assigned G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData then
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData :=
	    stdCopyRationalClasses(G`SuzukiReductionData`stdCopy);
    end if;

    if not assigned G`SuzukiReductionData`stdCopy`
	SuzukiConjugacyClassData`rationalClasses then
	info := stdCopyClasses(G`SuzukiReductionData`stdCopy);
	
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`
	    rationalClasses := info`rationalClasses;
	
	G`SuzukiReductionData`stdCopy`SuzukiConjugacyClassData`
	    indicesGen := info`indicesGen;
    end if;
    
    if not SuzukiStandardRecogniser(G) then
	rationalClasses := [<x[1], x[2], G`SuzukiReductionData`inv(x[3])> : x
	    in G`SuzukiReductionData`stdCopy`
	    SuzukiConjugacyClassData`rationalClasses];

	G`SuzukiConjugacyClassData := rec<SuzukiConjugacyClassInfo |
	    rationalClasses := rationalClasses,
	    indicesGen := G`SuzukiReductionData`stdCopy`
	    SuzukiConjugacyClassData`indicesGen>;
    end if;
    
    return G`SuzukiConjugacyClassData`rationalClasses,
	G`SuzukiConjugacyClassData`indicesGen;
end intrinsic;

intrinsic SzClassRepresentative(G :: GrpMat, g :: GrpMatElt) ->
    GrpMatElt, GrpMatElt
    { G is isomorphic to Sz(q), RecogniseSz(G) has returned true, 
    and g is in G. Returns the conjugacy class representative of g, from the
    list returned by SzConjugacyClasses. Also returns a conjugating element
    to this representative. }
	
    if not assigned G`SuzukiReductionData then
	error "G must be a recognised Suzuki group";
    end if;

    h := G`SuzukiReductionData`iso(g);
    if not SuzukiStandardMembership(h) then
	error "g must be an element of the Suzuki group";
    end if;
    
    assert assigned G`SuzukiReductionData`stdCopy;
    
    rep, conj := stdCopyRepresentative(G`SuzukiReductionData`stdCopy, h,
	WordGroup(G));
    assert SuzukiStandardMembership(conj);
    
    return G`SuzukiReductionData`inv(rep), G`SuzukiReductionData`inv(conj);
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function getTorusElements(G)
    F := CoefficientRing(G);
    q := #F;
    
    if not assigned G`SuzukiMaximals then
	vprint SuzukiElements, 1:
	    "Construct maximals subgroups of standard copy";
	
	maximals, slps := SuzukiStandardMaximalSubgroups(G);
	G`SuzukiMaximals :=
	    rec<SuzukiMaximalsInfo |
	    maximals := maximals,
	    slps := slps>;
    end if;

    maximals := G`SuzukiMaximals`maximals;
    
    // Generators of cyclic subgroups to search in
    torus_gens := [maximals[2].2, maximals[3].1 * maximals[3].2^2,
	maximals[4].1 * maximals[4].2^2];
    
    // Also need normalising elements
    torus_normalisers := [maximals[2].1, maximals[3].1 * maximals[3].2,
	maximals[4].1 * maximals[4].2];

    // Lowest order should come first
    Sort(~torus_gens, func<x, y | Order(x) - Order(y)>, ~perm);
    
    // Sort normalisers accordingly
    torus_normalisers := PermuteSequence(torus_normalisers, perm);    

    // Make sure the normalising element acts as the q-th power
    for i in [1, 3] do
	assert torus_gens[i]^torus_normalisers[i] in
	    {torus_gens[i]^q, torus_gens[i]^(-q)};

	if torus_gens[i]^torus_normalisers[i] ne torus_gens[i]^q then
	    torus_normalisers[i] ^:= 3;
	end if;
    end for;
    
    return torus_gens, torus_normalisers;
end function;

function stdCopyRepresentative(G, g, wordGroup)

    assert assigned G`RandomProcess;
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);
    _, gens := SuzukiStandardGeneratorsNaturalRep(m);

    if not assigned G`SuzukiConjugacyClassData then
	torus_gens, torus_normalisers := getTorusElements(G);
	
	G`SuzukiConjugacyClassData := rec<SuzukiConjugacyClassInfo |
	    torusBases := torus_gens,
	    torusNormalisers := torus_normalisers>;
    end if;
        

    if IsIdentity(g) then
	return Identity(G), Identity(G);
    end if;

    o := Order(g);
    
    if o eq 2 then
	conj := DihedralTrick(rec<MatSLP | mat := g,
	    slp := Identity(wordGroup)>, rec<MatSLP | mat := gens[3]^2,
	    slp := Identity(wordGroup)>, G`RandomProcess);

	return gens[3]^2, conj`mat;
    end if;

    if o eq 4 then
	P := Eigenspace(g, 1);
	assert Dimension(P) eq 1;

	// Map point to infinity point
	if P.1 eq Vector(F, [0, 0, 0, 1]) then
	    conj1 := gens[1];
	else
	    conj1 := getZeroMappingMatrix(G, P.1)[2];
	end if;
	rep := g^conj1;

	// Pick out a,b s.t. rep = S(a,b)
	a := rep[2, 1];
	assert a ne 0;
	
	b := rep[3, 1];
	P<x> := PolynomialAlgebra(F);
	s := 2^m;
	c := a^(-1);

	// Final scaling conjugation
	conj3 := Generic(G) !
	    DiagonalMatrix([c^(1 + s), c^s, c^(-s), c^(-1-s)]);

	// Element satisfies one of two equations, depending on its
	// conjugacy class
	flag, alpha := HasRoot(x^2 * a^(t - 1) + b^t / a + a^t * x + b);
	if flag then
	    conj2 := getSuzukiSylowGen(F, alpha, 0);
	else
	    flag, alpha :=
		HasRoot(x^2 * a^(t - 1) + b^t / a + a^t * x + b +
		c^(-t - 1) + c^(-t - 2) / a);
	    assert flag;
	    
	    conj2 := getSuzukiSylowGen(F, alpha, 0);
	end if;

	rep ^:= conj2 * conj3;
	assert rep in {gens[3], gens[3]^(-1)};
	return rep, conj1 * conj2 * conj3;
    end if;

    if IsDivisibleBy(q - 1, o) then
	divisor := (q - 1) div o;
	conj := cyclicSylowConjugation(G, sub<Generic(G) | g>,
	    sub<Generic(G) |
	    G`SuzukiConjugacyClassData`torusBases[2]>);
	rep := g^conj;

	// Find correct power in cyclic group
	power := Log(G`SuzukiConjugacyClassData`torusBases[2][2, 2],
	    rep[2, 2]);
	assert power gt 0;

	// Power is determined up to inverse
	candidates := {@ rep, rep^(-1) @};
	powers := [1, -1];
	k := Index(candidates, G`SuzukiConjugacyClassData`torusBases[2]^power);
	assert k gt 0;
	power *:= powers[k];

	// Need a positive integer for the minimum test
	power mod:= (q - 1);
	assert G`SuzukiConjugacyClassData`torusBases[2]^power eq rep;

	// Determine if we need to invert representative
	_, k := Min([power mod (q - 1), (-power) mod (q - 1)]);
	rep ^:= G`SuzukiConjugacyClassData`torusNormalisers[2]^(k - 1);
	conj *:= G`SuzukiConjugacyClassData`torusNormalisers[2]^(k - 1);

	return rep, conj;
    end if;

    assert IsDivisibleBy(q - t + 1, o) or IsDivisibleBy(q + t + 1, o);
    
    if IsDivisibleBy(q - t + 1, o) then
	divisor := (q - t + 1) div o;
	idx := -1;
    else
	divisor := (q + t + 1) div o;
	idx := 1;
    end if;
    
    conj := hardSylowConjugation(G, sub<Generic(G) |
	G`SuzukiConjugacyClassData`torusBases[2 + idx]^divisor>,
	sub<Generic(G) | g>);
    conj ^:= -1;
    rep := g^conj;

    F4 := ext<F | 4>;
    _, inc := ExtendField(Generic(G), F4);
    
    // Diagonalise over larger field
    base := DiagonaliseMatrix(inc(G`SuzukiConjugacyClassData`
	torusBases[2 + idx]));
    diag := DiagonaliseMatrix(inc(rep));

    // Determine power in cyclic group (discrete log in GF(q^4))
    power := Log(base[1, 1], diag[1, 1]);
    assert power gt 0;

    // Power is determined up to 4 elements
    candidates := {@ rep, rep^(-1), rep^q, rep^(-q) @};
    powers := [1, -1, -q, q];
    k := Index(candidates,
	G`SuzukiConjugacyClassData`torusBases[2 + idx]^power);
    assert k gt 0;
    power *:= powers[k];

    // Need positive power for the minimum test
    power mod:= Order(G`SuzukiConjugacyClassData`torusBases[2 + idx]);
    assert G`SuzukiConjugacyClassData`torusBases[2 + idx]^power eq rep;

    // Find power of normalising element that we need to get correct
    // representative
    x, k := Min([j mod Order(G`SuzukiConjugacyClassData`torusBases[2 + idx]) :
	j in [power, power * q, -power, (-power) * q]]);

    assert G`SuzukiConjugacyClassData`torusBases[2 + idx]^x eq
	rep^(G`SuzukiConjugacyClassData`torusNormalisers[2 + idx]^(k - 1));
    
    rep ^:= G`SuzukiConjugacyClassData`torusNormalisers[2 + idx]^(k - 1);
    conj *:= G`SuzukiConjugacyClassData`torusNormalisers[2 + idx]^(k - 1);

    return rep, conj;
end function;

function stdCopyRationalClasses(G)

    assert assigned G`RandomProcess;
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);

    if not assigned G`SuzukiConjugacyClassData then
	torus_gens, torus_normalisers := getTorusElements(G);	
    else
	torus_gens := G`SuzukiConjugacyClassData`torusBases;
    end if;

    _, gens := SuzukiStandardGeneratorsNaturalRep(m);
    
    // List in Magma format
    // First unipotent classes
    classes := [<1, 1, Identity(G)>,
	<4, #G div (2 * q), gens[3]>,
	<4, #G div (2 * q), gens[3]^(-1)>];

    cent_sizes := [q - t + 1, q - 1, q + t + 1];
    classes cat:= [<Order(torus_gens[i]), #G div cent_sizes[i],
	torus_gens[i]> : i in [1 .. #torus_gens]];

    
    easyCyclicIndices := function()
	return [1 .. (q - 2) div 2];
    end function;

    hardCyclicIndices := [function()
	indices := [];
    
	for i in [1 .. cent_sizes[k]] do
	    idx := [j mod cent_sizes[k] : j in [i, -i, i * q, -i * q]];
	    if i eq Min(idx) then
		Append(~indices, i);
	    end if;

	    if #indices eq (#cent_sizes - 1) div 4 then
		break;
	    end if;
	end for;
	
	return indices;
    end function : k in [1, 3]];

    evenOrderIndices := function()
	return [1, 2];
    end function;

    return rec<SuzukiConjugacyClassInfo |
	rationalClasses := classes,
	torusBases := torus_gens,
	torusNormalisers := torus_normalisers,
	indicesGen := [function() return [1]; end function,
        evenOrderIndices, function() return [1]; end function,
        hardCyclicIndices[1], easyCyclicIndices,
	hardCyclicIndices[2]]>;
end function;

function stdCopyClasses(G)

    assert assigned G`RandomProcess;
    F := CoefficientRing(G);
    q := #F;
    m := (Degree(F) - 1) div 2;
    t := 2^(m + 1);

    if not assigned G`SuzukiConjugacyClassData then
	torus_gens, torus_normalisers := getTorusElements(G);	
    else
	torus_gens := G`SuzukiConjugacyClassData`torusBases;
	torus_normalisers := G`SuzukiConjugacyClassData`torusNormalisers;
    end if;
    
    _, gens := SuzukiStandardGeneratorsNaturalRep(m);
    
    // List in Magma format
    // First unipotent classes
    classes := [<1, 1, Identity(G)>,
	<2, #G div q^2, gens[3]^2>,
	<4, #G div (2 * q), gens[3]>,
	<4, #G div (2 * q), gens[3]^(-1)>];

    // Numbers and sizes of semisimple classes
    num_classes := [(q - t) div 4, (q - 2) div 2, (q + t) div 4];
    cent_sizes := [q - t + 1, q - 1, q + t + 1];

    // Search for torus representatives
    for i in [1 .. #torus_gens] do
	traces := {};
	torus_reps := [];
	g := torus_gens[i];

	// Check elements in the cyclic group until we have found enough
	for j in [1 .. Order(torus_gens[i]) - 1] do
	    trace := Trace(g);

	    if trace notin traces then
		x := Min([x mod Order(torus_gens[i]) :
		    x in [j, -j, j * q, -j * q]]);
		assert j eq x;

		Include(~traces, trace);
		Append(~torus_reps, g);
	    end if;

	    if #traces eq num_classes[i] then
		break;
	    end if;

	    // Check next element
	    g *:= torus_gens[i];
	end for;
	
	classes cat:= [<Order(x), #G div cent_sizes[i], x> : x in torus_reps];
    end for;

    // Sort representatives on element order
    Sort(~classes, func<x, y | x[1] - y[1]>);
    
    return rec<SuzukiConjugacyClassInfo |
	classes := classes,
	representatives := {@ x[3] : x in classes @},
	torusBases := torus_gens,
	torusNormalisers := torus_normalisers>;
end function;
