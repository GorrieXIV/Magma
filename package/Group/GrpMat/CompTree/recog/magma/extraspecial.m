/******************************************************************************
 *
 *    closure.m Normal Closure algorithm
 *
 *    File      : $HeadURL:: https://subversion.sfac.auckland.ac.nz/svn/prj_#$:
 *    Author    : Henrik B��rnhielm and Eamonn O'Brien
 *    Dev start : 2008-05-04
 *
 *    Version   : $Revision:: 2600                                           $:
 *    Date      : $Date:: 2014-04-21 03:54:16 +1000 (Mon, 21 Apr 2014)       $:
 *    Last edit : $Author:: jbaa004                                          $:
 *
 *    $Id:: extraspecial.m 2600 2014-04-20 17:54:16Z jbaa004               $:
 *
 *****************************************************************************/

freeze;
 
/*****************************************************************************/
/* DECLARATIONS                                                              */
/*****************************************************************************/

import "../../GrpMat/util/closure.m" : NormalClosureEngine, RandomSubProduct;

import "../../GrpMat/Smash/normaliser.m" :
    RecogniseNormaliserExtraSpecial, EpimorphicImage;

// Structure for storing a matrix and its SLP
EltSLP := recformat<elt : GrpElt, slp : GrpSLPElt>;

declare attributes GrpMat : ExtraSpecialData;
declare verbose C6, 10;

forward BlindDescent, Decompose, RadicalBasis, RadicalAction,
    SymplecticAction, UserGenerators;

ExtraSpecialInfo := recformat<
    ExtraSpecialGroup : GrpMat,
    ExtraSpecialSLPs : SeqEnum,
    Hom        : Map,
    CBM        : GrpMatElt,
    Parameters : SeqEnum,
    Normaliser : Grp
    >;

/*****************************************************************************/
/* MAIN INTRINSICS                                                           */
/*****************************************************************************/

intrinsic HasC6Decomposition(G :: GrpMat : Randomiser :=
    RandomProcessWithWords(G : WordGroup := WordGroup(G), Scramble := 1),
    ErrorProb := 2^(-1), MaxIterations := 10) -> BoolElt
    {

    Given G that normalises an extraspecial r-group or 2-group of symplectic
    type, tries to find a certain homomorphism into a permutation or a
    matrix group.
    
    Returns true if a homomorphism has been found. Returns false if G is
    known not to normalise an extraspecial r-group or a 2-group of symplectic
    type. Returns "unknown" if no homomorphism can be found.

    The algorithm is one-sided Monte Carlo. If it answers "unknown", with
    probability at most ErrorProb, a homomorphism of the required kind
    still exists.

    The algorithm is Brooksbank, Niemeyer and Seress:
    "A reduction algorithm for matrix groups with an extraspecial normal
    subgroup", Math Reviews number 2257997.
    
    }

    if assigned G`ExtraSpecialData then
	return true;
    end if;
    
    F := CoefficientRing(G);
    require ISA(Type(F), FldFin) :
	"Matrix group must be defined over a finite field";

    fac := Factorisation(Degree(G));
    if #fac gt 1 or Degree(G) lt 2 then
	return false;
    end if;
    
    r := fac[1][1];
    n := fac[1][2];
    
    if not IsDivisibleBy(#F - 1, r) then
	return false;
    end if;

    if n eq 1 then
	if r ne 2 then
	    vprint C6, 1 : "HasC6Decomposition prime-degree case";
	    
	    // Use the special Niemeyer algorithm
	    if RecogniseNormaliserExtraSpecial(G) cmpeq true then
		image := sub<GL(2, r) | G`ExtraSpecialNormaliser>;
		action := hom<G -> image | g :->
		EpimorphicImage(G`ExtraSpecialGroup, g)>;
		
		G`ExtraSpecialData := rec<ExtraSpecialInfo |
		    ExtraSpecialGroup := G`ExtraSpecialGroup,
		    ExtraSpecialSLPs  := [],
		    CBM               := ExtraSpecialBasis(G),
		    Hom               := action,
		    Normaliser        := image,
		    Parameters        := [r, n]
		    >;
		return true;
	    end if;
	else
	    return "unknown";
	end if;
   end if;
    
    vprint C6, 1 : "Entering HasC6Decomposition";
    vprintf C6, 2 : "Parameters: r = %o, n = %o\n", r, n;
    delta := ErrorProb / 6;

    vprint C6, 2 : "Find normalised group by blind descent";
    flag, U, U_slps, u := BlindDescent(G, Randomiser, delta, r, n :
	MaxIterations := MaxIterations);
    if flag cmpeq false then
	return false;
    end if;
    
    if flag cmpne true then
	vprint C6, 1 : "Probably not an extra-special normaliser";
	return "unknown";
    end if;

    vprint C6, 2 : "Find coordinsation";
    flag, B, spaces, A, F_inc := Decompose(U, U_slps, r, n);

    if not flag then
	return "unknown";
    end if;
    
    if not IsScalarGroup(A) then
	vprint C6, 2 : "Non-scalar case, setup radical basis";
	cbm, nComponents := RadicalBasis(A);

	assert IsDivisibleBy(Degree(A), nComponents);
	assert IsAbelian(A);
	
	action := hom<G -> Sym(nComponents) |
	g :-> RadicalAction(Generic(Parent(cbm)) ! g, cbm, nComponents)>;

	// In this case we don't get the full kernel of the action
	K := U;
	K_slps := [];
	cbm := Identity(G);
    else
	vprint C6, 2 : "Symplectic case";
	F := GF(r);
	
	flatB := F_inc(&cat[[b[1], b[2]] : b in B]);
	action := hom<G -> GL(#B * 2, r) | g :->
	SymplecticAction(F_inc(g), flatB, spaces, F, n)>;
	
	// In this case we obtain the kernel with SLPs
	// However, occasionally it's not the full kernel
	K := U;
	K_slps := U_slps;
	cbm := Identity(G);
    end if;

    vprint C6, 2 : "Find image";
    image := sub<Codomain(action) | [Function(action)(g) :
	g in UserGenerators(G)]>;
    
    G`ExtraSpecialData := rec<ExtraSpecialInfo |
	ExtraSpecialGroup := K,
	ExtraSpecialSLPs  := K_slps,
	Hom               := action,
	CBM               := cbm,
	Normaliser        := image,
	Parameters        := [r, n]
	>;

    vprint C6, 1 : "Leaving HasC6Decomposition";
    return true;
end intrinsic;

intrinsic C6Parameters(G :: GrpMat) -> SeqEnum
    { Return prime and exponent of the extraspecial or symplectic subgroup normalised by G. }
    require assigned G`ExtraSpecialData :
	"G is not an extraspecial normaliser";

    return G`ExtraSpecialData`Parameters;
end intrinsic;

intrinsic C6Basis(G :: GrpMat) -> GrpMatElt
    { Return change-of-basis matrix for extraspecial subgroup normalised by G. }
    require assigned G`ExtraSpecialData :
	"G is not an extraspecial normaliser";

    return G`ExtraSpecialData`CBM;
end intrinsic;

intrinsic C6Kernel(G :: GrpMat) -> GrpMat, GrpSLP
    { Kernel of homomorphism found by HasC6Decomposition. }
    require assigned G`ExtraSpecialData :
	"G is not an extraspecial normaliser";

    if #G`ExtraSpecialData`ExtraSpecialSLPs gt 0 then
	return G`ExtraSpecialData`ExtraSpecialGroup,
	    G`ExtraSpecialData`ExtraSpecialSLPs;
    else
	return G`ExtraSpecialData`ExtraSpecialGroup, _;
    end if;
end intrinsic;

intrinsic C6Action(G :: GrpMat, g :: GrpMatElt) -> GrpElt
    { Action element of g on extraspecial or symplectic group normalised by G. }
    require assigned G`ExtraSpecialData :
	"G is not an extraspecial normaliser";

    return Function(G`ExtraSpecialData`Hom)(g);
end intrinsic;

intrinsic C6Image(G :: GrpMat) -> Grp
    { Image of homomorphism found by HasC6Decomposition. }
    require assigned G`ExtraSpecialData :
	"G is not an extraspecial normaliser";

    return G`ExtraSpecialData`Normaliser;
end intrinsic;

/*****************************************************************************/
/* AUXILIARY FUNCTIONS                                                       */
/*****************************************************************************/

function UserGenerators(G)
    return [G.i : i in [1 .. NumberOfGenerators(G)]];
end function;

function RadicalAction(g, cbm, l)
    M := [];
    rows := RowSequence(g^cbm);

    perm := [];
    for i in [1 .. #rows] do
	if not exists(j){j : j in [1 .. #rows] | not IsZero(rows[i][j])} then
	    return false;
	end if;
	
	Append(~perm, ((j - 1) * l) div Degree(g) + 1);
    end for;

    parts := [SequenceToSet(P) : P in Partition(perm, Degree(g) div l)];
    assert forall{x : x in parts | #x eq 1};
    assert #parts eq l;
    return Sym(l) ! &cat[SetToSequence(x) : x in parts];
end function;

function NormalClosureC6(G, W, u, delta, r, n)
    assert not IsIdentity(u`elt);

    L := [Generic(G) | u`elt];
    L_slps := [u`slp];
    iterations := Ceiling(16 * n * Log(r) * Log(1 / delta));

    return NormalClosureEngine(G, sub<Generic(G) | L>, UserGenerators(W),
	L_slps, iterations);
end function;

function TestAbelian(G, W, u, delta, r, n)
    L, L_slps := NormalClosureC6(G, W, u, delta / 2, r, n);
    iterations := Ceiling(4 / 3 * Log(2 / delta));
    vprint C6, 6 : "Test abelian iterations:", iterations;

    assert not IsTrivial(L);
    gens := UserGenerators(L);
    
    for i in [1 .. iterations] do
	y, y_w := RandomSubProduct(gens, L_slps);
	x, x_w := RandomSubProduct(gens, L_slps);
	
	if not IsScalar((x, y)) then
	    return false, rec<EltSLP | elt := (x, y),
		slp := (x_w, y_w)>, _, _;
	end if;
    end for;
    
    return true, _, L, L_slps;
end function;

function BlindDescent(G, R, delta, r, n : MaxIterations := 0)
    symporder := r eq 2 select SimpleGroupOrder(<2, n, r>)
    else 2 * SimpleGroupOrder(<2, n, r>);

    W := WordGroup(R);
    repeat
	x, x_w := Random(R);
    until not IsScalar(x);
    
    x := rec<EltSLP | elt := x, slp := x_w>;
    iterations := Ceiling(48 * n * Log(1 / delta));
    if MaxIterations gt 0 then
	iterations := Min(iterations, MaxIterations);
    end if;
    
    vprint C6, 2 : "Blind descent max iterations:", iterations;
    
    for i in [1 .. iterations] do
	vprint C6, 4 : "Blind descent iteration:", i;
	repeat
	    y, y_w := Random(R);
	until not IsScalar(y);

	y := rec<EltSLP | elt := y, slp := y_w>;

	o_y_fac := FactoredProjectiveOrder(y`elt : Proof := false);
	o_y := &* [a[1]^a[2] : a in o_y_fac];
	
	if not IsDivisibleBy(symporder, o_y) then
	    return false, _, _, _;
	end if;
	
	flag, quot := IsDivisibleBy(o_y, r);
	if flag then
	    u := rec<EltSLP | elt := y`elt^quot, slp := y`slp^quot>;
	    assert not IsIdentity(u`elt);

	    flag, _, L, L_slps := TestAbelian(G, W, u, delta, r, n);
	    
	    if flag then
		return true, L, L_slps, u;
	    end if;
	end if;

	for p in Append(o_y_fac, <o_y, 1>) do
	    u := rec<EltSLP | elt := (x`elt, y`elt^(o_y div p[1])),
		slp := (x`slp, y`slp^(o_y div p[1]))>;

	    if not IsScalar(u`elt) then
		x := u;
	    end if;
	end for;

	o_x := ProjectiveOrder(x`elt : Proof := false);
	
	if not IsDivisibleBy(symporder, o_y) then
	    return false, _, _, _;
	end if;
	
	flag, quot := IsDivisibleBy(o_x, r);
	if flag then
	    u := rec<EltSLP | elt := x`elt^quot, slp := x`slp^quot>;
	    assert not IsIdentity(u`elt);

	    flag, w, L, L_slps := TestAbelian(G, W, u, delta, r, n);
	    if flag then
		return true, L, L_slps, u;
	    else
		x := w;
	    end if;
	else
	    assert not IsIdentity(x`elt);
	    flag, u := TestAbelian(G, W, rec<EltSLP |
		elt := x`elt, slp := x`slp>,
		delta, r, n);

	    if not flag then
		x := u;
	    end if;
	end if;
    end for;

    return "unknown", _, _, _;
end function;

function FindPowers(y, spaces)
    powers := [];
    for eigs in spaces do
	M := Matrix([Rep(Basis(E)) : E in eigs]);
	v := Solution(M, Rep(Basis(eigs[1] * y)));

	k := rep{i : i in [1 .. Degree(v)] | not IsZero(v[i])};
	Append(~powers, k - 1);
    end for;
    
    return Reverse(powers);
end function;

function SortedEigenspaces(g, h)    
    eigs := Eigenvalues(g);
    if IsEmpty(eigs) then
	return {@ @};
    end if;
    
    eigsList := {@ Eigenspace(g, Rep(eigs)[1]) @};

    while #eigsList lt #eigs do
	E := eigsList[#eigsList] * h;
	assert E notin eigsList;
	
	Include(~eigsList, E);
    end while;

    return eigsList;
end function;

function Decompose(U, U_slps, r, n)
    L1 := [];
    L2 := {@ @};
    
    F := CoefficientRing(U);
    if r eq 2 and (#F mod 4) eq 3 then
	F_ext := ext<F | 2>;
	U_ext, F_inc := ExtendField(Generic(U), F_ext);
    else
	F_inc := IdentityHomomorphism(Generic(U));
    end if;
    
    gens := F_inc(Generators(U));    
    spaces := [];
    
    while not IsEmpty(gens) do
	ExtractRep(~gens, ~g);
	
	if forall(h){h : h in gens | g^h eq g} then
	    Include(~L2, g);
	else
	    Append(~L1, [g, h]);
	    Exclude(~gens, h);
	
	    vprint C6, 3 : "Find sorted eigenspaces";
	    eigs := [SortedEigenspaces(g, h),
		SortedEigenspaces(h, g)];
	    if exists{E : E in eigs | IsEmpty(E)} then
		return false, _, _, _, _;
	    end if;
	    
	    Append(~spaces, eigs);

	    vprint C6, 3 : "Rewrite generators";
	    newGens := {};
	    newSLPs := AssociativeArray();
	    for y in gens do
		vprint C6, 8 : "Find powers";

		powers := FindPowers(y, eigs);		
		z := y * g^-powers[1] * h^-powers[2];
		assert forall{E : E in (&join eigs) | E^z eq E};
		
		Include(~newGens, z);
	    end for;
	    
	    gens := newGens;
	end if;
    end while;

    return true, L1, spaces, sub<Generic(U) | L2>, F_inc;
end function;

function RadicalBasis(A)
    MA := MatrixAlgebra(CoefficientRing(A), Degree(A));
    basis, M := Diagonalisation([MA | g : g in Generators(A)]);
    F := CoefficientRing(M);
    V := VectorSpace(F, Degree(A));
    action := Transpose(Matrix([(V ! Diagonal(b)) / basis[1][1, 1] :
	b in basis]));
    assert NumberOfRows(M) eq NumberOfRows(action);
    
    rows := RowSequence(action);
    actionSet := {@ r : r in rows @};

    Sort(~rows, func<x, y | Index(actionSet, x) - Index(actionSet, y)>,	~perm);
    P := GL(Degree(A), F) ! PermutationMatrix(F, perm)^(-1);
    
    return (GL(Degree(A), F) ! M^(-1))^P, #actionSet;
end function;

function SymplecticAction(g, flatB, eigs, F, n)

    image := [];
    assert #flatB le 2 * n;

    for h in flatB do
	x := h^g;
	exp := &cat [FindPowers(x, eigs[i]) : i in [1 .. #eigs]];
	assert #exp eq #flatB;
	assert forall{e : e in exp | 0 le e and e le #F};
	
	rad := [flatB[i]^(-exp[i]) : i in [1 .. #flatB]];
	if not IsScalar(x * (&* rad)) then
	    return false;
	end if;

	assert #exp eq #flatB;
	Append(~image, exp);
    end for;

    return GL(#flatB, F) ! image;
end function;

    
