// *********************************************************************
// * Package: surface_resolution.mag:                                  *
// * ================================                                  *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 29.12.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute formal surface desingularizations.                      *
// *                                                                   *
// *********************************************************************
freeze;




// ======================================
// = Auxillary functions (not exported) =
// ======================================

// turn certain nested polynomial rings into distributed representation
// --------------------------------------------------------------------
// input:  univariate polynomial ring 'P' (in 'z') over bivar. polynomial ring
// output: homomorphism to a polynomial ring in three variables ('z' becoming
//         the third variable)
function PolyRingFlattener(P)
	S := BaseRing(P); F := BaseRing(S);
	P2 := PolynomialRing(F, 3);
	AssignNames(~P2,[Sprint(P.1),Sprint(S.1),Sprint(S.2)]);
	return hom<P -> P2 | hom<S -> P2 | P2.1, P2.2>, P2.3>;
end function;


// find order of a non-zero series
// -------------------------------
// input:  a continuous transformation 'trafo' acting on series (resp. their
//         approximations) and a sequence 'seriesseq' of series with
//         integral exponents
// output: the order of the series 'trafo(seriesseq)'
// 
// This function terminates only when the order is finite.
// 
// The function computes increasingly higher approximations of the series and
// applies 'trafo' in order to determine the order of the result. A computed
// order will be accepted if it is smaller by the value of 'Bias' than the
// approximation order used for expanding the series.
// 
// So 'Bias' has to be set according to the contraction/expansion ratio of
// 'trafo'. This can be useful, for example, if the transformation involves
// deriving the series. As a rule of thumb: If derivations of order 'n' are
// involved, set 'Bias := n'.
function FindOrder(trafo, seriesseq : Bias := 0)

// "\n********"; "seriesseq univ:", Universe(seriesseq); "Domain:", Domain(seriesseq[1]);

	red := func<x | x>;

	D := Domain(seriesseq[1]);
	if
	Type(D) eq RngMPol then
	    F := BaseRing(D);
	    // coeffs of tst are in F
// "F:", F; Type(F);
	    if
		Type(F) eq FldFunRat and
		Type(BaseRing(F)) eq FldRat
	    then
		// IR := IntegerRing(F); "IR:", IR; Type(IR);

// "F:", F; "BaseRing:", BaseRing(F); "Type(BaseRing):", Type(BaseRing(F));

		E := Random(10^15);

		function red(f)
// "DO RED FldFunRat:", Type(f);
		    assert Type(f) eq RngMPolElt;
		    c := Coefficients(f);
		    U := Universe(c);
// "coeffs:", c; U<[u]> := U;
		    if Type(U) eq FldFunRat and Rank(U) eq 1 then
			//BR := BaseRing(U);
			//c := [BR | Evaluate(g, E): g in c];
			c := [Evaluate(g, E): g in c];
// "new coeffs [FldFunRat]:", c;
// Pf<[z]> := Parent(f); "ORIG f:", f; Parent(f);
			f := Polynomial(c, Monomials(f));
// "NEW f:", f;
		    end if;
		    return f;
		end function;

	    elif
		Type(F) eq FldFun and
		Type(ConstantField(F)) eq FldRat and
		Type(BaseRing(F)) eq FldFunRat
	    then

		BR := BaseRing(F);

// "FldFun BR:", BR;
// "FldFun ConstantField:", ConstantField(F);

		def := DefiningPolynomial(F);
//"Def poly:", def;
// Parent(def);
		q := 0;
		for i := 1 to 5 do
		    E := Random(10^15);
		    ndef := Polynomial([Evaluate(c, E): c in Eltseq(def)]);
// "E:", E; "ndef:", ndef;
		    if not IsIrreducible(ndef) then
			continue;
		    end if;

		    q := quo<Parent(ndef) | ndef>;
		    break;
		end for;

		function red(f)
// "DO RED FldFun:", Type(f);
		    assert Type(f) eq RngMPolElt;
		    c := Coefficients(f);
//"coeffs:", c;
		    U := Universe(c);
// "coeff Univ:", U; assert U eq F; "es:", [Eltseq(x): x in c];

		    if q cmpne 0 then
			PP := PolynomialRing(q, Rank(Parent(f)): Global);
			c := [q![Evaluate(g, E): g in Eltseq(h)]: h in c];
// "new coeffs:", c;
			if f eq 0 then
			    f := PP!f;
			else
			    f := Polynomial(c, [PP!m: m in Monomials(f)]);
			end if;
//"NEW f:", f;
		    end if;
		    return f;
		end function;
	    end if;
	end if;

	// look for the order step by step
	i := 0; while true do
		// reapproximate series in sequence
		approx := [];
		for j := 1 to #seriesseq do
			good, app := Expand(seriesseq[j], i+1);
			if not good then error "series not expandable"; end if;
			
			Append(~approx, app);
		end for;

// "oapprox:", approx;

// otst := trafo(approx);
// ot := TrailingTerm(otst);

		approx := [red(x): x in approx];

// "eval approx:", approx;
		
		// apply transformation
// "approx:", approx; Parent(approx); time
		tst := trafo(approx);
		
// "Got tst:", tst; Parent(tst);
		// found order?
		t := TrailingTerm(tst);
// "t:", t;


    /*
    if
	t eq 0 and ot ne 0 or
	ot eq 0 and t ne 0 or
	TotalDegree(t) ne TotalDegree(ot)
    then
	"FAIL";

// "t:", t; TotalDegree(t); "ot:", ot; TotalDegree(ot);
// "tst:", tst; "otst:", otst;
	error "STOP";
    end if;
    */

		if (t eq 0) then
			i := i+1;
		else
			d := TotalDegree(t);
			if (d + Bias le i) then
				return d;
			else
				i := d + Bias;
			end if;
		end if;
	end while;
end function;


// compute order of an element (not in the kernel) under formal map
// ----------------------------------------------------------------
// input:  a univariate polynomial 'E(x,y)(z)' over a bivariate polynomial ring
//         and representations 'SX', 'SY' and 'SZ' of power series 'alphaX',
//         'alphaY' and 'alphaZ'
// output: the order of 'E(alphaX,alphaY,alphaZ)'
function ElementOrder(E, SX, SY, SZ)
	F := PolyRingFlattener(Parent(E))(E);
// "*****\nParent(F):", Parent(F); "F:", F;
	ord := FindOrder(func<seq | Evaluate(F, seq)>, [SX, SY, SZ]);
	return ord;
end function;


// compute order of the (non-vanishing) Jacobian of a map
// ------------------------------------------------------
// input:  a homomorphism 'm' between polynomial rings (of rank 3 and 2, but
//         first ring is for a projective space) and representations 'SX' and
//         'SY' of power series 'alphaX' and 'alphaY' (with integral exponents)
// output: if 'b' is the homomorphism from a bivariate polynomial ring to the
//         corresponding ring of power series defined by 'x :-> alphaX' and
//         'y :-> alphaY', then return the order of the Jacobian of the
//         composed homomorphism 'b*m'
function JacobianOrder(m, SX, SY)
	D := Domain(m); if Rank(D) eq 3 then
		C:= [c: c in [m(D.1),m(D.2),m(D.3)] | not c eq 1];
		X := C[1]; Y := C[2];
	else
		X := m(D.1); Y := m(D.2);
	end if;
	jac := Derivative(X,1)*Derivative(Y,2)-Derivative(X,2)*Derivative(Y,1);
	return FindOrder(func<seq | Evaluate(jac, seq)>, [SX, SY]);
end function;


// find the generators of the intersection of the dual lattice with
// the positive quadrant
// ----------------------------------------------------------------
// input:  a series 'series' with exponent lattice, say, '1/e*Gamma'
//         containing 'Z^2'
// output: a set of generators of the monoid '(1/e*Gamma)^* meet R^2_(>= 0)'
//         (i.e. the intersection of the dual lattice with the positive
//         quadrant), if 'AdjComp' is true only the subset necessary for
//         adjoint computations is returned
function DualGenerators(series : AdjComp := false)
	IntVec := RSpace(Integers(),2);
	
	Gamma, e := Explode(ExponentLattice(series));
	L := (1/e)*Gamma; D := Dual(L : Rescale := false);
	
	// dual cone contains
	dc := [ IntVec ! [0, e], IntVec ! [e, 0] ];
	
	// add all non-zero representatives of classes modulo 'e'
	ind := Index(D, sub<D | dc >); b1 := Basis(D)[1]; b2 := Basis(D)[2];
	for i := 0 to ind-1 do
		for j := 0 to ind-1 do
			b := i * b1 + j * b2;
			c := IntVec ! [b[1] mod e, b[2] mod e];
			if (not c eq Zero(IntVec)) then Append(~dc, c); end if;
		end for;
	end for;
	
	// compute hull
	return GetIntegerNewtonPolygon(dc : OnlyVertices := AdjComp);
end function;


// compute formal prime divisors from toroidal isomorphism
// -------------------------------------------------------
// input:  three series representations 'X', 'Y', 'Z' and a sequence 'lambda'
//         defining a toroidal isomorphism
// output: the corresponding list of formal prime divisors, if 'AdjComp'
//         is true only the subset necessary for adjoint computations is
//         returned
function ToricChange(X, Y, Z, lambda, AdjComp)
	S := Domain(Z); F := BaseRing(S);
	
	// substitute according to lambda
	subs := [PolyToSeries(lambda[1]*S.1), PolyToSeries(lambda[2]*S.2)];
	duals := [RSpace(Integers(), 2).i : i in [1..2]];
	XT := EvaluationPowerSeries(X, duals, subs);
	YT := EvaluationPowerSeries(Y, duals, subs);
	
	// structures for analytic neighborhood
	F1 := FunctionField(F); s := F1.1; S1 := PolynomialRing(F1, 1, "glex"); t := S1.1;
	
	// compute chart information
	dg := DualGenerators(Z : AdjComp := AdjComp);
	
	// return formal desingularization
	res := [**];
	if (#dg gt 2) then
		mdg := Prune(dg); mdg[1] := mdg[1]+mdg[2];
		g1 := mdg[#mdg]; Prune(~mdg);
		while not IsEmpty(mdg) do
			g2 := mdg[#mdg]; Prune(~mdg);
			tt := func<series | EvaluationPowerSeries(series, [g2, g1],
			    [PolyToSeries(S1 ! s), PolyToSeries(t)])>;
			Append(~res, <tt(XT), tt(YT), tt(Z), g1[1]+g1[2]-1>);
			g1 := g2;
		end while;
	end if;
	
	return res;
end function;


// compute the set of formal prime divisors over a normal crossing
// ---------------------------------------------------------------
// input:  a univariate polynomial 'p' over a bivariate polynomial ring in
//         variables, say, 'x' and 'y', and an irreducible factor 'd' of the
//         discriminant (assuming that the discriminant is normal crossing at
//         the origin and that the other factor is 'y')
// output: the list of formal prime divisors centered over the origin, if
//         'AdjComp' is true only the subset necessary for adjoint computations
//         is returned
function ToroidalIsos(p, d, AdjComp, ExtName, ExtCount)
	S := Parent(d); P := PolynomialRing(S);
	
	// compute formal coordinate transform
	pn := hom< S -> P | P.1, S.2>(d) - S.1; // !!! normal crossing test ???
	X := ImplicitFunction(pn); Y := PolyToSeries(S.2);
	
	// compute bivariate parametrizations
	_, params, ExtCount := RationalPuiseux(p : subs := [X, Y],
	    Duval := true, OnlySingular:= true, ExtName := ExtName,
	    ExtCount := ExtCount);
	
	// substitute to produce univariate parametrizations
	isos := [**]; for prm in params do
		isos := isos cat
		    ToricChange(X, Y, prm[2], prm[1], AdjComp);
	end for;
	
	// return them
	return isos, ExtCount;
end function;


// find a point not on the surface
// -------------------------------
// input:  a polynomial 'p' in four variables, defining a projective surface
// output: a point of the form '[x,y,z,1]' not lying on the surface
function FindProjPoint(p)
	S := Parent(p); F := BaseRing(S);
	found := false;
	
	// first try origin
	if not Evaluate(p, [0, 0, 0, 1]) eq 0 then
		point := [0, 0, 0, 1]; found := true;
	end if;
	
	// then try only one coordinate
	if not (found or Evaluate(p, [S.1, 0, 0, 1]) eq 0) then
		i := 0;
		while Evaluate(p, [i, 0, 0, 1]) eq 0 do i := i+1; end while;
		point := [i, 0, 0, 1]; found := true;
	end if;
	
	// then try two coordinates
	if not (found or Evaluate(p, [S.1, S.2, 0, 1]) eq 0) then
		i := 0; j := 0;
		while Evaluate(p, [i, S.2, 0, 1]) eq 0 do i := i+1; end while;
		while Evaluate(p, [i, j, 0, 1]) eq 0 do j := j+1; end while;
		point := [i, j, 0, 1]; found := true;
	end if;
	
	// then try all three coordinates
	if not found then
		i := 0; j := 0; k := 0;
		while Evaluate(p, [i, S.2, S.3,1]) eq 0 do i := i+1; end while;
		while Evaluate(p, [i, j, S.3, 1]) eq 0 do j := j+1; end while;
		while Evaluate(p, [i, j, k, 1]) eq 0 do k := k+1; end while;
		point := [i, j, k, 1];
	end if;
	
	return point;
end function;


// compute all permutations
// ------------------------
// input:  a sequence 'seq'
// output: the sequence of all premutations of 'seq'
function AllPerms(seq)
	if #seq eq 0 then return [seq]; end if;
	res := [];
	for i := 1 to #seq do
		e := seq[i]; rem := Remove(seq,i);
		res := res cat [[e] cat x : x in AllPerms(rem)];
	end for;
	return res;
end function;


// compute the inverse of a permutation
// ------------------------------------
// input:  a sequence 'seq' of integers, representing a permutation
// output: the sequence representing the inverse permutation
function InvPerm(seq)
	res := [];
	for i := 1 to #seq do
		res[seq[i]] := i;
	end for;
	return res;
end function;


// find a (sparse) automorphism of projective space for Noether normalization
// --------------------------------------------------------------------------
// input:  a polynomial 'p' in four variables, defining a projective surface
// output: an automorphism 'auto' of the polynomial ring (and its inverse)
//         s.t. 'auto(p)' is monic in its last variable
function FindMap(p)
	S := Parent(p);	cmin := 5;
	
	for perm in AllPerms([1..4]) do
		// try this permutation of variables
		tt := hom< S->S | [S.i : i in perm]>;
		bt := hom< S->S | [S.i : i in InvPerm(perm)]>;
		pt := tt(p);
		
		// try to find a point with few non-zeroes
		point := FindProjPoint(pt);
		c := #[i : i in point | not (i eq 0)];
		
		// found a better point
		if c lt cmin then
			cmin := c; t0 := tt; b0 := bt;
			t1 := hom< S->S | S.1 + point[1]*S.4,
			                  S.2 + point[2]*S.4,
			                  S.3 + point[3]*S.4,
			                  S.4>;
			b1 := hom< S->S | S.1 - point[1]*S.4,
			                  S.2 - point[2]*S.4,
			                  S.3 - point[3]*S.4,
					  S.4>;
		end if;
		
		// early abort
		if cmin eq 1 then break; end if;
	end for;
	
	t := t0*t1; b := b1*b0;
	vprintf Resolve: "Projective transformation: %o, %o, %o, %o \n",
	    t(S.1),t(S.2),t(S.3),t(S.4);
	return t, b;
end function;




// ======================
// = Exported functions =
// ======================
forward ResolveSurfaceCovering;

// compute formal desingularization of a projective surface
// --------------------------------------------------------
// Computes a formal desingularization of the projective surface defined by
// 'surf' where 'surf' is a homogeneous, irreducible polynomial of degree 'd'
// in four variables, say, 'x', 'y', 'z' and 'w', over an algebraic number
// field.
// 
// The first return value is a sequence of elements of the form
// '<<X, Y, Z, W>, o>' where 'X', 'Y', 'Z' and 'W' are univariate
// (non-fractionary) algebraic power series in a common domain s.t.
// 'surf(X,Y,Z,W)=0'. A formal prime divisor of the desingularization is then
// induced by sending 'x' to 'X', 'y' to 'Y', 'z' to 'Z' and 'w' to 'W'.
// Finally 'o' is the adjoint order at that divisor.
// 
// If 'AdjComp' is set to 'true' then only a subset of a formal
// desingularization is computed which is still sufficient for computations
// of sheaves of differentials of the first kind.
// 
// If the ground field has to be extended, the algebraic elements will be
// assigned the name 'ExtName_i' where 'i' starts from 'ExtCount'. The last
// return value is the value of 'ExtCount' plus the number of field extensions
// that have been introduced during the computation.
intrinsic FormallyResolveProjectiveHypersurface(surf::RngMPolElt
	: AdjComp := false, ExtName := "gamma", ExtCount := 0)
-> List, RngIntElt
{
Compute a formal desingularization of the projective surface defined by the
irreducible, homogeneous polynomial 'surf' in four variables (over a field of
characteristic zero).
}
	S := Parent(surf); F := BaseRing(S);
	require (Rank(S) eq 4) and IsHomogeneous(surf) and IsField(F) and
			(Characteristic(F) eq 0):
	  "Argument must be a homogeneous polynomial in four variables",
	  "over a field of characteristic 0";
	
	vprint Resolve: "-------- Entering FormallyResolveProjectiveHypersurface ---------";
	
	// find a good transformed surface
	there, _ := FindMap(surf); surf1 := there(surf);
	vprintf Resolve: "there: %o, %o, %o, %o \n",
	               there(S.1), there(S.2), there(S.3), there(S.4);
	
	// produce covering
	S0 := PolynomialRing(F, 3); P := PolynomialRing(S0);
	hh := hom<S -> P | S0.1, S0.2, S0.3, P.1 >;
	surf2 := hh(surf1);
	
	// resolve discriminant
	disc := Discriminant(surf2);
	NCs, EXs, DCs, ExtCount := ResolveProjectiveCurve(disc
	    : ExtName := ExtName, ExtCount := ExtCount);
	vprintf Resolve: "EXs, NCs, DCs: %o, %o, %o\n", #EXs, #NCs, #DCs;
	
	// resolve surface covering
	partial := hh(Derivative(surf1, 4));
	res, ExtCount := ResolveSurfaceCovering(surf2, partial, NCs, EXs, DCs :
	    AdjComp := AdjComp, ExtName := ExtName, ExtCount := ExtCount);
	
	// adapt result
	adptres := [];
	for pd in res do
		mp := there*hh*pd[1];
		flat := PolyRingFlattener(Codomain(mp));
		mp := mp*flat;
		ps := pd[2];
		
		Append(~adptres, <[AlgComb(mp(S.1),ps),AlgComb(mp(S.2),ps),
		    AlgComb(mp(S.3), ps),AlgComb(mp(S.4), ps)], pd[3]>);
	end for;
	
	// return
	vprint Resolve: "-------- Leaving FormallyResolveProjectiveHypersurface ---------";
	return adptres, ExtCount;
end intrinsic;

intrinsic FormallyResolveProjectiveHypersurface(S::Srfc
	: AdjComp := false, ExtName := "gamma", ExtCount := 0)
-> List
{
Compute a formal desingularization of the surface in ordinary projective 3-space
over a field of characteristic zero.
}
	rl := [**];
	if assigned S`res_list then
	  rl := S`res_list;
	  for r in rl do
	    if (r[1] eq 1) then
	      if AdjComp or r[3] then return r[2]; end if;
	    end if;
	  end for;
	end if;
	require IsOrdinaryProjective(S) and Dimension(Ambient(S)) eq 3:
	  "S must be a surface in ordinary projective 3-space";
	require Characteristic(BaseRing(S)) eq 0:
	  "S be defined over a field of characteristic zero for formal desingularization";

	adptres,ec := FormallyResolveProjectiveHypersurface(DefiningPolynomial(S) :
	  AdjComp := AdjComp, ExtName := ExtName, ExtCount := ExtCount);
	Append(~rl,<1,adptres,not AdjComp>);
	S`res_list := rl;
        return adptres;

end intrinsic;


// Resolve affine surface defined by monic equation
// ------------------------------------------------
// As above, but a formal prime divisor is represented as '<<X, Y, Z, W>, o>'
// only. Also 'AdjComp' switch is missing. One can restricts the
// desingularization to the part above the ideal 'Focus'.
intrinsic ResolveAffineMonicSurface(surf::RngUPolElt
	: Focus := 0, ExtName := "gamma", ExtCount := 0)
-> List, RngIntElt
{
Compute a formal desingularization of the affine surface defined by the
irreducible, monic polynomial 'surf' (univariate over bivariate ring over
field of characteristic zero).
}
	vprint Resolve: "------- Entering ResolveAffineMonicSurface --------";
	P := Parent(surf); S0 := BaseRing(P); F := BaseRing(S0);
	
	// resolve discriminant
	disc := Discriminant(surf);
	NCs, EXs, DCs, ExtCount := ResolveAffineCurve(disc
	    : Focus := Focus, ExtName := ExtName, ExtCount := ExtCount);
	vprintf Resolve: "EXs, NCs, DCs: %o, %o, %o\n", #EXs, #NCs, #DCs;
	
	// resolve surface covering
	partial := Derivative(surf); // Better use discriminant?
	res, ExtCount := ResolveSurfaceCovering(surf, partial, NCs, EXs, DCs :
	    AdjComp := false, ExtName := ExtName, ExtCount := ExtCount);
	
	// adapt result
	adptres := [];
	for pd in res do
		flat := PolyRingFlattener(Codomain(pd[1]));
		mp := pd[1]*flat; ps := pd[2];
		
		Append(~adptres, <[AlgComb(mp(S0.1),ps),AlgComb(mp(S0.2),ps),
		    AlgComb(mp(P.1), ps)], pd[3]>);
	end for;
	
	// return
	vprint Resolve: "------- Leaving ResolveAffineMonicSurface --------";
	return adptres, ExtCount;
end intrinsic;


// compute formal desingularization of a "monic" projective surface
// ----------------------------------------------------------------
// (description as above, but surf should be monic in last variable)
function ResolveSurfaceCovering(surface, denom, NCs, EXs, DCs
    : AdjComp := false, ExtName := "gamma", ExtCount := 0)
	vprint Resolve: "----- Entering ResolveSurfaceCovering ------";
	P := Parent(surface); S := BaseRing(P); F := BaseRing(S);
	val := [];
	
	// add valuations for each exceptional divisor ...
	valnum := 0;
	vprintf Resolve: "Valuations for EXs: ";
	for ex in EXs do
		vprintf Resolve: "|";
		// is exceptional divisor essential? ??? ALWAYS ESSENTIAL ???
		if AdjComp and (ex[2][2] eq 1) then
			continue;
		end if;
		
		// compute chart equation
		S1 := Codomain(ex[1]); F1 := BaseRing(S1);
		P1 := PolynomialRing(S1);
		h1 := hom< P -> P1 | ex[1], P1.1 >;
		surface1 := h1(surface);
		
		// structures for analytic neighborhood
		F2 := FunctionField(F1); s := F2.1;
		S2 := PolynomialRing(F2, 1, "glex"); t := S2.1;
		P2 := PolynomialRing(S2); z := P2.1;
		
		// move 'x' to coefficient field
		h2 := hom< P1 -> P2 | hom< S1 -> P2 | s, t >, P2.1 >;
		surface2 := h2(surface1);
		
		// compute series solutions and produce valuations
		_, params, ExtCount := RationalPuiseux(surface2 :
		Duval := true, OnlySingular:= true, ExtName := ExtName,
	        ExtCount := ExtCount);
		for param in params do
			lambda := param[1][1]; root := param[2];
			Gamma, e := Explode(ExponentLattice(root));
			S3 := Domain(root); F3 := BaseRing(S3);
			
			X := PolyToSeries(S3 ! s);
			Y := PolyToSeries(lambda*(S3.1)^e);
			Z := EvaluationPowerSeries(root, [e*RSpace(Integers(), 1).1],
			                [PolyToSeries(S3.1)]);
			
			ord := ElementOrder(h1(denom),X,Y,Z) -
			       (JacobianOrder(ex[1],X,Y)+e-1);
			if not(AdjComp and (ord le 0)) then
				Append(~val, [* h1, [X, Y, Z], ord *]);
				vprintf Resolve: ".";
				valnum := valnum + 1;
			end if;
		end for;
	end for;
	vprintf Resolve: "\nNumber of valuations for EX: %o\n", valnum;
	
	
	// add valuations for each normal crossing locus ...
	valnum := 0;
	vprintf Resolve: "Valuations for NCs: ";
	for nc in NCs do
		vprintf Resolve: "|";
		// is normal crossing essential?
		if AdjComp and (nc[2][2] eq 1 or nc[3][2] eq 1) then
			continue;
		end if;
		
		// compute chart equation
		S1 := Codomain(nc[1]); F1 := BaseRing(S1);
		P1 := PolynomialRing(S1);
		h1 := hom< P -> P1 | nc[1], P1.1 >;
		surface1 := h1(surface);
		
		// compute valuations
		isos, ExtCount := ToroidalIsos(surface1, nc[3][1],
		    AdjComp, ExtName, ExtCount);
		
		// add valuations
		for v in isos do
			ord := ElementOrder(h1(denom),v[1],v[2],v[3])-
			       (JacobianOrder(nc[1],v[1],v[2])+v[4]);
			if not(AdjComp and (ord le 0)) then
				Append(~val, [* h1, [v[1], v[2], v[3]],
				                ord *]);
				vprintf Resolve: ".";
				valnum := valnum + 1;
			end if;
		end for;
	end for;
	vprintf Resolve: "\nNumber of valuations for NC: %o\n", valnum;
	
	
	// add valuations for each factor of the discriminant ...
	valnum := 0;
	vprintf Resolve: "Valuations for DCs: ";
	for dc in DCs do
		vprintf Resolve: "|";
		f := dc[2][1];
		
		// is curve component essential?
		if AdjComp and (dc[2][2] eq 1) then
			continue;
		end if;
		
		// compute chart equation
		S0 := Codomain(dc[1]); F0 := BaseRing(S0);
		P0 := PolynomialRing(S0);
		h0 := hom< P -> P0 | dc[1], P0.1 >;
		surface0 := h0(surface);
		
		// structures for analytic neighborhood
		uni, fu, i := IsUnivariate(f);
		if uni then
			roots, ExtCount := AllRoots(fu : ExtName := ExtName,
						ExtCount := ExtCount);
			solfu := roots[1][1]; F1 := Parent(solfu);
			F2 := FunctionField(F1); AssignNames(~F2, ["s"]);
		else
			F1 := FunctionField(F); AssignNames(~F1, ["s"]);
			fb := hom< S0 -> R | F1.1, R.1>(f)
					where R is PolynomialRing(F1);
			roots, ExtCount := AllRoots(fb : ExtName := ExtName,
						ExtCount := ExtCount);
			solfb := roots[1][1]; F2 := Parent(solfb);
		end if;
		S2 := PolynomialRing(F2, 1, "glex"); t := S2.1;
		P2 := PolynomialRing(S2);
		
		// plane morphism
		if uni then
			if i eq 1 then
				c2h := hom< S0 -> S2 | solfu + t, F2.1 >;
			else
				c2h := hom< S0 -> S2 | F2.1, solfu + t >;
			end if;
		else
			c2h := hom< S0 -> S2 | F1.1 + t, solfb >;
		end if;
		
		// space morphism
		s2h := hom< P0 -> P2 | c2h, P2.1 >; surface2 := s2h(surface0);
		
		// compute series solutions and produce valuations
		_, params, ExtCount := RationalPuiseux(surface2 :
		Duval := true, OnlySingular:= true, ExtName := ExtName,
		ExtCount := ExtCount);
		for param in params do
			lambda := param[1][1]; root := param[2];
			Gamma, e := Explode(ExponentLattice(root));
			S3 := Domain(root); F3 := BaseRing(S3);
			
			X := PolyToSeries(S3 ! Evaluate(c2h(S0.1),
			                  [lambda * (S3 ! (t^e))]));
			Y := PolyToSeries(S3 ! Evaluate(c2h(S0.2),
			                  [lambda * (S3 ! (t^e))]));
			Z := EvaluationPowerSeries(root, [e*RSpace(Integers(), 1).1],
			                [PolyToSeries(S3 ! t)]);
			
			ord := ElementOrder(h0(denom),X,Y,Z) - (e - 1);
			if not(AdjComp and (ord le 0)) then
				Append(~val, [* h0, [X, Y, Z], ord *]);
				vprintf Resolve: ".";
				valnum := valnum + 1;
			end if;
		end for;
	end for;
	vprintf Resolve: "\nNumber of valuations for DC: %o\n", valnum;
	
	vprint Resolve: "----- Leaving ResolveSurfaceCovering ------";
	return val, ExtCount;
end function;
