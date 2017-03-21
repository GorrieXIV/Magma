freeze;

///////////////////////////////////////////////////////////////////////
//	Transferred functionality from function fields
// Rational functions
// Maps to projective space
// Divisor theory moved to divisors.m
///////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////
// Test function: no_pole_on_curve 
////////////////////////////////////////////////////////////////////////

// THINK:  to be removed
function no_pole_on_curve(C,f)
    // Input: An irreducible, reduced curve C, and f = p/q, 
    // a rational function on the ambient of C.
    // Ouput: true iff the denominator q is coprime to 
    // the defining polynomial of C.
    df := Denominator(f);
    pc := Polynomial(C);
    Rf := Parent(df);
    if Parent(pc) cmpne Rf then
        if IsProjective(C) then 
            pc := Polynomial(AffinePatch(C,1));
        end if;
        pc := Evaluate(pc,[Rf.1,Rf.2]);
    end if;
    return not IsDivisibleBy(df,pc);
end function;

///////////////////////////////////////////////////////////////////////
//			Rational functions
//  Valuation and evaluation at points and places
///////////////////////////////////////////////////////////////////////

intrinsic IsAnalyticallyIrreducible(C::Crv,p::Pt) -> BoolElt
{True iff the curve C has exactly one place at the point p}
    require p in C: "Second argument must be a point of the first";
    Pl := Places(C!p);
    return #Pl eq 1 and Degree(Pl[1]) eq 1;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//			Rational functions
//  Valuation and evaluation at points and places
///////////////////////////////////////////////////////////////////////

intrinsic Evaluate(f::RngElt, p::Pt) -> RngElt
{Evaluate the rational function f at the point p of a scheme.}
    X := Scheme(p);
    if IsCurve(X) then
	F := FunctionField(X);
    else
	F := FunctionField(Ambient(X));
    end if;
    coercible,f := IsCoercible(F,f);
    require coercible: "First argument is not a function on the scheme "
	    * "containing the second argument";
    return f(p);
end intrinsic;

intrinsic '@'(p::Pt,f::FldFunFracSchElt) -> RngElt
    {Evaluate the rational function f at the point p of a scheme.}
    X := Scheme(p);
    /*
    Want to use TotalRingOfQuotients here when it exists?
    No:  this evaluation should be the trivial thing of evaluating
    num and denom whenever possible, and TRQ won't exist when scheme
    is defined over a non-gb coeff ring.
    */
    F := FunctionField(Ambient(X));
    coercible,f := IsCoercible(F,f);
    require coercible: "First argument is not a function on the scheme "
	    * "containing the second argument";
    // curves can use their function fields to handle more complicated
    // evaluations, so do the curve case separately.
    if IsCurve(X) then

        // first try  naive evaluation, as it's faster 
        // (only in the case where you get 0/0 that you need to 
        //  worry about whether there's more than one place!)
        n,d := IntegralSplit(f,Ambient(X));
        cp := Coordinates(p);
        den := Evaluate(d,cp);
        num := Evaluate(n,cp);
        if den ne 0 then return num/den;
        elif num ne 0 then return Infinity();
        end if;

	F := FunctionField(X);
	coercible,ff := IsCoercible(F,f);
	if coercible then
	    pls := Places(p);
	    _,m := AlgorithmicFunctionField(F);
	    val := Evaluate(m(ff),FunctionFieldPlace(pls[1]));
	    // if more than 1 place over p, check function well defined.
	    //  Must allow this case as user may well have defined a
	    //  perfectly good function on a singular curve that he wants to
	    //  evaluate at a singular point!
	    for i in [2..#pls] do
		error if not(val cmpeq Evaluate(m(ff),FunctionFieldPlace(pls[i]))),
		    "First argument not well-defined at second";
	    end for;
	    return val;
	end if;
    end if;
/*
    // Move to the projective closure for default easy evaluation.
    // (This cannot handle the case when naive evaluation is to zero/zero.)
    f := ProjectiveFunction(f);
    m := ProjectiveClosureMap(Ambient(X));
    cp := Coordinates(m(p));
    den := Evaluate(Denominator(f),cp);
    num := Evaluate(Numerator(f),cp);
*/
    n,d := IntegralSplit(f,Ambient(X));
    cp := Coordinates(p);
    den := Evaluate(d,cp);
    num := Evaluate(n,cp);
    require ((num ne 0) or (den ne 0)):
      "Unable to evaluate: the function (or the given representation of it)"
      * " is not well defined at the given point";

    return ((den eq 0) select Infinity() else num/den);
end intrinsic;

intrinsic Evaluate(f::FldFunFracSchElt,p::PlcCrvElt) -> RngElt
{Evaluate the rational function f at degree 1 place p of a curve}
    F := FunctionField(Curve(p));
    coercible,f := IsCoercible(F,f);
    require coercible: "First argument is not a function on the scheme "
                * "containing the second argument";
    _,m := AlgorithmicFunctionField(F);
    return Evaluate(m(f),FunctionFieldPlace(p));
end intrinsic;

intrinsic Valuation(f::RngElt,p::Pt) -> RngIntElt
{The valuation of the rational function f at the nonsingular
(or analytically irreducible) point p of a curve}
    bool,C := IsCurve(Scheme(p));
    require bool: "Second argument must be a point on a curve";
    p := C ! p;
    pls := Places(p);
    require #pls eq 1: "Second argument does not determine a unique place";
    return Valuation(f,pls[1]);
end intrinsic;

intrinsic Valuation(f::RngElt,p::PlcCrvElt) -> RngIntElt
{The valuation of the rational function f at the place p of a curve}
    C := Curve(p);
    assert IsField(BaseRing(C));
    coercible,f := IsCoercible(FunctionField(C),f);
    require coercible: "First argument is not a function on the scheme "
                * "containing the second argument";
    _,m := AlgorithmicFunctionField(FunctionField(C));
    return Valuation(m(f),FunctionFieldPlace(p));
end intrinsic;

intrinsic Valuation(p::Pt) -> Map
{The valuation of the function field of the curve on which nonsingular
point p lies}
    bool,C := IsCurve(Scheme(p));
    require bool and IsNonsingular(C,p):
	"Point must be a nonsingular point of some curve";
    require IsField(BaseRing(C)) : 
			"Point must be of a scheme defined over a field";
    return map< FunctionField(C) -> Integers() | f :-> Valuation(f,p) >;
end intrinsic;

intrinsic Valuation(p::PlcCrvElt) -> Map
{The valuation of the function field of the curve on which place p lies}
    return map< FunctionField(Curve(p)) -> Integers() | f :-> Valuation(f,p) >;
end intrinsic;

intrinsic FieldOfGeometricIrreducibility(C::Crv) -> Rng,Map
{The exact constant field of the function field F of the curve C, that is the
algebraic closure in F of the constant field of F together with the
inclusion map}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    return ExactConstantField(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic NumberOfPlacesDegECF(C::Crv[FldFin],m::RngIntElt) -> RngIntElt
{The number of places of degree m (over the field of geometric irreducibility) on the curve C defined over a finite field}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    F := AlgorithmicFunctionField(FunctionField(C));
    return NumberOfPlacesDegECF(F,m);
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOneECF(C::Crv[FldFin]) -> RngIntElt
{The number of places of degree one (over the field of geometric irreducibility) on the curve C defined over a finite field}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    F := AlgorithmicFunctionField(FunctionField(C));
    return NumberOfPlacesOfDegreeOneECF(F);
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOneECF(C::Crv[FldFin],m::RngIntElt) -> RngIntElt
{The number of places of degree one on the curve C defined over the finite
extension of degree m of the finite base field of C}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    F := AlgorithmicFunctionField(FunctionField(C));
    return NumberOfPlacesOfDegreeOneECF(F,m);
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOneECFBound(C::Crv[FldFin]) -> RngIntElt
{The number of places of degree one (over the field of geometric irreducibility) on the curve C defined over a finite field}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    F := AlgorithmicFunctionField(FunctionField(C));
    return NumberOfPlacesOfDegreeOneECFBound(F);
end intrinsic;

intrinsic NumberOfPlacesOfDegreeOneECFBound(C::Crv[FldFin],m::RngIntElt) -> RngIntElt
{The number of places of degree one on the curve C defined over the finite
extension of degree m of the finite base field of C}
    require HasFunctionField(C) : "Curve must be able to have a function field computed";
    F := AlgorithmicFunctionField(FunctionField(C));
    return NumberOfPlacesOfDegreeOneECFBound(F,m);
end intrinsic;

intrinsic IsAbsolutelyIrreducible(C::Crv) -> BoolElt
{True iff the degree of the exact constant field of the curve C is 1}
    require IsField(BaseRing(C)) : "Curve must be defined over a field";
    if ISA(Type(C),CrvPln) then
      F := DefiningPolynomial(C);
      facts := Factorisation(F);
      if #facts gt 1 then return false; end if; // C not irreducible!
      if facts[1][2] ne 1 then // C not reduced
         C := Curve(facts[1][1]); // replace with reduced curve
      end if;
    else
      if not HasFunctionField(C) then
        return false;  //BAD! Should really run this on the reduced curve!
      end if;
    end if;
    return DegreeOfExactConstantField(AlgorithmicFunctionField(
                FunctionField(C))) eq 1;
end intrinsic;

intrinsic CommonZeros(C::Crv, L::[FldFunFracSchElt]) -> SeqEnum
{Return the common zeros of the elements of the sequence L as places of the 
curve C}
    require HasFunctionField(C):
	 "Curve must be able to have a function field computed";
    bool, L := CanChangeUniverse(L, FunctionField(C));
    require bool : "Sequence must contain functions on argument 1";
    return CommonZeros(L);
end intrinsic;

intrinsic CommonZeros(L::[FldFunFracSchElt[Crv]]) -> SeqEnum
{Return the common zeros of the elements of the sequence L as places of the 
parent curve C}
    F := Universe(L);
    C := Curve(F);
    _,m := AlgorithmicFunctionField(F);
    Z := CommonZeros([m(f):f in L]);
    return [CurvePlace(C, z) : z in Z];
end intrinsic;

intrinsic TwoGenerators(P::PlcCrvElt) -> FldFunFracSchElt, FldFunFracSchElt
{Two algebraic functions of which P is the unique common zero.}
    C := Curve(P);
    _,m := AlgorithmicFunctionField(FunctionField(C));
    f,g := TwoGenerators(FunctionFieldPlace(P));
    return minv(f),minv(g) where minv is Inverse(m);
end intrinsic;

intrinsic WeierstrassPlaces(C::Crv) -> SeqEnum
{The weierstrass places of the (zero divisor of the) curve C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return [CurvePlace(C, p) : p in WeierstrassPlaces(AlgorithmicFunctionField(FunctionField(C)))];
end intrinsic;

intrinsic GapNumbers(C::Crv) -> SeqEnum
{The gap numbers of the curve C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return GapNumbers(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic GapNumbers(C::Crv, P::PlcCrvElt) -> SeqEnum
{The gap numbers of the curve C at the degree 1 place P}
    require HasFunctionField(C) : "Curve must have a computable function field";
    require FunctionField(Curve(P)) eq FunctionField(C) :
					"Curve and place are not compatible";
    require Degree(P) eq 1 : "Place must have degree 1";
    return GapNumbers(AlgorithmicFunctionField(FunctionField(C)), FunctionFieldPlace(P));
end intrinsic;

intrinsic RamificationDivisor(C::Crv) -> DivCrvElt
{The ramification divisor of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return RamificationDivisor(DivisorGroup(C)!0);
end intrinsic;

intrinsic WronskianOrders(C::Crv) -> SeqEnum
{The wronskian orders of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return WronskianOrders(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic SerreBound(C::Crv[FldFin]) -> RngIntElt
{The Serre bound on the number of places of degree 1 of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return SerreBound(C, 1);
end intrinsic;

intrinsic SerreBound(C::Crv[FldFin], m::RngIntElt) -> RngIntElt
{The Serre bound on the number of places of C of degree m
over the base field}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return SerreBound(AlgorithmicFunctionField(FunctionField(C)), m);
end intrinsic;

intrinsic IharaBound(C::Crv[FldFin]) -> RngIntElt
{The Ihara bound on the number of places of degree 1 of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return IharaBound(C, 1);
end intrinsic;

intrinsic IharaBound(C::Crv[FldFin], m::RngIntElt) -> RngIntElt
{The Ihara bound on the number of places of C of degree m
over the base field}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return IharaBound(AlgorithmicFunctionField(FunctionField(C)), m);
end intrinsic;

intrinsic LPolynomial(C::Crv[FldFin]) -> RngUPolElt
{The L-polynomial of the curve C (with respect to the field of geometric 
irreducibility)}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return LPolynomial(C, 1);
end intrinsic;

intrinsic LPolynomial(C::Crv[FldFin], m::RngIntElt) -> RngUPolElt
{The L-polynomial of the curve C over the extension of degree m of its base field (with respect to the field of geometric irreducibility)}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return LPolynomial(AlgorithmicFunctionField(FunctionField(C)), m);
end intrinsic;

intrinsic ZetaFunction(C::Crv[FldFin]) -> FldFunRatUElt
{The zeta function of the curve C (with respect to the field of geometric 
irreducibility}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return ZetaFunction(C, 1);
end intrinsic;

intrinsic ZetaFunction(C::Crv[FldFin], m::RngIntElt) -> FldFunRatUElt
{The zeta function of the curve C over the extension of degree m of its base field (with respect to the field of geometric irreducibility)}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return ZetaFunction(AlgorithmicFunctionField(FunctionField(C)), m);
end intrinsic;

intrinsic ClassGroupAbelianInvariants(C::Crv[FldFin]) -> SeqEnum
{The abelian invariants of the divisor class group of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return ClassGroupAbelianInvariants(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic ClassGroupPRank(C::Crv[FldFin]) -> RngIntElt
{The p-rank of the class group of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return ClassGroupPRank(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic HasseWittInvariant(C::Crv[FldFin]) -> RngIntElt
{The Hasse-Witt invariant of C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return HasseWittInvariant(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic DivisorOfDegreeOne(C::Crv[FldFin]) -> DivCrvElt
{A divisor of degree 1 over the field of geometric irreducibility of the curve C}
    require HasFunctionField(C) : "Curve must have a computable function field";
    return CurveDivisor(C, DivisorOfDegreeOne(AlgorithmicFunctionField(FunctionField(C))));
end intrinsic;

intrinsic DimensionOfFieldOfGeometricIrreducibility(C::Crv) -> RngIntElt
{The dimension of the field of geometric irreducibility of C over the base ring of C};
    require HasFunctionField(C) : "Curve must have a computable function field";
    return DimensionOfExactConstantField(AlgorithmicFunctionField(FunctionField(C)));
end intrinsic;

intrinsic Expand(f::FldFunFracSchElt, P::PlcCrvElt : AbsPrec := 10, RelPrec := 10) -> RngSerElt, FldFunFracSchElt
{Expand the element f at the place P to a series of given precision and also return the uniformizing parameter};
    C := Curve(P);
    require f in FunctionField(C) : "Arguments are not compatible";
    A, m := AlgorithmicFunctionField(FunctionField(C));
    if AbsPrec ne 10 then
	require RelPrec eq 10 : "Only one precision parameter can be set";
	s, u := Expand(m(f), FunctionFieldPlace(P) : AbsPrec := AbsPrec);
    else
	s, u := Expand(m(f), FunctionFieldPlace(P) : RelPrec := RelPrec);
    end if;
    return s, u @@ m;
end intrinsic;

intrinsic Completion(F::FldFunFracSch[Crv], P::PlcCrvElt : Precision := 20) -> RngSerLaur, Map
{The Completion of the function field F at the place P and the map into that series ring}
    C := Curve(P);
    require F eq FunctionField(C) : "Arguments are not compatible";
    A, m := AlgorithmicFunctionField(FunctionField(C));
    Cpl, cm := Completion(A, FunctionFieldPlace(P) : Precision := Precision);
    return Cpl, m * cm;
end intrinsic;

intrinsic Relations(L::[FldFunFracSchElt[Crv]]) -> ModTupRng
{The module of R linear relations between the elements of L where R is the base field 
of the curve of the elements of L}
    return Relations(L, 0);
end intrinsic;

intrinsic Relations(L::[FldFunFracSchElt[Crv]], m::RngIntElt) -> ModTupRng
{The module of R linear relations between the elements of L where R is the base ring of the curve of the elements of L. m is a reduction parameter.}
    A, mp := AlgorithmicFunctionField(Universe(L));
    return Relations(L@mp, BaseRing(Curve(Universe(L))), m);
end intrinsic;

intrinsic Module(L::[FldFunFracSchElt[Crv]]) -> Mod, Map, SeqEnum
{The R-module generated by the elements of L where R is the base field of the curve of the elements of L}
    A, m := AlgorithmicFunctionField(Universe(L));
    M, mm, p := Module(m(L), BaseRing(Curve(Universe(L))):PreImages := true);
    mmm := map<M -> Universe(L) | x :-> mm(x) @@ m>;
    return M, mmm, p;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//			Place/Places Helper Function
//  More efficient function to find the maximal affine ideal of a point
//  on an affine scheme defined over a finite field extension of the base
//  field. Suggested by Steve Donnelly and partially adapted from his code.
//  mch - 10/08
///////////////////////////////////////////////////////////////////////

intrinsic InternalMaximalEquations(pt::Pt,mpols::SeqEnum) -> SeqEnum
{Internal function}
// Function takes the point pt and the sequence of minimal polynomials of
// the coordinates of the point over the base field (field of the scheme).
// Returns a sequence of defining polys for the maximal ideal.

    L := Ring(Parent(pt));
    S := Scheme(Parent(pt));
    K := BaseRing(S);
    coords := Eltseq(pt);

    // if pt is on an affine patch of a curve with function field,
    //  try to choose the base index <-> the base var of the FF
    if IsAffine(S) and ISA(Type(S),Crv) and (FFPatchIndex(S) ne 0) then
	F := FunctionField(S);
	AFF,fmp := AlgorithmicFunctionField(F);
	F1 := AFF;
	while IsFinite(Degree(F1)) do F1 := BaseField(F1); end while;
	bv := AFF!(F1.1);
	P := CoordinateRing(Ambient(S));
	i0 := Rank(P);
	while i0 gt 0 do
	    if bv eq fmp(F!(P.i0)) then break; end if;
	    i0 -:= 1;
	end while;
    else
	i0 := 0;	
    end if; 

    // convert top field L to be a direct extension of K if necessary
    if(BaseField(L) ne K) then
	if ISA(Type(L),FldAlg) then
	    L := RelativeField(K,L);
	else
	    assert Type(L) eq FldFin;
	    L1 := ext<K|MinimalPolynomial(PrimitiveElement(L),K)>;
	    Embed(L,L1);
            L := L1;
	end if;
	coords := [L!c : c in coords];
    end if;

    d := Degree(L);
    n := #coords;
    R := Universe(mpols); // = K[x1,..,xn] - mpols[i]=fi(xi), fi the min poly of coords[i]
    degs := [Degree(mpols[i],i) : i in [1..#mpols]];
    
    max_degs := [j : j in [1..n] | degs[j] eq d];
    // special (usual!) case : one coordinate generates L/K
    if #max_degs gt 0 then
	if i0 in max_degs then i := i0;
	else i := max_degs[#max_degs]; end if; //good to pick last for lex ordering?
	mpols_new := [R!0 : j in [1..n]];
	mpols_new[1] := mpols[i];
	gens := [L!1]; gen := gens[1];
        for j in [1..d-1] do gen *:= coords[i]; Append(~gens,gen); end for;
	mat := Matrix(K,[Eltseq(g) : g in gens]);
	vecs := [m1[j] : j in [1..n-1]] where m1 is
		Matrix(K,[Eltseq(coords[j]) : j in [1..n] | j ne i]);
	cs1 := Solution(mat,vecs); k := 1; mons := [(R.i)^j : j in [0..d-1]];
	for j in [1..n] do
	    if j eq i then 
		k := 0;
	    else
		mpols_new[j+k] := R.j - Polynomial(Eltseq(cs1[j+k-1]),mons);
	    end if;
	end for;
	return mpols_new;
    end if;

    // In the general case, replace K with the field generated by a coordinate
    //  of maximal degree in the number field case. Over finite fields be lazy
    //  for now and fall back on the general method.
    if Type(L) eq FldFin then
	I := ideal<R|mpols>;
	ps := RadicalDecomposition(I);
	for p in ps do
	    if &and[Evaluate(b,coords) eq K!0 : b in Basis(p)] then
		return Basis(p);
	    end if;
	end for;
	error "Something went wrong in finding the maximal ideal of the point";
    end if;

    max_degs := [j : j in [1..n] | degs[j] eq dm] where dm is Max(degs);
    if i0 in max_degs then i := i0;
    else i := max_degs[#max_degs]; end if;
    mpoli := mpols[i];
    K1 := ext<K|UnivariatePolynomial(mpoli)>;
    if not(Type(K1) cmpeq FldRat) then 
      Embed(K1,L,coords[i]);
    end if;
    L := RelativeField(K1,L); coords := [L!coords[j] : j in [1..n] | j ne i];
    R1 := PolynomialRing(K1,n-1);
    mps := [Evaluate(MinimalPolynomial(coords[j],K1),R1.j) : j in [1..n-1]];
    mons := [R1!1]; vals := [L!1];
    for j in [1..n-1] do
	val := L!1;
	for k in [1..Degree(mps[j],j)-1] do
	    val *:= coords[j];
	    mons cat:= [m*(R1.j) : m in mons];
	    vals cat:= [val*v : v in vals];
	end for;
    end for;
    if #vals gt 0 then	
	mat := Matrix(K1,[Eltseq(v) : v in vals]);
	ker := KernelMatrix(mat);
	mps cat:= [Polynomial(r,mons) : r in RowSequence(ker)];
    end if;
    B := GroebnerBasis(mps);
    U := PolynomialRing(K);
    hm := hom<R1 -> R | map<K1 -> R | x :-> Evaluate(PolynomialRing(K)!Eltseq(x),R.i)>,
	[R.j : j in [1..n] | j ne i]>;
    return [mpoli] cat [hm(b) : b in B];

end intrinsic;

/////////////// mch - 11/13 - new ZetaFunction function ///////////////////////

intrinsic ZetaFunctionOfCurveModel(C::Crv[FldFin] : Zfn := 0 ) -> FldFunRatUElt
{ Returns the zeta function of the actual (integral) curve C defined over a finite
  field rather than the zeta function of the projective normalisation of C. The
  zeta function of the projective normalisation (which is what the other ZetaFunction
  intrinsics compute) is computed first and this is still the major part of the computation. 
  The parameter Zfn should be set to the zeta function of the projective normalisation
  if this is already known. }

    k := BaseRing(C);
    require Type(k) cmpeq FldFin : "C must be defined over a finite field";
    isAff := IsAffine(C);
    F := Parent(Zfn); 
    if Type(F) cmpeq RngInt then
	Zfn := ZetaFunction(C);
	F := Parent(Zfn);
    end if;
    t := F.1;

    //1. Get data for infinite places if C is affine
    if isAff then
      Cp := ProjectiveClosure(C);
      pcm := ProjectiveClosureMap(Ambient(C));
      z := R.i where i is Index(DefiningPolynomials(pcm),R!1) where R is
		CoordinateRing(Ambient(Cp));
      Z := Scheme(Ambient(Cp),z);
      Dinf := Divisor(Cp,Z); // divisor of 'points at infinity' with some multiplicities
      pl_inf := Support(Dinf); // sequence of places at infinity
      // adjustment factor for the zetafunction
      f_inf := &*[1-t^Degree(p) : p in pl_inf];
    else
      Cp := C;
    end if;

    //2. Get data for singular places on C
    sngs := SingularSubscheme(C);
    if IsEmpty(sngs) then
	pts_scheme := [];
    else
        pts_scheme := PrimeComponents(sngs);
    end if;
    f_sing := F!1;
    for p_sch in pts_scheme do
	Z := Cluster(Ambient(p_sch), Ideal(p_sch)); // make sure its of cluster type;
	d := Degree(Z); // corresponds to d (singular) points over
			// GF(q^d) where k is GF(q)
	if isAff then Z := pcm(Z); end if;
	Dpt := Divisor(Cp,Z);
        pl_pt := Support(Dpt); // sequence of places over the singular point
	if (#pl_pt eq 1) and (Degree(pl_pt[1]) eq d) then
	   continue; // no change to zeta-function
	end if;
	f_sing *:= &*[1-t^Degree(p) : p in pl_pt]/(1-t^d);	
    end for;

    Zf := Zfn*f_sing;
    if isAff then Zf *:= f_inf; end if;
    return Zf;

end intrinsic; 
