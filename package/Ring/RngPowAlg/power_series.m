// *********************************************************************
// * Package: power_series.mag                                         *
// * =========================                                         *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 08.08.2007                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Power series implementation by two subtypes.                    *
// *                                                                   *
// *********************************************************************
freeze;

declare verbose AlgSeries, 1;


// ======================================
// = Auxillary functions (not exported) =
// ======================================

// check for degree ordering - for now just allow glex and grevlex
function hasDegreeOrdering(R)
   return (MonomialOrder(R))[1] in {"glex","grevlex"};
end function;

// find trailing coefficient and monomial
// --------------------------------------
// input:  multivariate polynomial 'p'
// output: '(0,0)' if 'p=0',
//         '(TrailingCoefficient(p),TrailingMonomial(p))' otherwise
function Trailing(p)
	S := Parent(p);
	if (p eq 0) then return 0, S ! 0; end if;
	
	return TrailingCoefficient(p),
	    Monomial(S,Exponents(TrailingTerm(p)));
end function;


// find order of polynomial
// ------------------------
// input:  multivariate polynomial 'p'
// output: '-1' if 'p=0', 'ord(p)' otherwise
function PlOrd(p)
	return TotalDegree(TrailingTerm(p));
end function;


// get initial segment up to total degree less than 'd'
// ----------------------------------------------------
// input:  multivariate polynomial 'c' and integer order 'd'
// output: approximation/truncation of polynomial up to specified order
function Crop(c, d) // ??? is this correct, maybe improvable ???
	// get sequence of terms
	l := Terms(c);
	
	// special cases
	if (#l eq 0) or (TotalDegree(l[#l]) ge d) then
		return Parent(c) ! 0;
	end if;
	if TotalDegree(l[1]) lt d then
		return c;
	end if;
	
	// find least position of a term with degree 'd'
	i := 1; j := #l;
	while (j-i) gt 1 do
		p := (j+i) div 2;
		if TotalDegree(l[p]) ge d then
			i := p;
		else
			j := p;
		end if;
	end while;
	
	// produce cropped polynomial
	res := RemoveLeadingTerms(c, i);
	//assert res eq &+l[i+1..#l];
	return res;
end function;


// scale exponents of multivariate polynomials
// -------------------------------------------
// input:  multivariate polynomial 's', integer 'e'
// output: polynomial 's' after substitution 'x_i :-> x_i^e' for all 'i'
function ScalePolynomial1(s, e)
	S := Parent(s);
	
	scl := []; for i:=1 to Rank(S) do Append(~scl, (S.i)^e); end for;
	sn := map<S -> S | x :-> Evaluate(x, scl)>(s);
	
	return sn;
end function;


// apply above function to exponents of univariate polynomial
// ----------------------------------------------------------
// input:  univariate polynomial 'p' over multivariate polynomial ring,
//         integer 'e'
// output: polynomial 'p' after applying 'ScalePolynomial1' to
//         its coefficients
function ScalePolynomial2(p, e)
	P := Parent(p);	S := BaseRing(P);
	pn :=
	hom<P -> P | map<S -> P | x :-> P ! ScalePolynomial1(x, e)>, P.1>(p);
	
	return pn;
end function;


// crop down a polynomial according to a slope
// -------------------------------------------
// input:  a univariate polynomial 'p' over a multivariate polynomial ring
//         and integers 'ord' and 'slope'
// output: cropped polynomial which is still suitable for expanding
function TruncDefPoly(p, ord, slope)
	return Parent(p) !
	    [Crop(Coefficient(p,i), ord-i*slope)  : i in [0..Degree(p)]];
end function;

// square and multiply
// -------------------
// input:  a polynomial 's', an exponent 'e' and a degree 'deg'
// output: 's^e' modulo all terms of degree greater or equal 'deg'
function SqM(s, e, deg)

// printf "SqM: e = %o, spar: %o\ns: %o\n", e, Parent(s), s;
// ZEIT := Cputime();

	// early aboard
	if e eq 0 then return Parent(s) ! 1; end if;
	
	// square or multiply according to leading bit
	while not e eq 0 do
	        if IsEven(e) then
// IndentPush();
        	        r := Crop(SqM(s, e div 2, deg)^2, deg);
// IndentPop();
// printf "SqM: e: %o time: %o\n", e, Cputime(ZEIT);
			return r;
	        else
// IndentPush();
        	        r := Crop(s*SqM(s, e - 1, deg), deg);
// IndentPop();
// printf "SqM: e = %o time: %o\n", e, Cputime(ZEIT);
			return r;
	        end if;
	end while;
end function;


// evaluation of polynomials
// -------------------------
// input:  a sequence 'subs' of polynomials and a degree 'deg'
// output: a function that evaluates polynomials at 'subs' modulo all terms of
//         degree greater or equal 'deg'
function EvlMod(subs, deg)
	r := #subs; S := Parent(subs[1]); IVec := RSpace(Integers(), r);
	
	// a function that evaluates modulo 'deg'
	return function(p)
		res := S ! 0;
		
		// substitute in every term
		for trm in Terms(p) do
			// get coefficient and exponent
			cf := LeadingCoefficient(trm); mu := Exponents(trm);
			
			// compute the power product
			prod := S ! 1; for i := 1 to r do
				prod := Crop(prod*SqM(subs[i],mu[i],deg), deg);
			end for;
			
			// add to result
			res := res + cf*prod;
		end for;
		
		return res;
	end function;
end function;

// approximate a defining polynomial
// ---------------------------------
// input:  a univariate polynomial 'p' over a multivariate polynomial ring in
//         'r' variables, a sequence 'subs' of length 'r' of series for
//         substitution, a sequence 'mults' of length 'r' of integers to adapt
//         lattices and an approximation order
// output: approximation up to order 'appord' of 'p' with the elements of
//         'subs' substituted for the variables and a boolean 'good' indicating
//         if approximation was successful
function ApproxDefPoly(p, subs, mults, appord)
	P := Parent(p); R := BaseRing(P);
	S := Domain(subs[1]); Q := PolynomialRing(S);
	
	// expand substitution series
	subsapp := []; good := true;
	for i := 1 to #subs do
		g, app := Expand(subs[i],Ceiling(appord/mults[i]));
		good := good and g;
		Append(~subsapp,Crop(ScalePolynomial1(app, mults[i]), appord));
	end for;
	
	// save by cropped evaluation
	evl := EvlMod(subsapp, appord);
	return hom<P -> Q | hom<R -> S | cf :-> evl(cf)>, Q.1>(p), good;
end function;


// combine lattices
// ----------------
// input:  a sequence 'lats' of lattices of the form '<Gamma, e>' where 'Gamma'
//         is an integral lattice and 'e' the integral denominator
// output: the reduced representation (in the same form) of the sum of 'lats'
//         and a sequence of multiplicities for lattice adaption
function CombinedLattice(series)
	lats := [ExponentLattice(s) : s in series];
	
	// find least common multiple of denominators and cofactors
	denoms := [lat[2] : lat in lats];
	e := denoms[#denoms]; tst := Prune(denoms);
	for d in tst do e := Lcm(e, d); end for;
	mults := [ExactQuotient(e, d) : d in denoms];
	
	// add the scaled lattices
	Gamma := &+[mults[i]*lats[i][1] : i in [1..#lats]];
	
	// return
	return Gamma, e, mults;
end function;


// "evaluation" for lattice based polynomials
// ------------------------------------------
// input:  a sequence of dual vectors 'nu[i]/e' and elements 'v[i]' in some
//         common ring 'R'
// output: a homomorphism from 'P' to 'R' where 'P' is the subring of any
//         polynomial ring (with compatible coefficient field) consisting
//         of polynomials supported on a lattice 'lat' s.t. the 'nu[i]/e' lie
//         in th dual of 'lat', the homomorphism then maps 
//         'x^mu :-> prod_i v[i]^(<nu[i],mu>/e)' where 'x' is the coordinate
//         vector of 'P'
function DualLatticeBasedHom(nu, e, v)
	R := Universe(v); r := #v;
	IVec := RSpace(Integers(), r);
	
	return func< x | &+[R |
	    &*[v[i]^((nu[i], IVec ! Exponents(t)) div e) : i in [1..r]] *
	    LeadingCoefficient(t) : t in Terms(x)] >;
end function;


// structure preserving homomorphisms by scaling of monomial generators
// --------------------------------------------------------------------
// input:  a multivariate polynomial ring 'S', a full integer lattice 'Gamma'
//         of rank, say, 'r' and a sequence 'lambda' of length 'r' of scalars
// output: a homomorphism from 'R' to 'S' where 'R' can be the subring of any
//         multivariate polynomial ring with fractionary exponents (with
//         compatible coefficient field and the right number of variables)
//         consisting of polynomials supported on the lattice '1/f*Gamma', the
//         homomorphism maps 'x^(v_i) :-> lambda[i]*y^(v_i)' (multindex
//         notation) where 'x' is the coordinate vector of 'R', 'y' the one of
//         'S' and 'v_i' is '1/num' times the 'i'-th basis vector of 'Gamma'
function ScalingHelper(S, Gamma, f, lambda)
	dim := Rank(S); IVec := RSpace(Integers(), dim);
	
	// extract data for fast coordinate computation
	B := Transpose((ChangeRing(BasisMatrix(Gamma), Rationals()))^(-1));
	den := 1; for i:=1 to dim do for j:=1 to dim do
		den := Lcm(den, Denominator(B[i,j]));
	end for; end for;
	duals := [IVec ! [ExactQuotient(Numerator(e)*den,Denominator(e))
	    : e in r] : r in RowSequence(B)];
	
	// construct parametrized transformation
	crd := func<i, t, n | ExactQuotient(
	    n*(duals[i], (IVec ! Exponents(t))), den)>;
	return func<s, e | &+[S | (S ! t)*&*[lambda[i]^crd(i, t, f div e)
	    : i in [1..#lambda]] : t in Terms(s)]>;
end function;


// apply a structure preserving homomorphism
// -----------------------------------------
// input:  a series and a structure preserving homomorphism
//         'fun' for approximations
// output: the series with 'fun' applied
forward ASHA, ASHB;
function ApplyStructureHom(series, fun)
	typ := series`type;
	
	case typ:
		when 0: //atomic
			return ASHA(series, fun);
		when 1: //substitution
			return ASHB(series, fun);
		else
			error "not available for this series type";
	end case;
end function;
function ASHA(sA, fun)
	cop := Copy(sA);
	
	// apply homomorphism to init part
	cop`init := fun(cop`init, cop`e);
	
	if assigned cop`subs then
		// apply homomorphism to substitution series
		cop`subs := [ApplyStructureHom(s, fun): s in cop`subs];
	else
		// apply homomorphism to defining polynomial
		P := Parent(cop`defpol); S := BaseRing(P);
		Sext := Parent(cop`init); Pext := ChangeRing(P, Sext);
		cop`defpol := hom<P -> Pext | map<S -> Sext |
		    x :-> fun(x, 1)>, P.1>(cop`defpol);
	end if;
	
	return cop;
end function;
function ASHB(sB, fun)
	// apply homomorphism to substitution series
	new_subs := [ApplyStructureHom(s, fun): s in sB`subs];
	new_ser := InternalAlgebraicSeriesS(sB`series,
		sB`duals,new_subs,sB`e,sB`Gamma);
	new_ser`magic := sB`magic; new_ser`mults := sB`mults;

	return new_ser;

end function;




// ======================
// = Exported functions =
// ======================

// information retrieval
// =====================

// get underlying polynomial domain
forward DA, DB;
intrinsic Domain(series::SerPowAlg)
-> RngMPol
{
Get the domain of the power series (resp. its polynomial approximants).
}
	typ := series`type;
	
	case typ:
		when 0: //atomic
			return DA(series);
		when 1: //substitution
			return DB(series);
		else
			require false : "not available for this series type";
	end case;
end intrinsic;
function DA(sA)
	return Parent(sA`init);
end function;
function DB(sB)
	return Domain(sB`subs[1]);
end function;


// get lattice of exponents
intrinsic ExponentLattice(series::SerPowAlg)
-> Tup
{
Get the exponent lattice of the power series represented by 'series'.
}	
	return <series`Gamma, series`e>;
end intrinsic;


// real work
// =========

// expand a series
forward  EB;
intrinsic Expand(series::SerPowAlg, ord::RngIntElt)
-> BoolElt, RngMPolElt
{
Given a representation 'series' of a power series 'alpha'. Let
'beta := alpha(x_1^e,...,x_n^e)' where 'e' is the denominator of the exponent
lattice in 'tagged_series'. Return the expansion of 'beta' up to order less
than 'ord'.
}
	typ := series`type;
	
	case typ:
		when 0: //atomic
			return InternalExpand(series,ord);
		when 1: //substitution
			return EB(series,ord);
		else
			require false : "not available for this series type";
	end case;

end intrinsic;


function EB(sB, ord)
	IVec := RSpace(Integers(), Rank(Domain(sB`series)));
	S := Domain(sB`subs[1]);
	
	// compute a sufficient approximation of substitution series
	subsapp := []; //good := true;
	for i := 1 to #sB`subs do
		g, app := Expand(sB`subs[i], Ceiling(ord/sB`mults[i]));
		if not g then return g,_; end if;
		Append(~subsapp,Crop(ScalePolynomial1(app, sB`mults[i]), ord));
	end for;
	
	// compute a sufficient approximation of parent series
	_, f := Explode(ExponentLattice(sB`series));
	parord := Ceiling((f*ord)/sB`magic);
	g, parapp := Expand(sB`series, parord);
	if not g then return g,_; end if;
	
	// compute a sufficient approximation of parent series
	_, f := Explode(ExponentLattice(sB`series));
	parord := Ceiling((f*ord)/sB`magic);
	g, parapp := Expand(sB`series, parord);
	if not g then return g,_; end if;
	
	// transform parent series
	F := BaseRing(S); Saux := PolynomialRing(F, #sB`subs, "glex");
	trans := Saux ! 0;
	for trm in Terms(parapp) do
		// get coefficient and exponent
		cf := LeadingCoefficient(trm); mu := IVec ! Exponents(trm);
		
		// get new exponent
		nmu := [(nu, mu) div f : nu in sB`duals];
		
		// add new term to result
		trans := trans + (F ! cf)*Monomial(Saux, nmu);
	end for;
	
	// substitute
	return true, EvlMod(subsapp, ord)(trans);
end function;


// get defining polynomial
forward DPA, DPB;
intrinsic DefiningPolynomial(series::SerPowAlg)
-> RngUPolElt
{
Get the defining polynomial of the power series represented by 'tagged'.
}
	typ := series`type;
	
	case typ:
		when 0: //atomic
			return DPA(series);
		when 1: //substitution
			return DPB(series);
		else
			require false : "not available for this series type";
	end case;
end intrinsic;
function DPA(sA)
	// maybe just read of defining polynomial
	if not assigned sA`subs then
		return sA`defpol;
	end if;
	
	// otherwise compute resultants
	P := Parent(sA`defpol);	R := BaseRing(P);
	S := Domain(sA`subs[1]);
	m := Rank(R); n := Rank(S);
	F := BaseRing(S); Q := PolynomialRing(S);
	
	// universal polynomial domain and homomorphisms to and from
	U := PolynomialRing(F, m+n+1);
	// !!! assure compatibility of fields !!!
	thereR := hom<R -> U | [U.i : i in [1..m]]>;
	thereP := hom<P -> U | thereR, U.(m+n+1)>;
	thereS := hom<S -> U | [U.(m+i) : i in [1..n]]>;
	thereQ := [hom<Q -> U | thereS, U.i> : i in [1..m]];
	backQ := hom<U -> Q | [Q | 0 : i in [1..m]] cat
	                      [Q | S.i : i in [1..n]] cat [Q.1]>;
	
	// eliminate variables
	q := thereP(sA`defpol);
	for i := 1 to m do
	  q := Resultant(q, thereQ[i](DefiningPolynomial(sA`subs[i])), i);
	end for;
	
	// return the iterated resultant (squarefree part)
	return backQ(SquarefreePart(q));
end function;
function DPB(sB)
	// compute resultants
	defpol0 := DefiningPolynomial(sB`series);
	P := Parent(defpol0); R := BaseRing(P);
	S := Domain(sB`subs[1]); F := BaseRing(S); Q := PolynomialRing(S);
	m := Rank(R); n := Rank(S);
	
	// universal polynomial domain and homomorphisms to and from
	U := PolynomialRing(F, m+n+1);
	// !!! assure compatibility of fields !!!
	thereR := hom<R -> U | [U.i : i in [1..m]]>;
	thereP := hom<P -> U | thereR, U.(m+n+1)>;
	thereS := hom<S -> U | [U.(m+i) : i in [1..n]]>;
	thereQ := [hom<Q -> U | thereS, U.i> : i in [1..m]];
	backQ := hom<U -> Q | [Q | 0 : i in [1..m]] cat
	                      [Q | S.i : i in [1..n]] cat [Q.1]>;
	
	// eliminate variables
	q := thereP(defpol0);
	Saux := PolynomialRing(F, #sB`subs, "glex");
	for i := 1 to m do
		expo := [sB`duals[j][i] : j in [1..#sB`duals]];
		aux := AlgComb(Monomial(Saux, expo), sB`subs);
		newpol := DefiningPolynomial(aux);
	  	q := Resultant(q, thereQ[i](newpol), i);
	end for;
	
	// return the iterated resultant (squarefree part)
	return backQ(SquarefreePart(q));
end function;


// order of a series
intrinsic Order(series::SerPowAlg: TestZero := false)
-> RngIntElt
{
Given a series 'series' return its order times the exponent denominator,
i.e., the order of the first term returned by 'Expand'. If 'series' is
the zero series, this function will not terminate. Set 'TestZero' to 'true' if
you want a return value of '-1' in this case. But note that zero testing is
expensive and the return value 'infinity' would be more appropriate for most
applications.
}
	// return minus one for zero series
	if TestZero and IsZero(series) then
		return -1;
	end if;
	
	// search step by step for first non-vanishing term
	ord := 1; while true do
		good, app := Expand(series, ord);
		require good : "series not expandable";
		if app ne 0 then
			return ord-1;
		end if;
		ord := ord + 1;
	end while;
end intrinsic;


// simplification (if it really is!?)
// ==================================

// transform to an atomic representation(no substitutions, irred. def. pol.)
forward FactorDefPol;
intrinsic SimplifyRep(series::SerPowAlg: Factorizing := true)
-> SerPowAlg
{
Simplifies the representation of series 'series'. This is an expensive
operation, but subsequent operations on 'series' will be fast.
}
	vprint AlgSeries : "-------- Entering SimplifyRep ---------";
	// compute defining polynomial and exponent lattice
	vprintf AlgSeries : "Computing defining polynomial: ";
	defpol := DefiningPolynomial(series);
	P := Parent(defpol);
	Gamma, e := Explode(ExponentLattice(series));
	
	// compute large enough initial segment
	scaledpol := ScalePolynomial2(defpol, e);
	ord := 1; while true do // ??? is this optimal: development of ord ???
		vprintf AlgSeries : "done\n";
		vprintf AlgSeries : "checking initial segment order %o: ",ord;
		// compute Newton polygon of translated defining polynomial
		good, init := Expand(series, ord);
		require good : "series not expandable";
		tstpol := Evaluate(scaledpol, P.1 + init);
		ordcf0 := PlOrd(Coefficient(tstpol,0));
		ordcf1 := PlOrd(Coefficient(tstpol,1));
		
		// does linear coefficient exits?
		if ordcf1 eq -1 then
			ord := 2*ord; continue;
		end if;
		magic := ordcf1;
		
		// linear order should be correct!
		if magic ge ord then
			ord := magic + 1; continue;
		end if;
		
		// is linear edge slope large enough?
		if (ordcf0 eq -1) or (ordcf0 - ordcf1) ge ord then
			break;
		end if;
		
		// another round...
		ord := 2*ord;
	end while;
	vprintf AlgSeries : "enough\n";
	
	// generate atomic representation and factorize defining polynomial
	sA := InternalAlgebraicSeries(defpol, init, [], e, Gamma);
	if Factorizing then
		vprintf AlgSeries: "Factorizing defining polynomial: ";
		sA := FactorDefPol(sA);
		vprintf AlgSeries : "done\n";
	end if;
	vprint AlgSeries : "-------- Leaving SimplifyRep ---------";
	return sA;
end intrinsic;
// factorize defining polynomial and choose right irreducible factor
function FactorDefPol(sA)
	defpol := sA`defpol; init := sA`init; e := sA`e;
	P := Parent(defpol);
	
	// compute factors of defining polynomial
	factors := [f[1] : f in Factorization(defpol)];
	
	// check if defpol was already irreducible
	if #factors eq 1 then return sA; end if;
	
	// find the factor with good linear edge
	for fact in factors do
		// scale and translate factor
		tstpol := Evaluate(ScalePolynomial2(fact,e), P.1 + init);
		ordcf0 := PlOrd(Coefficient(tstpol,0));
		ordcf1 := PlOrd(Coefficient(tstpol,1));
		deginit := TotalDegree(init);
		
		// check linear edge
		if (not ordcf1 eq -1) and
		   ((ordcf0 eq -1) or (ordcf0 - ordcf1) gt deginit) then
			cop := Copy(sA);
			cop`defpol := fact; cop`magic := ordcf1; return cop;
		end if;
	end for;
	
	// should never be reached
	error "internal error: series representation inconsistent";
	return -1;
end function;


// some predicates
// ===============

// zero testing
intrinsic IsZero(series::SerPowAlg)
-> BoolElt
{
Determines if the power series is zero.
}
	defpol := DefiningPolynomial(series);
	
	// not zero if constant part not zero
	if not Evaluate(defpol, 0) eq 0 then
		return false;
	end if;
	
	// otherwise a large enough initial segment has to be zero
	c, t := Trailing(Coefficient(defpol,1));
	good, approx := Expand(series, TotalDegree(t)+1);
	require good : "series not expandable";
	return approx eq 0;
end intrinsic;


// equality testing
intrinsic 'eq'(alpha :: SerPowAlg, beta :: SerPowAlg)
-> BoolElt
{
Decides if two power series are equal.
}
	if IsIdentical(alpha, beta) then return true; end if;
	// !!! introduce some fast inequality tests !!!
	// !!! are power series comparable at all? !!!
	return IsZero(Sub(alpha,beta));
end intrinsic;

intrinsic IsEqual(alpha :: SerPowAlg, beta :: SerPowAlg) -> BoolElt
{}
    return alpha eq beta;
end intrinsic;


// testing for polynomiality
intrinsic IsPolynomial(series :: SerPowAlg) -> BoolElt, RngMPolElt
{
Determines whether the series is actually a polynomial (with integral
exponents).
}
	defpol := DefiningPolynomial(SimplifyRep(series));
	ispoly := (Degree(defpol) eq 1) and
	    (TotalDegree(Coefficient(defpol,1)) eq 0);
	if ispoly then
		return true,
		   ExactQuotient(Coefficient(defpol,0),-Coefficient(defpol,1));
	else
		return false, _;
	end if;
end intrinsic;


// some creation functions
// =======================

// series representation of a polynomial
intrinsic PolyToSeries(s::RngMPolElt)
-> SerPowAlg
{
Given a multivariate polynomial 's'. Return the atomic algebraic power series
representation of 's'.
}
	S := Parent(s); P := PolynomialRing(S); r := Rank(S);
	require hasDegreeOrdering(S):
	  "Parent of s must have 'glex' or 'grevlex' ordering";
	
	return InternalAlgebraicSeries(P.1 - s, s, [], 1, StandardLattice(r));
end intrinsic;

// basic constructor for atomic type
intrinsic AlgebraicPowerSeries(defpol :: RngUPolElt, init :: RngMPolElt :
   subs := []) -> SerPowAlg
{
Define an atomic algebraic power series by giving its defining polynomial 
'defpol', an initial expansion 'init'. The exponent lattice is taken to be
the standard lattice. Optionally specify
a sequence 'subs' of series that should be substituted into 'defpol'.
}
	Gamma := StandardLattice(Rank(Parent(init))); e := 1;
	return AlgebraicPowerSeries(defpol,init,Gamma,e : subs := subs);
end intrinsic;

// longer constructors for atomic type
intrinsic AlgebraicPowerSeries(defpol :: RngUPolElt, init :: RngMPolElt,
   e :: RngIntElt : subs := []) -> SerPowAlg
{
Define an atomic algebraic power series by giving its defining polynomial 
'defpol', an initial expansion 'init'. The exponent lattice is taken to be
(1/e)*the standard lattice. Optionally specify
a sequence 'subs' of series that should be substituted into 'defpol'.
}
	Gamma := StandardLattice(Rank(Parent(init)));
	return AlgebraicPowerSeries(defpol,init,Gamma,e : subs := subs);
end intrinsic;

intrinsic AlgebraicPowerSeries(defpol :: RngUPolElt, init :: RngMPolElt,
Gamma :: Lat, e :: RngIntElt : subs := [])
-> SerPowAlg
{
Define an atomic algebraic power series by giving its defining polynomial 
'defpol', an initial
expansion 'init' and its exponent lattice '1/e*Gamma'. Optionally specify
a sequence 'subs' of series that should be substituted into 'defpol'.
}
	// sanity checks
	dom := Generic(Parent(init));
	require hasDegreeOrdering(dom) and IsField(BaseRing(dom)):
	  "approximation domain must have 'glex' or 'grevlex' ordering and be over a field";
	
	dom1 := BaseRing(defpol);
	if #subs gt 0 then // check all subs have the same domain
	    boo := &and[Domain(s) cmpeq dom : s in subs];
	    require boo:
	      "the domain of power series in subs must be that of init";
	    require (Type(dom1) eq RngMPol) and (Rank(dom1) eq #subs):
	      "defpol is inconsistent with subs";
	else
	    require dom cmpeq dom1:
	      "coefficient ring of defpol should be the parent ring of init";
	end if;

	return InternalAlgebraicSeries(defpol, init, subs, e, Gamma);
end intrinsic;


// constructor for substitution type
intrinsic EvaluationPowerSeries(series :: SerPowAlg, nu :: SeqEnum, v :: SeqEnum)
-> SerPowAlg
{
Given a series 'series', a sequence 'nu' of vectors in the dual of
the exponent lattice and a sequence 'v' (of the same length) of polynomials.
Return the series obtained by substituting 'x^mu :-> prod_i v[i]^<nu[i],mu>'
where 'x' is the coordinate vector of 'series' (if that homomorphism is
defined).
}
	// some sanity checks
	require #nu eq #v :
	   "number of (dual) vectors must match number of substitution series";
	r := #nu;
	
	// check if vectors are in dual cone and lattice
	Gamma, e := Explode(ExponentLattice(series));
	for n in nu do
		for i in ElementToSequence(n) do
			require i ge 0 :
			    "vectors are not in dual cone";
		end for;
		for b in Basis(Gamma) do
			require IsDivisibleBy((n, Parent(n) ! b), e) :
			    "vectors are not in dual lattice";
		end for;
	end for;
	
	// check compatibility of domains
	dom := Domain(series);
	require Rank(dom) eq r:
	  "number of variables of series must match number of substitution series";
	if r gt 1 then
	  require &and[Domain(v[i]) eq dom1 : i in [2..r]] where dom1
	    is Domain(v[1]): 
		"all substitution series should have the same domain";
	end if;

	// compute magic value
	Gamma, e, m := CombinedLattice(v);
	Nu := ElementToSequence(&+[Order(v[i])*m[i]*nu[i]: i in [1..r]]);
	magic := Nu[#Nu]; Prune(~Nu);
	for t in Nu do magic := Min(t,magic); end for;
	require magic gt 0 : "evaluation not defined";
	
	// just encapsulate now
	eval_ser := InternalAlgebraicSeriesS(series,nu,v,e,Gamma);
	eval_ser`magic := magic; eval_ser`mults := m;
	return eval_ser;

end intrinsic;


// compute Taylor expansions by implicit function theorem
intrinsic ImplicitFunction(defpol :: RngUPolElt : subs := [])
-> SerPowAlg
{
The unique series with zero constant term defined by 'defpol' (fulfilling
the conditions of the implicit function theorem). Optionally specify
a sequence 'subs' of series that should be substituted into 'defpol'.
}

    require ISA(Type(subs),SeqEnum):
      "subs parameter should be a sequence";
    if IsEmpty(subs) then
      S := BaseRing(Parent(defpol));
      require IsField(BaseRing(S)):
  "approximation domain must be a multivariate polynomial ring over a field";
      require hasDegreeOrdering(S):
	 "approximation domain must have 'glex' or 'grevlex' ordering";
      require (Degree(defpol) ge 1) and
		(MonomialCoefficient(Coefficient(defpol,0),S!1) eq 0) and
		  (MonomialCoefficient(Coefficient(defpol,1),S!1) ne 0):
	"defpol doesn't satisfy conditions (see handbook) for the intrinsic";
      return AlgebraicPowerSeries(defpol, S ! 0,
		                       StandardLattice(Rank(S)), 1);
    else
      require ISA(Type(subs[1]),SerPowAlg):
	"subs parameter should be a sequence of algebraic power series"; 
      S := Domain(subs[1]);
      Gamma, e, _ := CombinedLattice(subs);
      s := AlgebraicPowerSeries(defpol, S ! 0, Gamma, e : subs := subs);
      // check conditions for ImplicitFunction thm
      subs0 := [];
      for i in [1..#subs] do
	boo,s1 := Expand(subs[i],1);
	require boo: "Error expanding substitution series number "
			cat IntegerToString(i);
	Append(~subs0,MonomialCoefficient(s1,S!1));	
      end for;
      require (Degree(defpol) ge 1) and
		(Evaluate(Coefficient(defpol,0),subs0) eq 0) and
		  (Evaluate(Coefficient(defpol,1),subs0) ne 0):
	"defpol doesn't satisfy conditions (see handbook) for the intrinsic";
      return s;
    end if;

end intrinsic;


// scale generators by multiplying with scalars
intrinsic ScaleGenerators(series :: SerPowAlg, lambda :: SeqEnum) -> SerPowAlg
{
If '1/e*Gamma' is the exponent lattice of the power series 'series' and
'(mu_i)_i' the sequence of its generators return the power series after the
substitution 'x^(mu_i) :-> lambda[i]*x^(mu_i)'.
}		
	S := Domain(series);
	Gamma, e := Explode(ExponentLattice(series));
	
	// compute parametrized trasnformation
	fun := ScalingHelper(S, Gamma, e, lambda);
	
	// call recursive routine
	return ApplyStructureHom(series, fun);
end intrinsic;


// coerce according to approximation domain
intrinsic ChangeRing(series :: SerPowAlg, S :: RngMPol) -> SerPowAlg
{
If 'S' is a multivariate polynomial domain compatible with the approximation
domain of the power series 'series' return the same power series with
new approximation domain 'S'.
}
	require hasDegreeOrdering(S):
	  "new approximation domain S must have 'glex' or 'grevlex' ordering";
	// get coercion if it exists
	crc := Coercion(Domain(series), S);
	
	// call recursive routine
	return ApplyStructureHom(series, func<s, e | crc(s)>);
end intrinsic;

// algebraic combinations of power series
intrinsic AlgComb(comb :: RngMPolElt, series :: SeqEnum[SerPowAlg])
-> SerPowAlg
{
Given a polynomial 'comb' in 'r' variables and a sequence 'series' of 'r'
algebraic power series (in the same domain) returns the power series obtained
by substituting the elements of 'series' for the variables of 'comb'.
}
	//add more sanity checks here or just leave to the constructor?
	P := PolynomialRing(Parent(comb)); S := Domain(series[1]);
	Gamma, e, mults := CombinedLattice(series);
	return InternalAlgebraicSeries(P.1-comb, S ! 0, series, e, Gamma);
end intrinsic;

// some arithmetic operations on power series
intrinsic Add(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{}
    return alpha+beta;
end intrinsic;

intrinsic '+'(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{
Add two power series.
}
	return AlgComb(P.1+P.2, [alpha,beta])
		where P is PolynomialRing(Integers(),2);
end intrinsic;
intrinsic Sub(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{}
    return alpha - beta;
end intrinsic;

intrinsic '-'(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{
Subtract two power series.
}
	return AlgComb(P.1-P.2, [alpha,beta])
		where P is PolynomialRing(Integers(),2);
end intrinsic;
intrinsic Mult(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{}
    return alpha * beta;
end intrinsic;

intrinsic '*'(alpha :: SerPowAlg, beta :: SerPowAlg) -> SerPowAlg
{
Multiply two power series.
}
	return AlgComb(P.1*P.2, [alpha,beta])
		where P is PolynomialRing(Integers(),2);
end intrinsic;
