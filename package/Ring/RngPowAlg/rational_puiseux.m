// *********************************************************************
// * Package: rational_puiseux.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 27.12.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute rational (Puiseux series) parametrizations              *
// *   of a polynomial.                                                *
// *                                                                   *
// *********************************************************************
freeze;

import "power_series.m": Trailing, ScalePolynomial1, ScalePolynomial2,
                           ApproxDefPoly, TruncDefPoly, CombinedLattice,
                           ScalingHelper, ApplyStructureHom, hasDegreeOrdering;




// ======================================
// = Auxillary functions (not exported) =
// ======================================

// compute slope from edge
// -----------------------
// input:  a tuple 'edge' of the form '<<z1,x1>,<z2,x1>>' (start and end
//         point) where 'x1','x2' are monomials and 'z1','z2' are integers
// output: the rational slope '<nslz, nslx>' where 'nslx' is a monomial
//         and 'nslz' is an integer (the denominator of the exponent)
function GetSlope(edge)
	P := Parent(edge[1][2]);
	
	// find slope of edge in reducible representation
	slx := edge[2][2] div edge[1][2]; slz := edge[1][1] - edge[2][1];
	
	// find greatest common denominator
	g := slz; for i := 1 to Rank(P) do
		g := Gcd(Degree(slx, i), g);
	end for;
	
	// compute reduced representation
	nslx := 1; for i := 1 to Rank(P) do
		nslx := nslx*(P.i)^ExactQuotient(Degree(slx, i), g);
	end for;
	nslz := ExactQuotient(slz, g);
	
	return <nslz, nslx>;
end function;


// compute complete edge polynomial
// --------------------------------
// input:  a polynomial 'p', an edge 'edge' and its slope 'slope'
// output: the univariate polynomial with coefficients taken along
//         the edge 'edge' from 'p'
function NewtonPolynomial(p, edge, slope)
	P := Parent(p); S := BaseRing(P); F := BaseRing(S);
	R := PolynomialRing(F);
	
	// first value needed for edge test
	n1 := slope[2]^edge[2][1] * edge[2][2]^slope[1];
	
	// extract edge polynomial
	np := R ! 0;
	for i := edge[2][1] to edge[1][1] do
		c, t := Trailing(Coefficient(p, i));
		
		// second value needed for edge test
		n2 := slope[2]^i * t^slope[1];
		
		// add coefficient if monomial lies on edge
		if (n1 eq n2) then
			np := np + c*(R.1)^i;
		end if;
	end for;
	
	return np;
end function;


// compute edge polynomial for rational Puiseux
// --------------------------------------------
// input:  a non-zero polynomial 'np' (as returned by 'NewtonPolynomial')
//         and the step size 'b'
// output: the newton equation as needed for Puiseux algorithm
function NewtonEquation(np, b)
	d := Degree(np); ld := Degree(TrailingTerm(np));
	steps := ExactQuotient((d - ld), b);
	
	// start with lowest degree 'ld' and do steps of size 'b'
	return Parent(np) ! [Coefficient(np, ld+i*b) : i in [0..steps]];
end function;


// extend lattice by new vector and compute some additional information
// --------------------------------------------------------------------
// input:  an integral lattice 'Gamma' of rank 'r', an integral vector 'mu0'
//         and an integer 'e'
// ouptut: the lattice 'Gamma0 := e*Gamma + Z*mu0',
//         the 'r X r'-matrix giving the embedding of 'e*Gamma' into 'Gamma0',
//         the minimal natural number 'b' s.t. 'b*mu0' is in 'e*Gamma',
//         the 'r'-tuple 'c' giving the coordinates of 'b*mu0' in 'e*Gamma'
//         and an 'r+1'-tuple 'cof' giving a partition of unity for '[b,-c-]'
//         (i.e. we have the scalar product '<[b,-c-],cof> = 1')
function ExtendLattice(Gamma, mu0, e)
	r := Dimension(Gamma);
	
	// extend lattice by new vector
	eGamma := e*Gamma; Gamma0 := ext<eGamma | mu0>; mu0 := Gamma0 ! mu0;
	
	// represent old basis 
	C := RMatrixSpace(Integers(), r, r) !
	    Flat([Coordinates(Gamma0, b) : b in Basis(eGamma)]);
	
	// find minimal 'b' s.t. 'b*mu0' in 'e*Gamma' and
	// represent that vector w.r.t. scaled old basis
	b := Index(Gamma0, eGamma); c := Coordinates(eGamma ! (b*mu0));
	
	// compute the cofactors
	l := [b] cat c; g, cof := Xgcd(l); assert g eq 1;
	
	// minimize cofactors vector
	L1 := Lattice(BasisMatrix(Nullspace(m)))
	    where m := (RMatrixSpace(Integers(),r+1,1) ! l);
	cof := Eltseq(cof2 - ClosestVectors(L1, cof2 : Max := 1)[1])
	    where cof2 := (RSpace(Integers(), r+1) ! cof);
	
	return Gamma0, C, b, c, cof;
end function;


// recursive part of rational Puiseux algorithm
// --------------------------------------------
// input:  a univariate polynomial 'p' over a multivariate polynomial ring
//         (approximating a squarefree polynomial over a series ring)
//         with exponents in the lattice 'Gamma', a multiexponent 'mu' and
//         the precision
// output: a list of candidates for Puiseux series roots of order greater or
//         equal to 'mu', the new value of ExtCount, and an integer indicating
//         whether a higher precision is needed
function RationalRec(p, Gamma, mu, precision, First, OnlySingular, Duval,
                     ExtName, ExtCount)
	P := Parent(p); S := BaseRing(P); F := BaseRing(S); r := Rank(S);
	inc := 10; // => heuristic value of precision increment!
	
	// 'p' may not be zero!
	if p eq 0 then return [* *], 0, precision + inc; end if;
	
	// early abort: no roots!
	if Degree(p) eq 0 then return [**], ExtCount, 0; end if;
	
	// compute the (reverse) list of vertices of the Newton Polygon
	np := Reverse(GetMonoidNewtonPolygon(p));
	
	// zero is no double root of squarefree polynomial, we want to see it!
	if np[1][1] gt 1 then return [* *], 0, precision + inc; end if;
	
	// is precision of constant term high enough?
	if np[1][1] eq 1 then
		req := TotalDegree(np[1][2]) + (&+Eltseq(mu)) + 1;
	else
		req := TotalDegree(np[1][2]) + 1;
	end if;
	if req gt precision then return [* *], 0, req; end if;
	
/*
"BEGIN RationalRec";
ZEIT := Cputime();
"F:", F;
"S:", S;
"P:", P;
"r:", r;
"Degree(p):", Degree(p);
//"p:", p;
"Gamma:", Gamma;
"mu:", mu;
"precision:", precision;
"First:", First;
"Duval:", Duval;
"OnlySingular:", OnlySingular;
"np:", np;
*/

	// truncate polynomial for simpler computations
	p := TruncDefPoly(p, precision, (&+Eltseq(mu)));

//"Trunc p:", p;
	
	// find solutions for all edges
	pt2 := np[#np]; Prune(~np); L := [* *];
	while not IsEmpty(np) do
//"Now #np:", #np;
		pt1 := pt2; pt2 := np[#np]; Prune(~np); edge := <pt1,pt2>;
//"edge:", edge;
		
		// don't consider edge if slope too steep or partially negative
		if First then
			if not IsDivisibleBy(pt2[2],pt1[2]) then
				continue;
			end if;
		else
			n1 := pt1[2]*Monomial(S,Eltseq(mu))^pt1[1];
			n2 := pt2[2]*Monomial(S,Eltseq(mu))^pt2[1];
			if (n1 ge n2) or not IsDivisibleBy(pt2[2],pt1[2]) then
				continue;
			end if;
		end if;
		
		// compute slope of edge
		slope := GetSlope(edge); e := slope[1];
		mu0 := RSpace(Integers(), r) ! Exponents(slope[2]);
		
		// base case: linear Newton polygon
		if pt1[1] eq 1 then
			if not (OnlySingular and (pt1[2] eq 1)) then
				Append(~L, <[ F | 1 : x in [1..r] ], S ! 0,
				            Gamma, 1, 1, 1>);
			end if;
			continue;
		end if;
		
		// compute new lattice and transformations
		Gamma0, C, b, c, cof := ExtendLattice(Gamma, mu0, e);
		
		// extract Newton Equation and do translations for each root
		newp := NewtonPolynomial(p, edge, slope);
		neweq := Duval select NewtonEquation(newp, b)
		               else   NewtonEquation(newp, 1);
//"Call AllRoots";
//IndentPush();
		rts, ExtCount := AllRoots(neweq : ExtName := ExtName,
		                                  ExtCount := ExtCount);
//IndentPop();

//"Got num rts:", #rts;
		for rt in rts do
//"Do root", rt;
			a := rt[1]; Fext := Parent(a);
			
			// does parametrization require a field extension?
			if (Fext eq F) then Sext := S; Pext := P; else
				Sext := ChangeRing(S, Fext);
				Pext := ChangeRing(P, Sext);
			end if;
			
			// compute vector for lattice homomorphism and
			// coefficient of new term
			if Duval then
				lambda0 := [a^(-cof[i+1]) : i in [1..r]];
				a0 := a^cof[1];
			else
				lambda0 := [Fext ! 1 : i in [1..r]];
				a0 := a;
			end if;
			
			// transform polynomial by Newton step
			p2:= hom<P -> Pext | map<S -> Pext |
			    x :-> Pext ! scale(x, 1)>, Pext.1>(p) where
			    scale is ScalingHelper(Sext, Gamma, 1, lambda0);
//"Do p1 := ScalePolynomial2(p2, e);"; time
			p1:= ScalePolynomial2(p2, e);
//"Do p0:= Evaluate(p1..."; time
			p0:= Evaluate(p1,Pext.1+a0*Monomial(Sext,Eltseq(mu0)));
			
//ZEIT1 := Cputime();
//IndentPush();
			// go into recursion
			R, ExtCount, required := RationalRec(p0, Gamma0, mu0,
			    e*precision, false, OnlySingular, Duval,
			    ExtName, ExtCount);
//IndentPop();
//"Total recursive time:", Cputime(ZEIT1);
			if required gt 0 then return [**], 0, required; end if;
			
			// backsubstitute
//"Do backsubstitute";
//ZEIT1 := Cputime();
			for l in R do
//"Do l:", l;
//IndentPush();
				lambdap, alphap, Gammap, ep, N,E := Explode(l);
				Sextp:=Parent(alphap); Fextp:=BaseRing(Sextp);
				
				lambda1 := [Fextp | lambda0[j]*
				 (&* [Fextp | lambdap[i]^C[j,i] : i in [1..r]])
				 : j in [1..r]];
//time
				ad2 := (Fextp!a0)*Monomial(Sextp,Eltseq(mu0));
//time
				ad1 := ScalingHelper(Sextp, Gamma0, 1, lambdap)
				    (ad2, 1);
//time
				ad0 := ScalePolynomial1(ad1, ep);
				Append(~L,<lambda1, alphap+ad0, Gammap, e*ep,
				           N*b, E*Degree(Fext, F)>);
//IndentPop();
			end for;
//"Total backsubstitute time:", Cputime(ZEIT1);
		end for;
	end while;
	
	// special case: polynomial root
	if (pt2[1] eq 1) and not (OnlySingular and (pt2[2] eq 1)) then
		Append(~L, <[F| 1 : x in [1..r]], S ! 0, Gamma, 1, 1, 1>);
	end if;

/*
"END RationalRec";
"Total RationalRec time:", Cputime(ZEIT);
"RES L parent:", Parent(L);
if #L gt 0 then
    "RES L[1] parent:", Parent(L[1]);
end if;
*/
	
	return L, ExtCount, 0;
end function;




// ======================
// = Exported functions =
// ======================

// compute rational Puiseux parametrizations
// -----------------------------------------
// We first specify the behaviour of this function in the case that no special
// value of 'subs' has been given. This function assumes that 'poly' is a
// univariate polynomial over a multivariate polynomial ring
// 'S = k[x_1, ..., x_r]' and that 'poly' is quasi-ordinary. In this case it
// will compute a set of rational parametrizations of 'poly'. Note that for
// reasons of efficiency the user has to make sure that 'poly' is actually
// quasi-ordinary! (Otherwise, further processing of the output may result
// in runtime errors.)
// 
// The first return value will be the exponent lattice of the input polynomial
// in the usual format '<Gamma_0, e_0>'. If the parameter 'Gamma' has been
// specified, then 'Gamma_0 = Gamma' and 'e_0 = 1'. In this case 'Gamma' has
// to be an integral 'r'-dimensional lattice of full rank containing all the
// exponents of 'poly'. Otherwise 'Gamma_0' will be set to the 'r'-dimensional
// standard lattice and again 'e_0=1'.
// 
// As a second value a complete list of rational parametrizations in the format
// '<lambda, s, N, E>' is returned. Here 'lambda' is a sequence of 'r' field
// elements and 's' is a fractionary algebraic power series. Let 'poly_1'
// denote the image of 'poly' under the transformation
// 'x^{mu_i} :-> lambda_i x^{mu_i}' where '(mu_i)_i' is the basis of the
// exponent lattice 'e_0^(-1) Gamma_0' then 's' is a solution of 'poly_1',
// i.e., we have 'poly_1(s) = 0'. Note that if neither 'Gamma' nor 'subs' have
// been supplied this just means that 'x_i' is substituted by 'lambda_i x_i'.
// Finally 'N' is the index of 'e_0^(-1) Gamma_0' in the exponent lattice of
// 's' and 'E' is the degree of the extension of the coefficient field needed
// for defining 's'.
// 
// The behaviour described above corresponds to the Newton-Puiseux algorithm
// with Duval's trick. The field extensions that are used for expressing the
// series fulfill a certain minimality condition. If 'Duval' is set to 'false'
// then the function returns a complete set of representatives (up to
// conjugacy) of Puiseux series roots of the original polynomial 'poly', in
// other words, the 'lambda'-vectors will always be vectors of ones.
// 
// If 'OnlySingular' is set to 'true' then only those parametrizations that
// correspond to singular branches are returned.
// 
// If the ground field has to be extended, the algebraic elements will be
// assigned the name 'ExtName_i' where 'i' starts from 'ExtCount'. The last
// return value is the value of 'ExtCount' plus the number of field extensions
// that have been introduced during the computation.
// 
// Finally, if the parameter 'subs' is passed, then it has to be a sequence of
// 'r' power series in a common domain and internally the variables in 'poly'
// will be substituted by the corresponding series. Again the resulting
// polynomial has to be quasi-ordinary. In this case 'Gamma_0' and 'e_0' are
// determined by building the sum of the exponent lattices of all series in
// 'subs'. The parameter 'Gamma' then has no effect.
intrinsic RationalPuiseux(poly::RngUPolElt : Gamma := StandardLattice(0),
    subs := [], Duval := false, OnlySingular := false,
    ExtName := "gamma", ExtCount := 0)
-> Tup, SeqEnum, RngIntElt
{
Given a univariate polynomial 'poly' over a multivariate polynomial ring,
assuming that it is quasi-ordinary, return a complete set of rational
parametrizations (if 'Duval' is 'true').

The parameter 'Gamma' can be used to specify the exponent lattice of 'poly'.

If 'subs' is passed, it has to be a sequence of series in a common domain
and internally the variables of 'poly' will be substituted by the corresponding
series.

If 'Duval' is 'false' then the function returns a set of representatives of
actual Puiseux series roots of 'poly', i.e., Duval's trick is not applied.

If 'OnlySingular' is 'true' then only parametrizations corresponding to
singular branches are returned.

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'.

The first return value is the exponent lattice of 'poly', the second is the
sequence of parametrizations and the last value is 'ExtCount' plus the number
of field extensions that have been introduced during the computation.
}
	// !!! add some sanity checks !!!
	
	P := Parent(poly); S := BaseRing(P); F := BaseRing(S); r := Rank(S);
	IVec := RSpace(Integers(), r);
	require Type(S) eq RngMPol:
	  "coefficient ring of poly must be a multivariate polynomial ring";
	
	if IsEmpty(subs) then
		require hasDegreeOrdering(S):
	  	"multivariate coefficient ring of poly must have 'glex' or 'grevlex' ordering";
		if Gamma eq StandardLattice(0) then
			Gamma0 := StandardLattice(r);
		else
			Gamma0 := Gamma;
		end if;
		e0 := 1;
	else
		require Rank(S) eq #subs:
		  "coefficient ring of poly is inconsistent with subs";
		Gamma0, e0, mults := CombinedLattice(subs);
	end if;
	
	// find a good approximation order to start => heuristical!
	if IsEmpty(subs) then
		maxord := TotalDegree(Coefficient(poly, 0));
		for i:=1 to Degree(poly) do
		    maxord := Max(maxord, TotalDegree(Coefficient(poly, i)));
		end for;
		appord := maxord+1;    // use degree as precision!
	else
		appord := 1; // try to use an approximation small as possible!
	end if;
	
	// try to find all solutions using better and better approximations
	repeat
		// approximate defining polynomial
		if IsEmpty(subs) then
			apppoly := TruncDefPoly(poly, appord, 0);
		else
			apppoly, good := ApproxDefPoly(poly,subs,mults,appord);
			require good : "bad defining polynomial";
		end if;
		
		// try to find parametrizations
		R, EC, appord := RationalRec(apppoly, Gamma0, IVec ! 0, appord,
		    true, OnlySingular, Duval, ExtName, ExtCount);
	until appord eq 0;
	ExtCount := EC;
	
	// transform parametrizations
	res := [**]; for param in R do
		lambda, alpha, Gamma, e1, N, E := Explode(param); e := e0*e1;
		Sext := Parent(alpha); Fext := BaseRing(Sext);
		Pext := ChangeRing(P, Sext);
		
		// substitute according to lambda
		scale := ScalingHelper(Sext, Gamma0, e0, lambda);
		if IsEmpty(subs) then
			subspoly := hom<P -> Pext | map<S -> Pext |
			    x :-> Pext ! scale(x, 1)>, Pext.1>(poly);
			
			subsext := [];
		else
			subspoly := poly;
			
			subsext := [ApplyStructureHom(s, scale) : s in subs];
		end if;
		
		// add to result list
		Append(~res, <lambda, AlgebraicPowerSeries(subspoly,alpha,Gamma,e
		    : subs:=subsext), N, E>);
	end for;
	
	return <Gamma0, e0>, res, ExtCount;
end intrinsic;
