// *********************************************************************
// * Package: curve_resolution.mag                                     *
// * =============================                                     *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 29.11.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Compute a certain type of "resolution" of a plane curve         *
// *   (basically a collection of local charts).                       *
// *                                                                   *
// * Example call:                                                     *
// * -------------                                                     *
// *                                                                   *
// *   Attach("solve_system.mag");                                     *
// *   Attach("curve_resolution.mag");                                 *
// *   Q := Rationals(); P<x, y> := PolynomialRing(Q, 2);              *
// *                                                                   *
// *   // Curve without singularity:                                   *
// *   p0 := y-x^3;                                                    *
// *   // Curves with one singularity:                                 *
// *   p1 := y^2-x^2-x^3;                                              *
// *   p2 := y^2-x^3;                                                  *
// *   // Curve with two pairs of conjugate singularities:             *
// *   p3 := 6*x^2+4*x-6*y^2-8*y+2*x^2*y-2*x^4+y^4+x^2*y^2+            *
// *         8*x*y^2-12*x^3+6*y^3+2*x^5-2*y^5+2*x^3*y^2-3*x*y^4+       *
// *         x^2*y^3-x^4*y;                                            *
// *   p4 := x^4-2*x^2*y^2+y^4-x^5+y^5+x*y^7+2*x^9;                    *
// *                                                                   *
// *   ResolveAffineCurve(p0); ResolveAffineCurve(p1);                 *
// *   ResolveAffineCurve(p2); ResolveAffineCurve(p3);                 *
// *   lNCs, lEXs, _, _ :=  ResolveAffineCurve(p3);                    *
// *   TestLists(p3, lNCs, lEXs);                                      *
// *                                                                   *
// *                                                                   *
// *********************************************************************
freeze;
declare verbose Resolve, 1;




// ======================================
// = Auxillary functions (not exported) =
// ======================================

// compute normal-crossing locus of a list of bivariate polynomials and 'y'
// ------------------------------------------------------------------------
// input:  a sequence 'f' of bivariate polynomials, a focus ideal 'Focus'
// output: two lists 'lNC' and 'lnonNC' where 'lNC' contains the normal
//         crossing intersections with 'y=0' and 'lnonNC' the other
//         intersections (only intersections in the zero set of 'Focus' are
//         taken into consideration)
function NCLocus(f : Focus := 0, ExtName := "alpha", ExtCount := 0)
	S := Parent(Representative(f)[1]); F := BaseRing(S);
	S2 := PolynomialRing(F); t := S2.1; h := hom<S -> S2 | t, 0>;
	
	// find all crossings with 'y=0'
	p := S2 ! 1;
	for q in f do
		q2 := SquarefreePart(h(q[1]));
		p := (p*q2) div Gcd(p,q2);
	end for;
	sols, ExtCount :=
	    AllRoots(p : ExtName := ExtName, ExtCount := ExtCount);
	
	// extract points in focus
	Points := [**];
	for sol in sols do
		x := sol[1]; Fext := Parent(x);
		Point := <x, Fext ! 0>;
		
		// check if point in focus		
		for g in Basis(Focus) do
			if not Evaluate(g, Point) eq 0 then
				continue sol;
			end if;
		end for;
		
		// add this point
		Append(~Points, Point);
	end for;
	
	// sort normals from non-normals
	lNC := [**]; lnonNC := [**];
	for Point in Points do
		cand := [q : q in f | Evaluate(q[1], Point) eq 0];
		
		// two many components => non-NC
		if #cand gt 1 then
			Append(~lnonNC, Point);
			continue;
		end if;
		
		// move interesting point to origin
		if (F eq Parent(Point[1])) then S3 := S;
		else S3 := ChangeRing(S, Parent(Point[1])); end if;
		
		// not a generator of maximal ideal => non-NC
		q := Evaluate(cand[1][1], [Point[1]+S3.1, Point[2]]);
		if Coefficient(q, S3.1, 1) eq 0 then
			Append(~lnonNC, Point);
			continue;
		end if;
		
		// else => NC
		Append(~lNC, Point);
	end for;
	
	return lNC, lnonNC, ExtCount;
end function;


// compute strict transforms and multiplicity
// ------------------------------------------
// input:  a bivariate polynomial 'p' and a homomorphism 'b' between
//         bivariate polynomial rings
// output: if 'm' denotes the maximum power of 'y' (the exceptional divisor)
//         that can be divided from 'b(p)', then 'b(p)/y^m, m' is returned
//         (i.e. the strict transformation and the multiplicity of the
//          exceptional divisor)
function StrictTrafo(p, b)
	S := Codomain(b);
	
	q := b(p); m := 0;
	while (IsDivisibleBy(q, S.2)) do
		m := m + 1;
		q := q div S.2;
	end while;
	
	return q, m;
end function;


// compute strict transforms and multiplicity
// ------------------------------------------
// input:  a list 'l' of tuples of bivariate polynomials and multiplicities
//         describing the decomposition of a curve, and a homomorphism 'b'
//         between bivariate polynomial rings
// output: applies 'StrictTrafo' to each element of the list, returns
//         list of strict transforms (with the original multiplicities) and the
//         overall multiplicity of the exceptional divisor
function StrictTrafoList(l, b)
	m := 0; l1 := [];
	
	for x in l do
		y, my := StrictTrafo(x[1], b);
		m := m + my*x[2];
		Append(~l1, <y, x[2]>);
	end for;
	return l1, m;
end function;




// ======================
// = Exported functions =
// ======================

// compute resolution of a curve
forward ResolveRec;
intrinsic ResolveAffineCurve(p::RngMPolElt
: Factors := [], Ps := 0, Focus := 0, ExtName := "alpha", ExtCount := 0)
-> List, List, List, RngIntElt
{
Compute an embedded (piecewise) resolution of a curve (defined by the non-zero
bivariate polynomial 'p' over the rational numbers or over a number field)
using a succession of point blow ups. Only the part of the curve in the zero
set of the ideal 'Focus' is considered.

If known, a factorization of 'p' (as returned by 'Factorization') can be passed
through the parameter 'Factors' and its squarefree part (as returned by
'SquarefreePart') can be passed through 'Ps'. 

Let '[* [* b1, <y, mult11>, <p1, mult12> *] ... *],
[* [* b2, <y, mult2> *] ... *], [* [* b3, <p3, mult3> *] ... *]'
be the returned lists. Here 'b1', 'b2' and 'b3' are maps to some bivariate
polynomial ring representing a chart that arose during the resolution
procedure. The integer values 'mult11' and 'mult2' give the multiplicity of the
exceptional divisor 'y=0' in the respective chart. 

The first list gathers normal crossings. The polynomial 'p1' is the
(irreducible) equation of a component that meets 'y=0' in the origin of the
respective chart and 'mult12' is its multiplicity.

The second list just gathers exceptional divisors. (Note that one and the same
geometric exceptional divisor might show up several times in the first list.)

Finally, the last list contains the defining equations 'p3' of all original
curve components with multiplicites (more precisely, those in the zero set
of 'Focus').

The two first lists are complete in the sense that they contain all exceptional
divisors that would show up in a complete embedded resolution and all normal
crossings of the transformed curve and these exceptional divisors (always up to
conjugates).

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return
value is the value of 'ExtCount' plus the number of field extensions that
have been introduced during the computation.
}
	S := Parent(p);
	t := Type(BaseRing(S));
	require (p ne S!0) and (Rank(S) eq 2) and 
	    		((t cmpeq FldRat) or ISA(t,FldAlg)):
	  "Argument should be a non-zero polynomial in two variables over",
	  "a number field";

	vprint Resolve: "--------- Entering ResolveAffineCurve ----------";
	
	// factorize polynomial and setup ideal for singular locus
	if #Factors eq 0 then facts := Factorization(p);
	else facts := Factors; end if;
	if Ps eq 0 then ps := SquarefreePart(p);
	else ps := Ps; end if;
	foc := ideal<S | ps, Focus> + JacobianIdeal(ps);
	
	// early abort
	if #facts eq 0 then
		return [], [], [], ExtCount;
	end if;
	
	// call recursive procedure
	LNCs, LEXs, ExtCount := ResolveRec(facts, 0, foc, ExtName, ExtCount);
	
	// add factors of curve
	vprint Resolve: "--------- Leaving ResolveAffineCurve ----------";
	return LNCs, LEXs, [* [* id, f *] : f in facts | 
	    (ideal<S | Focus> subset ideal<S | f[1]>) and 
	    not TotalDegree(f[1]) eq 0 *], ExtCount
	    where id := hom<S -> S | S.1, S.2>;
end intrinsic;
// recursive part of function resolve
function ResolveRec(f, my, Focus, ExtName, ExtCount)
//printf "ENTER:";
	S := Parent(Representative(f)[1]); F := BaseRing(S);
	LNcInt := [**]; LExcDiv := [**];
	
	// compute list of normal crossings and non-normal crossings
	if (my eq 0) then
//		lNC := [**]; lnonNC, ExtCount := SolveZeroDim(Focus : ExtName := ExtName, ExtCount := ExtCount);
		roots, ExtCount := SolveZeroDimIdeal(ideal<S | Focus>
		    : ExtName := ExtName, ExtCount := ExtCount);
		lNC := [**]; lnonNC := [* <rt[1][1], rt[1][2]> : rt in roots*];
	else
		lNC, lnonNC, ExtCount :=
		NCLocus(f : Focus := Focus,
			ExtName := ExtName, ExtCount := ExtCount);
	end if;
	
	// add charts with normal crossing to result list
	for Point in lNC do
		if (F eq Parent(Point[1])) then Sext := S;
		else Sext := ChangeRing(S, Parent(Point[1])); end if;
		
		bt := hom< S -> Sext | Sext.1 + Point[1],
		                       Sext.2 + Point[2] >;
		faux := [<bt(x[1]),x[2]> : x in f];
		ft := ([x : x in faux | Evaluate(x[1],[0,0]) eq 0])[1];
		
//printf " NC(%o) ", ft;
		Append(~LNcInt, [* bt, <Sext.2, my>, ft *]);
	end for;
	
	// consider each non-NC point
	for Point in lnonNC do
		if (F eq Parent(Point[1])) then Sext := S;
		else Sext := ChangeRing(S, Parent(Point[1])); end if;
		
		// move point to origin
		bt := hom< S -> Sext | Sext.1 + Point[1],
		                       Sext.2 + Point[2] >;
		ft := [<bt(x[1]),x[2]> : x in f];
		
		// blow it up
		b1 := hom< Sext -> Sext | Sext.1*Sext.2, Sext.2   >;
		b2 := hom< Sext -> Sext | Sext.2,   Sext.1*Sext.2 >;
		f1,  m := StrictTrafoList(ft, b1);
		f2,  _ := StrictTrafoList(ft, b2);
		if not my eq 0 then
			Append(~f2, <Sext.1, my>);
		end if;
		
		// add new exceptional divisor
//printf " ED ";
		br := hom< S -> Sext | b1(bt(S.1)), b1(bt(S.2))>;
		Append(~LExcDiv, [* br, <Sext.2, my+m> *]);
		
		// go into recursion
		r1, r2, ExtCount :=
		ResolveRec(f1, my+m, ideal<Sext | Sext.2>, ExtName, ExtCount);
		s1, s2, ExtCount :=
		ResolveRec(f2, my+m, ideal<Sext | Sext.1, Sext.2>,
		           ExtName, ExtCount);
		
		// update list of exceptional divisors
		for ed in r2 do
			br := hom< S -> Codomain(ed[1]) | ed[1](b1(bt(S.1))),
			                                  ed[1](b1(bt(S.2)))>;
			Append(~LExcDiv, [* br, ed[2] *]);
		end for;
		for ed in s2 do
			br := hom< S -> Codomain(ed[1]) | ed[1](b2(bt(S.1))),
			                                  ed[1](b2(bt(S.2)))>;
			Append(~LExcDiv, [* br, ed[2] *]);
		end for;
		
		// update list of normal crossing intersections
		for nc in r1 do
			br := hom< S -> Codomain(nc[1]) | nc[1](b1(bt(S.1))),
			                                  nc[1](b1(bt(S.2)))>;
			Append(~LNcInt, [* br, nc[2], nc[3] *]);
		end for;
		for nc in s1 do
			br := hom< S -> Codomain(nc[1]) | nc[1](b2(bt(S.1))),
			                                  nc[1](b2(bt(S.2)))>;
			Append(~LNcInt, [* br, nc[2], nc[3] *]);
		end for;
	end for;
	
//printf ":RETURN\n";
	return LNcInt, LExcDiv, ExtCount;
end function;


// compute resolution of a projective curve
intrinsic ResolveProjectiveCurve(p::RngMPolElt
: Focus := 0, ExtName := "alpha", ExtCount := 0)
-> List, List, List, RngIntElt
{
Similar to 'ResolveAffineCurve', but now 'p' is a homogeneous polynomial in three
variables that defines a projective curve.
}
	S := Parent(p); F := BaseRing(S);
	require (p ne S!0) and IsHomogeneous(p) and (Rank(S) eq 3) and 
	    		((Type(F) cmpeq FldRat) or ISA(Type(F),FldAlg)):
	  "Argument should be a non-zero homogeneous polynomial in three",
	  "variables over a number field";
	vprint Resolve: "--------- Entering ResolveProjectiveCurve ----------";
	
	// maybe factorize polynomial
	facts := Factorization(p);
	ps := SquarefreePart(p);
	
	// homomorphisms to charts
	Sn<x,y> := PolynomialRing(F, 2, "glex");
	charts := [<hom<S -> Sn | 1, x, y>, ideal< Sn | 0 >>,
	           <hom<S -> Sn | y, 1, x>, ideal< Sn | y >>,
	           <hom<S -> Sn | x, y, 1>, ideal< Sn | x, y >>];
	
	// call recursive procedure on each chart
	LNCs := [**]; LEXs := [**]; LDCs := [**];
	for chart in charts do
		thishom := chart[1]; thisfoc := chart[2];
		thisfacts := [<thishom(g[1]), g[2]> : g in facts];
		thisp := thishom(p); thisps := thishom(ps);
		lncs, lexs, ldcs, ExtCount := ResolveAffineCurve(thishom(p) :
		     Focus := thisfoc, Factors := thisfacts, Ps := thisps,
		     ExtName := ExtName, ExtCount := ExtCount);
		LNCs := LNCs cat [* [* thishom*nc[1], nc[2], nc[3] *]
		                    : nc in lncs *];
		LEXs := LEXs cat [* [* thishom*ex[1], ex[2] *] : ex in lexs *];
		LDCs := LDCs cat [* [* thishom*dc[1], dc[2] *] : dc in ldcs *];
	end for;
	
	// add factors of curve
	vprint Resolve: "--------- Leaving ResolveProjectiveCurve ----------";
	return LNCs, LEXs, LDCs, ExtCount;
end intrinsic;




// =====================
// = Testing of output =
// =====================
/*
forward TestEX, TestNC;
intrinsic TestLists(p::RngMPolElt, LNcInt::List, LExcDiv::List)
-> BoolElt
{
Given a polynomial 'p' defining a curve and lists 'LNcInt' (normal
crossings) and 'LExcDiv' (exceptional divisors) as in the output
of a curve resolution function. Test whether they are really lists
of normal crossings and exceptional divisors. Note: This does not
imply completeness of these lists.
}
	for i:=1 to #LExcDiv do
		if not TestEX(p,LExcDiv[i]) then
			print "Exceptional Divisor", i;
			return false;
		end if;
	end for;
	for i:=1 to #LNcInt do
		if not TestNC(p,LNcInt[i]) then
			print "Normal Crossing", i;
			return false;
		end if;
	end for;
	return true;
end intrinsic;
function TestEX(p,EX)
	map := EX[1]; p0 := map(p);
	f := EX[2][1]; m := EX[2][2];
	
	if not IsDivisibleBy(p0, f^m) then
		print "Multiplicity too high!";
		return false;
	end if;
	p0 := ExactQuotient(p0, f^m);
	if IsDivisibleBy(p0, f) then
		print "Multiplicity too low!";
		return false;
	end if;
	
	return true;
end function;
function TestNC(p,NC)
	map := NC[1]; p0 := map(p);
	f1 := NC[2][1]; m1 := NC[2][2];
	f2 := NC[3][1]; m2 := NC[3][2];
	
	if not IsDivisibleBy(p0, f1^m1) then
		print "Multiplicity 1 too high!";
		return false;
	end if;
	p0 := ExactQuotient(p0, f1^m1);
	if IsDivisibleBy(p0, f1) then
		print "Multiplicity 1 too low!";
		return false;
	end if;
	if not IsDivisibleBy(p0, f2^m2) then
		print "Multiplicity 2 too high!";
		return false;
	end if;
	p0 := ExactQuotient(p0, f2^m2);
	if IsDivisibleBy(p0, f2) then
		print "Multiplicity 2 too low!";
		return false;
	end if;
	if Evaluate(p0, [0,0]) eq 0 then
		print "Extreneous factor!";
		return false;
	end if;
		
	return true;
end function;
*/
