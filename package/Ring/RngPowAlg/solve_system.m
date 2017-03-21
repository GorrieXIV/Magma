freeze;

// *********************************************************************
// * Package: solve_system.mag                                         *
// * =========================                                         *
// *                                                                   *
// * Author: Tobias Beck                                               *
// *                                                                   *
// * Email : Tobias.Beck@oeaw.ac.at                                    *
// *                                                                   *
// * Date  : 22.12.2005                                                *
// *                                                                   *
// *                                                                   *
// * Purpose:                                                          *
// * --------                                                          *
// *                                                                   *
// *   Solve zero-dimensional systems by introducing algebraic field   *
// *   extensions.                                                     *
// *                                                                   *
// * Example call:                                                     *
// * -------------                                                     *
// *                                                                   *
// *   Attach("solve_system.mag");                                     *
// *   Q := Rationals(); P1<x, y> := PolynomialRing(Q, 2);             *
// *   P2<z> := PolynomialRing(Q);                                     *
// *   seq := [y^2 + 1, (x^2*y+y+x^5)*(x-1)];                          *
// *   I := ideal< P1 | seq >;                                         *
// *   p := (2*z-1)*(3*z-2)^2*(z^2-2)^3;                               *
// *                                                                   *
// *   for s in SolveZeroDimIdeal(I) do                                *
// *     for q in seq do                                               *
// *       print Evaluate(q, s[1]);                                    *
// *     end for;                                                      *
// *   end for;                                                        *
// *                                                                   *
// *   for rt in AllRoots(p) do                                        *
// *     print Evaluate(p, rt[1]);                                     *
// *   end for;                                                        *
// *                                                                   *
// * TODO:                                                             *
// * -----                                                             *
// *                                                                   *
// *   - Better solution for extending infinite dimensional algebraic  *
// *     function fields?                                              *
// *                                                                   *
// *********************************************************************

DUMP := true;
DUMP := false;

// ======================
// = Exported functions =
// ======================

// solve polynomial for its roots
intrinsic AllRoots(p::RngUPolElt : ExtName := "alpha", ExtCount := 0)
-> List, RngElt
{
Find all roots to a polynomial equation. For a class of conjugate roots
(with respect to the ground field) only one representative (in an appropriate
extension) is returned.

The first return value is a list '[*  [* x, m *] ... *]' where 'x' is a root
with multiplicity 'm'.

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return
value is the value of 'ExtCount' plus the number of field extensions that
have been introduced during the computation.
}
	P := Parent(p);	F := BaseRing(P);
	require ISA(Type(F),Fld):
		"coefficient ring of 'p' is not a field";
	
	// compute irreducible factors
//"START AllRoots"; "Base Ring:", F; "p:", p;
//SetVerbose("PolyFact",1); time
	factors := Factorization(p);
//SetVerbose("PolyFact",0); "AllRoots #factors:", #factors;

	// for all factors produce ONE of the conjugate roots
	res := [**];
	for fhlp in factors do
		fact := fhlp[1]; mult := fhlp[2];
		
		// find root in ground field ...
		if (Degree(fact) eq 1) then
			root := -Coefficient(fact,0)/Coefficient(fact,1);
		// ... or extend the field as necessary
		else
                        if Type(F) eq FldFun and Degree(F) eq Infinity() then
                            // transform infinite degree extension
                            Fh := RationalExtensionRepresentation(F);
                            Ph := ChangeRing(P, Fh);
                            Fext := FunctionField(Ph ! fact);
                        else
//"DO EXT"; "F:", F; "fact:", fact; time
                            Fext := ext< F | fact: Check := false >;
                        end if;
			root := Fext.1;
			AssignNames(~Fext,
				    [ExtName*"_"*IntegerToString(ExtCount)]);
			ExtCount := ExtCount + 1;
		end if;
		Append(~res, [* root, mult *]);
	end for;
	
	return res, ExtCount;
end intrinsic;


// This is a more friendly interface to SolveZeroDimIdeal
// SRD, Feb 2011

intrinsic RepresentativePoints(X : Simple:=false) -> List
{The scheme points of the zero-dimensional scheme X,
returned as points of X over field extensions.
(There is one point for each irreducible component)}

   F := BaseRing(X);
   a := Dimension(Ambient(X));
   d := Dimension(X);
   require d le 0: "The scheme must be zero-dimensional";
   require IsAffine(X) or IsProjective(X): 
                   "The scheme must be affine or projective";

   if d lt 0 then 
      return [* *];
   elif a eq 0 then
      return [* pt : pt in RationalPoints(Ambient(X)) *];
   end if;

   if IsProjective(X) then
      // Decompose X as disjoint union of affine Xi, 
      // where Xi has X.j = 1 for j < i, and X.i = 1
      pts := [* *];
      for i := 1 to a+1 do
         Xi := AffinePatch(Scheme(X, [X.j : j in [1..i-1]]), a+2-i);
         pts cat:= [* X(Ring(Parent(pt))) ! pt : pt in RepresentativePoints(Xi) *];
      end for;
      assert &+[Degree(Ring(Parent(pt)), F) : pt in pts] eq Degree(X);
      return pts;
   end if;

   solns := SolveZeroDimIdeal(Ideal(X));
   pts := [* *];

   for s in solns do 
      coords := s[1];
      K := Universe(coords);
      if Simple then
         if ISA(Type(K),FldAlg) then
            if Type(F) eq FldRat then
               K := SimpleExtension(K);
            else  
               K := SimpleExtension(K,F);
            end if;
         elif ISA(Type(K),FldFun) then
            if Type(F) eq FldFunRat or AbsoluteDegree(F) eq 1 then
               K := RationalExtensionRepresentation(K); 
            else
               error "Not implemented for relative function field extensions";
            end if;
         end if;
      end if;
      Append(~pts, X(K)!coords);
   end for;

   return pts;
end intrinsic;

// solve (at most) zero-dimensional ideal

intrinsic SolveZeroDimIdeal(id::RngMPol : ExtName := "alpha", ExtCount := 0)
-> List, RngIntElt
{
Find the solutions of the (at most) zero-dimensional ideal 'I' of a
multivariate polynomial ring. For a class of conjugate solutions (with respect
to the ground field) only one representative (in an appropriate extension)
is returned.

The first return value is a list '[* <[x_1, ..., x_n], m, d>, ... *]' where
'[x_1, ..., x_n]' is a solution of 'I', 'm' its multiplicity and 'd' the
degree of the residue field over the ground field.

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return
value is the value of 'ExtCount' plus the number of field extensions that
have been introduced during the computation.
}

NEW := false;
NEW := true;

	// convert to nice ring
	n := Rank(id);
	//id2 := ChangeOrder(id, "univ", n);

	if n eq 1 then // PUT IN C!
	    B := Basis(id);
	    B := [UnivariatePolynomial(f): f in B];
	    f := GCD(B);
	    id := Ideal([MultivariatePolynomial(Generic(id), f, n)]);
	end if;

	if DUMP then id<[x]>:=id; end if;

	id2 := EasyIdeal(id);
	dim := Dimension(id2);

	if DUMP then
printf "\n*****\nSolveZeroDimIdeal: rank: %o, quot dim: %o, base ring: %o\n",
		n, QuotientDimension(id2), BaseRing(id2);

	    "%%%%";
	    "id:", id;
	    "id2:", id2;
	    "%%%%";
	end if;

	// case of no solutions
	if dim eq -1 then return [* *], ExtCount; end if;
	assert dim eq 0;

//"Get last univ poly"; time

	if NEW and n gt 1 then
	    Q := Generic(id2)/id2;

	    p := 0;
	    if 1 eq 1 and n eq 2 and Type(BaseRing(id)) eq FldRat then
		// Skip easy above???
		B := Basis(id);
		B2 := Basis(id2);
		if #B2 lt #B then
		    B := B2;
		end if;
		B := [f: f in B | f ne 0];
		if #B gt 1 then
		    f := B[1];
		    res := [Resultant(f, B[i], n - 1): i in [2 .. #B]];
		    res := [UnivariatePolynomial(f): f in res];
//"res:", res;
		    f := GCD(res);
//"orig f:", f;
		    Lf := Factorization(f);
//"Lf:", Lf;
		    p := Floor(2^23.5);
		    repeat
			p := PreviousPrime(p);
			K := GF(p);
			PK := PolynomialRing(K);
			good := true;
			for t in Lf do
			    good, g := IsCoercible(PK, t[1]);
			    good := good and Degree(g) eq Degree(t[1]);
			    if not good then
				break;
			    end if;
			end for;
		    until good;
		    QK := ChangeRing(Q, K);
		    pK := RepresentationMatrix(QK.n);
		    pK := MinimalPolynomial(pK: Proof := false);
		    pfact := [<t[1], Valuation(pK, PK!t[1])>: t in Lf];
		    pfact := [t: t in pfact | t[2] gt 0];
		    p := &*[t[1]^t[2]: t in pfact];
// "pfact:", pfact;
// "p:", p;
// "pK:", pK;
		end if;
	    end if;

	    if p cmpeq 0 then
		p := RepresentationMatrix(Q.n);
		//"rep mat:", p;
		p := MinimalPolynomial(p: Proof := false);
// "slow p:", p;
	    end if;

	    basis := Basis(id2);
	    P := Generic(id2);
	    blen := #basis;
	else
	    id2 := ChangeOrder(id, "univ", n);
	    Groebner(id2);
	    basis := Basis(id2);
//"basis:", basis;
	    P := Universe(basis);
	    p := UnivariatePolynomial(basis[#basis]);
	    blen := #basis - 1;
	end if;
//printf "Got p; degree: %o\n", Degree(p);

//"Get roots"; time
	// extend base ring according to univariate polynomial
	rts, ExtCount :=
	    AllRoots(p : ExtName := ExtName, ExtCount := ExtCount);
	
//"Number of roots:"; #rts;

//"basis:", basis;
	// end recursion?
	if n eq 1 then
		return [* <[r[1]], r[2], Degree(Parent(r[1]))> : r in rts *],
		    ExtCount;
	end if;
	
	// go into recursion
	res := [**];
	for r in rts do
//"Do root", r;
		val := r[1]; mult := r[2]; deg := Degree(Parent(val));
		
		// construct ideal modulo last equation
		E := Parent(val); PE := PolynomialRing(E, n-1);
		P2PE := hom<P -> PE | [PE.i : i in [1..n-1]] cat [val]>;
//"eval images:", [PE.i : i in [1..n-1]] cat [val];
//"Get eval ideal"; time
		id3 := ideal<PE | [P2PE(basis[i]) : i in [1..blen]]>;
//"Now id3:", id3;
		
//IndentPush();
		// solve it
		sols, ExtCount := SolveZeroDimIdeal(id3: ExtName := ExtName,
		                                         ExtCount := ExtCount);
//IndentPop();
		
		// add last component
		res := res cat [* <Append(sol[1],val), sol[2]*mult, sol[3]*deg>
		                  : sol in sols *];
	end for;
	
	return res, ExtCount;
end intrinsic;

intrinsic OSolveZeroDimIdeal(id::RngMPol : ExtName := "alpha", ExtCount := 0)
-> List, RngIntElt
{
Find the solutions of the (at most) zero-dimensional ideal 'I' of a
multivariate polynomial ring. For a class of conjugate solutions (with respect
to the ground field) only one representative (in an appropriate extension)
is returned.

The first return value is a list '[* <[x_1, ..., x_n], m, d>, ... *]' where
'[x_1, ..., x_n]' is a solution of 'I', 'm' its multiplicity and 'd' the
degree of the residue field over the ground field.

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return
value is the value of 'ExtCount' plus the number of field extensions that
have been introduced during the computation.
}

	id2 := ChangeOrder(id, "lex"); Groebner(id2);

/*
printf "\n*****\nOLD SolveZeroDimIdeal: rank: %o, quot dim: %o, base ring: %o\n",
    Rank(id2), QuotientDimension(id2), BaseRing(id2);

"%%%%";
"id2:", id2;
"%%%%";
*/

	// convert to nice ring
	basis := Basis(id2); P := Universe(basis); Q := BaseRing(P);
	n := Rank(P); dim := Dimension(id2);
	
	// case of no solutions
	if dim eq -1 then return [* *], ExtCount; end if;
	assert dim eq 0;
	
	// extend base ring according to univariate polynomial
	p := UnivariatePolynomial(basis[#basis]);
	rts, ExtCount :=
	    AllRoots(p : ExtName := ExtName, ExtCount := ExtCount);
	
	// end recursion?
	if n eq 1 then
		return [* <[r[1]], r[2], Degree(Parent(r[1]))> : r in rts *],
		    ExtCount;
	end if;
	
	// go into recursion
	res := [**];
	for r in rts do
		val := r[1]; mult := r[2]; deg := Degree(Parent(val));
		
		// construct ideal modulo last equation
		E := Parent(val); PE := PolynomialRing(E, n-1);
		P2PE := hom<P -> PE | [PE.i : i in [1..n-1]] cat [val]>;
		id3 := ideal<PE | [P2PE(basis[i]) : i in [1..#basis-1]]>;
		
		// solve it
		sols, ExtCount := SolveZeroDimIdeal(id3: ExtName := ExtName,
		                                         ExtCount := ExtCount);
		
		// add last component
		res := res cat [* <Append(sol[1],val), sol[2]*mult, sol[3]*deg>
		                  : sol in sols *];
	end for;
	
	return res, ExtCount;
end intrinsic;


// solve for roots in product spaces
intrinsic SolveInProductSpace(id::RngMPol
    : seq := [0], ExtName := "alpha", ExtCount := 0)
-> List, RngIntElt
{
Given an ideal 'id' of a polynomial ring 'P' of rank 'n' and a sequence 'seq'
s.t. the 'seq[i]' mark blocks of projective coordinates. Assuming that 'id'
defines a zero-dimensional subset in the corresponding product space (with
projective and affine components) returns a list of all (finitely many) points
in the subset.

For example, if 'n=6' and 'seq=[0,2,5]' then '[P.1 : P.2]' and
'[P.3 : P.4 : P.5]' are the blocks of projective coordinates and 'P.6' is an
affine coordinate. Then 'id' should be a two-dimensional ideal homogeneous
w.r.t. total degrees for both blocks separately. It defines a point set in
'P^1 X P^2 X A^1'. If no projective coordinates are intended use 'seq=[0]'.

If the ground field has to be extended, the algebraic elements will be
displayed as 'ExtName_i' where 'i' starts from 'ExtCount'. The last return
value is the value of 'ExtCount' plus the number of field extensions that
have been introduced during the computation.
}
	P := Universe(Basis(id)); Q := BaseRing(P); n := Rank(P);
	
	// purely affine case?
	if #seq eq 1 then
		sols, ExtCount :=
		    SolveZeroDimIdeal(id : ExtName := ExtName,
		                           ExtCount := ExtCount);
		return [* s[1] : s in sols *], ExtCount;
	end if;
	
	// one point projective space?
	if (n eq 1) and (seq[#seq]-seq[#seq-1] eq 1) then
		return IsZero(id) select [* [Q | 1] *] else [* *], ExtCount;
	end if;
	
	// reduced polynomial ring
	P2 := PolynomialRing(Q, n-1);
	
	// first solve in affine chart
	vs := [P2.i : i in [1..(seq[#seq]-1)]] cat [1]
	    cat [P2.i : i in [seq[#seq]..n-1]]; 
	dehomo := hom<P -> P2 | vs>;
	dehomoRe := func<x | x[1..(seq[#seq]-1)] cat [1]
	    cat x[seq[#seq]..n-1]>;
	id2 := ideal<P2 | [dehomo(e) : e in Basis(id)]>;
	seq2 := seq[1..#seq-1];
	affsols, ExtCount :=
	    SolveInProductSpace(id2 : seq := seq2, ExtName := ExtName,
	                         ExtCount := ExtCount);
	sols := [* dehomoRe(s) : s in affsols *];
	
	// then maybe solve at infinity
	if seq[#seq]-seq[#seq-1] gt 1 then
		vs := [P2.i : i in [1..(seq[#seq]-1)]] cat [0]
		    cat [P2.i : i in [seq[#seq]..n-1]]; 
		infini := hom<P -> P2 | vs>;
		infiniRe := func<x | x[1..(seq[#seq]-1)] cat [0]
		    cat x[seq[#seq]..n-1]>;
		id2 := ideal<P2 | [infini(e) : e in Basis(id)]>;
		seq2 := seq[1..#seq-1] cat [seq[#seq]-1];
		infsols, ExtCount :=
		    SolveInProductSpace(id2 : seq := seq2, ExtName := ExtName,
		                         ExtCount := ExtCount);
		sols := sols cat [* infiniRe(s) : s in infsols *];
	end if;
	
	return sols, ExtCount;
end intrinsic;
