freeze;

///////////////////////////////////////////////////////////////////
//     Intrinsics for computing all intersection points          //
//  along with multiplicities of two plane curves in a single	 //
//       computation, following the algorithm of 	     	 //
//            Jan Hilmar and Chris Smyth.			 //
//   mch - 01/2013 - Magma conversion of a Maple           	 //
//    program kindly provided by Chris Smyth.			 //
///////////////////////////////////////////////////////////////////

function cycle_minus(c)
// c is a (not necessarily reduced) sequence representing a cycle C.
// Return a sequence representing -C.
    return [* <m[1],-m[2]> : m in c *];
end function;

function triple_compare(e,f)
// e and f are lists of 3 elements. Returns whether e[i]=f[i] for i=1..3
    return &and[e[i] cmpeq f[i] : i in [1..3]];
end function;

function cycle_combine(cy)
// cy is a not necessarily reduced sequence of <m,[a,b,c]> terms representing
// a cycle C.
// Return a reduced sequence representing C.
//return cy;
    c := cy;
    i := 1;
    while i le #c do
	p := c[i][1];
	js := [j : j in [i+1..#c] | triple_compare(c[j][1],p)];
	if #js gt 0 then
	  m := c[i][2] + &+[c[j][2] : j in js];
	  for j in Reverse(js) do Remove(~c,j); end for;
	  if m eq 0 then
	    Remove(~c,i); i -:= 1;
	  else
	    c[i] := <p,m>;
	  end if;
	end if;
	i +:= 1;
    end while;
    return c;

end function;

function my_quotrem(A,B)
// A,B are (homogeneous) polys in k[x,y,z] with (d=deg(A,x)) >= (e=deg(B,x)) > 0
//  if m in k[y,z] is the leading term of A as a poly in x then this function
//  returns q,r,M in k[x,y,z] s.t. M*A=q*B+r and deg(r,x) < e, M = m^(d-e+1).

    P := Generic(Parent(A));
    csA := Reverse(Coefficients(A,1));
    csB := Reverse(Coefficients(B,1));
    d := #csA-1;
    e := #csB-1;
    m := csB[1];

    r := d-e;
    if e lt r then
	csB cat:= [P!0 : i in [1..r-e]];
    end if;
    cs := [csA[1]];
    for i in [1..r] do
	csr := csA[i+1];
	for j in [1..i] do
	  csr := m*csr-cs[j]*csB[i+2-j];
	end for;
	Append(~cs,csr);
    end for;
    mpow := m;
    for i in [0..r-1] do
	cs[r-i] *:= mpow;
	mpow *:= m;
    end for;
    // mpow is now m^(r+1) and Reverse(cs) are the coeffs of q;
    csq := &cat[Coefficients(c) : c in cs];
    msq := &cat[[Monomial(P,[r+1-i] cat Exponents(e)[2..3]) : e in Monomials(cs[i])]
			: i in [1..r+1]];
    q := Polynomial(csq,msq);
    r := mpow*A-q*B;
    assert Degree(r,1) lt e;
    return q,r,mpow;

end function;

function RKtoR2(f,R2)
// f is a monic polynomial of deg >= 1 in K[x] and R2 is k[x,y]
// where K=k(a) is a finite, simple algebraic extension of k.
// Converts f to a polynomial R2 in the obvious way (a <-> y)

    assert IsMonic(f);
    RK := Generic(Parent(f));
    k := BaseRing(R2);
    cs := Coefficients(f);
    cs1 := [k|]; mons := [R2|];
    for i in [1..(#cs)-1] do
      if IsZero(cs[i]) then continue; end if;
      es := Eltseq(cs[i],k);
      js := [j : j in [1..#es] | not IsZero(es[j])];
      cs1 cat:= [es[j] : j in js];
      mons cat:= [Monomial(R2,[i-1,j-1]) : j in js];
    end for;
    // add x^deg term
    Append(~cs1,k!1); Append(~mons,Monomial(R2,[(#cs)-1,0]));
    return Polynomial(cs1,mons);

end function; 

function int1(A,m)
// A is a homogeneous polynomial in just x,y and m is a +ive
//  integer. Returns the intersection cycle A.(m(z)).

    P := Generic(Parent(A));
    k := BaseRing(P);
    R := PolynomialRing(k);

    //firstly, get factorisation of A(x,1)
    afact := Factorisation(Evaluate(A,[R.1,1,1]));
    ymult := LeadingTotalDegree(A)-&+[Integers()|Degree(e[1])*e[2] : e in afact];

    //write down cycle for m * sum (mult * (irred factor).(z))
    c := [* <[* fc[1], k!1, k!0 *], m*fc[2]> : fc in afact *];
    if ymult gt 0 then
	Insert(~c,1, <[* k!1,k!0,k!0 *], m*ymult>);
    end if;
    return c;

end function;

function int0(A,B)
// Finds intersection cycle A.B for A=0,B=0 where A,B are homogeneous
//  polynomials with no common factor, A in x,y,z and B in y,z.

    P := Generic(Parent(A));
    k := BaseRing(P);
    d := LeadingTotalDegree(A);
    R := PolynomialRing(k);
    R2 := PolynomialRing(k,2 : Global := true);
    hm12 := hom<R->R2 | R2.1>;

    //firstly, get factorisation of B(y,1)
    bfact := Factorisation(Evaluate(B,[1,R.1,1]));
    zmul := LeadingTotalDegree(B)-&+[Integers()|Degree(e[1])*e[2] : e in bfact];
    // start with the A.(m*(z)) part of A.B
    c := (zmul eq 0) select [**] else int1(Evaluate(A,[P.1,P.2,0]),zmul);

    //compute other A.(irred factor) cycles
    for fc in bfact do
	f := fc[1];
	m := fc[2];
	if Degree(f) eq 1 then  //f = y-a
	  a := -Coefficient(f,0);
	  fact := Factorisation(Evaluate(A,[R.1,a,1]));
	  zmult := d-&+[Integers()|Degree(e[1])*e[2] : e in fact];
	  c1 := [* <[* hm12(fc[1]),f,k!1 *], m*fc[2]> : fc in fact *];
	else //deg(f) > 1
	  K<a> := ext<k|f>;
	  RK := PolynomialRing(K);
	  fact := Factorisation(Evaluate(A,[RK.1,a,K!1]));
	  zmult := (d-&+[Integers()|Degree(e[1])*e[2] : e in fact])*Degree(f);
	  c1 := [* <[* RKtoR2(fc[1],R2),f,k!1 *], m*fc[2]> : fc in fact *];
	end if;
	if zmult gt 0 then 
	  Insert(~c1,1, <[* k!1,k!0,k!0 *], m*zmult>);
	end if;
	c cat:= c1;
    end for;

    return c;

end function;

function inter(A,B)
// Finds intersection cycle A.B for A=0,B=0 where A,B are homogeneous
//  polynomials in 3 variables with no common factor

    if Degree(A,1) lt Degree(B,1) then
	return inter(B,A);
    elif TotalDegree(B) le 0 then
	lst := [**];
    elif Degree(B,1) eq 0 then //B a poly in y,z
	lst := int0(A,B);
    else //induction on Deg_x(B)
	// M*A=B*q+C where M is a poly in y,z, C has
	//  Deg_x(C) < Deg_x(B) and G=GCD(M,C)=GCD(M,B)
        // Then A.B = (B/G).(C/G) - (B/G).(M/G) + A.G
	q,C,M := my_quotrem(A,B);
	g := GCD([M,q,C]);
	M := M div g; C := C div g;
	G := GCD(M,C);
	if G eq 1 then
	  lst := inter(B,C) cat cycle_minus(inter(B,M));
	else
	  B := B div G; C := C div G; M := M div G;
	  lst := inter(B,C) cat cycle_minus(inter(B,M)) cat
			inter(A,G);
	end if;
    end if;
    // combine mutiple cycle terms and return
    return cycle_combine(lst);

end function;

function change_rep(c,P2)
// Convert a cycle given as a list of <m,[f,g,h]> terms with f,g,h polynomials
//  into a list of <m,P> terms where P is a point in P2(K) for appropriate K
//  (so the term actually corresponds to m*sum P^s, where P^s ranges over
//  a set of conjugate points over the base field k
// Any field extension generators are labelled a1,a2,.. etc.

    c1 := [**]; j := 1;
    k := BaseRing(P2);
    notFF := not (Type(k) cmpeq FldFin);
    for t in c do
	s := t[1];
	if IsZero(s[3]) then
	  if IsZero(s[2]) then //[1,0,0]
	    P := P2![k|1,0,0];
	  else //[f,1,0]
	    assert IsOne(s[2]);
	    f := s[1];
	    if Degree(f) eq 1 then
	      P := P2![-Coefficient(f,0),1,0];
	    else
	      K := ext<k|f>;
	      if notFF then AssignNames(~K,["a" cat IntegerToString(j)]); j +:= 1; end if;
	      P := P2(K)![K.1,1,0];
	    end if;
	  end if;
	else //[f(x,y),g(y),1]
	  assert IsOne(s[3]);
	  f := s[1]; g := s[2];
	  if Degree(g) eq 1 then
	    p2 := -Coefficient(g,0); K := k;
	  else
	    K := ext<k|g>;
	    if notFF then AssignNames(~K,["a" cat IntegerToString(j)]); j +:= 1; end if;
	    p2 := K.1;
	  end if;
	  if Degree(f,1) eq 1 then
	    P := P2(K)![K|-Evaluate(UnivariatePolynomial(Coefficients(f,1)[1]),p2),p2,1];
	  else	  
	    fK := Evaluate(f,[PK.1,p2]) where PK is PolynomialRing(K);
	    L := ext<K|fK>;
	    if notFF then AssignNames(~L,["a" cat IntegerToString(j)]); j +:= 1; end if;
	    P := P2(L)![L.1,L!p2,1];
	  end if;
	end if;
	Append(~c1,<P,t[2]>);
    end for;
    return c1;

end function;

function change_to_non_global(c,k)
// In the polynomial case where c is a list of pairs with first elements
//  of the form [*f,g,1*], [*g,1,0*] or [*1,0,0*] with f and g in the
//  global rings of bivariate polynomials and univariate polynomials over
//  k, convert to using non-global polynomial rings with variable names
//  x,y resp. y 

    R<x,y> := PolynomialRing(k,2);
    P := PolynomialRing(k : Global := false); y := P.1;
    c1 := [* *];
    for t in c do
	p := t[1];
	if IsZero(p[3]) then
	  if IsZero(p[2]) then //[1,0,0]
	    p1 := p;
	  else //[g,1,0]
	    p1 := [* P!Coefficients(p[1]),k!1,k!0 *];
	  end if;
	else //[f,g,1]
	  p1 := [* Polynomial(Coefficients(p[1]),
			[Monomial(R,Exponents(e)) : e in Terms(p[1])]),
		    P!Coefficients(p[2]),k!1 *];
	end if;
	Append(~c1,<p1,t[2]>);
    end for;
    return c1;

end function;

intrinsic IntersectionNumbers(A::RngMPolElt, B::RngMPolElt : Global := false) -> List
{ A and B should be relatively prime homogeneous polynomials in the same 3-variable
  polynomial ring k[x,y,z] over a finite or number field. Returns the cycle of
  the intersection of the curves A=0 and B=0 as a list of pairs <p,m> where
  p is polynomial data defining a set of conjugate points in the intersection
  (as described in the handbook) and m is the intersection multiplicity at these points.
  By default, non-global uni- and bi-variate polynomial rings are used for the elements
  of p. The Global parameter can be set to true if global versions of these
  rings are preferred.}

    P := Generic(Parent(A));
    k := BaseRing(P);
    require IsIdentical(Generic(Parent(B)),P):
	"Arguments must lie in the same polynomial ring";
    require (Rank(P) eq 3) and IsHomogeneous(A) and IsHomogeneous(B):
	"Arguments must be homogeneous elements of a 3-variable polynomial ring";
    require (k cmpeq Rationals()) or ISA(Type(k),FldAlg) or ISA(Type(k),FldFin):
	"Arguments must lie in a polynomial ring over a finite field or number field";
    require GCD(A,B) eq P!1:
	"Arguments must be relatively prime polynomials";

    c := inter(A,B);
    if not Global then c := change_to_non_global(c,k); end if;
    return c;

end intrinsic;

intrinsic IntersectionNumbers(C::CrvPln, D::CrvPln) -> List
{ C and D should be curves with no common component in the same ordinary projective plane
  P2 over a finite field or number field k. Returns the cycle of intersection of C and D 
  as a list of pairs <p,m> where p is a point in P2(K) for a finite extension K of k and
  m is the intersection multiplicity of C and D at p}

    P2 := Ambient(C);
    k := BaseRing(P2);
    require IsIdentical(Ambient(D),P2):
	"Arguments must lie in the same projective plane";
    require IsOrdinaryProjective(P2) and (Rank(CoordinateRing(P2)) eq 3):
	"Arguments must be curves in an ordinary projective plane";
    require (k cmpeq Rationals()) or ISA(Type(k),FldAlg) or ISA(Type(k),FldFin):
	"Arguments must lie in a projective plane over a finite field or number field";
    A := Equation(C); B := Equation(D);
    require GCD(A,B) eq 1:
	"Arguments must have no common irreducible component";

    c := inter(A,B);
    c1 := change_rep(c,P2);
    return c1;

end intrinsic;
