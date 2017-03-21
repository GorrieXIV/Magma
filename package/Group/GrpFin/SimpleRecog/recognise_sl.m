freeze;
 
SLdata := recformat<
    B,
    B1,
    B1finv,
    baseQ,
    baseQgamma,
    bbg,
    c,
    cprog,
    centre,
    centreprog,
    conj,
    FB,
    gen,
    gens,
    jgamma,
    Lgen,
    lincombQ,
    lincombQgamma,
    power,
    prime,
    pQ,
    Q,
    Qgamma,
    sinv,
    slpgrp,
    sprog,
    T,
    T1,
    t21,
    t21invtran,
    tran,
    trangp,
    trangp1,
    trangpgamma,
    trangpQ,
    trangpQgamma
    >;

function Fails(x)
    /*
    if x then
	Traceback();
    end if;
    */
    return "fails";
end function;

/*
procedure Inform(x)
    print x;
end procedure;
*/

procedure AdjustSeqenceUniverse(~Q, x)
    S := CoveringStructure(Universe(Q), Parent(x));
    ChangeUniverse(~Q, S);
end procedure;

//////////////////////////////////////////////////////////////////////////////
//                                                                          //
//I This is the implementation of the Kantor-Seress algorithm for PSL(d,q)  //
//                                                                          //
////////////////////////////////////////////////////////////////////////////// 
//////////////////////////////////////////////////////////////////////////////
//
//F BoundedOrder( <bbgroup> , <elt> , <power>, <primes> )
//
// This is a subroutine needed in the sequel which takes as input an element
// $r$ of bbg and a positive integer $n$ such that $r^n=1$ and will return
// the flag "true" if and only if $n$ is the order of $r$.

function BoundedOrder(bbg, r, n, primes)
// Inform("BoundedOrder");

    return forall{prime: prime in primes | r^(n div prime) ne one}
	where one is One(bbg);
end function;

/////////////////////////////////////////////////////////////////////////////
//
//F BinFunc ( <integer> )
//
// BinFunc takes an integer $n$ and returns a list containing the binary
// representation of $n$.

function BinFunc(n)
// Inform("BinFunc");

    return IntegerToSequence(n, 2);
end function;

///////////////////////////////////////////////////////////////////////////
//
//F NtoPadic( <prime> , <power>, <number> )
//
// Writes a number 0 <= n < p^e in base p

function NtoPadic(p, e, n)
// Inform("NtoPadic");

    return IntegerToSequence(n, p, e);
end function;

///////////////////////////////////////////////////////////////////////////
//
//F PadictoN( <prime> , <power>, <vector> )
//
// Writes a vector in GF(p)^e as a number 0 <= n < p^e 

function PadictoN(p, e, vector)
// Inform("PadictoN");

    return &+ [p^(j - 1) * Integers()!vector[j]: j in [1 .. e]];
end function;

//////////////////////////////////////////////////////////////////////////////
//
//F IS_IN_CENTRE( <bbgroup> , <elt> )
//
// In case the group we are dealing with is a PSL instead of an SL, we 
// will need to check with certain elements lie in the centre of our group.

function IS_IN_CENTRE(bbg, x)
// Inform("IS_IN_CENTRE");

    return forall{i: i in [1 .. Ngens(bbg)] | one eq (x, bbg.i)}
	where one is One(bbg);
end function;

//////////////////////////////////////////////////////////////////////////////
//
//F AppendTran( <bbg> , <H> , <x> , <p> )
//
// The idea here is that $H$ is a proper subgroup (subspace) of a transvection
// group $T$ with parent group $bbg$. $x$ is a verified element of $T$, and
// $dim$ is the dimension of the new subspace of $T$ spanned by $H$ and $x$.
// The subroutine will return this new $H$ and alter the vectors of its elms.

procedure AppendTran(bbg, ~H, x, p)
// Inform("AppendTran");

    tau := One(bbg);
    length := #H;
    for i in [1 .. p - 1] do
	tau *:= x;
	H join:= {@ H[j] * tau: j in [1 .. length] @};
    end for;
end procedure;

/////////////////////////////////////////////////////////////////////////////
//
//F IsInTranGroup ( <bbgroup> , <listedgroup> , <tran> )
//
// This subroutine takes a list (which will actually be a subgroup of a
// transvection group) which is contained in bbgroup, together with a
// transvection, and outputs `true' iff tran is in list.

function IsInTranGroup(bbg, H, x)
// Inform("IsInTranGroup");

    return exists{z: z in H | x eq z};
end function;

/////////////////////////////////////////////////////////////////////////////
//
//F MatrixOfEndo( <group>, <elem.ab.subgp>, <prime>, <dimension>, <automorph> )
//
// Computes the matrix of the linear transformation $s$ 
// in terms of // the standard basis of $T$. The routine assumes 
// that $T$ is listed in the order as in AppendTran.
// $|T|=p^e$, $T \le bbg$

function MatrixOfEndo(bbg, T, p, e, s)
// Inform("MatrixOfEndo");

    assert #T eq p^e;
    matrixofs := [];
    for i in [0 .. e - 1] do
	// the basis vectors of T are in position p^i + 1
	// find conj in T
	j := Position(T, T[p^i + 1]^s);
	if j eq 0 then
	    return Fails(true);
	end if;
	Append(~matrixofs, NtoPadic(p, e, j - 1));
    end for;
    return Matrix(GF(p), matrixofs);
end function;

////////////////////////////////////////////     
//
    function extractgen(matrixofs, endo, p, e, weights, limit)
    // Inform("extractgen");

	conj := IdentityMatrix(GF(p), e);
	stop := false;
	j := 0;

	K := GF(p);
	repeat
	    temp := Vector(K, [0: k in [1 .. e]]);
	    ans := Vector(K, [1] cat [0: k in [2 .. e]]);
	    for k in [1 .. e - 1] do
		ans *:= conj * endo;
		temp[1] +:= weights[e + 1 - k];
		temp *:= conj * endo;
	    end for;
	    ans *:= conj * endo;
	    temp[1] +:= weights[1];
	    if ans eq temp then
		return j;
	    end if;
	    j +:= 1;
	    conj *:= matrixofs;
	until stop or j eq limit;

	return j;
    end function;

//////////////////////////////////////////////////////////////////////////////
//
//F FindGoodElement ( <bbgroup> , <bbrand> , <prime> , <power> , <dim> , <limit> )
//
// This function will take as input a bbgroup which is somehow known to be 
// isomorphic to $SL(d,q)$ or $PSL(d,q)$ where $q=p^e$. The function will 
// (if anything) output a bbgroup element r of order p*ppd/(p;e(d-2)).
//
// Added random process for bbgroup, called bbrand. Use Random(bbrand)  
// instead of Random(bbg). billu 1/9/03

function FindGoodElement(bbg, bbrand, p, e, d, limit)
// Inform("FindGoodElement");

    q := p^e;
    one := One(bbg);
    if d eq 3 and q eq 4 then
	if exists(r){r: i in [1 .. limit] | r^12 eq one and r^6 ne one
		where r is Random(bbrand)} then
	    return r^6;
	end if;
    elif d eq 3 and q eq 2 then
	if exists(r){r: i in [1 .. limit] | r^4 eq one
		where r is Random(bbrand)} then
	    return r^2 eq one select r else r^2;
	end if;
    elif d eq 3 and q eq 25 then
        if exists(r){r: i in [1 .. limit] | r^40 eq one and r^8 ne one
                and r^5 ne one where r is Random(bbrand)} then
            return r;
        end if;
    else
	ed2 := e * (d - 2);
	z := p^ed2 - 1;

	if p eq 2 and ed2 eq 6 then
	    tst := func<v |
		(v^7 ne one and v^9 ne one) or
		(v^3 ne one and v^9 eq one)
	    >;
	elif ed2 eq 2 and IsPowerOf(p + 1, 2) then
	    _, w := Valuation(z, 2);
	    w *:= 2;
	    tst := func<v | v^w ne one>;
	else
	    primes := [x[1]: x in Factorization(ed2)];
	    psi := 1;
	    phi := z;
	    if ed2 gt 1 then
		for c in primes do
		    a := GCD(phi, p^(ed2 div c) - 1);
		    while a gt 1 do
			psi *:= a;
			phi div:= a;
			a := GCD(phi, a);
		    end while;
		end for;
	    end if;
	    tst := func<v | v^psi ne one>;
	end if;

	if exists(r){r: i in [1 .. limit] | v^z eq one and r^z ne one and tst(v)
		where v is r^p where r is Random(bbrand)} then
	    return r;
	end if;
    end if;

    return Fails(true);
end function;

//////////////////////////////////////////////////////////////////////////////
//
//F SL4FindGoodElement ( <bbgroup> , <bbrand> , <prime> , <power> , <limit> )
//
// This function will take as input a bbgroup which is somehow known to be 
// isomorphic to $SL(4,q)$ or $PSL(4,q)$ where $q=p^e$. The function will 
// (if anything) output a bbgroup element r of order p*ppd/(p;2e).
//
// Added random process for bbgroup, called bbrand. Use Random(bbrand)  
// instead of Random(bbg). billu 1/9/03

function SL4FindGoodElement(bbg, bbrand, p, e, limit)
// Inform("SL4FindGoodElement");

    q := p^e;
    one := One(bbg);
    if q eq 2 then
	if exists(r){r: i in [1 .. limit] | r^6 eq one and
		r^3 ne one and r^2 ne one
		where r is Random(bbrand)} then
	    return r;
	end if;
    elif q eq 3 then
	if exists(r){r: i in [1 .. limit] | r^12 eq one and r^4 ne one and
		not IS_IN_CENTRE(bbg, r^6)
		where r is Random(bbrand)} then
	    return r;
	end if;
    elif q eq 5 then
	if exists(r){r: i in [1 .. limit] | r^15 eq one and
		r^3 ne one and r^5 ne one
		where r is Random(bbrand)^4} then
	    return r;
	end if;
    elif q eq 9 then
	if exists(r){r: i in [1 .. limit] | r^15 eq one and
		r^3 ne one and r^5 ne one
		where r is Random(bbrand)^8} then
	    return r;
	end if;
    elif q eq 17 then
	if exists(r){r: i in [1 .. limit] | r^153 eq one and
		r^9 ne one and r^17 ne one
		where r is Random(bbrand)^16} then
	    return r;
	end if;
    else
	if exists(r){r: i in [1 .. limit] | r^(p*(q^2-1)) eq one and
		r^(q^2-1) ne one and r^(8*p*(q+1)) ne one and r^(p*(q-1)) ne one
		where r is Random(bbrand)} then
	    return r;
	end if;
    end if;
    return Fails(true);
end function;

///////////////////////////////////////////////////////////////////////////////
//
//F CommutesWith( <bbgroup> , <set> , <x> )
//
// This short routine, needed in the sequel, returns true if and only if <x>
// commutes with every element in the set <set>.

function CommutesWith(bbg, S, x)
// Inform("CommutesWith");

    return forall{s: s in S | (s, x) eq one} where one is One(bbg);
end function;

////////////////////////////////////////////////////////////////////////////////
//
//F EvaluateBBGp( <bbg>, <gens> , <slp> )
//
// This routine will evaluate a straightline program from the black box
// group piece of gens.

function EvaluateBBGp(bbg, gens, slp)
// Inform("EvaluateBBGp");

    return Evaluate(slp, [x[1]: x in gens]);
end function;

////////////////////////////////////////////////////////////////////////////
//
//F EvaluateMat( <gens> , <slp>, <dim>, <field size> )
//
// This is in all respects identical to the above, except that we evaluate
// from the matrix group piece of gens.

fullgen := function(x, d, q)
// Inform("");

    M := IdentityMatrix(GF(q), d);
    for t in x do
	M[t[1]][t[2]] := t[3];
    end for;
    return M;
end function;

function EvaluateMat(gens, slp, d, q)
// Inform("EvaluateMat");

    return Matrix(Evaluate(slp, [GL(d, q) | fullgen(x[2], d, q): x in gens]));
end function;

/////////////////////////////////////////////////////////////////////////////
//
//F SL2Search ( <bbgroup> , <bbrand>, <prime> , <power> [, <transvection> ] )
//
// This function will take as input a bbgroup known to be isomorphic to
// $PSL(2,q)$ for known $q=p^e$ and will output an element of order $p$
// and one of order q-1 or (q-1)/(2,q-1) with
// probablility at least 0.94.
// We may already have a transvection in the input
//
// Added random process for bbgroup, called bbrand. Use Random(bbrand)  
// instead of Random(bbg). billu 1/9/03

function SL2Search(bbg, bbrand, p, e: Transvection := "compute")
// Inform("SL2Search");

    out := rec<SLdata | >;
    if Transvection cmpne "compute" then
	out`tran := Transvection;
    end if;

    primes := {x[1]: x in Factorisation(p^e - 1)};
    m := 6 * p^e;
    count := 1;
    one := One(bbg);

    if p eq 2 then
	tst := func<r | r^n eq one and BoundedOrder(bbg, r, n, primes), r>
	    where n is p^e - 1;
    elif p^e mod 4 eq 3 then
	Exclude(~primes, 2);
	tst := func<r | r2^n eq one and BoundedOrder(bbg, r2, n, primes),
	    r2 where r2 is r^2> where n is (p^e - 1) div 2;
    else
	tst := func<r | (r^n eq one and BoundedOrder(bbg, r, n, primes)) or
		(r^(n div 2) eq one and BoundedOrder(bbg, r, n div 2, primes)
		    and not IS_IN_CENTRE(bbg, r^(n div 4))), r>
	    where n is p^e - 1;
    end if;

    while count lt m do
	r := Random(bbrand);
	if not one eq r then
	    if not assigned out`tran and one eq r^p then
		out`tran := r;
	    end if;
	    if not assigned out`gen then
		f, rr := tst(r);
		if f then
		    out`gen := rr;
		end if;
	    end if;
	end if;
	count +:= 1;
	if assigned out`tran and assigned out`gen then
	    return out;
	end if;
    end while;
    return Fails(true);
end function;

//////////////////////////////////////////////////////////////////////////////
//
//F ConstructTranGroup( <bbgroup> , <bbrand>, <tran> , <prime> , <power> )
//
// Given a bbgroup purportedly isomorphic to $SL(2,q)$ or $PSL(2,q)$ where
// q=p^e, this will return the full transvection group $T$ containing $tran$
// or report failure. In the case that bbgroup is what it should be, then
// success is highly probable.
//
// Added random process for bbgroup, called bbrand. Use Random(bbrand)  
// instead of Random(bbg). billu 1/9/03

function ConstructTranGroup(bbg, bbrand, tran, p, e)
// Inform("ConstructTranGroup");

    t := tran;
    m := 128 * (p^e + 1) * e;

    B := [t];
    H := [i eq 1 select One(bbg) else Self(i - 1) * t: i in [1 .. p]];
    H := {@ x: x in H @};
    if e eq 1 then
	assert #H eq p;
	return H;
    end if;

    tinv := t^-1;
    count := 1;
    while count lt m do
	x := t ^ Random(bbrand);
	count +:= 1;
	if x eq tinv * x * t and not IsInTranGroup(bbg, H, x) then
	    Append(~B, x);
	    AppendTran(bbg, ~H, x, p);
	    if #H eq p^e then
		return H;
	    end if;
	end if;
    end while;
    return Fails(true);
end function;

//////////////////////////////////////////////////////////////////////////
//
//F Dislodge( <bbgroup> , <trangroup> )
//
// returns a generator of $G$ which does not normalize $T$

function Dislodge(bbg, T)
// Inform("Dislodge");

    t := T[2];
    tinv := t^-1;
    one := One(bbg);
    if exists(g){g: i in [1 .. Ngens(bbg)] | g ne one and tg ne tinv * tg * t
	    where tg is t^g where g is bbg.i} then
	return g;
    end if;
    return Fails(true);
end function;

///////////////////////////////////////////////////////////////////////////
//
//F Standardize( <bbgroup> , <trangroup> , <conj> , <gen> )
//
// We found <gen> in SL2Search to be an element of order $(q-1)$ or $(q-1)/2$
// <gen> will normalize two transvection groups (conjugates of $T$). We wish
// to conjugate <gen> to an $s$ which will normalize $T$ and $T^<conj>$.

function Standardize(bbg, T, j, s)
// Inform("Standardize");

    t := T[2];
    out := rec<SLdata | >;
    sinv := s^-1;

    firstconj := sinv * t * s;
    if firstconj eq firstconj^t then
	out`gen := s;
	if exists(u){u: u in T | y eq y^ytos where ytos is sinv * y * s
		where y is t^(j * u) } then
	    out`conj := j * u;
	    return out;
	end if;
	return Fails(true);
    else
	fixed :=  [u: u in T | #Self() lt 2 and
	    (y eq y^ytos where ytos is sinv * y * s where y is t^(j * u)) ];
	if #fixed lt 2 then
	    return Fails(true);
	end if;
	c := (j * fixed[1])^-1;
	out`gen := s^c;
	out`conj := z * c where z is j * fixed[2];
	return out;
    end if;
end function;

/////////////////////////////////////////////////////////////////////////////
//
//F SL2ReOrder( <bbgroup> , <trangroup> , <s> , <j> , <prime> , <power> )
//
// The idea of this subroutine is to reorder $T$ and more importantly, the
// permutation domain $Y$, so as to be compatible with our labelling of the
// projective line $PG(1)$. This will then enable us to determine up to
// scalar, the matrix image of an $x$ in our bbgroup.

function SL2ReOrder(bbg, T, s, j, p, e)
// Inform("SL2ReOrder");

    t := T[2];
    one := One(bbg);

    // handle the case of prime field first
    if e eq 1 then
	auto := function(bbg, x, pow, conj)
	    return x^w;
	end function where w is PrimitiveRoot(p);

	// define dummy variables
	pow := 0;
	conj := 0;
    else
	K := GF(p^e);
	P := PrimeField(K);
	rho := PrimitiveElement(K);
	B := [rho^(i - 1): i in [1 .. e]];
	_, phi := VectorSpace(K, P, B);
	weights := phi(rho^e);

	// first we defined the correct automorphism of $T$
	matrixofs := MatrixOfEndo(bbg, T, p, e, s);
	if matrixofs cmpeq "fails" then
	    return Fails(false);
	end if;

	if p mod 2 eq 1 then
	    // list and order the images of t under s
	    row := Vector(P, [1] cat [0: i in [2 .. e]]);
	    images := [i eq 0 select row else Self(i) * matrixofs:
			    i in [0 .. (p^e - 3) div 2]];
	    setofimages := {PadictoN(p, e, x): x in images};
	    Include(~setofimages, 0);

	    // find an endomorphism which does not fix the list images
	    if not exists(i){i: count in [1 .. 30] | pos notin setofimages
		    where pos is PadictoN(p, e, autom)
		    where autom is images[i] + row
		    where i is Random([1 .. #images]) } then
		return Fails(true);
	    end if;

	    matrixofpow := matrixofs^(i - 1);
	    pow := s^(i - 1);

	    good := extractgen(matrixofs, matrixofpow + IdentityMatrix(GF(p),e),
		    p, e, weights, (p^e - 1) div 2);
	    if good eq (p^e - 1) div 2 then
		return Fails(true);
	    end if;
	    conj := s^good;

	    auto := function(bbg, x, pow, conj)
		firstconj := x^conj;
		return firstconj * (firstconj^pow);
	    end function;
	else
	    good := extractgen(matrixofs, IdentityMatrix(GF(p), e),
		    p, e, weights, p^e - 1);
	    if good eq p^e - 1 then
		return Fails(true);
	    end if;
	    conj := s^good;
	    pow := one;

	    auto := function(bbg, x, pow, conj)
		return x^conj;
	    end function;
	end if;
    end if;

    // now re-order according to auto

    newT := [Generic(Parent(one))|one, t];
    newT := [Generic(Parent(one))|i le 2 select newT[i]
		    else auto(bbg, Self(i-1), pow, conj): i in [1 .. p^e]];
    Tgamma := [Generic(Parent(one))|x^j: x in newT];

    // shift Tgamma so that the first nontriv. element is mapped to
    // [[1,1],[0,1]]
    // what we do below is to compute the label of the point alpha^Tgamma[2]
    // and replace Tgamma[2] by an element of its transvection group
    u := newT[2]^Tgamma[2];
    uinv := u^-1;
    if not exists(i){i: i in [2 .. p^e] | tg2^nti eq uinv * tg2^nti * u
	    where tg2 is Tgamma[2] where nti is newT[i] } then
	return Fails(true);
    end if;

    if i gt 2 then
	Tgamma := [Generic(Parent(one))|one] cat Tgamma[i .. p^e] cat 
		    Tgamma[2 .. i - 1];
    end if;

    return rec<SLdata | trangp := newT, trangpgamma := Tgamma>;
end function;

/////////////////////////////////////////////////////////////////////////////
//
//F SLSprog( <data>, <dim> )
//
// The output is a straight-line program to an element which
// is almost the identity matrix of dimension d, but
// upper left corner = rho^(-1), lower right corner = rho

function SLSprog(data, d)
// Inform("SLSprog");

    p := data`prime;
    e := data`power;
    K := GF(p^e); w := K.1;
    rho := PrimitiveElement(K);
    coeff1 := data`FB[Log(rho, rho) + 1];
    coeff2 := data`FB[Log(rho, -rho^-1) + 1];
    SG := data`slpgrp;
    slp := Id(SG);

    for i in [1 .. e] do
	slp *:= SG.((d - 1) * (d - 2) * e + i) ^ coeff1[i];
    end for;
    t1 := slp;
	// so far [[1,0], [rho,1]]
    for i in [1 .. e] do
	slp *:= SG.((d - 1) * (d - 1) * e + i) ^ coeff2[i];
    end for;
	// so far [[1,-rho^-1], [rho,0]]
    slp *:= t1;
	// so far [[0,-rho^-1], [rho,0]]
    t2 := SG.((d - 1) * (d - 2) * e + 1)^-1;
    slp *:= t2;
	// so far [[rho^-1,-rho^-1], [rho,0]]
    slp *:= SG.((d - 1) * (d - 1) * e + 1);
	// so far [[rho^-1,0], [rho,rho]]
    slp *:= t2;
	// so far [[rho^-1,0], [0,rho]]
    return slp;
end function;

////////////////////////////////////////////////////////////////////////////
//
//F EqualPoints( <bbgroup> , <x> , <y> , <Qalpha> )
//
// The most commonly used application of this routine will be to decide
// whether $Q(alpha)^x=Q(alpha)^y$, but it can also be used to determine
// whether or not an element of G normalizes Q. Note that this test can
// be used in any dimension without specification; d=|Qalpha|+1.

function EqualPoints(bbg, x, y, Qalpha)
// Inform("EqualPoints");

    return forall{q: q in Qalpha | (g, yinv * q * y) eq one}
	where g is Qalpha[1]^x where yinv is y^-1 where one is One(bbg);
end function;

////////////////////////////////////////////////////////////////////////////
//
//F IsOnAxis( <bbgroup> , <x> , <Qalpha> , <Q> )
//
// Tests whether the `point' $Q(alpha)^x$ `is on' the hyperplane $Q$.

function IsOnAxis(bbg, x, Qalpha, Q)
// Inform("IsOnAxis");

    return forall{q: q in Q | (g, q, q) eq one}
	where g is Qalpha[1]^x where one is One(bbg);
end function;

///////////////////////////////////////////////////////////////////////////
//
//F IsInQ( <bbgroup> , <x> , <Q> )
//
// This is a simple test to see if a given element is in Q. It can also be
// used to test whether such is in a conjugate of Qa if needed.

function IsInQ(bbg, x, Q)
// Inform("IsInQ");

    return CommutesWith(bbg, Q, x);
end function;

////////////////////////////////////////////////////////////////////////////
//
//F SLConjInQ( <bbg>, <y>, <Qgamma>, <Q>, <Tgamma>, <T>, <something>, <p>, <e> )
//
// Finds an element of Q conjugating $Q(gamma)$ to $Q(gamma)^y$ whenever
// these points are not on Q.
// Qgamma and Q are given by GF(q)-bases
// <something> is the concatenation of GF(p)-bases of the transvection
// groups in Q (if we are in 3.3, and no nice basis yet) or the conjugating
// element c (if we are after 3.4)
// we consider only the case conjugating Q(gamma) to somewhere

function SLConjInQ(bbg, y, Qgamma, Q, Tgamma, T, j, p, e)
// Inform("SLConjInQ");

    // handle trivial case
    one := One(bbg);
    if EqualPoints(bbg, one, y, Qgamma) then
	return one;
    end if;

    len := #Q;
    lengamma := #Qgamma;
    q := p^e;
    a0 := Qgamma[1];

    if not EqualPoints(bbg, y, y * a0, Qgamma) then

	IsOK := function(z)
	    if IsInQ(bbg, z, Q) then
		b := Qgamma[2]^y;
		if exists(z){z: k in [1..q] |
			EqualPoints(bbg, one, z, Q)
			where z is b^Tgamma[k] } then
		    return true, z;
		end if;
		return false, 0;
	    end if;
	    return true, z;
	end function;

	b := Qgamma[1]^y;
	if not exists(z){zz: i in [1 .. q] |
		EqualPoints(bbg, one, z, Q) and f
		where f, zz is IsOK(z)
		where z is b^Tgamma[i] } then
	    return Fails(true);
	end if;

    else
	if not exists(c){c: i in [1 .. lengamma] | c ne one
		where c is (a0, Qgamma[i]^y) } then
	    return Fails(true);
	end if;

	if not exists(z){z: i in [1 .. q] | EqualPoints(bbg, one, z, Q)
		where z is c * Tgamma[i] } then
	    return Fails(true);
	end if;
    end if;

    if not exists(i){i + 1: i in [1 .. len] | (Q[i], z) ne one} then
	return Fails(true);
    end if;

    U := {@ one @};
    if Type(j) eq SeqEnum then
	// we are at the construction of L
	for k in [e * (i - 2) + 1 .. e * (i - 1)] do
	    AppendTran(bbg, ~U, j[k], p);
	end for;
    else
	// j is a conjugating element
	jj := j^(i - 2);
	for k in [2 .. e + 1] do
	    AppendTran(bbg, ~U, T[k]^jj, p);
	end for;
    end if;

    // in any case, U is the listing of the trans group in Q not commuting
    // with z

    if not exists(u){u: i in [1 .. q] | EqualPoints(bbg, u, y, Qgamma)
	    where u is (U[i], z) } then
	return Fails(true);
    end if;
    return u;
end function;

////////////////////////////////////////////////////////////////////////////
//F SLLinearCombQ(<trangp>, <transv>, <c>, <dim>, <w>)
// <trangp> is the listed transvection group in <Q>
// t21, c as in section 3.4.1
// <w> is the vector to decompose
// to apply the routine in Qgamma, we need the inverse transpose of <transv>

function SLLinearCombQ(T, t21, c, d, w)
// Inform("SLLinearCombQ");

    cinv := c^-1;
    q := #T;
    K := GF(q);
    rho := PrimitiveElement(K);
    wconj := w;
    copyw := w;
    cpower := c;
    vec := [K | ];
    for i in [2 .. d - 1] do
	coord := (wconj, t21);
	k := Position(T, coord);
	if k eq 0 then
	    return Fails(true);
	end if;
	vec[i] := k eq 1 select 0 else rho^(k - 2);

	// divide out component just found and get next component into position
	wconj *:= cinv * coord^-1 * c;
	wconj := c * wconj * cinv;
	copyw *:= (coord^cpower)^-1;
	cpower *:= c;
    end for;

    // find the coordinate of the first component
    wconj := c * wconj * cinv;	// something pointless seems to be happening
    k := Position(T, copyw);
    if k eq 0 then
	return Fails(true);
    end if;
    vec[1] := k eq 1 select 0 else rho^(k - 2);
    return vec;
end function;

/////////////////////////////////////////////////////////////////////////
//
//F SLSLP ( <data structure for bbg>, <bbg element or matrix>, <dimension> )
//
// writes a straight-line program reaching the given element from the
// generators in the data structure

//1/09/04 - Derek Holt added extra parameter xismat, to avoid problem when
//the bbg element happens to be a matrix
function SLSLP(data, x, d, xismat)
// Inform("SLSLP");

    p := data`prime;
    e := data`power;
    q := p^e;
    K := GF(q);
    w := PrimitiveElement(K);
    FB := data`FB;
    gens := data`gens;
    bbg := data`bbg;
    SG := data`slpgrp;
    one := One(bbg);

    //if ISA(Type(x), Mtrx) then
    if xismat then
	if not Determinant(x) eq 1 then
	    return Fails(true);
	end if;
	leftslp := Id(SG);
	rightslp := Id(SG);
	// in leftslp, we collect an slp for the INVERSE of the matrix
	// 	we multiply with from the left
	// in leftslp, we collect an slp for the right multiplier matrix
	W := Matrix(x);
	for i in [0 .. d - 2] do
	    // put non-zero element in lower right corner
	    if W[d - i][d - i] eq 0 then
		j := rep{a: a in [1 .. d - i] | not W[a][d - i] eq 0};
		leftslp *:= SG.((d-i-1) * (d-i-2) * e + (j-1) * e + 1);
		for k in [1 .. d - i] do
		    W[d - i][k] := W[d - i][k] - W[j][k];
		end for;
	    end if;
	    // clear last column
	    for j in [1 .. d - i - 1] do
		if not W[j][d - i] eq 0 then
		    // a is the nontriv element of the multiplying matrix
		    a := -W[j][d - i] / W[d - i][d - i];
		    // b is what we have to express as a linear combination
		    //     in the standard basis of GF(q)
		    b := -a;
		    coeffs := FB[Log(w, b) + 1];
		    for k in [1 .. e] do
			leftslp *:= SG.((d-i-1)^2*e+(j-1)*e+k) ^ coeffs[k];
		    end for;
		    for k in [1 .. d - i] do
			W[j][k] := W[j][k] + a * W[d - i][k];
		    end for;
		end if;
	    end for;
	    // clear last row
	    for j in [1 .. d - i - 1] do
		if not W[d - i][j] eq 0 then
		    // a is the nontriv element of the multiplying matrix
		    a := -W[d - i][j] / W[d - i][d - i];
		    // no inverse is taken here
		    coeffs := FB[Log(w, a) + 1];
		    for k in [1 .. e] do
			rightslp *:= SG.((d-i-1)*(d-i-2)*e+(j-1)*e+k)^coeffs[k];
		    end for;
		    for k in [1 .. d - i] do
			W[k][j] +:= a * W[k][d - i];
		    end for;
		end if;
	    end for;
	end for;
	// now we have a diagonal matrix
	for i in [0 .. d - 2] do
	    if not W[d - i][d - i] eq 0 then
		k := Log(w, W[d - i][d - i]);
		sprog := data`sprog[d - i] ^ k;
		leftslp *:= sprog;
	    end if;
	end for;
	rightslp := rightslp ^ -1;
	return leftslp * rightslp;
    else	// we have a bbg element
	rightslp := Id(SG);
	xinv := x^-1;
	Q := [gens[(d-1)*(d-2)*e + (j-1)*e + 1][1]: j in [1 .. d - 1]];
	Qgamma := [gens[(d-1)^2*e + (j-1)*e + 1][1]: j in [1 .. d - 1]];

	// first modify x to normalize Q
	if forall{j: j in Q | IsInQ(bbg, xinv * j * x, Q)} then
	    W := x;
	else
	    if exists(i){i: i in [1 .. d - 1] |
		    not IsOnAxis(bbg, Q[i]^-1 * xinv, Qgamma, Q) } then
		rightslp := SG.((d-1)*(d-2)*e + (i-1)*e + 1);
		u := Q[i];
	    elif not IsOnAxis(bbg, xinv, Qgamma, Q) then
		u := one;
	    else
		return Fails(true);
	    end if;

	    // y will be in <Qgamma>, conjugating Q to Q^(x*u)
	    // we apply SLConjInQ for the dual situation
	    if d gt 2 then
		y := SLConjInQ(bbg, x * u, Q, Qgamma, data`trangp[d - 1],
		    data`trangpgamma[d - 1], data`c[d - 1], p, e);
		if y cmpeq "fails" then
		    return Fails(false);
		end if;
	    else
		if not exists(y){y: k in [1 .. q] | EqualPoints(bbg, y, x*u, Q)
			where y is data`trangpgamma[1][k] } then
		    return Fails(true);
		end if;
	    end if;

	    // x * u * y^-1 normalizes Q
	    vec := SLLinearCombQ(data`trangpgamma[d - 1], data`t21invtran,
		data`c[d - 1], d, y^-1);
	    if vec cmpeq "fails" then
		return Fails(false);
	    end if;
	    for j in [1 .. d - 1] do
		if not (vec[j] eq 0) then
		    coeffs := FB[Log(w, vec[j]) + 1];
		    for k in [1 .. e] do
			rightslp *:= SG.((d-1)^2*e + (j-1)*e + k) ^ coeffs[k];
		    end for;
		end if;
	    end for;
	    W := x * u * y^-1;
	end if;

	// compute the matrix for the action of W on Q
	mat := [];
	for j in [1 .. d - 1] do
	    vec := SLLinearCombQ(data`trangp[d - 1], data`t21,
				data`c[d - 1], d, Q[j]^W);
	    if vec cmpeq "fails" then
		return Fails(false);
	    end if;
	    Append(~mat, vec);
	end for;

	mat := Matrix(mat);
	det := Determinant(mat);
	if not (det eq 1) then
	    gcd := GCD(d, q - 1);
	    exp := Solution(d div gcd, Log(w, det) div gcd, (q - 1) div gcd);
	    slprog := data`sprog[d] ^ exp;
	    rightslp *:= slprog;
	    W *:= EvaluateBBGp(bbg, gens, slprog);
	    smat := w^-exp * IdentityMatrix(K, d - 1);
	    smat[1][1] := w^(-2*exp);
	    mat *:= smat;
	end if;
	if d gt 2 then
	    slp := SLSLP(data, mat^-1, d - 1, true);
	    if slp cmpeq "fails" then
		return Fails(false);
	    end if;
	    rightslp *:= slp;
	    W *:= EvaluateBBGp(bbg, gens, slp);
	end if;

	// now W acts trivially on Q
	W2 := W^-q;
	if W2 ne one then
	    cent := data`centre;
	    gcd := GCD(q - 1, d);
	    if gcd eq 1 then
                return Fails(false);
            end if;
	    //assert gcd gt 1;
	    i := 1;
	    stop := false;
	    repeat
		if W2 eq cent then
		    stop := true;
		else
		    i +:= 1;
		    cent *:= data`centre;
		end if;
	    until stop or i eq gcd;
	    if not stop then
		return Fails(true);
	    end if;
	    centprog := data`centreprog ^ i;
	    rightslp *:= centprog;
	    W *:= W2;
	end if;

	// now W is in Q
	vec := SLLinearCombQ(data`trangp[d-1], data`t21, data`c[d-1], d, W^-1);
	if vec cmpeq "fails" then
	    return Fails(false);
	end if;
	for j in [1 .. d - 1] do
	    if not vec[j] eq 0 then
		coeffs := FB[Log(w, vec[j]) + 1];
		for k in [1 .. e] do
		    rightslp *:= SG.((d-1)*(d-2)*e + (j-1)*e + k) ^ coeffs[k];
		end for;
	    end if;
	end for;
	rightslp := rightslp ^ -1;
	return rightslp;
    end if;
end function;

//////////////////////////////////////////////////////////////////////////////
//
//F SL2DataStructure( <bbg>, <bbrand>, <prime>, <power> )
///	optional parameters: TranGroup := <transv.grp>, Gen := <gen>
//
// We now want to group these subroutines together in order to get the
// permutation domain of $G$ acting on 1-spaces. This information alone will
// allow us to compute the matrix image of an $x$ in bbg.

function SL2DataStructure(bbg, bbrand, p, e:
    TranGroup := "compute", Gen := "compute", Transvection := "compute")

    one := One(bbg);
    if TranGroup cmpeq "compute" then
	if Transvection cmpne "compute" then
	    assert Gen cmpne "compute";
	    data1 := rec<SLdata | tran := Transvection, gen := Gen>;
	else
	    assert Gen cmpeq "compute";

	    data1 := SL2Search(bbg, bbrand, p, e);
	    if data1 cmpeq "fails" then
		return Fails(false);
	    end if;
	end if;

	t := data1`tran;
	s1 := data1`gen;

	T := ConstructTranGroup(bbg, bbrand, t, p, e);
	if T cmpeq "fails" then
	    return Fails(false);
	end if;

	j1 := Dislodge(bbg, T);
	if j1 cmpeq "fails" then
	    return Fails(false);
	end if;
    else
	assert Gen cmpne "compute";

	T := TranGroup;
	j1 := Gen;
	if p^e gt 3 then
	    data1 := SL2Search(bbg, bbrand, p, e: Transvection := T[2]);
	    if data1 cmpeq "fails" then
		return Fails(false);
	    end if;
	    s1 := data1`gen;
	else
	    s1 := one;
	end if;
	t := T[2];
    end if;

    data2 := Standardize(bbg, T, j1, s1);
    if data2 cmpeq "fails" then
	return Fails(false);
    end if;

    j := data2`conj;
    s := data2`gen;

    data3 := SL2ReOrder(bbg, T, s, j, p, e);
    if data3 cmpeq "fails" then
	return Fails(false);
    end if;

    data := rec< SLdata | >;
    data`bbg := bbg;
    data`prime := p;
    data`power := e;

    K := GF(p^e); w := K.1;
    rho := PrimitiveElement(K);
    data`gens := [<data3`trangp[i+1], [<2, 1, rho^(i - 1)>]>: i in [1 .. e]]
	cat [<data3`trangpgamma[i+1], [<1, 2, rho^(i - 1)>]>: i in [1 .. e]];
    data`slpgrp := SLPGroup(2 * e);
    SG := data`slpgrp;

    _, phi := VectorSpace(K, PrimeField(K), [rho^(x - 1): x in [1 .. e]]);
    data`FB := [[Z | x: x in Eltseq(phi(rho^(i-1)))]: i in [1 .. p^e - 1]]
	where Z is Integers();

    data`sprog := [];
    data`sprog[2] := SLSprog(data, 2);
    data`trangp := [];
    data`trangp[1] := data3`trangp;
    data`trangpgamma := [];
    data`trangpgamma[1] := data3`trangpgamma;

    if p eq 2 then
	data`centre := one;
	data`centreprog := Id(SG);
    else
	cslp := data`sprog[2] ^ ((p^e - 1) div 2);
	data`centre := EvaluateBBGp(bbg, data`gens, cslp);
	if data`centre eq one then
	    data`centreprog := Id(SG);
	else
	    data`centreprog := cslp;
	end if;
    end if;

    // the following components will be used in recursion
    data`c := [* *];
    data`c[1] := one;
    data`cprog := [];
    data`cprog[1] := Id(SG);
    data`cprog[2] := t1 * SG.(e + 1) * t1 where t1 is SG.1^-1;
    data`c[2] := data`gens[1][1]^-1 * data`gens[e+1][1] * data`gens[1][1]^-1;
    data`t21 := data`gens[1][1];
    data`t21invtran := data`t21^data`c[2];

    // in section 3.4.2, we need the inverse of the s computed here
    // that's why it is called sinv
    data`sinv := EvaluateBBGp(bbg, data`gens, data`sprog[2]);
	
    return data;
end function;
///////////////////////////////////////////////////////////////////////////////
//
//F SL3ConstructQ( <bbgroup> , <bbrand>, <t> , <prime> , <power> )
//
// Now that we have a transvection, we wish to construct the group $Q$ of all
// transvections having the same centre or axis as $t$. In fact, we will be
// assuming that $Q$ is the latter. The output will consist of a record
// whose fields are
//     <tran> and <tran1> - GF(p) bases for two tran gps spanning $Q$
//           <conj>       - an elt of bbg interchanging the tran gps of $Q$
//
// Added random process for bbgroup, called bbrand. Use Random(bbrand)  
// instead of Random(bbg). billu 1/9/03

function SL3ConstructQ(bbg, bbrand, t, pp, e)
// Inform("SL3ConstructQ");

    one := One(bbg);
    tinv := t^-1;
    S := [t];
    T1 := {@ one @};
    /* from QuickSL3DataStructure, we call with the value pp=-p, to distinguish
       from the genuine input case. Reason: with reasonable probability,
       QuickSL may have incorrect input, and we don't want to waste time here
       to construct the non-existing T1. The tighter limit still has >96%
       probability for success, if the input is correct.  */
    if pp lt 0 then
	p := -pp;
	m := Floor((p^e+1) * (p^e2 + p^e + 1) * 4 * e * p / ((p-1) * 2 * p^e2))
	    where e2 is 2 * e;
    else
	p := pp;
	m := 8 * p^e * e;
    end if;

    i := 1;
    repeat
	r := Random(bbrand);
	u := t^r;
	cand := tinv * u^-1 * t * u;
	if cand ne one and CommutesWith(bbg, S, cand) then
	    if #S eq 1 then
		f := r;
		u1 := u;
		t1 := u1^-1 * tinv * u1 * t;
		AppendTran(bbg, ~T1, t1, p);
		Append(~S, t1);
	    else
		t1new := (u1, cand);
		if not IsInTranGroup(bbg, T1, t1new) then
		    AppendTran(bbg, ~T1, t1new, p);
		end if;
	    end if;
	end if;
	i +:= 1;
    until #T1 eq p^e or i eq m;
    if #T1 lt p^e then
	return Fails(true);
    end if;

    out := rec<SLdata | tran := t, trangp1 := T1, conj := f>;
    return out;
end function;

// So we now have a listing of T1, bases B and B1 for the tran groups T and T1,
// and the element f = conj.
//
//       $Q$                  <-------->              < B , B1 >
//   $Q(alpha)$               <-------->         < B , B1^(f^(-1)) >
// $Q(beta)$ = $Q(alpha)^f$   <-------->            < B^f , B1 >
//      $L$                   <-------->        < B^f , B1^(f^(-1)) >
//
// We now want to regard $L$ as a black box group in its own right, and make
// a recursive call to dimension 2. Note we don't need to compute everything
// in the data structure here, since we already have $t1$ so we don't need to
// compute a transvection. We don't have $s$, and we don't have $j$, but we do
// have the effect of conjugation by $j$, since we have B^f. Also, we have
// a complete listing of $T1^(f^(-1))$, which will be the eventual primary
// transvection group, so we don't need `ConstructTranGroup'. So we need to use
// a shortcut `SL2Search' to find $s$, we need `Standardize' and we need the
// full `SL2Reorder'.
// The truncated call to SL2DataStructure will take as input the (listed)
// principal transvection group (which will be T1^(f^(-1)), together with a
// tran of L not in T1^(f^(-1)) (this will be t^f)
/////////////////////////////////////////////////////////////////////////////
//
//F LDataStructure( <bbg> , <prime> , <power> , <trangp> , <t> )
//
// Here L = < T1^(f^(-1)) , t^f > is an SL(2,q).
// The output will be a reordered T, together with bases (with their matrix
// images) of T and T^j. We will also have straightline line programs to $s$
// normalizing T and T^j of order q-1 and to $j$.
// <trangp> will actually be T1^(f^(-1)), and <t> will be t^f.

function LDataStructure(bbg, p, e, T, x)
// Inform("LDataStructure");

    gens := [T[p ^ (y - 1) + 1]: y in [1 .. e]] cat [x];
    lbbg := sub<bbg | gens>;
    RPlbbg  := RandomProcess(lbbg);
    return SL2DataStructure(lbbg, RPlbbg, p, e: TranGroup := T, Gen := x);
end function;

//////////////////////////////////////////////////////////////////////////
//
//F ComputeGamma( <bbgroup> , <f> , <Q> , <trangp> )
//
// Note. This construction will only be used in dimension 3.
// Q, Qalpha are given by GF(q)-generators, trangp is listed,
// f is in the paper, section 3.6.3
// We construct an element 'test' which conjugates alpha to gamma.
// At this stage, we do not need a transvection to do the job.

function ComputeGamma(bbg, f, Q, T)
// Inform("ComputeGamma");

    one := One(bbg);
    t := T[2];
    u1 := Q[1]^f;
    u2 := Q[2]^f;
    finv := f^-1;
    if exists(test){test: t1 in T | (u1, t^test, u1) eq one and
	    (u2, t^test, u2) eq one where test is finv * t1 } then
	return test;
    end if;
    return Fails(true);
end function;

////////////////////////////////////////////////////////////////////////////
//
//F SLConstructBasisQ( <bbg>, <data>, <Q>, <Qgamma>, <dim>, <field size> )
//
// <data> is the data structure of L to construct straight-line programs

function SLConstructBasisQ(bbg, data, Q, Qgamma, d, q)
// Inform("SLConstructBasisQ");

    t21 := data`t21;
    t21invtran := data`t21invtran;
    sinv := data`sinv;
    s := sinv^-1;
    c := data`c[d - 1];
    one := One(bbg);
    GPone := Generic(Parent(one));
    
    // find a nontrivial element of the first transvection group of Q
    if not exists(b1){b1: q in Q | b1 ne one
	    where b1 is (q, t21)} then
	return Fails(true);
    end if;

    // find a nontrivial element of the first transvection group of Qgamma
    if not exists(b1prime){b1prime: q in Qgamma | b1prime ne one
	    where b1prime is (q, t21invtran)} then
	return Fails(true);
    end if;

    // list the transvection groups and bases
    T := [GPone|one, b1];
    T := [GPone|i le 2 select T[i] else sinv * Self(i-1) * s: i in [1 .. q]];
    Tgamma := [GPone|one, b1prime];
    Tgamma := [GPone|i le 2 select Tgamma[i] else s * Self(i-1) * sinv: i in [1..q]];
    baseQ := [GPone|i eq 1 select b1 else Self(i - 1) ^ c: i in [1 .. d-1]];
    baseQgamma := [GPone|i eq 1 select b1prime else Self(i-1) ^ c: i in [1 .. d-1]];

    return rec<SLdata | trangpQ := T, baseQ := baseQ, baseQgamma := baseQgamma,
	trangpQgamma := Tgamma, conj := c, lincombQ := t21,
	lincombQgamma := t21invtran>;
end function;

//////////////////////////////////////////////////////////////////////////
//
//F SLLabelPoint( <bbg> , <h> , <basisrecord> , <prime> , <power> , <dim> )
//
// Given a group element <h> we wish to label the `point' corresponding to
// the group <Qgamma>^<h>, given the required info.
// <basisrecord> is the output of SLConstructBasisQ

function SLLabelPoint(bbg, h, data, p, e, d)
// Inform("SLLabelPoint");

    K := GF(p^e);
    rho := PrimitiveElement(K);
    Q := data`baseQ;
    Qgamma := data`baseQgamma;
    T := data`trangpQ;
    Tgamma := data`trangpQgamma;
    c := data`conj;
    t21 := data`lincombQ;

    if EqualPoints(bbg, One(bbg), h, Qgamma) then
	vec := [K | 0: i in [1 .. d - 1]] cat [K | 1];
    elif not IsOnAxis(bbg, h, Qgamma, Q) then
	w := SLConjInQ(bbg, h, Qgamma, Q, Tgamma, T, c, p, e);
	if w cmpeq "fails" then
	    return Fails(false);
	end if;
	vec := SLLinearCombQ(T, t21, c, d, w);
	if vec cmpeq "fails" then
	    return Fails(false);
	end if;
	vec[d] := K!1;
    else
	IsOK := function(a)
	    w := (a, q1);
	    if w ne one then
		return true, w;
	    end if;
	    w := (a, q2);
	    if w ne one then
		return true, w;
	    end if;
	    return false, 0;
	end function where q1 is Q[1] where q2 is Q[2] where one is One(bbg);

	if not exists(w){w: i in [1 .. d - 1] | f where f, w is IsOK(a)
		where a is Qgamma[i]^h } then
	    return Fails(true);
	end if;
	vec := SLLinearCombQ(T, t21, c, d, w);
	if vec cmpeq "fails" then
	    return Fails(false);
	end if;
	vec[d] := K!0;
    end if;
    return vec;
end function;

//////////////////////////////////////////////////////////////////////////
//
//F SLConstructGammaTransv( <bbgrp>, <transv grp>, <point> )
//
// Given the transvection group T and and a basis for Q(gamma)
// find a transvection conjugating T into Q(gamma)

function SLConstructGammaTransv(bbg, T, Qgamma)
// Inform("SLConstructGammaTransv");

    one := One(bbg);
    qg1 := Qgamma[1];
    t2 := T[2];
    // T^Qgamma[1] has an element conjugating alpha to gamma
    if not exists(jgamma){x: i in [2 .. #T] |
	    EqualPoints(bbg, t2^x, one, Qgamma)
	    where x is t^qg1 where t is T[i] } then
	return Fails(true);
    end if;
    return jgamma;
end function;

///////////////////////////////////////////////////////////////////////////
//
//F SLExchangeL(<data>, <GF(q) basis>, <GF(q) basis>, <GF(p) basis>, <dim> )
//
// After recursion, we have to choose between Llambda and its inverse
// transpose. In fact, we shall exchange Q and Qgamma

function SLExchangeL(data, Q, Qgamma, pQ, d)
// Inform("SLExchangeL");

    bbg := data`bbg;
    t21 := data`t21;
    t21invtran := data`t21invtran;
    p := data`prime;
    e := data`power;
    q := p^e;
    one := One(bbg);

    // find a non-trivial element of the first transvection group of Q
    if not exists(i){i: i in [1 .. #Q] | (Q[i], t21) ne one } then
	return Fails(true);
    end if;

    // construct the transvection subgroup of Q containing b1
    j := 1;
    trangp := {@ Generic(Parent(one))| one @};
    repeat
	comm := (pQ[(i - 1) * e + j], t21);
	if not IsInTranGroup(bbg, trangp, comm) then
	    AppendTran(bbg, ~trangp, comm, p);
	end if;
	j +:= 1;
    until #trangp eq q or j gt e;
    if #trangp lt q then
	return Fails(true);
    end if;

    t31 := data`gens[2 * e + 1][1];
    if not forall{x: x in Q | IsInTranGroup(bbg, trangp, (x, t31))}
    then
	temp := Q;
	Q := Qgamma;
	Qgamma := temp;
    end if;
    return [Q, Qgamma];
end function;

/////////////////////////////////////////////////////////////////////////
//
//F AttachSLNewgens( <SLdatastr>, <basisrecord>, <dim>, <jgamma> )
//
// Attaches (bboxgenerator,matrix) pairs to the list obtained from
// recursion. No output, only the side effect on the input generator list.
// <SLdatastr> is the record of SL, <basisrecord> is the output of
// SLConstructBasisQ

procedure AttachSLNewgens(~data, ~data3, d, jgamma)
// Inform("AttachSLNewgens");

    e := data`power;
    K := GF(data`prime^e);
    rho := PrimitiveElement(K);
    one := One(data`bbg);
    conj := one;
    vec := SLLabelPoint(data`bbg, jgamma^-1 * data3`trangpQgamma[2],
			data3, data`prime, e, d);
    if vec cmpeq "fails" or vec[1] eq 0 then
	return;
    end if;
    a := Log(rho, vec[1]);
    if a gt 0 then
	newTgamma := [one] cat data3`trangpQgamma[a + 2 .. data`prime^e] cat
	    data3`trangpQgamma[2 .. a + 1];
	data3`trangpQgamma := newTgamma;
    end if;

    error if #data`gens ne (d - 1) * (d - 2) * e,
	"gens length error: ", #data`gens, d, e, (d - 1) * (d - 2) * e;
    newgensA := [];
    newgensB := [];
    for j in [1 .. d - 1] do
	newgensA cat:= [
	    <data3`trangpQ[i + 1]^conj, [<d, j, rho^(i - 1)>] >: i in [1 .. e]
	];
	newgensB cat:= [
	    < data3`trangpQgamma[i + 1]^conj, [<j, d, rho^(i - 1)>] >:
	    i in [1 .. e]
	];
	conj *:= data`c[d - 1];
    end for;
    data`gens cat:= newgensA cat newgensB;
    assert #data`gens eq d * (d - 1) * e;

    oldSG := data`slpgrp;
    SG := SLPGroup(d * (d - 1) * e);

    // update all the straight-line programs in data ...
    //     (sprog[i], cprog[i], centreprog)
    phi := hom<oldSG -> SG | [SG.i: i in [1 .. Ngens(oldSG)]]>;
    sprog := [];
    for i in [1 .. #data`sprog] do
	if IsDefined(data`sprog, i) then
	    sprog[i] := phi(data`sprog[i]);
	end if;
    end for;
    data`sprog := sprog;
    cprog := [];
    for i in [1 .. #data`cprog] do
	if IsDefined(data`cprog, i) then
	    cprog[i] := phi(data`cprog[i]);
	end if;
    end for;
    data`cprog := cprog;
    data`centreprog := phi(data`centreprog);
    data`slpgrp := SG;
end procedure;

///////////////////////////////////////////////////////////////////////////
//
//F SLFinishConstruction( <bbgroup>, <data>, <basisrecord>, <dim> )
//
// last steps of the SL data structure construction
// <data> is the data structure already constructed,
// <basisrecord> is the output of SLConstructBasisQ

function SLFinishConstruction(bbg, data2, data3, d)
// Inform("SLFinishConstruction");

    p := data2`prime;
    e := data2`power;
    q := p^e;
    K := GF(q);
    w := PrimitiveElement(K);

    // we construct a transvection for jgamma
    jgamma := SLConstructGammaTransv(bbg, data3`trangpQ, data3`baseQgamma);
    if jgamma cmpeq "fails" then
	return Fails(false);
    end if;

    AttachSLNewgens(~data2, ~data3, d, jgamma);
    if #data2`gens lt d * (d - 1) * e then
	return Fails(true);
    end if;

    data2`bbg := bbg;
    data2`sprog[d] := SLSprog(data2, d);
    mat := IdentityMatrix(K, d);
    mat[1][1] := 0;
    mat[d][d] := 0;
    mat[1][d] := (-1)^d;
    mat[d][1] := (-1)^(d - 1);
    cprog := SLSLP(data2, mat, d, true);
    data2`cprog[d] := data2`cprog[d - 1] * cprog;
    data2`c[d] := data2`c[d - 1] * EvaluateBBGp(bbg, data2`gens, cprog);
    AdjustSeqenceUniverse(~data2`trangp, data3`trangpQ);
    AdjustSeqenceUniverse(~data2`trangpgamma, data3`trangpQgamma);
    data2`trangp[d - 1] := data3`trangpQ;
    data2`trangpgamma[d - 1] := data3`trangpQgamma;

    gcd := GCD(q - 1, d);
    if gcd eq 1 then
	data2`centre := One(bbg);
	data2`centreprog := One(data2`slpgrp);
    else
	centgen := w^((q - 1) div gcd) * IdentityMatrix(K, d);
	centslp := SLSLP(data2, centgen, d, true);
	data2`centre := EvaluateBBGp(bbg, data2`gens, centslp);
	if data2`centre eq One(bbg) then
	    data2`centreprog := One(data2`slpgrp);
	else
	    data2`centreprog := centslp;
	end if;
    end if;
    return data2;
end function;

//////////////////////////////////////////////////////////////////////////
//
//F SL3DataStructure( <bbgroup> , <bbrand>, <prime> , <power> )
//
// Gather together all of the necessary information.

function SL3DataStructure(bbg, bbrand, p, e)
// Inform("SL3DataStructure");

    K := GF(p^e);
    rho := PrimitiveElement(K);
    r := FindGoodElement(bbg, bbrand, p, e, 3, 14 * p^e);
    if r cmpeq "fails" then
	/* print "FindGoodElement could not find r"; */
	return Fails(false);
    end if;

    t := r ^ (p^e - 1);

    data1 := SL3ConstructQ(bbg, bbrand, t, p, e);
    if data1 cmpeq "fails" then
	return Fails(false);
    end if;
    T1 := data1`trangp1;
    // T1 was listed by AppendTran => generators in positions p^i + 1
    t1 := T1[2];
    t1inv := t1^-1;
    f := data1`conj;
    finv := f^-1;
    T1finv := [f * x * finv: x in T1];
    T := [x^-1 * t1inv * x * t1: x in T1finv];
    jgamma := ComputeGamma(bbg, f, [t, t1], T);
    if jgamma cmpeq "fails" then
	return Fails(false);
    end if;

    data2 := LDataStructure(bbg, p, e, T1finv, t^f);
    if data2 cmpeq "fails" then
	return Fails(false);
    end if;
    Qgamma := [x, x^data2`c[2]] where x is t^jgamma;

    data3 := SLConstructBasisQ(bbg, data2, [t, t1], Qgamma, 3, p^e);

    data2 := SLFinishConstruction(bbg, data2, data3, 3);
    return data2;

end function;

//////////////////////////////////////////////////////////////////////////
//
//F QuickSL3DataStructure( <bbgroup> , <bbrand>, <prime> , <power> )
//
// info needed in section 3.2.2

function QuickSL3DataStructure(bbg, bbrand, p, e)
// Inform("QuickSL3DataStructure");

    t := bbg.1;
    data1 := SL3ConstructQ(bbg, bbrand, t, -p, e);
    // We call SL3ConstructQ with a negative value so that routine knows
    // that the call is from here and not from SL3DataStructure
    if data1 cmpeq "fails" then
	return Fails(false);
    end if;

    T1 := data1`trangp1;
    // T1 was listed by AppendTran => generators in positions p^i + 1
    t1 := T1[2];
    t1inv := t1^-1;
    f := data1`conj;
    finv := f^-1;
    T1finv := [f * x * finv: x in T1];
    T := [x^-1 * t1inv * x * t1: x in T1finv];
    jgamma := ComputeGamma(bbg, f, [bbg | t, t1], T);
    if jgamma cmpeq "fails" then
	return Fails(false);
    end if;

    B := [T[p^(x - 1) + 1]: x in [1 .. e]];
    B1 := [T1[p^(x - 1) + 1]: x in [1 .. e]];
    B1finv := [T1finv[p^(x - 1) + 1]: x in [1 .. e]];

    return rec<SLdata | T := T, T1 := T1, B := B, B1 := B1, B1finv := B1finv,
			jgamma := jgamma, Lgen := B[1]^f>;
end function;

///////////////////////////////////////////////////////////////////////////
// SLFindGenerators(<bbg>,<J data str.>,<random elmt>,<prime>,<power>,<dim>)
//
// given J as in sec. 3.2.2, we create generators for L, Q, Qgamma

function SLFindGenerators(bbg, data1, r, p, e, d)
// Inform("SLFindGenerators");

    B := ChangeUniverse(data1`B, bbg);
    B1 := ChangeUniverse(data1`B1, bbg);
    B1finv := ChangeUniverse(data1`B1finv, bbg);

    q := p^e;
    tau := r^p;
    tauinv := tau^-1;
    jgamma := bbg ! data1`jgamma;
    jgammainv := jgamma^-1;
    Q := [B[1], B1[1]];
    Qgamma := [jgammainv*B[1]*jgamma, jgammainv*B1finv[1]*jgamma];
    qalpha := B1finv[1];
    pQ := B cat B1;
    pQalpha := B cat B1finv;
    Lgen := [bbg ! data1`Lgen];
    if d mod 2 eq 0 then
	limit := d - 2;
    elif q eq 2 then
	limit := d + 1;
    else
	limit := d - 1;
    end if;
    for i in [2 .. limit] do
	// *** problem here ***
	Q[i + 1] := tauinv * Q[i] * tau;
	qalpha := tauinv * qalpha * tau;
	Qgamma[i + 1] := jgammainv * qalpha * jgamma;
	Lgen[i] := Lgen[i - 1] ^ tau;
	for j in [1 .. e] do
	    Append(~pQ, tauinv * pQ[(i - 1) * e + j] * tau);
	    Append(~pQalpha, pQalpha[(i - 1) * e + j] ^ tau);
	end for;
    end for;
    // H as in 3.3.1 is generated by pQ and Lgen and pQalpha
    // LQ/Q is generated by Lgen and all but first e elements of pQalpha

    Tgamma := {@ One(bbg) @};
    for i in [1 .. e] do
	AppendTran(bbg, ~Tgamma, jgammainv * pQalpha[i] * jgamma, p);
    end for;

    for i in [e + 1 .. #pQalpha] do
	if not exists(u){u: j in [1 .. q] |
		EqualPoints(bbg, pQalpha[i], u, Qgamma)
		where u is data1`T[j] } then
	    /* print "SLFindGenerators: failed modifying L"; */
	    return Fails(true);
	end if;
	pQalpha[i] *:= u^-1;
    end for;
    for i in [1 .. #Lgen] do
	u := SLConjInQ(bbg, Lgen[i], Qgamma, Q, Tgamma, data1`T, pQ, p, e);
	if u cmpeq "fails" then
	    /* print "SLFindGenerators: failed modifying L,2";*/
	    return Fails(false);
	end if;
	Lgen[i] *:= u^-1;
    end for;

    // we conjugate the L-generators in pQalpha so that Random
    // does not get an input overwhelmingly in a small subgroup
    for i in [1 .. limit] do
	for j in [1 .. e] do
	    Append(~Lgen, pQalpha[i * e + j] ^ Lgen[i]);
	end for;
    end for;

    return rec<SLdata | Lgen := Lgen, Q := Q, Qgamma := Qgamma, pQ := pQ>;
end function;

/////////////////////////////////////////////////////////////////////////
//
//F SLDataStructure( <bbg>, <bbrand>, <prime>, <power>, <dim>
//
// Main function to compute constructive isomorphism

function SLDataStructure(bbg, bbrand, p, e, d)
// Inform("SLDataStructure");

/*
    printf "SLDataStructure(G, %o, %o, %o) where G is generated by %o gens\n",
	    p, e, d, Ngens(bbg);
    print bbg;
*/
    if d eq 2 then
	return SL2DataStructure(bbg, bbrand, p, e);
    end if;
    if d eq 3 then
	return SL3DataStructure(bbg, bbrand, p, e);
    end if;
    q := p^e;
    if d eq 4 and q in {2, 3, 5, 9, 17} then
	/*
	We cannot guarantee that the p-part of the random r is a transvection.
	The probability for that is at least 2/3, so going back to
	FindGoodElement 8 times ensures success w/ prob > 1-1/2^8, since with
	good input, we have success with prob well above 3/4.
	We work with a tighter limit on the number of triples tried, so
	we do not waste too much time in case of a bad $r$
	*/
	j := 1;
	stop := false;
	repeat
	    r := SL4FindGoodElement(bbg, bbrand, p, e, 30*q);
	    if r cmpeq "fails" then
		j +:= 1;
	    else
		i := 1;
		t := r ^ (p ^ (e * (d - 2)) - 1);
		repeat
		    u1 := t ^ Random(bbrand);
		    if not (t, u1)^p eq One(bbg) then
			u2 := t ^ Random(bbrand);
			sl3 := sub<bbg | [t, u1, u2]>;
			RPsl3 := RandomProcess(sl3);
			data1 := QuickSL3DataStructure(sl3, RPsl3, p, e);
			if not data1 cmpeq "fails" then
			    stop := true;
			end if;
		    else
			i +:= 1;
		    end if;
		until stop or i gt 2 * (1 - 1.0/q)^-5;
		if not stop then
		    j +:= 1;
		else
		    genrec := SLFindGenerators(bbg, data1, r, p, e, d);
		    if genrec cmpeq "fails" then
			stop := false;
			j +:= 1;
		    end if;
		end if;
	    end if;
	until stop or j eq 9;
	if not stop then
	    /*print "could not construct L"; */
	    return Fails(true);
	end if;
    else
	// now r is guaranteed to be a transvection, if bbg is really SL(d, q)
	if d gt 4 then
	    r := FindGoodElement(bbg, bbrand, p, e, d, 4 * q * (d - 2) * Ilog2(d));
	else
	    r := SL4FindGoodElement(bbg, bbrand, p, e, 16 * q);
	end if;
	if r cmpeq "fails" then
	    // print "FindGoodElement could not find r";
	    return Fails(false);
	end if;
	t := r ^ (p ^ (e * (d - 2)) - 1);
	stop := false;
	i := 1;
	repeat
	    u1 := t ^ Random(bbrand);
	    if not (t, u1)^p eq One(bbg) then
		u2 := t ^ Random(bbrand);
		sl3 := sub<bbg | [t, u1, u2]>;
		RPsl3 := RandomProcess(sl3);
		data1 := QuickSL3DataStructure(sl3, RPsl3, p, e);
		if not data1 cmpeq "fails" then
		    stop := true;
		end if;
	    else
		i +:= 1;
	    end if;
	until stop or (i gt (1 - 1.0/q)^(-5) * Ilog2(8 * d^2));
	if not stop then
	    // print "could not construct L";
	    return Fails(true);
	end if;
	genrec := SLFindGenerators(bbg, data1, r, p, e, d);
	if genrec cmpeq "fails" then
	    return Fails(false);
	end if;
    end if;

    Lgen := genrec`Lgen;
    Q := genrec`Q;
    Qgamma := genrec`Qgamma;
    pQ := genrec`pQ;

    L := sub<bbg | Lgen>;
    RPL := RandomProcess(L);

    data2 := SLDataStructure(L, RPL, p, e, d - 1);
    if data2 cmpeq "fails" then
	return Fails(false);
    end if;

    vectors := SLExchangeL(data2, Q, Qgamma, pQ, d);
    if vectors cmpeq "fails" then
	return Fails(false);
    end if;

    data3 := SLConstructBasisQ(bbg, data2, vectors[1], vectors[2], d, q);

    data2 := SLFinishConstruction(bbg, data2, data3, d);

    return data2;
end function;

intrinsic RecogniseSL(G::Grp, d::RngIntElt, q::RngIntElt) -> BoolElt, Map, Map
{Try to find an isomorphism between G and SL(d, q)}
    requirege d, 2;
    f := Factorization(q);
    require #f eq 1: "Argument 3 must be a prime power";

    p := f[1][1];
    e := f[1][2];

    RPG := RandomProcess(G);
    data := SLDataStructure(G, RPG, p, e, d);
    if data cmpeq "fails" then
	return false, _, _;
    end if;
    for x in Generators(G) do if SLSLP(data, x, d, false) cmpeq "fails" then
        return false, _, _;
    end if; end for;

    H := SL(d, q);
/*
*    forw := hom<G -> H |
*          x :-> EvaluateMat(data`gens, SLSLP(data, x, d, false), d, q)>;
*    back := hom<H -> G |
*          x :-> EvaluateBBGp(G, data`gens, SLSLP(data, x, d, true))>;
*/
    forw := func<x | EvaluateMat(data`gens, SLSLP(data, x, d, false), d, q)>;
    back := func<x | EvaluateBBGp(G, data`gens, SLSLP(data, x, d, true))>;

    return true, forw, back;
end intrinsic;

intrinsic RecognizeSL(G::Grp, d::RngIntElt, q::RngIntElt) -> BoolElt, Map, Map
{Try to find an isomorphism between G and SL(d, q)}
   return RecogniseSL (G, d, q);
end intrinsic;
