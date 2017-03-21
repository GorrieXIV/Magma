freeze;
 
///////////////////////////////////////////////////////////////////////
//		Catalogues of subcanonical curves
// Gavin Brown
// September 2003, Sydney.
///////////////////////////////////////////////////////////////////////

/*
Standard notation:
	C	a curve
	g	= g_C
	K	= K_C, the canonical class of C
	D	a divisor on C such that rD = K for some r
	d	= deg D
	V	a sequence containing the first 2g-1 coeffs of P(t)
	p	the Hilbert polynomial p(t) = m*t + 1 - g
	h	the Hilbert series of the pair p,V
	W	the degrees of a set of proposed generators
	num	the Hilbert numerator with respect to W.

Functions here will generate lists of subcanonical curves.
They
    -- compute all prima facie possibilities V of h^0(nD) for low n
    -- compute hilbert series for g,m,V
    -- make a first attempt to compute generators for a graded ring
    -- print out the result.

The first of these has the following rough prescription:
Input:
        d = deg D, g = g_C
Output:
        all sequences [p_0,p_1,..., p_(2g-2)/d] of h^0(nD) allowed
        by RR and Clifford.
        We allow p_1 = 0, but note that Clifford's theorem only holds
        for effective divisors.
Note: at the moment I'm having trouble not doubling some output
in cases like g = 4, d = 3 and D effective. In that case, Clifford's
theorem doesn't actually say anything since we only return 3 coeffs
[ 1, h^0(D), g ] and the Clifford estimate for the middle one is
not an integer. So when I add the hyperelliptic case on at the end
it is already present.
The same goes for D = K, although that isn't really what I'm going to
use this code for.

THINK:  at this stage the calculation is daft.  It collects all
possible initial terms V and then works through them.  But this
sequence of initial terms gets very large as g grows.
*/


///////////////////////////////////////////////////////////////////////
//		Building the catalogue
// The objects corresponding to curves will be records of the form:
//	< g, d, V, h, W, num, betti >
// They will be collected in a sequence called 'results'.
///////////////////////////////////////////////////////////////////////

intrinsic EffectiveSubcanonicalCurves(g::RngIntElt) -> SeqEnum
{}
    require g ge 3: "Genus g must be >= 3";
    results := [];
    k := 2*g - 2;
    possm := [ i : i in [1..Maximum(2,g-1)] | IsDivisibleBy(k,i) ];
    		// Max(2,g-1) so I include g = 0,1 THINK??
    for m in possm do
	results cat:= EffectiveSubcanonicalCurves(g,m);
    end for;
    return results;
end intrinsic;

intrinsic EffectiveSubcanonicalCurves(g::RngIntElt,d::RngIntElt) -> SeqEnum
{A sequence containing data of effective subcanonical curves of genus g >= 3
(polarised by a divisor of degree m if given)}
    result := [];
    p := HilbertPolynomialOfCurve(g,d);
    Vs := EffectivePossibilities(g,d);
    for V in Vs do
	bool,C := IsSubcanonicalCurve(g,d,V);
	if bool then
	    Append(~result,C);
	end if;
    end for;
    return result;
end intrinsic;

intrinsic IneffectiveSubcanonicalCurves(g::RngIntElt) -> SeqEnum
{}
    require g ge 3: "Genus g must be >= 3";
    results := [];
    k := 2*g - 2;
    possm := [ i : i in [1..Maximum(2,g-1)] | IsDivisibleBy(k,i) ];
    		// Max(2,g-1) so I include g = 0,1 THINK??
    for m in possm do
	results cat:= IneffectiveSubcanonicalCurves(g,m);
    end for;
    return results;
end intrinsic;

intrinsic IneffectiveSubcanonicalCurves(g::RngIntElt,d::RngIntElt) -> SeqEnum
{A sequence containing data of effective subcanonical curves of genus g >= 3
(polarised by a divisor of degree m if given)}
    result := [];
    p := HilbertPolynomialOfCurve(g,d);
    Vs := IneffectivePossibilities(g,d);
    for V in Vs do
	bool,C := IsSubcanonicalCurve(g,d,V);
	if bool then
	    Append(~result,C);
	end if;
    end for;
    return result;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//      Computing possible early coefficients: D effective
///////////////////////////////////////////////////////////////////////

forward integer_below,round_down,plus_dual_eff;
intrinsic EffectivePossibilities(g::RngIntElt,d::RngIntElt) -> SeqEnum
{}
    ok,top := IsDivisibleBy(2*g - 2,d);
    require ok: "d must divide 2*g - 2";
    if IsEven(top) then
        half := top div 2;
    else
        half := (top - 1) div 2;
    end if;

    prehyper := [ i*d/2 + 1 : i in [0..half] ];
    hyper := [ round_down(h) : h in prehyper ];
    maxnonhyper := [ integer_below(h) : h in prehyper ];
    maxnonhyper[1] := 1;        // the previous line wrongly computes this as 0
    seqs := [ [1] ];
    for i in [1..half] do
        seqs0 := [];
        for Q in seqs do
            n := Q[#Q];
            seqs0 cat:= [ Q cat [j] : j in [n..m] ]
                        where m is Minimum([n+d,maxnonhyper[#Q+1]]);
        end for;
        seqs := seqs0;
    end for;

    // include duals
    seqs1 := [];
    for Q in seqs do
        bool,Q1 := plus_dual_eff(Q,g,d,half,top);
        if not bool then
            continue Q;
        end if;
        Append(~seqs1,Q1);
    end for;
    // include case when some multiple of D is hyperelliptic
    _,hyper1 := plus_dual_eff(hyper,g,d,half,top);
    Append(~seqs1,hyper1);

    return seqs1;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//      Computing possible early coefficients: D ineffective
///////////////////////////////////////////////////////////////////////

forward plus_dual_ineff,multiples_ok;
intrinsic IneffectivePossibilities(g::RngIntElt,d::RngIntElt) -> SeqEnum
{}
    ok,top := IsDivisibleBy(2*g - 2,d);
    require ok: "d must divide 2*g - 2";
    if IsEven(top) then
        half := top div 2;
    else
        half := (top - 1) div 2;
    end if;

    prehyper := [ i*d/2 + 1 : i in [0..half] ];
    hyper := [ round_down(h) : h in prehyper ];
    maxnonhyper := [ integer_below(h) : h in prehyper ];
    maxnonhyper[1] := 1;        // the previous line wrongly computes this as 0
    seqs := [ [1,0] ];
    for i in [2..half] do
        seqs0 := [];
        for Q in seqs do
            seqs0 cat:= [ Q cat [j] : j in [0..m] ]
                        where m is maxnonhyper[#Q+1];
                // THINK: this is the main change: what's the right bound?
        end for;
        seqs := seqs0;
    end for;

    // include duals
    seqs1 := [];
    for Q in seqs do
        bool,Q1 := plus_dual_ineff(Q,g,d,half,top);
        if not bool then
            continue Q;
        end if;
        Append(~seqs1,Q1);
    end for;

    // I need to check that multiples of an effective are still eff.
    // (Would be best to do this sooner, but needs a little change first)
    seqs1 := [ Q : Q in seqs1 | multiples_ok(Q,half) ];

    return seqs1;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//                      Auxilliary functions
///////////////////////////////////////////////////////////////////////

function integer_below(q)
    n := Round(q);      // rounds 1/2 upwards (and -1/2 down, but we're > 0)
    if n lt q then
        return n;
    else
        return n - 1;
    end if;
end function;

function round_down(q)
    n := Round(q);
    if n le q then
        return n;
    else
        return n - 1;
    end if;
end function;

///////////////////////////////////////////////////////////////////////

    // h^0(nD) - h^0((k-n)D) = d*n + 1 - g so
    //          h^0(nD) = d*n + 1 - g + h^0((k-n)D)
function plus_dual_eff(Q,g,d,half,top)
    // do first step separately since RR could imply false gap
    n := #Q;
    Q[n+1] := (d*n + 1 - g) + Q[top-n+1];
    if Q[n+1] - Q[n] gt d then
        print "!!!!!!!!!",g,d,Q;
        return false,_;
    end if;
    for i in [n+1..top] do
        Q[i+1] := (d*i + 1 - g) + Q[top-i+1];
    end for;
    return true,Q;
end function;

// THINK: only difference is to ignore a test in the ineffective case
function plus_dual_ineff(Q,g,d,half,top)
    // do first step separately since RR could imply false gap
    n := #Q;
    Q[n+1] := (d*n + 1 - g) + Q[top-n+1];
    // if Q[n+1] - Q[n] gt d then
    //     print "!!!!!!!!!",g,d,Q;
    //     return false,_;
    // end if;
    for i in [n+1..top] do
        Q[i+1] := (d*i + 1 - g) + Q[top-i+1];
    end for;
    return true,Q;
end function;

///////////////////////////////////////////////////////////////////////

function remove(Q,A)
    // remove items in for a in A from Q
    for a in A do
        n := Index(Q,a);
        if n gt 0 then
            Remove(~Q,n);
        end if;
    end for;
    return Q;
end function;

// Check that in the ineffective case we don't have something like
//      [ 1, 0, 1, 1, 0, 1, ... ]
// in the first half of Q. The point is that h^0(4D) > 0 because
// h^0(2D) already is.
function multiples_ok(Q,half)
    Q := Q[2..#Q];
    if half-1 lt 2 then
        return true;
    end if;
    lefttocheck := [2..half-1];
    repeat
        n := lefttocheck[1];
        if Q[n] eq 0 then
            // that's fine: remove it and continue
            lefttocheck := lefttocheck[2..#lefttocheck];
            continue;
        else
            mults := [2..integer_below(half/n)+1];
            if &or[ Q[m*n] eq 0 : m in mults ] then
                return false;
            else
                lefttocheck := remove(lefttocheck,[n] cat mults);
            end if;
        end if;
    until #lefttocheck eq 0;
    return true;
end function;

