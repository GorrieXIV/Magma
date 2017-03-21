freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!

////////////////////////////////////////////////////////////////////////
//
//  Computes a nice model of a quadratic twist of a hyperelliptic curve
//  over Q given by y^2 = f(x)
//
//  Paulette Lieby (March 2001)
//
//  All the functions below must be credited to
//  Paul Van Wamelen whose original (Pari)
//  code can be found at
//
//  http://www.math.lsu.edu/~wamelen/genus2.html
//
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//
//     ReduceCurve(C::CrvHyp) -> CrvHyp
//
///////////////////////////////////////////////////////////////////////////
//
//  This code is a naive attempt to do the following (in combination):
//
//  Minimal twisting: scales out the content of f
//
//  Minimization: removes primes in certain situations (single repeated root?)
//
//  Reduction: applies standard generators of SL_2(Z) in the obvious way,
//  measuring improvement by the size of the coefficients of f.

//  Does not keep track of the transformation.
//
//  --SRD
//
///////////////////////////////////////////////////////////////////////////
 
/*
CHANGES:
 
   2001-06:
 
   Scheme merge.

   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   
   2002-05: David Kohel
   Change intrinsic ReduceCurve to function WamemelenReduction
   Used in ReducedModel and HyperellipticCurveFromIgusaClebsch.       

   2003-07: Paul van Wamelen
   Changed PolLinTrans so that PolLinTrans(f, a, b, c, d) takes f to
   f((a*x+b)/(c*x+d))*(c*x+d)^6, where before it was multiplying by
   (c*x+d)^Deg(f). This is usually ok but not if f has degree 5 and zero 
   constant term.
   Changed the calling of NewPowDiv so that it gets 6 coefficients even if
   the polynomial is of degree 5. Otherwise it failed on quintics.

   2003-10: Paul van Wamelen
   In RedDisc, don't try too hard to factor discriminant
   In RedDisc, only reduce at local degree 6 roots
   Fixed and rewrote SlowRed
   TODO: right at the start go to integer polynomials and stay with them,
     should improve speed?

   --------------------------------------------------------------------------

*/

// Redefinition of verbose mode from CrvHyp/reduce.m

declare verbose CrvHypReduce, 3;

BIGVAL := 1000;

function ClearNumDen(f)
    // Clear denominator of f and divide out integer content

    C := Coefficients(f);
    return f*LCM([Denominator(c) : c in C])/GCD([Numerator(c) : c in C]);
end function;

function SizePol(f)
    // Average size of the coefficients squared of f

    c := 0;
    for i in [0..Degree(f)] do
	c +:= Coefficient(f, i)^2;
    end for;
    c /:= 7;
    return Log(10, c)/2;
end function;

function PolLinTrans(f, a, b, c, d)
    // Applying the (a*x+b)/(c*x+d) translation to f

    x := Parent(f).1;
    H := Parent(f)!0;
    for i in [0..Degree(f)] do
	H := H
	+ Coefficient(f, i) * (a*x + b)^i * ((c*x + d)^(6 - i));
    end for;
    return H;
end function;

function ThisVal(a, p)
    // Valuation with Infinity = BIGVAL
    if a eq 0 then
	return BIGVAL;
    else
	return Valuation(a, p);
    end if;
end function;


function SlowRed(f)
    // another reduction function for f:
    // substituting x
    // for x*m or x/m in order
    // to minimze the size of the product
    // of f's coefficients

    f := ClearNumDen(f);

    S := [Integers()!Coefficient(f,i) : i in [0..6]];
    gcd := GCD([S[i] : i in [5,6,7]]);
    plst := {f[1] : f in Factorization(gcd)};
    gcd := GCD([S[i] : i in [1,2,3]]);
    plst := plst join {f[1] : f in Factorization(gcd)};

    vprintf CrvHypReduce, 3 : "will try reduction at these primes: %o\n", plst;
    
    for p in plst do
      vlst := [ThisVal(s,p) : s in S];
      kmax := Min([vlst[7] div 3, vlst[6] div 2, vlst[5]]);
      kmin := Max([-vlst[3], -(vlst[2] div 2), -(vlst[1] div 3)]);
      klst := [kmin..kmax];
      mlst := [Min([vlst[i]-(i-1)*k : i in [1..7]]) : k in klst];
      max, ind := Max([3*klst[i]+mlst[i] : i in [1..#klst]]);
      if max gt 0 then
        k := klst[ind];
        m := mlst[ind];
        S := [S[i]*p^(-(i-1)*k-m) : i in [1..7]];
      end if;
    end for;

    assert {IsIntegral(s) : s in S} eq {true};
 
    return Parent(f)!S;
end function;


function MyNsmPol(f)
    // Successively applying (x+b) translations
    // to f until no reduction in size (of f) can be
    // further achieved
    
    f := ClearNumDen(f);
    s := SizePol(f);
    done := false;
    back := false;   // here we haven't done
    // the inverse translation yet (ie (x-d) as opposed
    // to (x+d) (or vice-versa)
    rev := false;    // here  we haven't investigated
		     // the reverse poly yet

    D := 1;   // average step size
    B := true; // forward dir (ie (x+d) translations only)
    step := D;   // step;
    d := step;  // current length of translation
    pstep := D;  // previous step

    while not done do
	
	temp_f := SlowRed(PolLinTrans(f, 1, d, 0, 1));
	temp_s := SizePol(temp_f);
	if temp_s lt s then
	    f := temp_f;
	    s := temp_s;
	    vprintf CrvHypReduce : "step %o, lower size %o\n", step, s;
	    back := false;
	    rev := false;

	    step *:= 2;
	    d := step;
	elif B and step div 2 gt 0 then
	    // must update steps and d
	    step := step div 2;
	    d := step;
	    vprintf CrvHypReduce : "step/2 %o\n", step;
	elif (not B)
	    and step div 2 lt 0 and step div 2 gt step then
	    step := step div 2;
	    d := step;
	    vprintf CrvHypReduce : "step/2 %o\n", step;
	elif not back then
	    if B then
		assert d eq 1;
	    else
		assert d eq -1;
	    end if;

	    // flip: do (x-d) translation as opposed to
	    // (x+d) translation, or vice-versa
	    step := -step;
	    d := step;
	    back := true;
	    B := not B;
	    vprintf CrvHypReduce : "flip\n";

	elif not rev then
	    // everything has been attempted so far,
	    // we try reversing f
	    assert back eq true;
	    rev := true;
	    f := SlowRed(PolLinTrans(f, 0, 1, 1, 0));
	    step := D; // start afresh
	    d := step; 
	    B := true; // forward dir
	    back := false;
	    vprintf CrvHypReduce : "reverse\n";
	else
	    // all possibilites are now exhausted
	    assert back eq true;
	    assert rev eq true;  
	    done := true;
	end if;
    end while;
    
    return f;
end function;

function RedDisc(ff)
    // Reduce f's discriminant by removing
    // any factor p^30 (p prime) it may have

    vprintf CrvHypReduce, 1 : "reducing the discriminant: start\n";
    f := ClearNumDen(ff);
    f := PolynomialRing(Integers())!ff;
    D := Discriminant(f);
    vprintf CrvHypReduce, 1 : "start factoring discriminant\n";
    faclst := Factorization(D: ECMLimit := 10, MPQSLimit := 0);
    vprintf CrvHypReduce, 1 : "end factoring discriminant\n";
    vprintf CrvHypReduce, 2 : "D now %o\n", faclst;
    for fac in faclst do
        if fac[2] ge 30 then
            p := fac[1];
	    Fp := GF(p);
	    rts6 := [rt[1] : rt in Roots(f,Fp) | rt[2] ge 6];
            while #rts6 gt 0 do
		vprintf CrvHypReduce, 1 : "reducing by %o\n", p;
		f := Evaluate(f,p*Parent(f).1 + Integers()!rts6[1]);
		vprintf CrvHypReduce, 3 : "f := %o\n", f;
		cont, f := Contpp(f);
		vprintf CrvHypReduce, 3 : "cont is %o\n", Factorization(cont);
		vprintf CrvHypReduce, 3 : "D now %o\n", TrialDivision(Discriminant(f));
                rts6 := [rt[1] : rt in Roots(f,Fp) | rt[2] ge 6];
            end while;
	end if;
    end for;
    
    vprintf CrvHypReduce, 2 : "reducing the discriminant: end\n";
    return Parent(ff)!f;
end function;

function Redf(f)
    // Reduce f's discriminant by removing
    // any factor p^30 (p prime) it may have
    
    f := RedDisc(f);
    f := ClearNumDen(f);

    if Degree(f) eq 6 then
		ff := Parent(f)!Reverse(Eltseq(f));
	else
		ff := Parent(f)!(Reverse(Eltseq(f)))*Parent(f).1;
    end if;
    return RedDisc(ff);
end function;


procedure UpdatePolList(~L, f, s, ~c)
    // update list of polynomials with a poly f of
    // smaller size s
	
    C := car< PolynomialRing(Rationals()), RealField(), Integers() >;

    l := #L;
    c := 0;
    for i in [1..l] do
	if s lt (L[l+1-i][2] + 10^(-5)) then
	    c := l+1-i;
	end if;
    end for;
    assert c gt 0;

    if s gt (L[c][2] - 10^(-5)) then
	c := l+1;
    else
        vprintf CrvHypReduce, 2 : "inserting in position c  %o\n", c;

	for i in [1..l-c] do
	    // push towards the end: insertion sort
	    L[l+1-i] := L[l-i];
	end for;
	L[c] := elt< C | f, s, 1>;

	if c eq 1 then
	    vprintf CrvHypReduce : "new low size:  %o\n", L[1][2];
	end if;
    end if;
end procedure;



procedure Small(~L, f, h, ~r)
    // try all possible (a*x+b)/(c*x+d) to see if size
    // can be reduced; store the polys of smaller size
    // in L

    x := Parent(f).1;
    done := #L + 1;
    s := L[#L][2];

    for b in [-h..h] do
	for c in [-(h-Abs(b))..h-Abs(b)] do
	    for d in [-(h-Abs(b)-Abs(c))..h-Abs(b)-Abs(c)] do
		a := h-Abs(b)-Abs(c)-Abs(d);
		if c ne 0 or d ne 0 then
		    vprintf CrvHypReduce, 3 : "a  %o\n", a;
		    vprintf CrvHypReduce, 3 : "b  %o\n", b;
		    vprintf CrvHypReduce, 3 : "c  %o\n", c;
		    vprintf CrvHypReduce, 3 : "d  %o\n", d;

		    dum := (a*x + b)/(c*x + d);
		    if not IsCoercible(Rationals(), (a*x+b)/(c*x+d)) then
			g := ClearNumDen(PolLinTrans(f, a, b, c, d));
			temp_s := SizePol(g);
			vprintf CrvHypReduce, 3 : "in Small temp_s  %o\n", temp_s;
			vprintf CrvHypReduce, 3 : "in Small s  %o\n", s;
			if temp_s lt s then
		            vprintf CrvHypReduce, 3 : "update \n";
	                    g := SlowRed(g);
			    UpdatePolList(~L, g, temp_s, ~res);
                            if res le #L then
                                vprintf CrvHypReduce, 2 : "f=%o\nof size %o under %o goes to\n",f,SizePol(f),[a,b,c,d];
                                vprintf CrvHypReduce, 2 : "%o\nof size %o and is now %o'th best\n",g,SizePol(g),res;
                            end if;
			    done := Min([done, res]);
			    vprintf CrvHypReduce, 3 : "in Small, done when update \n", done;
			    s := L[#L][2];
			end if;
		    end if;
		end if;
	    end for;
	end for;
    end for;

    vprintf CrvHypReduce, 3 : "in Small, done  %o\n", done;
    r := done;
end procedure;

function SmallPol(f, nbt, len)
    // create a database of len smallest-size polys,
    // the number of translations for each poly
    // is governed by nbt

    vprintf CrvHypReduce, 1 : "SmallPol called with f = %o\n", f;

    f := ClearNumDen(f);
    s := SizePol(f);

    C := car< PolynomialRing(Rationals()), RealField(), Integers() >;
    L := [ elt< C | f, 2*s, 1> : i in [1..len] ];
    nbtt := 2;

    while nbtt lt nbt do
	nbtt +:= 1;
	vprintf CrvHypReduce : "size of linear transforms now:  %o\n", nbtt;
	i := 1;
	c := len+1;
	h := 0;
	while i lt len+1 do
	    vprintf CrvHypReduce, 2 : "nbtt = %o, i = %o, c = %o\n", nbtt, i, c;
	    vprintf CrvHypReduce, 2 : "smallest f = %o\n", L[1][1];
	    while h lt nbtt do
		h := L[i][3]; 
		h +:= 1;
		vprintf CrvHypReduce, 2 : " h  %o\n", h;
		L[i][3] := h;
		Small(~L, L[i][1], h, ~c);
		vprintf CrvHypReduce, 2 : "c = %o, i = %o\n", c, i;

		if c le i then
		    i := c;
		    h := L[c][3];
		end if;
	    end while;
	    i := i + 1;
	    if i le len then 
		h := L[i][3];
	    else
		h := nbtt;
	    end if;
	end while;
    end while;
    return L[1][1];
end function;

function WamelenReduction(f) 
    // Input: Polynomial f of degree 5 or 6 over the rationals.
    // Ouput: Polynomial obtained by linear fractional transformation
    //        with reduced integral coefficients. 
    // error if not BaseRing(Parent(f)) cmpeq Rationals(),
    //     "Base field of argument must be the rationals";
    f1 := MyNsmPol(f);
    f2 := Redf(f1);
    f3 := MyNsmPol(f2);
    f4 := SmallPol(f3, 5, 10);

    return f4;
end function;
