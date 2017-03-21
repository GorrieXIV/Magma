freeze;

// ALWAYS DOCUMENT YOUR CHANGES (what/when/how)
// in the header of this file
// these package files are updated concurrently by
// ourselves (magma) AND M. Stoll
// Thank you!




////////////////////////////////////////////////////////////////////////
//                                                                    
//  Counting point stuff                                              
//
//  P. Gaudry (March 2001)
//                                                                    
////////////////////////////////////////////////////////////////////////
//
//  exported intrinsics:
//
//     Order (J::JacHyp: NaiveAlg := false,
//                       ShanksLimit := 10^10,
//	                 CartierManinLimit := 5*10^5, 
//		         UseSchoof := true,
//		         UseHalving := true,
//		         UseSubexpAlg := true
//            ) -> RngIntElt
//
//     EulerFactorModChar(J::JacHyp) -> RngUPolElt
//     
///////////////////////////////////////////////////////////////////////////
//
//  The intrinsic Order() tries to choose the best available algorithm
//  to compute the order of the given Jacobian.  It may rely on
//  probablistic methods, but the result should always be true.
//  
///////////////////////////////////////////////////////////////////////
//  CHANGES
//  =======
//
//  M. Stoll, 2001-05-25:
//
//    Replaced Max(max_deg, ...) by LCM(max_deg, ...) in Order
//
/*
 
   2001-07: Paulette
   Scheme merge: new types now (CrvHyp, SetPtHyp & PtHyp)
   (nothing to do)
                 HyperellipticCurve & Curve fix
		 
   2004-03: Mike Harrison
   Change to the Order code to make use of the more efficient
   p-adic methods (Kedlaya and Mestre) when appropriate. Most
   of the new link code for these methods is in curve.m.
   NaiveCount changed and renamed NaiveEuler.
   
   2004-05: Mike Harrison
   Added function GroupLawEquation to try to find an equivalent
   hyperelliptic equation for which an explicit group law for
   the Jacobian exists. This is called in the point counting code
   as a last resort before trying the FunctionField or Naive
   methods.
   
   2004-07: Mike Harrison
   Extended function TwoTorsionSubgroup to handle the case of
   odd genus and 0/2 rational points at infinity (2 pt case
   now has a group law!). Also fixed old bug (which probably
   never showed up in practise before!).
   Slightly altered GroupLawEquation to reflect the new cases
   where the group law exists (curve has 2 rat pts at infinity).
   
  ------------------------------------------------------------------*/

///////////////////////////////////////////////////////////////////////
//
//  Things TO DO:
//    * if Genus=2 and #J known, then finding #C is easy
//      Therefore it is necessary to store the result in a nice way.
//      Waiting the hyperelliptic curves to be included in the
//      Geometric machinery to do the changes...
//    * implement real representation arithmetic (a la Stein) for high
//      genus compuations
//
///////////////////////////////////////////////////////////////////////


forward NaiveEuler;
forward GetBounds;
forward JacobianOrderSquareRoot;
forward Shanks;
forward TwoTorsionSubgroupOrder;
forward InitializeHT;
forward IncludeHT;
forward IsInHT;
forward GroupLawEquation;

declare verbose JacHypCnt, 4;

import "../CrvG2/count.m" : JacobianOrderGenus2;
import "curve.m" : UseZetaMethod, ApplyZetaMethod, NaiveEulerFactor,
                        EulerFactorOverExtn;

///////////////////////////////////////////////////////////////////////////
//
//  Main function: Order
//
///////////////////////////////////////////////////////////////////////////

intrinsic Order(J::JacHyp : NaiveAlg := false,
                            ShanksLimit := 10^12,
		            CartierManinLimit := 5*10^5,
                            UseGenus2 := false, 
		            UseSchoof := true,
		            UseHalving := true,
		            UseSubexpAlg := true
               ) -> RngIntElt
    { The order of the Jacobian J defined over a finite field. }

    require IsFinite(BaseField(J)): "The base field must be finite.";

    if assigned J`Order then return J`Order; end if;
    if assigned J`EulerFactor then
        J`Order := &+ Coefficients(J`EulerFactor);
        return J`Order;
    end if;

    g := Dimension(J);
    // very easy genus 0 case 
    if g eq 0 then return 1; end if;

    // check for "zeta function" methods
    Fq := BaseRing(J);
    if NaiveAlg then
       usezeta := true;
       meth := 1; // naive algorithm
       C1 := Curve(J); twist := 1; F_min := Fq;
    else
       usezeta,meth,C1,twist := UseZetaMethod(Curve(J));
       F_min := BaseRing(C1);
    end if;
    ext_deg := Degree(Fq) div Degree(F_min);

    //UGLY HACK TO TRY TO USE SHANKS IF q^g "SMALL"
    if usezeta and (ext_deg eq 1) and (J`Type ne 0) then
       if (meth eq 1) and (not NaiveAlg) then  //naive
          if (#Fq)^g gt 50000 then usezeta := false; end if;
       end if;
       if (meth eq 3) or (meth eq 5) then //kedlaya
          if (#Fq)^g lt 10^15 then usezeta := false; end if;
       end if;
    end if;

    if usezeta and ((meth eq 1) or(not UseGenus2)) then
       cpol := ApplyZetaMethod(meth,C1,twist,ext_deg);
       J`EulerFactor := cpol;
       J`Order := &+ Coefficients(cpol);
       return J`Order;
    end if;


    if (g eq 2) and UseGenus2 then
	vprintf JacHypCnt : "Using genus 2 methods\n";
	return JacobianOrderGenus2(J : ShanksLimit := ShanksLimit,
                                       CartierManinLimit := CartierManinLimit,
	                               UseSchoof := UseSchoof,
	                               UseHalving := UseHalving);
    end if;
    
    q := #Fq;
    p := #PrimeField(Fq);
    n := Degree(Fq);


    // switch to function field subexponential algorithm if
    // genus is large and field is small
    if ((q eq 2 and g ge 22) or  // TODO: to be adjusted
	(q eq 3 and g ge 13) or
	(q eq 4 and g ge 11) or
	(q eq 5 and g ge 9) or
	(q eq 7 and g ge 8) or
	(q eq 8 and g ge 7) or
	(q eq 9 and g ge 7) or
	(q eq 11 and g ge 6) or
	(q eq 13 and g ge 6) or
	(q eq 16 and g ge 7) or
	(q eq 17 and g ge 7) or
	(q eq 19 and g ge 8) or
	(q eq 23 and g ge 11)) and UseSubexpAlg then

	vprintf JacHypCnt : "Using the subexponential algorithm taken from the function field machinery\n";
	J`Order := #TorsionSubgroup(ClassGroup(Curve(J)));
	return J`Order;
    end if;

    // if no group law available, use naive or subexp
    if J`Type eq 0 then
        // first look for equivalent hyperelliptic equation with group law.
	boo,C1 := GroupLawEquation(Curve(J));
        if boo then //success!!
            vprintf JacHypCnt : "Working with transformed equation.\n";
            J`Order := Order(Jacobian(C1) : ShanksLimit := ShanksLimit,
	    		            CartierManinLimit := CartierManinLimit,
		                    UseSubexpAlg := UseSubexpAlg);
            return J`Order;
        end if;
	if ((g eq 3 and q gt 101) or
	    (g eq 4 and q ge 31) or
	    (g eq 5 and q ge 17) or
	    (g ge 6)) and UseSubexpAlg then
	    vprintf JacHypCnt : "Using the subexponential algorithm taken from the function field machinery\n";
            J`Order := #TorsionSubgroup(ClassGroup(Curve(J)));
	else
            J`EulerFactor := NaiveEuler(C1,ext_deg);
            J`Order := &+ Coefficients(J`EulerFactor);
       end if;
       return J`Order;
    end if;
    
    // Get bounds
    lB, uB := GetBounds(J);
    vprintf JacHypCnt : "bounds are: %o, %o.\n", lB, uB;

    if 2*lB le uB then
        vprintf JacHypCnt : "these are too bad: go to naive method\n";
        J`EulerFactor := NaiveEuler(C1,ext_deg);
        J`Order := &+ Coefficients(J`EulerFactor);
        return J`Order;
    end if;

    // Find modular information
    NJ2 := TwoTorsionSubgroupOrder(J);
    if NJ2 eq 1 then
	N0 := 1;
	m := 2;
    else
	N0 := 0;
	m := NJ2;
    end if;
    vprintf JacHypCnt : "2-torsion gives: %o mod %o.\n", N0, m;

    // Use Cartier-Manin if we are on an extension
    if n gt 1 and p ne 2 and p le CartierManinLimit and IsOddDegree(Curve(J)) then
	vprintf JacHypCnt : "Compute the Hasse-Witt matrix.\n", N0, m;
	Zp := EulerFactorModChar(J);
	Jp := Evaluate(Zp, 1) mod p;
	vprintf JacHypCnt : "   it gives %o mod %o.\n", Jp, p;
	N0 := CRT( [N0, Jp], [m, p] );
	m := m*p;
    end if;

    // Try with a SquareRoot algorithm taking into account previous info
    vprintf JacHypCnt : "Try with a probabilistic sqrt algo.\n", N0, m;
    t, NJ := JacobianOrderSquareRoot(J, lB, uB, N0, m
                                     : BPAThreshold := ShanksLimit);
    
    if not t then
	vprintf JacHypCnt : "  failed!\n", N0, m;
	vprintf JacHypCnt : "Back to a deterministic version\n", N0, m;
	NJ := Shanks(J, lB, uB);
    end if;

    J`Order := NJ;
    return NJ;
end intrinsic;


////////////////////////////////////////////////////////////////////////////
// ---------------------------------------------------------------------- //
//          GENERIC Computations                                          //
// ---------------------------------------------------------------------- //
////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
//
// The naive way to do: call EulerFactor, which computes all the #C/F_q^i
//
///////////////////////////////////////////////////////////////////////////

function NaiveEuler(C,ext_deg)
    if ext_deg gt 1 then
        vprintf JacHypCnt: "Working over smaller field (degree %o).\n",
                Degree(BaseRing(C));
    end if;
    vprint JacHypCnt: "Using naive counting algorithm.";
    vtime JacHypCnt: e_fact := NaiveEulerFactor(C);
    if ext_deg gt 1 then // go back to original base field
        e_fact := EulerFactorOverExtn(e_fact,ext_deg);
    end if;
    return e_fact;
end function;

//////////////////////////////////////////////////////////
//
// Compute the number of 2-torsion points
// for this, count the branch points, and take care of points at infinity
//
//////////////////////////////////////////////////////////
//
// TODO: extend this to have TwoTorsionSubgroup in all the cases
// treated here (and not only the order!)
//

// intrinsic TwoTorsionSubgroupOrder(J::JacHyp) -> RngIntElt
//     { The order of the rational 2-torsion subgroup of J.}

/* NB. This has been extended from the original version to handle the
   case of odd genus and 0/2  pts at infinity. Here, divisors of
   (even) degree <= g are as before. The different cases to consider are
   divisor classes of degree g+1, where each class corresponds to a
   projective line, P1, of semi-reduced divisors. The class is of ord 2 iff
   this line of divisors is mapped to itself by the hyp involution (hi)
   action. If hi has fixed points on P1, then this corresponds to
   branch point divisors as before. But if the fixed points of hi are
   over the unique quadratic extension (char != 2) then we get extra terms
   (corr to branch point divisors over the extn field which are equiv
    to their conjugates).  
    
    BUG FIX: Replaced fact_even+(fact_odd div 2) with 
              fact_even+Max(fact_odd-1,0) and subsumed the ddf[1][1] eq 1
             case into this.
*/

function TwoTorsionSubgroupOrder(J)
    f, h := HyperellipticPolynomials(Curve(J));
    if Characteristic(BaseRing(J)) eq 2 then
	h := &* [Parent(h) |  x[1] : x in SquareFreeFactorization(h) ];
 	ddf := DistinctDegreeFactorization(h);
	if #PointsAtInfinity(Curve(J)) eq 1 then
	    n := &+[Integers()| Degree(x[2]) div x[1] : x in ddf ];
	    return 2^n;
	else
	    fact_even := 0; fact_odd := 0;
	    for x in ddf do
                if IsOdd(x[1]) then
	            fact_odd +:= Degree(x[2]) div x[1];
		else
		    fact_even +:= Degree(x[2]) div x[1];
		end if;
	    end for;
	    n := fact_even + Max(fact_odd-1,0);
	    return 2^n;
	end if;
    else  // Odd characteristic
	F := h^2+4*f;
	ddf := DistinctDegreeFactorization(F);
	if IsOdd(Degree(F)) then
	    n := &+[ Degree(x[2]) div x[1] : x in ddf ];
	    return 2^(n-1);
	else  
	    fact_even := 0; fact_odd := 0;
	    for x in ddf do
	        if IsOdd(x[1]) then
		   fact_odd +:= Degree(x[2]) div x[1];
	        else
	 	   fact_even +:= Degree(x[2]) div x[1];
	        end if;
	    end for;
	    if fact_odd gt 0 then
	        n := fact_even+fact_odd-1;
	    else // all irred factors of F are odd degree
		n := fact_even;
                if IsOdd(Dimension(J)) then
                // get an extra 2^(fact_even-1) points from branch
		// divisors over the quadratic extension k1 <->  expns
		// of F as a norm of a deg (g+1) poly over k1.
                     n +:= 1;
		end if;
	    end if;
	    return 2^(n-1);
	end if;
    end if;
end function;


/////////////////////////////////////////////////////////////////////
//
// returns bounds for Baby-Step Giant-Step, using Hasse-Weil interval
// and approximation method if genus >= 3.
//
/////////////////////////////////////////////////////////////////////

// intrinsic GetBounds(J::JacHyp : Naive:=false) -> RngIntElt, RngIntElt
//    { Bounds on the group order of J, using Hasse-Weil and approximations }

function GetBounds(J : Naive := false)
    Fq := BaseRing(J);
    q := #Fq;
    g := Dimension(J);

    sq := Sqrt(RealField(Floor(Log(10, q^g))+20)!q);
    NaivelB := Ceiling((sq-1)^(2*g));
    NaiveuB := Floor((sq+1)^(2*g));
    if g eq 2 or Naive then
	return NaivelB, NaiveuB;
    else
	//////////////////////////////////////////////////////////////
	// Approximate the group order by counting points on the curve
	// on the first few extensions fields 
	vprintf JacHypCnt : "Approximation method:\n";
	H:=Curve(J);
	if (g mod 5) eq 2 then
	    lambda := Floor((2*g-1)/5);
	else
	    lambda := Round((2*g-1)/5);
	end if;
	vprintf JacHypCnt : "Compute #C on the first %o extensions\n", lambda;
	// first compute #H over the first lambda extensions
	N := [ InternalOrder(BaseChange(H, ext<Fq|i>)) : i in [1..lambda] ];
	M := [ (N[i]-(q^i+1))/i : i in [1..lambda] ];
	PP<s, T> := PolynomialRing(Rationals(),2);
	UP := PolynomialRing(Rationals()); Z := UP.1;
	S := [];
	LL := &+[(-1)^(i+1)*Z^i/i : i in [1 .. lambda+1] ];
	for i := 1 to lambda do
	    // assume we have already computed the i-1 first s
	    U := &+ [PP| (-1)^k*S[k]*T^k : k in [1 .. i-1] ];
	    U +:= (-1)^i*s*T^i; // s in the one we want to find
	    LogL := Evaluate(LL, U) ;
	    r := Roots(Evaluate(Coefficient(LogL, T, i), [Z, 0]) - M[i]);
	    Append(~S,r[1][1]);
	end for;
	vprintf JacHypCnt, 2 : "Precomputed s_i are %o\n", S;
	// Find the equation relating the next si and the next Mi:
	U := &+ [PP| (-1)^k*S[k]*T^k : k in [1 .. lambda] ];
	U +:= (-1)^(lambda+1)*s*T^(lambda+1);
	LogL := Evaluate(LL, U) ;
	EqZ := Evaluate(Coefficient(LogL, T, lambda+1), [Z, 0]); 
	a := Coefficient(EqZ, 1);
	b := Coefficient(EqZ, 0);
	lB := -2*g*Sqrt(q^(lambda+1))/(lambda+1);
	uB := 2*g*Sqrt(q^(lambda+1))/(lambda+1);
	lB -:= b; uB -:= b;
	lB /:= a; uB /:=a;
	if (lB gt uB) then
	    aux := lB;
	    lB := uB;
	    uB := aux;
	end if;
	// Here we know that S[lambda+1] lies in [ lB .. uB ]
	// Compute the global bounds for number of points.
	low := 1+q^g;
	up := low;
	for i := 1 to g do
	    if i le lambda then
		low +:= (-1)^i*S[i]*(1+q^(g-i));
		up +:= (-1)^i*S[i]*(1+q^(g-i));
	    elif i eq lambda+1 then
		if IsEven(i) then
		    low +:= lB*(1+q^(g-i));
		    up +:= uB*(1+q^(g-i));
		else
		    low +:= -uB*(1+q^(g-i));
		    up +:= -lB*(1+q^(g-i));
		end if;
	    else
		bound := Binomial(2*g, i)*Sqrt(q^i)*(q^(g-(i+1)));
		low -:= bound;
		up +:= bound;
	    end if;
	end for;
	return Max(Ceiling(low),NaivelB), Min(Floor(up),NaiveuB);
    end if;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Generic SquareRoot Algorithm: try to guess the result by computing
// the order of a few elements.
//
// choose between Shanks and Pollard's Rho according to BPAThreshold
//
///////////////////////////////////////////////////////////////////////////

// intrinsic JacobianOrderSquareRoot(J::JacHyp, lB::RngIntElt,
//                                   uB::RngIntElt, N0::RngIntElt, m::RngIntElt
//                     : BPAThreshold := 1000000000000)
//                    -> BoolElt, RngIntElt
//     { Try to compute the group order.  The boolean tells whether it
//     succeeded  and in that case, the order is returned. }

function JacobianOrderSquareRoot(J, lB, uB, N0, m : BPAThreshold := 1000000000000)
    // Choose between BSGS and BPA
    // BSGS is faster and has deterministic runtime but uses more memory
    // There is a Threshold to be set, which is a function of (uB-lB)/m
    // say 10^12 (wich means that we are allowed to store 10^6 elements.

    if (uB-lB)/m gt BPAThreshold then
	TheCountAlgo := "PollardRho";
	vprintf JacHypCnt : "will use Birthday Paradox Algorithm\n"; 
    else
	TheCountAlgo := "Shanks";
	vprintf JacHypCnt : "will use Shanks Algorithm\n"; 
    end if;
    
    // Try with 3 random points. If we didn't get the result
    // therafter, the group may be highly non cyclic, and we have to go
    // back to deterministic, memory-consumming techniques.
    // TODO: find a better strategy...
    
    // The current knowledge is stored in a 3-uple [min, max, gap]
    // which means that h is in [ min..max by gap ]
    min := lB - (lB mod m) + N0;
    max := uB - (uB mod m) + N0;
    if max gt uB then max -:= m; end if;
    gap := m;

    // TODO: store the factorizations, instead of recomputing each time.
    for i := 1 to 3 do
	vprintf JacHypCnt : "min, max, gap = %o, %o, %o\n", min, max, gap;
	P := Random(J);
	hP := Order(P, lB, uB, N0, m : Alg := TheCountAlgo);
	vprintf JacHypCnt : "the order of P is %o\n", hP;

	// use the 2-torsion-subgroup to help a little bit:
	NJ2 := TwoTorsionSubgroupOrder(J);
	if IsOdd(hP) then
	    hP *:= NJ2;
	else
	    hP *:= NJ2 div 2;
	end if;
	vprintf JacHypCnt : "With 2-tors subgroup, we get a subgroup of order %o\n", hP;

	// solve hP.x = min mod gap  in the interval [min..max]
	x, y := Solution(hP, min, gap);
	assert(x ne -1);
	l := Ceiling(min/hP);
	L := Floor(max/hP);
	x0 := l - (l mod y) + x;
	error if x0 gt L, " bounds are false?\n";
	xn := L - (L mod y) + x;
	if xn gt L then xn -:= y; end if;
	if x0 lt l then x0 +:= y; end if;
	min := x0*hP;
	max := xn*hP;
	gap := y*hP;
	if min eq max then break; end if;
    end for;

    if min eq max then
	return true, min;
    else
	return false, min;
    end if;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Shanks' baby-steps giant-steps method
//
// The generic, time and space consuming Shanks algorithm.  It should
// almost nether be called: it's there to be in the safe side, in the
// case where everything else failed. (higly non-cyclic groups, for instance)
//
///////////////////////////////////////////////////////////////////////////

// G is a group for which
//     1) the group law is +
//     2) B/2 < C <= #G <= B 
//     3) Random(G) is allowed

// Algorithm taken from Cohen's book (warning, many errata in the
// first edition)
//
// using hashing techniques

// intrinsic Shanks(G::JacHyp, C::RngIntElt, B::RngIntElt)
//              -> RngIntElt
//     { Group order computation using shanks algorithm. }

function Shanks(G, C, B)
    // At each time, we have a subgroup of order h, described by S +
    // L where S and L are sets of elements. We start with the
    // trivial subgroup.
    
    // init:
    h:=1;  B1:=B;  C1:=C;  S:={ G!0 };  L:={ G!0 };
     
    // main loop: while h is not in the given interval [ C, B ]
    while h lt C do
	vprintf JacHypCnt, 2: "**** current value of h is %o\n", h; 
	// Choose a new element at random
	g := Random(G);
	q := Ceiling(Sqrt(B1-C1));
	vprintf JacHypCnt, 2: "**** current value of B1, C1, q are %o, %o, %o\n", B1, C1, q;

	// Main computation: find n such that (n.h). g \in S+L 
	found_with_small := false;
	// Firstly, small steps
	x0 := G!0;
	x1 := h*g;
	if x1 eq G!0 then 
	    found_with_small := true; 
	    n := 1;
	else
	    S1 := InitializeHT(q);
	    for p in S do IncludeHT(~S1, <p,0>); end for;
 xr := G!0;
 if q gt 1 then
	    for p in S do
		px1 := p+x1;
		if px1 eq G!0 then
		    found_with_small := true; 
		    n := 1; break;
		end if;
		IncludeHT(~S1, <px1, 1>);
	    end for;
	    xr := x1;
 end if;
 if q gt 2 then
	    for r := 2 to q-1 do
		if found_with_small then break; end if;
		xr +:= x1;
		for p in S do
		    pxr := p+xr;
		    if pxr eq G!0 then
			found_with_small := true; 
			n := r; break;
		    end if;
		    IncludeHT(~S1, <pxr, r>);
		end for;
	    end for;
 end if;
	end if;
	// secondly, large steps
	if not found_with_small then
	    y := xr + x1;
	    z := C1*x1; n := C1;
	    
	    found := false;
	    while n le B1+q and not found do
		for w in L do
		    z1 := z+w;
		    t, r := IsInHT(z1, S1);
		    if t then n -:= r; found := true; break; end if;
		end for;
		if not found then
		    z := z + y;
		    n := n + q;
		end if;
	    end while;
	    error if not found, "bounds are false?\n";
	end if;
	vprintf JacHypCnt, 2 : "order of x1 divides %o mod S+L\n", n;
	// now we know that (n.h) g is in S+L
	// compute the exact order of g mod S+L
	n *:= h;
	repeat
	    finished := true;
	    primes := PrimeDivisors(n);
            for p in primes do
		gnp := (n div p)*g;
		S1 := {gnp+s : s in S};
		if not IsDisjoint(S1, L) then 
		    finished := false;
		    n := n div p;
		    break;
		end if;
	    end for;
	until finished;
	vprintf JacHypCnt, 2 : "order of g is %o mod S+L\n", n; 
	// now n is the exact order of g mod S+L
	h *:= n;
	// finished ?
	if h ge C then break; end if;
	// test also if there is only one multiple of h in [C,B]
	if Ceiling(C/h) eq Floor(B/h) then return h*Floor(B/h); end if;
	// otherwise, update S, L, B, C
	B1 := Floor(B1/n); 
	C1 := Ceiling(C1/n);
	q := Ceiling(Sqrt(n));
	gr := G!0;
	NewS := S;
	for r:= 1 to q-1 do
	    gr+:=g;
	    NewS := NewS join { gr+p : p in S};
	end for;
	y := gr + g; ya := G!0;
	NewL := L;
	for a := 1 to q do
	    ya +:=y;
	    NewL := NewL join { ya+p : p in L};
	end for;
	S := NewS; L := NewL;
    end while;
    return h;
end function;

///////////////////////////////////////////////////////////////////////////
/////////// Hash Table Stuff... (very naive implementation...)

function InitializeHT(q)
     return [ [] : i in [1..NextPrime(q)]];
end function;

procedure IncludeHT(~S, x)
     Append(~S[(Hash(x[1]) mod #S) + 1], x);
end procedure;

function IsInHT(z, S)
     for x in S[(Hash(z) mod #S) + 1] do
        if z eq x[1] then return true, x[2]; end if;
     end for;
     return false, 0;
end function;


///////////////////////////////////////////////////////////////////////////
//
// Cartier-Manin operator
//
///////////////////////////////////////////////////////////////////////////
//
// We compute the Hasse-Witt matrix of a hyperelliptic curve and deduce
// the EulerFactor modulo the characteristic of the base field.
//
// See paper by Yui, 1978: On the jacobian varieties of hyperelliptic
//   curves over fields of characteristic p>2. J. Algebra 52, 378--410
// See also paper by Gaudry-Harley in Ants-IV.
//
// This is implemented only for curves of equations y^2=f(x),
//   with odd degree f.
//
///////////////////////////////////////////////////////////////////////////


// intrinsic HasseWittMatrix(J::JacHyp) -> AlgMatElt
//     { The Hasse-Witt matrix of the Jacobian of a curve of
//     the form y^2 = f(x) with odd degree f.}

function HasseWittMatrix(J)
    // require J`Type eq 1 : "This function is only implemented for curves of the form y^2 = f(x) with odd degree f";

    f, h := HyperellipticPolynomials(Curve(J));
    g := Dimension(J);
    p := Characteristic(BaseRing(J));
    fp := f^((p-1) div 2);
    M := Matrix( [ [ Coefficient(fp, i*p-j) : i in [1..g] ] : j in [1..g] ] );

    return M;
end function;


intrinsic EulerFactorModChar(J::JacHyp) -> RngUPolElt
    { The Euler factor of a Jacobian over a finite field computed modulo
    p, using the Hasse-Witt matrix. Warning: cost in M(g.p).log(g.p) }

    require J`Type eq 1 : "This function is only implemented for curves of the form y^2 = f(x) with odd degree f";

    g := Dimension(J);
    p := Characteristic(BaseRing(J));
    A := HasseWittMatrix(J);
    n := Degree(BaseRing(J), GF(p));
    
    Ap := A;
    Prod := A;
    for i := 1 to n-1 do
	Ap := Matrix(g, g, [ s^p : s in Eltseq(Ap)]);
	Prod *:= Ap;
    end for;
    Z := CharacteristicPolynomial(Prod);
    X := Parent(Z).1;
    Z := X^g*Z;
    Z := Parent(Z) ! Reverse(Eltseq(Z));
    return PolynomialRing(Integers())!Z;
end intrinsic;


///////////////////////////////////////////////////////////////////////////
//
// GroupLawEquation - called when J(C) has no explicit group law. Tries to
//   find a curve C' isomorphic to C for which J(C') has a group law.
//
///////////////////////////////////////////////////////////////////////////

/* With the extension of the group law, some of this function is now 
   redundant! The only case left where no group law applies is for
   odd genus and 0 rational points at infinity.
   when the function is called, give preference to finding a C' model
   with 1 pt at infinity (for faster group law!)
*/                               
function GroupLawEquation(C)

    g := Genus(C);
    assert g gt 2;
    assert (NumberOfPointsAtInfinity(C) eq 0) and IsOdd(g);

    K := BaseRing(C);
    char2 := Characteristic(K) eq 2;
    f,h := HyperellipticPolynomials(C);
    F := char2 select h else (4*f+h^2);
    boo,rt := HasRoot(F); 
    if not boo then //  no rational finite Weierstrass point
        pts_at_infty := IsOdd(g) select true else false;
        // For even genus we can transform so there are no
        // rational points at infinity. For odd genus we
	// look for 2 points at infinity (new!)
        // Find rt in K s.t. no K-rat pts with x=rt.
        // Here we assume that #C(K) < 2*(#K+1) - true if
        // #K >= 4*g^2.
        while true do
          rt := Random(K);
          if char2 then
            tr := Trace(Evaluate(f,rt)/Evaluate(h,rt)^2);
            if (tr eq K!0) eq pts_at_infty then
              break;
            end if;
          else
            if IsSquare(Evaluate(F,rt)) eq pts_at_infty then
              break;
            end if;
          end if;
        end while;
    end if;
    x := Parent(f).1;
    // transform by substitution x1 = 1/(x-rt), y1 := y/(x-rt)^(g+1)
    if char2 then
    // here deg(h)=g+1, deg(f)<=2g+2 as there are 0 or 2 pts at infty
       h := Evaluate(h,x+rt);
       h := Parent(h)!Reverse(Coefficients(h));
       f := Evaluate(f,x+rt);
       f := (Parent(f)!Reverse(Coefficients(f)))*(x^(2*g+2-Degree(f)));
       return true, HyperellipticCurve([f,h]);
    else
       F := Evaluate(F,x+rt);
       return true, HyperellipticCurve(
                Parent(f)!Reverse(Coefficients(F)) );
    end if;

end function;
