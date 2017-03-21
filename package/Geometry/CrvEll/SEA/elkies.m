freeze;

function WeierstrassFunction(E,prec)
    // The Weierstrass series of E, assumes that E is in 
    // simplified Weierstrass form. 

    error if (2*prec+1) ge Characteristic(BaseRing(E)),
	"Request for division by zero in kernel polynomial computation.";
    Q := LaurentSeriesRing(BaseRing(E));
    z := Q.1;
    _,_,_,a4,a6 := Explode(Coefficients(E));
    c := [ -a4/5, -a6/7 ];
    for k in [3..prec-1] do
        Append(~c, 3*( &+[ c[h]*c[k-1-h] : h in [1..k-2] ] )
                 / ((k-2) * (2*k + 3)) );
    end for;
    return z^-2 + &+[ c[k]*z^(2*k) : k in [1..prec-1] ] 
               + O(z^(2*prec));
end function;

function PolynomialExpression(S2,S1)
/*
Given power series S1 and S2 find a polynomial phi such that S2 = phi(S1).
It is assumed that S1 has negative valuation, and hence that S2 must also
have negative valuation (or be constant).
*/
    error if not Parent(S1) cmpeq Parent(S2),
       "Incompatible parents in polynomial reconstruction."; 
    error if RelativePrecision(S2) gt RelativePrecision(S1),
	"Not enough terms to reconstruct polynomial.";

    v1 := Valuation(S1);
    v2 := Valuation(S2);
    error if v1 ge 0 or v2 gt 0,
	"Invalid data in polynomial reconstruction.";

    d := v2 div v1;		// maximum degree of polynomial
    S1powers := [ n lt 2 select [1,S1][n+1] else S1*Self(n) : n in [0..d] ];
    S1power := func<n | S1powers[n+1] >;

    x := PolynomialRing(BaseRing(Parent(S1))).1;
    phi := Zero(Parent(x));
    while not IsWeaklyZero(S2) do
	v2 := Valuation(S2);
	n := v2 div v1;
	error if v2 gt 0 or v2 ne n*v1,
	    "Invalid data in polynomial reconstruction.";
	S1n := S1power(n);
	c := LeadingCoefficient(S2) / LeadingCoefficient(S1n);
	phi +:= c*x^n;
	S2 -:= c*S1n;
    end while;
    return phi, true;

end function;

function IsogenyPhi(E,F,psi,prec)
    // Find the polynomial phi s.t. the isogeny E -> F takes 
    // x |--> phi(x) / psi^2(x), where (x,y) is a point on E.

    wE := WeierstrassFunction(E,prec);
    wF := WeierstrassFunction(F,prec);
    den := Evaluate(psi,wE);
    num := den^2*wF;
    // Reconstruct phi = num as a polynomial in wE.
    return PolynomialExpression(num,wE);
end function;

function KernelPolynomial(E,ell,Eb,p1)
    // Find the kernel polynomial g, dividing the ell-division polynomial,
    // from the isogenous curve Eb and trace term p1.

    FF := BaseRing(E);
    xtr := 2;
    deg := (ell-1) div 2;
    error if (2*(deg+xtr)+3) ge Characteristic(FF),
	"Request for division by zero in kernel polynomial computation.";
    
    _,_,_,e4, e6 := Explode(Coefficients(E));
    _,_,_,e4_tilde, e6_tilde := Explode(Coefficients(Eb));
    c := WeierstrassFunction(E,deg+xtr+1);
    c_tilde := WeierstrassFunction(Eb,deg+xtr+1);

    P := PolynomialRing(FF); x := P.1;
    psi2 := 4*x^3 + 4*e4*x + 4*e6;
    dpsi2 := 6*x^2 + 2*e4;
    mulist := [ 2*e4 + 6*x^2 ];
    for k in [2..deg+xtr] do
        pp := Eltseq(mulist[k-1]);
	np := pp[2] * dpsi2;
        for ii in [3..#pp] do
            i := ii - 1;
	    np +:= i*pp[i+1]*(dpsi2*x^(i-1) + (i-1)*psi2*x^(i-2));
        end for;
        Append(~mulist, np);
    end for;

    M := KMatrixSpace(FF, deg+xtr, deg+2+xtr)!0;
    for k in [1..deg+xtr] do
        pp := Eltseq(mulist[k]);
	for i in [1..#pp] do
	    M[k,i] := pp[i] * 2 / Factorial(2*k);
	end for;
    end for;

    B := Vector( [ Coefficient(c_tilde,2*i) - 
                   Coefficient(c,2*i) : i in [1..deg+xtr] ] );
    v_raw, V := Solution(Transpose(M), B);
    if Dimension(V) ne 2 then
	error "Trace term not uniquely determined " *
	"in kernel polynomial computation.";
    end if;

    p0 := deg;
    v :=  v_raw + V.1 * (p0 - Eltseq(v_raw)[1]);
    v :=  v + V.2 * (p1 - Eltseq(v)[2]);
    ps := Eltseq(v);

    // Using Newton sums
    tlist := [ FF!0 : i in [1..deg+1+xtr] ];
    tlist[deg+1+xtr] := FF!1;
    for k in [1..deg+xtr] do
        tmp := FF!0;
        for i in [1..k-1] do
            tmp := tmp + tlist[deg+xtr-i+1] * ps[k-i+1];
        end for;
        tmp := -tmp - ps[k+1];
        tlist[deg+xtr-k+1] := tmp / k;
    end for;
    g := P![tlist[i] : i in [xtr+1..deg+xtr+1]];
    // Verify correctness.
    success := [ tlist[i] : i in [1..xtr] ] eq [ FF!0 : i in [1..xtr] ];
    return g, success;
end function;

function CodomainCanonical(E,ell,phic,ef)
   // E : elliptic curve,
   // ell : a prime,
   // phic : canonical modular equation
   // ef : root of phic defining isogenous curve Eb.
   // {Find the isogeous elliptic curve Eb, and the sum of the x-coordinates 
   // of the points in the kernel of the isogeny E -> Eb.}

   FJparent<F,J> := Parent(phic);
   s_val := 12 div Gcd(12, ell-1);
   v := s_val*(ell-1) div 12;
   j := jInvariant(E);
   ef_tilde := ell^s_val / ef;

   DFpoly := Derivative(phic, F);
   DF := ef * Evaluate(DFpoly, [ef, j]);
   DJpoly := Derivative(phic, J);
   DJ := j * Evaluate(DJpoly, [ef, j]);

   DFFpoly := ef^2 * Derivative(DFpoly, F);
   DFF := DF + Evaluate(DFFpoly, [ef, j]);
   DFJpoly := ef * j * Derivative(DJpoly, F);
   DFJ := Evaluate(DFJpoly, [ef, j]);
   DJJpoly := j^2 * Derivative(DJpoly, J);
   DJJ := DJ + Evaluate(DJJpoly, [ef, j]);

   _,_,_,e4,e6 := Explode(Coefficients(E));
   E4 := -e4 / 3;       // set lambda = 1
   E6 := -e6 / 2;       // set lambda = 1

   if DF eq 0 or E4 eq 0 then
      //print "    Can't process this prime - division by zero problem";
      return -9, -9;
   end if;

   E4_tilde := ( E4 
      + ( (144 * DJ^2 * E6^2) / (s_val^2 * DF^2 * E4^2) ) 
      - ( (48 * DJ * E6^2) / (s_val * DF * E4^2) ) 
      - ( (288 * DJ * DFJ * E6^2) / (s_val * DF^2 * E4^2) ) 
      + ( (144 * DJJ * E6^2) / (s_val * DF * E4^2) ) 
      + ( (72 * DJ * E4) / (s_val * DF) ) 
      + ( (144 * DJ^2 * DFF * E6^2) / (s_val * DF^3 * E4^2) )
   ) / ell^2;
   delta := (E4^3 - E6^2)/1728;
   delta_tilde := ef^(12 div s_val) * delta / (ell^12);

   j_tilde := E4_tilde^3 / delta_tilde;
   /* 
      additional div by 0 check - added mch 05/09 - note if
      j_tilde WERE zero, we could shortcut the whole process,
      as the original curve E would be isogenous to a j=0 curve
      and so have at most 6 possibilities for #E!
   */
   tmp := Evaluate(DJpoly,[(ell^s_val/ef),j_tilde]);
   if E4_tilde eq 0 or tmp eq 0 then
      //print "    Can't process this prime - division by zero problem";
      return -9, -9;
   end if;

   E6_tilde := (-E4_tilde) * ( (ell^s_val/ef) 
      * Evaluate(DFpoly,[(ell^s_val/ef),j_tilde]) * DJ * E6 ) /
      ( ell * j_tilde * tmp * DF * E4 );

   new_a := -3 * ell^4 * E4_tilde;
   new_b := -2 * ell^6 * E6_tilde;

   Eb := EllipticCurve([new_a, new_b]);
   p1 := (6 * ell * E6 * DJ) / (s_val * E4 * DF); 
   return Eb, p1;
end function;

function CodomainAtkin(E,ell,phis,ef,j_tilde)
    // Find the isogeous EC, and the sum of the x-coordinates of
    // the points in the kernel of the isogeny E -> Eb
 
    s_val := 12 div GCD(12, ell-1);
    v := s_val*(ell-1) div 12;
    j := jInvariant(E);
    _,_,_,e4,e6 := Explode(Coefficients(E));
    E4 := -e4 / 3;       // set lambda = 1
    E6 := -e6 / 2;       // set lambda = 1
    delta := (E4^3 - E6^2)/1728;
    FJparent<F, J> := Parent(phis);

    DFpoly := Derivative(phis, F);
    DF := ef * Evaluate(DFpoly, [ef, j]);
    DFstar := ef * Evaluate(DFpoly, [ef, j_tilde]);
    DJpoly := Derivative(phis, J);
    DJ := j * Evaluate(DJpoly, [ef, j]);
    DJstar := ell * j_tilde * Evaluate(DJpoly, [ef, j_tilde]);

    DFFpoly := Derivative(DFpoly, F);
    DFJpoly := Derivative(DJpoly, F);
    DJJpoly := Derivative(DJpoly, J);

    if DF eq 0 or E4 eq 0 then
	//print "   Can't process this prime - division by zero problem";
	return -9, -9;
    end if;

    ef_prime := (ef * E6 * DJ) / (E4 * DF);
    E4_tilde := (DFstar^2 * DJ^2 * E6^2 * j_tilde) /
		(DJstar^2 * DF^2 * E4^2 * (j_tilde - 1728));
    E6_tilde := (DFstar^3 * DJ^3 * E6^3 * j_tilde) /
		(DJstar^3 * DF^3 * E4^3 * (j_tilde - 1728));

    new_a := -3 * ell^4 * E4_tilde;
    new_b := -2 * ell^6 * E6_tilde;

    Eb := EllipticCurve([new_a,new_b]);

    pF := Evaluate(DFpoly,[ef,j]);
    pJ := Evaluate(DJpoly,[ef,j]);
    pFstar := Evaluate(DFpoly,[ef,j_tilde]);
    pJstar := Evaluate(DJpoly,[ef,j_tilde]);

    u1 := (1/pF) * 
	( - ef_prime * Evaluate(DFFpoly,[ef,j])
          + 2 * j * Evaluate(DFJpoly,[ef,j]) * E6 / E4
          - ( E6^2 / (ef_prime * E4^2))
          *  ( j * pJ  + j^2 * Evaluate(DJJpoly, [ef, j]) ) )
     +  (E6 / (3 * E4)) - (E4^2 / (2 * E6));

    u2 := (1/pFstar) * 
	(
          - ef_prime * Evaluate(DFFpoly, [ef, j_tilde])
          + 2 * ell * j_tilde * Evaluate(DFJpoly, [ef, j_tilde]) 
              * E6_tilde / E4_tilde
          - ell^2 * (E6_tilde^2 / (ef_prime * E4_tilde^2)) 
	        * (j_tilde * pJstar + j_tilde^2 
                * Evaluate(DJJpoly, [ef, j_tilde]))
	)
     + ell * ( (E6_tilde / (3 * E4_tilde)) - (E4_tilde^2 / (2 * E6_tilde)));
   p1 := (u1 - u2) * 6 * ell / 2; 
   return Eb, p1;
end function;

function Prime2BigChar(E,F)
    // Find the isogeous EC, and the sum of the x-coordinates 
    // of the points in the kernel of the isogeny E -> Eb, for 
    // the prime 2.

    FF := BaseRing(E);
    P := PolynomialRing(FF);
    X := P.1;
    j := jInvariant(E);
    _,_,_,a4,a6 := Explode(Coefficients(E));
    for c in AllRoots(a6 * (1728-j) / (2*j), 3) do
	if 3*c^2*j / (1728-j) eq a4 then	// got a good c
	    x0 := -c*(F+16) / (F-8);
	    break;
	end if;
    end for;
    if not assigned x0 then	// something's wrong
 	return E, X, false; 
    end if;
    if not DivisionPolynomial(E,2) mod (X-x0) eq 0 then 
	//print "mod fails";
 	return E, X, false; 
    end if;
    t := 3*x0^2 + a4;
    w := x0*t;
    Eb := EllipticCurve([FF | a4-5*t, a6 - 7*w]);
    return Eb, X-x0, true;
end function;

