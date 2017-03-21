freeze;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//               SCHOOF'S ALGORITHM ON KERNEL POLYNOMIALS             //
//                              David Kohel                           //
//              Based on code of Richard Rannard, July 1998           //
//                                                                    //
////////////////////////////////////////////////////////////////////////

forward DivisionBabyMatch, DivisionGiantMatch;
forward SignedTrace, IsEigenvalue, Y_power, BSGSBounds;  
forward VerifySignResultant, VerifySignAbscissa;
forward VerifySignAbscissaOdd, VerifySignAbscissaEven;

////////////////////////////////////////////////////////////////////////
//                        SCHOOF'S  ALGORITHM                         //
////////////////////////////////////////////////////////////////////////
 
procedure TraceSchoof(~T)
    // Computes the trace of Frobenius mod ell, given an 
    // ell-torsion kernel polynomial.

    E := T`E;
    FF := BaseRing(E);
    q := #FF;
    P := PolynomialRing(FF); x := P.1;

    ell := T`prime;
    kernel_poly := T`kernel_poly;

    d := Degree(kernel_poly);
    vprintf SEA, 4:
       "Computing x^q modulo the kernel polynomial (degree %o).\n", d;
    vtime SEA, 4:
    x_pow := Modexp(x,q,kernel_poly);
    T`x_pow := x_pow;

    tyme := Cputime();
    vprint SEA, 4: "Doing baby steps...";
    r, s, t, except := BSGSBounds(ell);
    lambda, psiQseq := DivisionBabyMatch(E, kernel_poly, x_pow, r);
    vprint SEA, 4: "Baby step time:", Cputime(tyme);
    if lambda ne 0 then
	vprint SEA, 4: "Found baby step match:", lambda;
    else 
	tyme := Cputime();
	vprint SEA, 4: "Doing giant steps...";
	j, i := DivisionGiantMatch(E, kernel_poly, x_pow, psiQseq, s, t);
	if j eq 0 then
	    lambda := except;
	else 
	    lambda := (Modinv(j,ell)*i) mod ell;
	end if;
	vprint SEA, 4: "Giant step time:", Cputime(tyme);
	vprint SEA, 4: "Found giant step match:", lambda;
    end if;
    error if lambda eq 0, "No eigenvalue found mod", ell;
    tyme := Cputime();
    vprint SEA, 4: "Determining sign on y coordinate.";
    SignedTrace(~T,lambda);
    vprint SEA, 4: "Sign time:", Cputime(tyme);
end procedure;

function DivisionBabyMatch(E, kernel_poly, x_pow, r)
    // Tests for a match x_pow with some multiplication map [k] for
    // 1 <= k <= r.  If no match is found, then returns the sequence
    // of reduced division polynomials (i.e. with no psi2 factor). 

    P := Parent(x_pow); x := P.1;
    Q := quo< P | kernel_poly>;
    xmxq := Q!(x-x_pow); 

    vprint SEA, 4 : "Looking for eigenvalue by baby steps...";
    vprint SEA, 4 : "Computing division polynomials:";

    psi2 := Q!DivisionPolynomial(E,2);
    psiQseq := [ Q | 1, 1 ];
    vprintf SEA, 4: "1..";
    if xmxq eq 0 then
	vprint SEA, 4: "(match)";
	return 1, _;
    end if;
    for k in [2..r] do
	_, psi := DivisionPolynomial(E, k+1, kernel_poly); 
	// Evaluate to x = xQ in Q:
	Append(~psiQseq,Q!psi);
	vprintf SEA, 4: "%o..", k;
	dendiff := xmxq * psiQseq[k]^2;
	numdiff := psiQseq[k-1] * psiQseq[k+1];
	if IsEven(k) then 
	    match := numdiff eq dendiff*psi2;
	else
	    match := numdiff*psi2 eq dendiff;
	end if;
	if match then
  	    vprint SEA, 4: "(match)";
	    return k, _;
	end if;
    end for;
    vprint SEA, 4: "(no match)";
    return 0, psiQseq; 
end function;

function DivisionGiantMatch(E, kernel_poly, x_pow, psiQseq, s, t)
    // Tests for a match of [j]*x_pow with some multiplication map 
    // [i] up to sign for 1 <= i <= s and 2 <= j <= t.  If no match
    // is found, then returns i, j = 0, 0.

    vprint SEA, 4 : "Looking for eigenvalue by giant steps...";

    P := Parent(x_pow); x := P.1;
    Q := Universe(psiQseq);
    xQ := Q.1;
    xQ_pow := Q!x_pow;
    xpmx := Q!(x_pow-x); 

    vprint SEA, 4 :
        "Computing multiplication maps from division polynomials.";
    tyme := Cputime();
    psi2 := Q!DivisionPolynomial(E,2);
    mults := [ xQ ];
    for i in [2..s] do
	num := psiQseq[i-1] * psiQseq[i+1];
	den := psiQseq[i]^2;
	if IsOdd(i) then
	    Append(~mults, xQ-(psi2*num)/den);
	else
	    Append(~mults, xQ-num/(psi2*den));
	end if;
    end for;
    vprint SEA, 4 : "Multiplication map time:", Cputime(tyme);
    vprint SEA, 4 : "Computing multiplicaton maps for x^q:";
    psi2pow := Evaluate(DivisionPolynomial(E,2),xQ_pow);
    psi3pow := Evaluate(DivisionPolynomial(E,3),xQ_pow);
    psiQpowseq := [ Q | 1,1,psi3pow];
    vprintf SEA, 4: "j = 1..";
    for j in [2..t] do
	// We've already tested j = 1 in previous step.
	vprintf SEA, 4: "%o..", j;
	num := psiQpowseq[j-1] * psiQpowseq[j+1];
	den := psiQpowseq[j]^2;
	if IsOdd(j) then
	    multpow := xQ_pow-(psi2pow*num)/den;
	else
	    multpow := xQ_pow-num/(psi2pow*den);
	end if;
	i := Index(mults,multpow);
	if i ne 0 then
	    vprintf SEA, 4: "(match i = %o)\n", i;
	    return j, i;
	end if;
	for i in [1..#mults] do
	    assert mults[i] ne multpow;
	end for;
	m := (j+2) div 2; 
	// Extend the psiQpowseq sequence to j+2.
	if j eq 2 then
	    _, psi4 := DivisionPolynomial(E,4);
	    psiQpow := Evaluate(psi4,xQ_pow);
	elif IsOdd(j) then 
	    if m mod 2 eq 0 then
		psiQpow := psiQpowseq[m+2] * psiQpowseq[m]^3 * psi2pow^2 -  
                           psiQpowseq[m-1] * psiQpowseq[m+1]^3; 
	    else
		psiQpow := psiQpowseq[m+2] * psiQpowseq[m]^3 -  
                           psiQpowseq[m-1] * psiQpowseq[m+1]^3 * psi2pow^2; 
	    end if;
	else
	    psiQpow := psiQpowseq[m] * (
 	        psiQpowseq[m+2] * psiQpowseq[m-1]^2 -  
                psiQpowseq[m-2] * psiQpowseq[m+1]^2 ); 
	end if;
	Append(~psiQpowseq,psiQpow);
    end for;
    vprint SEA, 4: "(no match)";
    return 0, 0; 
end function;

////////////////////////////////////////////////////////////////////////
//                          SIGN DETERMINATION                        //
////////////////////////////////////////////////////////////////////////
 
function PseudoOrderMod(u,ell)
    n := Modorder(u,ell);
    if n mod 2 eq 0 then
	return n div 2;
    end if;
    return n;
end function;

function VerifySignResultant(T)
    // Define s to be the order of lambda in Z/ellZ^*/{1,-1}, where
    // ell mod 4 eq 3.  We can test if the y-values of the ell-torsion
    // exists over the same field as the x-values by determining if
    // the resultant below is a square.

    E := T`E;
    q := #BaseRing(E);

    // It remains to implement the resultant method in even characteristic.
    // Eventially this should be removed.
    if q mod 2 eq 0 then
	return VerifySignAbscissaEven(T);
    end if;

    lambda := T`lambda;
    ell := T`prime;
    kernel_poly := T`kernel_poly;

    P := Parent(kernel_poly); x := P.1;
    _, a2, _, a4, a6 := Explode(Eltseq(E));
    Res := Resultant(kernel_poly,x^3+a2*x^2+a4*x+a6);
    s := PseudoOrderMod(lambda,ell);
    chi := lambda^s mod ell;
    rho := IsSquare(Res) select 1 else -1;
    // We define chi = lambda^s mod ell, where lambda is the
    // conjectured eigenvalue of Frobenius.  If chi is [-1] then
    // this indicates that this power of Frobenius should act as
    // [-1] if the sign of lambda is correct (s must be odd).
    // On the other hand, the value of rho is the correct value,
    // hence the product chi*rho is the sign correction term.
    return (chi*rho) mod ell eq 1;
end function;

function VerifySignAbscissa(T)
    if Characteristic(BaseRing(T`E)) eq 2 then
        return VerifySignAbscissaEven(T);
    else 
        return VerifySignAbscissaOdd(T);
    end if;
end function;

function VerifySignAbscissaOdd(T)
    E := T`E;
    lambda := T`lambda;
    kernel_poly := T`kernel_poly;
    q := #(BaseRing(E));
    psi2 := DivisionPolynomial(E,2);

    // check y-coordinates
    if lambda eq 1 then
	fkm2 := -1;
    else
	_, fkm2 := DivisionPolynomial(E, lambda-2, kernel_poly);
    end if;
    _, fkm1 := DivisionPolynomial(E, lambda-1, kernel_poly);
    _, fk := DivisionPolynomial(E, lambda, kernel_poly);
    _, fkp1 := DivisionPolynomial(E, lambda+1, kernel_poly);
    _, fkp2 := DivisionPolynomial(E, lambda+2, kernel_poly);
    prod3 := fkp2*fkm1*fkm1 - fkm2*fkp1*fkp1;
    if IsOdd(lambda) then
        pow2 := Modexp(psi2, ((q-1) div 2), kernel_poly);
    else
        pow2 := Modexp(psi2, ((q+3) div 2), kernel_poly);
    end if;
    return ((fk^3*pow2 - prod3) mod kernel_poly) eq 0;
end function;

function VerifySignAbscissaEven(T)
    E := T`E;
    lambda := T`lambda;
    kernel_poly := T`kernel_poly;
    a6 := aInvariants(E)[5];
    FF := BaseRing(E);
    Q := quo< PolynomialRing(FF) | kernel_poly>;
    z := Q.1;
    psi2 := Q!DivisionPolynomial(E,2);
    if lambda eq 1 then
	tmp := -1;
    else
	_, tmp := DivisionPolynomial(E, lambda-2, kernel_poly);
    end if;
    DP_lambda_m2 := Q!tmp;
    _, tmp := DivisionPolynomial(E, lambda-1, kernel_poly);
    DP_lambda_m1 := Q!tmp;
    _, tmp :=    DivisionPolynomial(E, lambda, kernel_poly);
    DP_lambda := Q!tmp;
    _, tmp := DivisionPolynomial(E, lambda+1, kernel_poly);
    DP_lambda_p1 := Q!tmp;

    if IsEven(lambda) then
        bigY_bot :=  (z*DP_lambda^3*psi2);
        Y0 := z*(z*DP_lambda^3*psi2) + z*DP_lambda*(DP_lambda_m1*DP_lambda_p1) +
              ( DP_lambda_m2*DP_lambda_p1^2) + 
                                  DP_lambda*(z^2)*DP_lambda_m1*DP_lambda_p1;
        Y1 := z*DP_lambda^3*psi2 + DP_lambda*DP_lambda_m1*DP_lambda_p1;
    else
        Y0 := z*z*DP_lambda^3 + psi2*z*DP_lambda*DP_lambda_m1*DP_lambda_p1 +
                 psi2*DP_lambda_m2*DP_lambda_p1^2 + 
                                 psi2*DP_lambda*(z^2)*DP_lambda_m1*DP_lambda_p1;
        Y1 := z*DP_lambda^3 + psi2*DP_lambda*DP_lambda_m1*DP_lambda_p1;
        bigY_bot :=  (z*DP_lambda^3);
    end if;
    Yq0, Yq1 := Y_power(E, Degree(FF), kernel_poly);
    a_br := (Q!Yq0*bigY_bot - Y0);
    b_br := (Q!Yq1*bigY_bot - Y1);
    cx := a_br^2 + (z*a_br*b_br) + (b_br^2)*(z^3 + a6);
    return cx eq 0;
end function;

function Y_power(E, exp, kernel_poly)
    // Calcuate y^(2*exp) = y_pow_0 + y_pow_1*y modulo 
    // the relation y^2 = x*y + x^3 + a6.

    x := Parent(kernel_poly).1;
    a6 := aInvariants(E)[5];

    y2_0 := x^3 + a6;
    y2_1 := x;
    y_pow_0 := y2_0;
    y_pow_1 := y2_1;
    for i in [2..exp] do
        y_pow_1_2 := Modexp(y_pow_1, 2, kernel_poly);
        y_pow_0 := ( y_pow_0^2 + (y2_0*y_pow_1_2) mod kernel_poly ) 
            mod kernel_poly;
        y_pow_1 := (y2_1*y_pow_1_2) mod kernel_poly;
    end for;
    return y_pow_0, y_pow_1;
end function;

////////////////////////////////////////////////////////////////////////
//                     EIGENVALUE VERIFICATION                        //
////////////////////////////////////////////////////////////////////////
 
function IsEigenvalue(E,lambda_test,xpmx,kernel_poly);
    // assert xpmx eq ((x^q - x) mod kernel_poly);

    Q := Parent(xpmx);
    psi_2 := Q!DivisionPolynomial(E,2);

    _, tmp := DivisionPolynomial(E, lambda_test-1, kernel_poly);
    fkm1 := Q!tmp;
    _, tmp :=    DivisionPolynomial(E, lambda_test, kernel_poly);
    fk := Q!tmp;
    _, tmp := DivisionPolynomial(E, lambda_test+1, kernel_poly);
    fkp1 := Q!tmp;
    prod1 := xpmx*fk*fk;
    prod2 := fkm1*fkp1;
    if IsEven(lambda_test) then
        ff := prod1*psi_2 + prod2;
    else
        ff := prod1 + psi_2*prod2;
    end if;
    return ff eq 0;
end function;

procedure SignedTrace(~T,lambda)
    q := #BaseRing(T`E);
    ell := T`prime;
    assert T`prime_exponent eq 1;
    // Value chosen arbitrarily.
    // max_sign := Log(q)/Log(8);
    max_sign := Infinity();
    if ell gt max_sign then
        trace := Integers()!(lambda + q*(GF(ell)!lambda)^-1);
        trace_vals := SetToSequence({trace,-trace});
        if #trace_vals eq 1 then
            T`trace := trace_vals[1];
            vprint SEA, 4: "Trace = ", T`trace, "mod", ell;
        else
            vprint SEA, 4: "Skipping sign determination.";
            T`trace := trace_vals;
            vprint SEA, 4: 
                "Possible values for trace mod", ell, "are", T`trace;
        end if;
        return;
    end if;
    // Finding the correct sign...
    tyme := Cputime();
    s := PseudoOrderMod(lambda,ell);
    T`lambda := lambda;
    if IsOdd(s) and ell mod 4 eq 3 then 
        yes := VerifySignResultant(T);
    else
	yes := VerifySignAbscissa(T);
    end if;
    if not yes then
	T`lambda := ell-lambda;
    end if;
    T`trace := Integers()!(T`lambda + q*(GF(ell)!T`lambda)^-1);
    vprint SEA, 4: "Sign time:", Cputime(tyme);
    vprint SEA, 4: "Eigenvalue =", lambda, "mod", ell;
    vprint SEA, 4: "Trace =", T`trace, "mod", ell;
end procedure;

////////////////////////////////////////////////////////////////////////
//          EXTENDING SCHOOF TRACE COMPUTATION TO PRIME POWER         //
////////////////////////////////////////////////////////////////////////

procedure TraceSchoofExtend(~T)
    // Determines an eigenvalue and trace modulo ell^n. 

    vprint SEA, 4: "In prime power Schoof algorithm...";

    E := T`E;
    ell := T`prime;
    n := T`prime_exponent;
    lambda_prev := T`lambda;
    kernel_poly := T`kernel_poly;
    FF := BaseRing(E);
    P := PolynomialRing(FF);
    x := P.1; 
    Q := quo< P | kernel_poly>;
    q := #(FF);
    _,_,_,a4,a6 := Explode(Coefficients(E));

    vprintf SEA, 4: 
      "Computing x^q mod kernel polynomial (degree %o)\n", 
      Degree(kernel_poly); 
    vtime SEA, 4: xpmx := Q!(Modexp(x,q,kernel_poly)-x);

    vprint SEA, 4: "Doing eigenvalue loop";
    lambda := 0;
    success := false;
    tyme := Cputime();
    lambda := lambda_prev;
    vprintf SEA, 4: "Computing IsEigenvalue: %o", lambda; 
    for mu in [0..ell-2] do
	test_value := Min(lambda,ell^n-lambda);
	if IsEigenvalue(E,test_value,xpmx,kernel_poly) then
            break;
        end if;
	lambda +:= ell^(n-1);
	vprintf SEA, 4: "..%o", lambda; 
    end for;
    vprint SEA, 4: "\nTime:", Cputime(tyme); 
    R := ResidueClassRing(ell^n);
    T`lambda := lambda;
    T`trace := Integers()!(lambda + (R!q)*(R!lambda)^-1);
    vprint SEA, 4: "Eigenvalue =", lambda, "mod", ell^n;
    vprint SEA, 4: "Trace =", T`trace, "mod", ell^n;
end procedure;

////////////////////////////////////////////////////////////////////////
//                                                                    //
//                        PSEUDO-BSGS BOUNDS                          //
//                                                                    //
////////////////////////////////////////////////////////////////////////

function ReplaceCheck(tup,tst,s,t)
    if tup[1] gt tst[2] then
	return true;
    elif tup[1] eq tst[2] and tup[2] gt tst[2] then
	return true;
    end if;
    return false;
end function;

function BSGSBounds(ell)
    /*
    {Returns optimal positive integers r, s, t, c such that with at
    most the exceptions, c and -c, that all values n in [1..ell-1]
    are assumed by the expressions i/j or -i/j where 1 <= i <= s,
    1 <= j <= t or by the expression i or -i with 1 <= i <= r.
    The value c = 0 is returned if there exists no exception}
    */
    n := ell div 2;
    r := 0;
    s := 0;
    t := 0;
    // S := [ [ Parent(<1,1>) | ] : i in [1..n] ];
    S := [ <ell,ell> : i in [1..n] ];
    B := Ceiling(Sqrt(ell-1));
    finish := [ 1 : i in [1..n] ];
    for k in [1..B] do
	if &+ finish le 1 then break k; end if;
	r := k; 
	finish[k] := 0;
	// Append(~S[k],<1,k>);
	S[k] := <1,k>;
    end for;
    j := 2;
    ibound := 1;
    for k in [2..ell div 2] do
	ibound +:= 1;
	for i in [1..ibound] do
	    if &+ finish le 1 then break k; end if;
	    if GCD(i,j) eq 1 then
		c := (i*InverseMod(j,ell)) mod ell;
		c := Min(c,ell - c);
		finish[c] := 0;
		// Append(~S[c],<ji,ii>);
		if ReplaceCheck(S[c],<j,i>,s,t) then
		    s := Max(s,i);
		    t := Max(t,j);
		    S[c] := <j,i>;
		end if;
	    end if;
	end for;
	ii := ibound + 1;
	j1 := ibound gt B select 1 else 2; 
	for ji in [j1..j] do
	    if &+ finish le 1 then break k; end if;
	    if GCD(ii,ji) eq 1 then
		c := (ii*InverseMod(ji,ell)) mod ell;
		c := Min(c,ell - c);
		finish[c] := 0;
		// Append(~S[c],<ji,ii>);
		if ReplaceCheck(S[c],<ji,ii>,s,t) then
		    s := Max(s,ii);
		    t := Max(t,ji);
		    S[c] := <ji,ii>;
		end if;
	    end if;
	end for;
	j +:= 1;
    end for;
    ex := Index(S,<ell,ell>);
    return r, s, t, ex;
end function;


