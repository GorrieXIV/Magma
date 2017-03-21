freeze;
// Computing zeta functions in families of hyperelliptic curves
// Deformation method - Odd characteristic case
// Implemented by Hendrik Hubrechts, KULeuven
// Version of 19 June 2006
//  some minor changes by mch - 07/06

// Supports in this version nonlinear deformations
// and base fields which are not prime


// Q = polynomial over finite field F in two variables, X and Y
//     monic of odd degree in X
//     F has odd characteristic
// y = (array of) non-zero element(s) of finite field Fq,
//     extension field of F

// This program works with the 1/sqrt(Q)^3 basis
// and uses Harrisons implementation for the Y=0 case and some
// intermediate steps
//
// Uses a naive lift for the p-adic numbers
//
// Verbose printing.
// Use: SetVerbose("JacHypCnt", 1or2); -> prints all comments


/////////////// Functions from FamHECMethods ////////////////////////////////////

function makingZeroXYP(poly,Qp,QpXYP,N)
   // Deletes 'zero modulo p^N' coefficients
   // Takes as input a polynomial or a power series in two variables,
   // output is a polynomial
   // Brings the accuracy level back to the original Qp precision
   // If possible, the result can be transformed in a univariate polynomial
   X := QpXYP.1; Y := QpXYP.2;
   Result := QpXYP!0; Temp := Qp!0;
   for i := 0 to Degree(poly, X) do
      for j := 0 to Degree(Coefficient(poly,X,i),Y) do
         Temp := MonomialCoefficient(poly,X^i*Y^j);
         Temp := Qp![Expand(x) : x in Eltseq(Temp)];
         if (Valuation(Temp) ge N) then Temp := 0; end if;
         Result := Result + Temp * X^i*Y^j;
   end for; end for;
   return Result;
end function;

function resultant(Q,g,Qp,N_1,R,QpXYP)
  // Computes the resultant of Q and derivative(Q,x) w.r.t. x
  // together with alpha and beta such that
  // resultant = alpha*Q + beta*derivative(Q,x)
  // This is just a classical XGCD algorithm
  X := R.1; d := Degree(Q,X);
  M := Matrix(R,2*d-1,2*d-1,[]); Nsmall := Matrix(R,2*d-2,2*d-2,[]);
  Qq := Derivative(Q,X);
  N := [Nsmall : k in [1..2*d-1]];
  for i := 1 to d-1 do  for j := 1 to 2*d-1 do
    M[i,j] := Coefficient(X^(d-1-i)*Q, X, (2*d-1-j));
  end for; end for;
  for i := d to 2*d-1 do  for j := 1 to 2*d-1 do
    M[i,j] := Coefficient(X^(2*d-1-i)*Qq, X, (2*d-1-j));
  end for; end for;
  for k := 1 to 2*d-1 do
    for i := 1 to k-1 do  for j := 1 to 2*d-2 do
      N[k][i,j] := M[i,j];
    end for; end for;
    for i := k+1 to 2*d-1 do  for j := 1 to 2*d-2 do
      N[k][i-1,j] := M[i,j];
  end for; end for; end for;
  r     := Determinant(M);
  alpha := &+[ (-1)^(k+1)*Determinant(N[k])*X^(d-1-k) : k in [1..d-1]];
  beta  := &+[ (-1)^(k+1)*Determinant(N[k])*X^(2*d-1-k) : k in [d..2*d-1]];
  r := makingZeroXYP(QpXYP!r, Qp, QpXYP, N_1-2*g);
  alpha := makingZeroXYP(QpXYP!alpha, Qp, QpXYP, N_1);
  beta := makingZeroXYP(QpXYP!beta, Qp, QpXYP, N_1);
  return r,alpha,beta;
end function;

function TeichmullerLift(t, q, N)
   // Computes the Teichmueller lift of t modulo p^N using Newton iteration
   // Takes q as the size of the residue field as input
   z := t;
   for i := 1 to Ceiling(Log(2,N)) do
      zF := z^(q-2); z := z - (zF*z-1)/((q-1)*zF); end for;
   return z;
end function;

function testResultant(y, Q)
   // Tests whether the resultant and y suffice for the algorithm
   // Returns an appropriate boolean and a string with the explanation
   R := Resultant(Q,Derivative(Q,Parent(Q).1),Parent(Q).1); 
   Ry := Evaluate(UnivariatePolynomial(R),y);
   if (Ry eq 0) then     return true, "Cannot continue, the parameter y case gives a reducible polynomial!!!"; end if;
   return false, "";
end function; 
function testResultantGeneric(r)
   // Tests whether the resultant suffices for the algorithm
   // Returns an appropriate boolean and a string with the explanation
   degree := Degree(r);
   lT := Valuation(LeadingCoefficient(r));
   cT := Valuation(Evaluate(r,0));
   if (degree eq 0) then return true, "Cannot continue, the resultant is a constant!!!"; end if;
   if (lT ge 1) then     return true, "Cannot continue, the resultant is not monic!!!"; end if;
   if (cT ge 1) then     return true, "Cannot continue, the parameter 0 case gives a reducible polynomial!!!"; end if;
   return false, "";
end function;

function liftCoeffs(p,f,FpXYP,ZpXYP);
   // Lifts the equation f from F(p^a)[X,Y] to Z(p^a)[X,Y]
   X := FpXYP.1; Y := FpXYP.2; x := ZpXYP.1; y := ZpXYP.2; 
   result := ZpXYP!0;
   for i := 0 to Degree(f,X) do  for j := 0 to Degree(f,Y) do
      result +:= ZpXYP!Eltseq(MonomialCoefficient(f,X^i*Y^j),FiniteField(p))*x^i*y^j;
   end for; end for;
   return result;
end function;

function subsQaQq(x,fa,Qp)
   // Puts fa from Qa into Qq with x as Qa.1 in Qq
   // Implements in fact the embedding Qa -> Qq, which seems not supported by Magma
   return Evaluate(PolynomialRing(Qp)!Eltseq(fa),x);
end function;

/*******************************************************************
 *******************************************************************

      KEDLAYA'S ALGORITHM (in ODD CHARACTERISTIC)

              Mike Harrison.
              
 (Adapted by Hendrik Hubrechts for use within deformation algorithm)
 (Returns the matrix of Frobenius up to a given accuracy, instead of
  the zeta function)

*******************************************************************
*******************************************************************/

LINEAR_LIMIT := 7;
ALWAYS_CUBE := true;  // Needed for deformation algorithm

function GetRing(R1,Q,prec)

    L<T> := LaurentSeriesRing(ChangePrecision(R1,prec));
    P1 := PolynomialRing(L);
    return quo<P1|P1!Q-T^-1>;

end function;

function myXGCD(p1,p2)

    // p1 and p2 are relatively prime integral polynomials over an
    // unramified pAdic field of bounded precision n.
    // It is assumed that the leading coeff of p1 is prime to p.
    // The function calculates and returns integral polynomials of
    // the same precision s.t. A*p1+B*p2 = 1 mod p^n.
    // Begins by lifting the Xgcd result over the Residue field and
    // iterates up mod p^i for 1 <= i <= n.
    R := Parent(p1);
    F,mp := ResidueClassField(IntegerRing(BaseRing(R)));
    S := PolynomialRing(F);
    p1r := S![mp(j) : j in Coefficients(p1)];
    p2r := S![mp(j) : j in Coefficients(p2)];
    _,Ar,Br := Xgcd(p1r,p2r);
    u := R!Ar; v := R!Br;
    A := u; B := v;
    delta := R!-1;
    p := Characteristic(F);
    for i in [1..BaseRing(R)`DefaultPrecision-1] do
        delta := (delta+u*p1+v*p2)/p;
        delr := S![mp(j) : j in Coefficients(delta)];
        v1 := (-Br*delr) mod p1r;
        v := R!v1;
        u := R!((-(delr+v1*p2r)) div p1r);
        /* NB. the simpler
          u := R!((-Ar*delr) mod p2r);
          v := R!((-Br*delr) mod p1r);
           doesn't necessarily work if p2 has leading
           coeff div by p, when deg p2r < deg p2.
            In this case, u*p1+v*p2 != -delta mod p if
           deg p1r+deg p2r <= deg delr (< deg p1+deg p2)
    */
        A +:= u*(p^i);
        B +:= v*(p^i);
    end for;
    return A,B;

end function;

function SigmaPowMat(M,m,n)

    // returns s^(n-1)(M)*s^(n-2)(M)*..*s(M)*M where M is
    // an m*m matrix over an unramified pAdic field and
    // s is the absolute Frobenius of that field. n >= 1.
    // Uses a basic left-right binary powering algorithm.

    if n eq 1 then return M; end if; //special case
    bits := Intseq(n,2);
    N := M;
    r := 1;
    for i := (#bits-1) to 1 by -1 do
        N := Matrix(m,[GaloisImage(x,r) : x in Eltseq(N)])*N;
        r *:= 2;
    if bits[i] eq 1 then
        N := Matrix(m,[GaloisImage(x,1) : x in Eltseq(N)])*M;
            r +:= 1;
    end if;
    end for;
    return N;

end function;

function FrobYInv(Q,p,N,x_pow,S,cube)

    // Computes p*(Frob y)^-1 (cube=false) or p*(Frob y)^(-3) (cube=true)
    // mod p^N.
    // This means calculating
    //     (1+((FrobQ)(x^p)-(Q(x))^p)*X^p)^(-1/2){resp(-3/2)}
    // to the required precision in S (S defined in Kedlaya fn).
    //
    // Starts by computing terms in the binomial expansion of the above
    // then uses Newton iteration. The first part computes the most
    // appropriate number <= LINEAR_LIMIT of terms for the Newton phase.
    // In the Newton phase, the power series (in T) coefficients of powers
    // of x are truncated noting that result mod p^t contains no non-zero
    // coefficients of T beyond T^(p*(t-1)).
    //
    // Q(x) is the defining polynomial for the hyperelliptic curve (y^2=Q(x))
    // and x_pow = x^(p-1) in S.

    R1 := BaseRing(BaseRing(S));
    T := BaseRing(S).1;
    E := 1 + (T^p)*(Evaluate(Parent(Q1)![GaloisImage(j,1):
            j in Coefficients(Q1)], x_pow*S.1) - Evaluate(Q1,S.1)^p)
                where Q1 is PolynomialRing(R1)!Q;
    // now compute E^(-1/2) (E^(-3/2) if cube) mod p^N
    // ( this is weaker than mod T^(p(N-1)+1) )
    // by "linear lift" followed by Newton iteration.

    //first backtrack to find starting point for Newton phase
    prec := N;
    adjs := [Booleans()|];
    while prec gt LINEAR_LIMIT do
        Append (~adjs,IsOdd(prec));
        if p eq 3 then
        prec := prec div 2;
    else
            prec := (prec+1) div 2;
        end if;
    end while;
    // now do the linear part
    Sc := GetRing(R1,Q,prec);
    Rc := BaseRing(BaseRing(Sc));
    u := Sc!1;
    Epow := u;
    E1 := Sc![BaseRing(Sc)!a : a in Coefficients(E)];
    half := cube select -(1/2) else (1/2);
    bincoeff := 1/1;
    for i in [1..prec] do
        bincoeff *:= (half-i)/i;
        Epow := (E1-1)*Epow;
    u := u + (Rc!bincoeff)*Epow;
    end for;
    delete Epow;
    // u is now the answer mod p^prec. Finish by Newton iteration
    // x -> (3*x - E*x^3)/2.
    if cube then E := E^3; end if;
    half := BaseRing(Parent(Q))!(1/2);
    if prec eq N then PolR := PolynomialRing(BaseRing(S)); end if;
    while prec lt N do
        tyme := Cputime();
    prec *:= 2;
        if adjs[#adjs] then
            prec +:= ((p eq 3) select 1 else -1);
        end if;
        Prune(~adjs);
        if prec lt N then
            Sc := GetRing(R1,Q,prec);
            E1 := Sc![BaseRing(Sc)!a : a in Coefficients(E)];
        else
            Sc := S; E1 := E;
        end if;
        T := BaseRing(Sc).1;
        PolR := PolynomialRing(BaseRing(Sc));
        u := Sc![BaseRing(Sc)!a : a in Coefficients(u)];
        v := Sc![j+O(T^(p*prec-(p-1))) : j in Coefficients(PolR!(u^2))];
        u := (3*u - E1*(u*v))*(BaseRing(BaseRing(Sc))!(1/2));
        // remove O(T^r) terms
        u := Sc![ elt<Parent(j)|v,coeffs,-1> where coeffs,v is
                  Coefficients(j) : j in Coefficients(PolR!u)];
        vprintf JacHypCnt, 3:
           "Reached precision %o   time = %o\n",prec,Cputime(tyme);
    end while;
    // now "clean" the result mod T^(pN-(p-1))
    u := S![ elt<Parent(j)|v,coeffs,-1> where coeffs,v is
       Coefficients(j+O(T^((p*(N-1))+1))) : j in Coefficients(PolR!(p*u))];
    return (u * T^(((cube select 3 else 1)*p) div 2));

end function;

function Convert(powTx,bdu,bdl,K)

    // Takes a differential powTx*(dx/y) where powTx is of the form
    //   p0(T) + p1(T)*x +... pr(T)*x^r
    //    (T := 1/y^2, pi(T) are finite-tailed Laurent series)
    // and returns [Ar,A(r+1),...],r where Ai = Coefficients(ai)
    //  powTx = ar(x)*T^r + a(r+1)(x)*T^(r+1) + ... (ai in K[x]).
    // K is the unramified pAdic coefficient field.
    // bdu,bdl are upper and lower bounds for non-zero powers of
    // T in {p0,p1,...}.

    vec := [PowerSequence(K)|];
    found_start := false;
    start_adj := 0;
    for i in [bdl..bdu] do
        v1 := [K!Coefficient(ser,i) : ser in Coefficients(powTx)];
    if not found_start then
        if &and[RelativePrecision(k) eq 0 : k in v1] then
            start_adj +:= 1;
        continue;
        else
            found_start := true;
        end if;
    end if;
    Append(~vec,v1);
    end for;
    return vec,bdl+start_adj;

end function;

function PrecDivDeriv(pol,d)

    // Used by ReduceB to avoid losing padic precision when dividing
    // polynomial Derivative(pol) by integer d (p may divide d).
    // If d isn't a padic unit, arbitrary "noise" is added to
    // restore full precision after the division.

    K := BaseRing(Parent(pol));
    p := Prime(K);
    val := Valuation(d,p);
    if val ne 0 then
        pol1 := Parent(pol)! ([K!0] cat
           [boo select
           O(UniformizingElement(K)^pow) else
           ChangePrecision(x,pow-v) where
       boo is ((RelativePrecision(x) eq 0) or (pow le v)) where
       v is Valuation(x) where
       pow is prec-Valuation(i,p) where
       x is Coefficient(pol,i):
            i in [1..Degree(pol)]]) where prec is K`DefaultPrecision + val;
    else
       pol1 := pol;
    end if;
    return ( Derivative(pol1)/d );

end function;

function ReduceA(polys,precs,n0)

    // Performs the reduction of
    // {a_(n0-1)(x)*y^(2*(n0-1)) + .. + a1(x)*y^2 + a0(x)}*(dx/y)
    // to canonical return_val *(dx/y) form.

    PolR := Parent(precs[1]);
    if IsEmpty(polys) then
        return PolR!0;
    end if;
    d := Degree(precs[1]);
    pol := PolR!polys[1];
    N := BaseRing(PolR)`DefaultPrecision;
    for k := (n0-1) to 0 by -1 do
        pol := ((k le (n0-#polys)) select PolR!0 else PolR!(polys[n0+1-k])) +
                  pol*precs[1];
    for j := (2*d-1) to d by -1 do
        lc := Coefficient(pol,j);
        if RelativePrecision(lc) ne 0 then
            pol := pol - ((PolR.1)^(j-d))*
                (ChangePrecision(lc,N)/((2*k-1)*d+2*(j+1))) *
                ((2*k+1)*precs[2]*PolR.1+2*(j+1-d)*precs[1]);
        end if;
    end for;
        pol := PolR![Coefficient(pol,i):i in [0..(d-1)]];
    end for;
    lc := Coefficient(pol,d-1);
    if RelativePrecision(lc) ne 0 then
        pol := pol - (ChangePrecision(lc,N)/d)*precs[2];
    end if;
    return pol;

end function;

function ReduceB(polys,precs,n0,cube)

    // Performs the reduction of
    // {a1(x)*(1/y^2) + .. a_n0(x)*(1/y^2n0)}*(dx/y^r)
    // to canonical return_val *(dx/y^r) form.
    // r = 1 if cube = false, else r = 3.

    PolR := Parent(precs[1]);
    if IsEmpty(polys) then
        return PolR!0;
    end if;
    divcase := (Valuation(LeadingCoefficient(precs[2])) gt 0);
    pol := PolR!polys[#polys];
    for k := (n0-1+#polys) to (cube select 2 else 1) by -1 do
        p1 := (pol*precs[4]) mod precs[1];
        if divcase then
           p2 := (pol-p1*precs[2]) div precs[1];
        else
           p2 := (pol*precs[3]) mod precs[2];
        end if;
        pol := ((k le n0) select PolR!0 else PolR!(polys[k-n0])) +
                   p2 + PrecDivDeriv(2*p1,2*k-1);
    end for;
    return pol;

end function;

function UpperCoeffs(M,g,ppow,e_val)

    // Calcs the sequence of the upper coefficients (x^g,..x^(2g))
    // of CharPoly(M) using the trace method. The magma intrinsic
    // could be used but this is slightly more efficient as only
    // Trace(M),Trace(M^2),..Trace(M^g) need be calculated rather
    // than Trace(M),..,Trace(M^(2g)).
    // If Nrows(M) = 2*g+1 then the extra eigenvalue of M, e_val,
    // is discarded. (e_val = q (1) if cube = false (true)).
    // The sequence [r(v)] is returned where, for a p-adic int v,
    // r(v) is the integer n s.t.|n|<ppow/2 and n=v mod ppow.

    pAd := pAdicField(Parent(M[1,1]));
    N := M;
    UCs := [pAd!1];   // coeffs (highest to lowest) of CharPoly(M)
    TrPows := [pAd|]; // [Trace(M),Trace(M^2),...]
    for i in [1..g] do
        Append(~TrPows,Eltseq(Trace(N))[1]);
        Append(~UCs, (- &+[TrPows[j]*UCs[i+1-j] : j in [1..i]])/i);
        if i lt g then N := N*M; end if;
    end for;
    if Nrows(M) ne 2*g then // original Q(x) of even degree
        for i in [1..g] do
            UCs[i+1] := UCs[i+1]+e_val*UCs[i];
        end for;
    end if;
    return [((2*uc gt ppow) select uc-ppow else uc) where uc is
              (IntegerRing()!x) mod ppow : x in UCs];

end function;

function Kedl1(poly,N_1,n,K)

    // Main function for the (odd char) Kedlaya algorithm.
    //  Computes the numerator of the zeta function for
    //       y^2 = poly (defined over over GF(p^n)).
    //  The cube boolean variable indicates which differential
    // basis is used for cohomological calculations -
    //   (dx/y), x(dx/y), x^2(dx/y), ... if cube = false
    //   (dx/y^3), x(dx/y^3), ...        if cube = true
    //  The 1st is the natural basis, but leads to a non-integral
    // transformation matrix if p is small compared to the genus.
    // The strategy is to use the first if this is not the case
    // unless the ALWAYS_CUBE value is true

    p := Characteristic(BaseRing(poly));
    d := Degree(poly)-1;
    g := d div 2;
    cube := true;
    if not ALWAYS_CUBE then
        if (IsEven(d) and p ge d) or  // deg=2*g+1
           (IsOdd(d) and p gt g) then // deg=2*g+2
            cube := false;
        end if;
    end if;
    N1 := N_1;
    N := N1 + Floor(Log(p,2*N1))+1;
    K := ChangePrecision(K,N);
    //K := UnramifiedExtension(pAdicField(p,N);
    R1 := quo<Integers(K)|UniformizingElement(K)^N>;
    Embed(BaseRing(Parent(poly)),ResidueClassField(R1));
    S := GetRing(R1,poly,N);
    x := S.1;
    precs := [PolynomialRing(K)!poly]; 
    Append(~precs,Derivative(precs[1]));
    A,B := myXGCD(precs[1],precs[2]);
    // A,B satisfy A*Q+B*Q'=1 where Q is the lift of poly to char 0.
    Append(~precs,A);
    Append(~precs,B);

    //Stage 1 - compute p*x^(p-1)*(y^Frob)^-1[3]
    vprintf JacHypCnt, 2:
      "Computing (y^Frobenius)^-%o ...\n",cube select 3 else 1;
    tyme :=Cputime();
    x_pow := x^(p-1);
    difl := FrobYInv(PolynomialRing(R1)!poly,p,N,x_pow,S,cube)*x_pow;
    x_pow := x_pow*x;
    vprintf JacHypCnt, 2: "Expansion time: %o\n",Cputime(tyme);

    //Stage 2 - loop to calculate the rows of the Frobenius matrix
    vprint JacHypCnt, 2: "Reducing differentials ...";
    R1 := quo<Integers(K)|UniformizingElement(K)^N1>;
    M := RMatrixSpace(R1,d,d)!0;
    i := 1;
    boundu := p*N+(p div 2)-1;
    S1 := PolynomialRing(BaseRing(S));
    vtime JacHypCnt, 2:
    while true do
        boundl := (p div 2) - Floor((i*p-1)/(d+1));
        polys,bot := Convert(S1!difl,boundu,boundl,K);
        diffr := ReduceA([polys[k] : k in [1..Min(1-bot,#polys)]],precs,-bot)+
      ReduceB([polys[k] : k in [Max(2-bot,1)..#polys]],precs,Max(bot,1),cube);
    M[i] := RSpace(R1,d)![R1!Coefficient(diffr,k) : k in [0..(d-1)]];
    if i eq d then break; end if;
    i +:= 1;
    difl := difl * x_pow;
    end while;

    vprint JacHypCnt, 2: "Computing Frobenius matrix by powering ...";
    vtime JacHypCnt, 2:
//    M := SigmaPowMat(M,d,n); 
// This step we cannot use in our deformation, as it interferes with
// the computation of F
    // Now change the precision to N1+Val(p,g!). The Val(p.. is needed
    // to add random noise as the characteristic polynomial calculation
    // uses the Trace method which involves dividing by 1,2,..g for the
    // top terms (later terms aren't needed) with a corresponding loss
    // in precision.
    N2 := N1 + Valuation(Factorial(g),p);
    if N2 gt N then ChangePrecision(~K,N2); end if;
    M := Matrix(K,M);
    if N2 gt N1 then
      M := Matrix(K,d,[ChangePrecision(K!x,N2-Valuation(x)) : x in Eltseq(M)]);
    end if;
    return M;

end function;

/////////////// Functions from FamHECMatrices ////////////////////////////////////

function matrixH(Q,g,alpha,beta,Qp,QpYP,QpXYP)
   H := Matrix(QpYP,2*g,2*g,[]); X := QpXYP.1; Y := QpXYP.2;
   for i := 1 to 2*g do // We go over the basis elements (hence the columns of H)
     // Determination of the nominator in Nabla(b_(i-1))
     NominatorH := X^(i-1)*Derivative(Q,Y);
     P := alpha*NominatorH; R := beta*NominatorH;
     NominatorH := -(3/2)*P - Derivative(R,X);
     // Reducing this nominator
     m := Degree(NominatorH,X); Qq := Derivative(Q,X);
     while(m ge (2*g)) do
       lc := LeadingCoefficient(NominatorH,X);
       if (m eq 2*g) then Half1 := 0; else
       Half1 := makingZeroXYP((m-2*g)/(m-3*g-1/2)*(X^m-X^(m-(2*g+1))*Q),Qp,QpXYP,Precision(Qp)-2*g); end if;
       Half2 := makingZeroXYP(1/(2*m-6*g-1)*((2*g+1)*X^m-X^(m-2*g)*Qq),Qp,QpXYP,Precision(Qp)-2*g);
       NominatorH := makingZeroXYP((NominatorH - LeadingTerm(NominatorH,X)) + lc*(Half1 - Half2),Qp,QpXYP,Precision(Qp)-2*g);
       m := Degree(NominatorH,X);
     end while;
     // Filling H with the resulting polynomial
     for j := 1 to 2*g do
        H[j,i] := QpYP!UnivariatePolynomial(Coefficient(NominatorH,X,j-1)); end for;
   end for; h := 0;
   // Determining the degree of H
   for i := 1 to 2*g do  for j := 1 to 2*g do
     h := Maximum(h,Degree(H[j,i]));
   end for; end for;
   // Splits the matrix H in an array of matrices
   HTemp := Matrix(Qp,2*g,2*g,[]); HSplit := [HTemp : k in [1..h+1]];
   for k := 0 to h do
      for i := 1 to 2*g do  for j := 1 to 2*g do
         HSplit[k+1][i,j] := Coefficient(H[i,j],k);
   end for; end for; end for;
   return HSplit, h, H;
end function;

function matrixC(g,H,h,r,N_2,Qp,QpFinal,QpYFinal)
   Temp := Matrix(Qp,2*g,2*g,[]);
   // Using recursion to compute the array C
   // C is represented as C[1..N_2] representing C_0 .. C_(N_2-1)
   C := [Temp : k in [1..N_2]]; C[1] := ScalarMatrix(2*g,Qp!1);
   rho := Degree(r); r0 := Coefficient(r,0);
   for i := 1 to N_2-1 do CTemp1 := Temp; CTemp2 := Temp;
      for j := 0 to Minimum(i-1,h) do
         CTemp1 := CTemp1 + H[j+1]*C[i-j]; end for;
      for j := 1 to Minimum(i-1,rho) do
         CTemp2 := CTemp2 + Coefficient(r,j)*(i-j)*C[i-j+1]; end for;
      for j := 1 to 2*g do  for k := 1 to 2*g do
         C[i+1][j,k] := Expand(-((CTemp1[j,k]+CTemp2[j,k]) / (i*r0))); end for; end for;
   end for;
   // Transforming C into (2*g)^2 arrays of entries of QpFinal, named Cc
   Temp := [QpFinal!0 : k in [1..N_2]]; Cc := [Temp : k in [1..4*g^2]];
   for i := 1 to N_2 do  for j := 1 to 4*g^2 do
      Cc[j][i] := QpFinal!C[i][((j-1) div (2*g))+1,((j-1) mod (2*g))+1]; end for; end for;
   // Substituting these arrays in a matrix of power series
   C := Matrix(QpYFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      C[i,j] := QpYFinal!Cc[2*g*(i-1)+j]; end for; end for;
   return C;
end function;

function inverseC(p,a,g,H,h,r,N_2,Qp,QpFinal,QpYFinal)
   Temp := Matrix(Qp,2*g,2*g,[]); N := ((N_2-1) div p)+1;
   // It's cheaper to compute Frob on H and r instead of on C at the end
   if (a gt 1) then
      for k := 1 to h+1 do for i := 1 to 2*g do for j := 1 to 2*g do
      H[k][i,j] := GaloisImage(H[k][i,j],1); end for; end for; end for;
      r := Parent(r)![GaloisImage(ri,1) : ri in Eltseq(r)];
   end if;
   // Using recursion to compute the array Ci, named C as above
   // Ci is represented as Ci[1..N] representing Ci_0 .. Ci_(N-1)
   C := [Temp : k in [1..N]]; C[1] := ScalarMatrix(2*g,Qp!1);
   rho := Degree(r); r0 := Coefficient(r,0);
   for i := 1 to N-1 do CTemp1 := Temp; CTemp2 := Temp;
      for j := 0 to Minimum(i-1,h) do
         CTemp1 := CTemp1 - C[i-j]*H[j+1]; end for;
      for j := 1 to Minimum(i-1,rho) do
         CTemp2 := CTemp2 + Coefficient(r,j)*(i-j)*C[i-j+1]; end for;
      for j := 1 to 2*g do  for k := 1 to 2*g do
         C[i+1][j,k] := Expand(-((CTemp1[j,k]+CTemp2[j,k]) / (i*r0))); end for; end for;
   end for;
   // Transforming Ci into (2*g)^2 arrays of entries of QpFinal, named Cc
   // This incorporates the change Y -> Y^p
   Temp := [QpFinal!0 : k in [1..N_2]]; Cc := [Temp : k in [1..4*g^2]];
   for i := 1 to N_2 do  for j := 1 to 4*g^2 do
      if (((i-1) mod p) eq 0) then
         Cc[j][i] := QpFinal!C[Integers()!((i-1)/p)+1][((j-1) div (2*g))+1,((j-1) mod (2*g))+1];
      else Cc[j][i] := 0; end if;
   end for; end for;
   // Substituting these arrays in a matrix of power series
   C := Matrix(QpYFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      C[i,j] := QpYFinal!Cc[2*g*(i-1)+j]; end for; end for;
   return C;
end function;

function Frob0(Q,a,g,N,QpFinal)
   // Computing Q0
   Q0 := UnivariatePolynomial(Evaluate(Q,Parent(Q).2,0));
   // Here we use Harrisons algorithm
   M00 := Kedl1(Q0,N,a,QpFinal); 
   M0 := Matrix(QpFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      M0[i,j] := QpFinal!M00[i,j]; end for; end for;
   return Transpose(M0);
end function;

function FrobY(r,M,H,HH,h,F0,g,p,a,N_2,Qp,QpFinal,QpYFinal)
   // Idea: solve r*rsigma*dF/dY + (rsigma*H-M*rsigma*rdot)*F = r*F*Hsigma*p*Y^(p-1) 
   // recursively. This F is r^M times the actual small Frobenius
   // 'Split' means a matrix of power series split up in an array of matrices
   // Computing rsigma and t := r*rsigma
   r0M := Evaluate(r,0)^M;
   rsigma := [Qp!0 : k in [0..p*Degree(r)]];
   if (a gt 1) then
      for i := 0 to Degree(r) do rsigma[p*i+1] := GaloisImage(Eltseq(r)[i+1],1); end for;
      else for i := 0 to Degree(r) do rsigma[p*i+1] := Eltseq(r)[i+1]; end for; end if;
   rsigma := Parent(r)!rsigma;
   t := r*rsigma; t1 := Degree(t); 
   // Computing rsigmaH = rsigma*H-M*rsigma*rdot*I, split
   temp1 := rsigma*HH - M*rsigma*Derivative(r); temp2 := Matrix(Qp,2*g,2*g,[]); 
   h1 := p*Degree(r)+Maximum(h,Degree(r)-1);
   rsigmaH := [temp2 : k in [0..h1]];
   for i := 1 to 2*g do  for j := 1 to 2*g do
      temp3 := Eltseq(temp1[i,j]); 
      for k := 0 to Degree(temp1[i,j]) do
         rsigmaH[k+1][i,j] := temp3[k+1];
      end for; end for; 
   end for; 
   // Computing rHsigma = r*Hsigma, split
   for i := 1 to 2*g do for j := 1 to 2*g do 
      temp1 := Eltseq(HH[i,j]); temp2 := [Qp!0 : k in [0..p*Degree(HH[i,j])]];
      for k := 0 to Degree(HH[i,j]) do 
         if (a gt 1) then temp2[p*k+1] := GaloisImage(temp1[k+1],1);
            else temp2[p*k+1] := temp1[k+1]; end if; end for;
      HH[i,j] := r*Parent(HH[i,j])!temp2; end for; end for;
   h2 := Degree(r)+p*h; temp2 := Matrix(Qp,2*g,2*g,[]);
   rHsigma := [temp2 : k in [0..h2]];
   for i := 1 to 2*g do  for j := 1 to 2*g do
      temp3 := Eltseq(HH[i,j]); 
      for k := 0 to Degree(HH[i,j]) do
         rHsigma[k+1][i,j] := temp3[k+1];
      end for; end for; 
   end for; 
   // Computing F(Y), split, using recursion
   F := [temp2 : k in [0..N_2-1]]; F[1] := F0*r0M;
   trow := Eltseq(t); t0 := trow[1];
   for k := 0 to N_2-2 do Ftemp1 := temp2; Ftemp2 := temp2; Ftemp3 := temp2;
      for j := 0 to Minimum(k-p+1,h2) do
         Ftemp1 +:= F[k-p-j+2]*rHsigma[j+1]; end for;
      for j := 0 to Minimum(k,h1) do
         Ftemp2 +:= rsigmaH[j+1]*F[k-j+1]; end for;
      for j := 1 to Minimum(k,t1) do
         Ftemp3 +:= trow[j+1]*(k-j+1)*F[k-j+2]; end for;
      for i := 1 to 2*g do  for j := 1 to 2*g do
         F[k+2][i,j] := Expand((p*Ftemp1[i,j]-Ftemp2[i,j]-Ftemp3[i,j])/((k+1)*t0));
      end for; end for;
   end for;
   // Conversion of F(Y) to a matrix of power series
   Temp := [QpFinal!0 : k in [1..N_2]]; Ff := [Temp : k in [1..4*g^2]];
   for i := 1 to N_2 do  for j := 1 to 4*g^2 do
      Ff[j][i] := QpFinal!F[i][((j-1) div (2*g))+1,((j-1) mod (2*g))+1]; end for; end for;
   F := Matrix(QpYFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      F[i,j] := QpYFinal!Ff[2*g*(i-1)+j]; end for; end for;
   return F; 
end function;

///////////// main function ///////////////////////////////////////////

ALTERNATE_SOLUTION := true;

function zetaFunctionDeformationInternal(Q,Y,p,Fq,a,n,g,kappa,M,factor)
    T1 := Cputime();

   // Creation of the constants.
   rho := Degree(Resultant(Q,Derivative(Q,Parent(Q).1),Parent(Q).1),2);
   error if (rho le 0),
      "Cannot continue: resultant mod p is a constant.";
   N_0 := Ceiling(n*g*a/2+(2*g+1)*Log(p,2));
   N_2 := rho*(M+2)*factor;
   N_3 := g*(2*Ceiling(Log(p,N_2))+Ceiling(Log(p,N_2/p)));
   N_4 := N_3 div p + 1;
   N_6 := 3*g*(Ceiling(Log(p,N_2))+Ceiling(Log(p,N_2/p)));
   N_1 := N_0+N_3+N_4+N_6;
   N_final := N_0+N_6;
   vprintf JacHypCnt, 2: "p = %o, a = %o, g = %o, n = %o, kappa = %o, rho = %o\n",p,a,g,n,kappa,rho;
   vprintf JacHypCnt, 2: "N_0 = %o, N_1 = %o, N_final = %o, M = %o, N_2 = %o\n\n",N_0,N_1,N_final,M,N_2;

   // Creation of big rings/fields
   Qp   := pAdicField(p,N_1); Zp := IntegerRing(Qp); Qp1 := Qp;
   if (a gt 1) then  // Computing in a degree one extension of Qp is slower than in Qp
      fa := DefiningPolynomial(BaseRing(Parent(Q)),FiniteField(p));
      Qp := UnramifiedExtension(Qp,fa);  Zp := IntegerRing(Qp); end if;
   ZpY  := PowerSeriesRing(Zp,N_2);      QpY  := PowerSeriesRing(Qp,N_2);
   ZpXY := PolynomialRing(ZpY);          QpYP := PolynomialRing(Qp);
   ZpXYP := PolynomialRing(Zp,2);        QpXYP := PolynomialRing(Qp,2);
   QpFinal := Qp; QpFinal := ChangePrecision(QpFinal,N_final);
   QpYFinal := PowerSeriesRing(QpFinal,N_2);
   QpYPFinal := PolynomialRing(QpFinal); X := QpXYP.1;
   // Advantage of polynomial rings ..P : objects are smaller, computations exact
   // Advantage of power series rings   : computations are faster, less exact

   // Lifting Q to char 0 (naive) and computing r, alpha, beta
   Qfinchar := Q;    // To check the result at the end
   Q := liftCoeffs(p,Q,Parent(Q),ZpXYP);
   r, alpha, beta := resultant(Q,g,Qp,N_1,ZpXYP,QpXYP);
   Q := QpXYP!Q; R := UnivariatePolynomial(r);
   // Checking some necessary conditions on the resultant
   check, comment := testResultantGeneric(R);
   error if check, comment;
   // In fact we also have to check that r is not 'hidden non-monic'...
   vprintf JacHypCnt:
      "# Algebraic structures and resultant computed, time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computation of the matrix H (split) and its degree h, HPoly is the polynomial version
   H, h, HPoly := matrixH(Q,g,alpha,beta,Qp,QpYP,QpXYP);
   vprintf JacHypCnt: "# H computed,    time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computation of F(0)
   vprint JacHypCnt: "Applying Kedlaya over the base field";
   F0 := Frob0(Qfinchar,a,g,N_final,QpFinal);
   vprintf JacHypCnt: "# F(0) computed, time %o\n",Cputime(T1);
   T1 := Cputime();

// If ALTERNATE_SOLUTION is set to true, we use Tsuzuki's alternative
// way of computing F(Y), which is faster
// It is adapted to compute the analytic continuation of F(Y) at once
if ALTERNATE_SOLUTION then
   // Computation of r^M*F(Y)
   FY := FrobY(UnivariatePolynomial(r),M,H,HPoly,h,F0,g,p,a,N_2,Qp,QpFinal,QpYFinal);
   vprintf JacHypCnt: "# r^M * F(Y) computed,             time %o\n",Cputime(T1);
   T1 := Cputime();
else
   // Computation of the matrix C
   C := matrixC(g,H,h,R,N_2,Qp,QpFinal,QpYFinal);
   vprintf JacHypCnt: "# C computed,    time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computation of the inverse of C and Frobenius of the inverse
   Cip := inverseC(p,a,g,H,h,R,N_2,Qp,QpFinal,QpYFinal);
   vprintf JacHypCnt: "# Cip computed,  time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computation of F(Y)
   FY := C*F0*Cip;
   vprintf JacHypCnt: "# F(Y) computed, time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computation of analytic continuation of F(Y)
   RMP :=(QpYPFinal!R)^M; RM := QpYFinal!RMP; // Necessary to get some precision in RM
   for i := 1 to 2*g do  for j := 1 to 2*g do
      FY[i,j] := FY[i,j] * RM; end for; end for;
   vprintf JacHypCnt: "# Continuation of F(Y) computed,   time %o\n",Cputime(T1);
   T1 := Cputime();
end if;

   // Defining the field Qq, by lifting the defining polynomial of Fq over its primefield
   QpFinal := ChangePrecision(Qp1,N_final); QpYP := PolynomialRing(QpFinal); 
   minPol := QpYP!DefiningPolynomial(Parent(Y[1]),FiniteField(p));
   Qq  := UnramifiedExtension(QpFinal, minPol); QqYP := PolynomialRing(Qq);

   // Here we compute an embedding of Qp = Q_{p^a} in Qq
   if (a gt 1) then
      Fq := Parent(Y[1]); Fa := BaseRing(Parent(Qfinchar));
      minPolFa := QqYP!PolynomialRing(Integers())!DefiningPolynomial(Fa,FiniteField(p));
      Fa1inFn := Fq!Fa.1; 
      // s is the image of Qp.1 in Qq
      s := HenselLift(minPolFa,Qq!Eltseq(Fa1inFn,FiniteField(p)),N_final);
   end if;
   vprintf JacHypCnt: "# Qq and Qa -> Qq computed,        time %o\n",Cputime(T1);
   T1 := Cputime();

   // Changing FY and R from being defined over Qa to a definition over Qq
   if (a gt 1) then
      QqY := PowerSeriesRing(Qq,N_2);
      FY1 := Matrix(QqY,2*g,2*g,[]);
      for i := 1 to 2*g do  for j := 1 to 2*g do
         FY1[i,j] := QqY![subsQaQq(s,coef,QpFinal) : coef in Eltseq(FY[i,j])];
      end for; end for; FY := FY1;
      R := QqY![subsQaQq(s,fa,QpFinal) : fa in Eltseq(R)];
      vprintf JacHypCnt:
         "# R, FY over Qa -> R, FY over Qq,  time %o\n",Cputime(T1);
      T1 := Cputime();
   else R := QqYP!QpYP!R; 
   end if;
  
   // Here we go over the sequence of y-values
   result := [PolynomialRing(Integers())!0 : i in [1..#Y]];
   text   := ["" : i in [1..#Y]];
   for k := 1 to #Y do T1 := Cputime(); y := Y[k];
   vprintf JacHypCnt: "Working on y-value number %o\n", k;
   
   // Checking if y is valid
   check, comment := testResultant(y,Qfinchar);
   error if check, "Parameter number ",k," doesn't give a HEC\n";

   // Computing the Teichmueller lift z of y
   t := Qq!Eltseq(y,FiniteField(p));
   z := TeichmullerLift(t, p^(a*n), N_final);
   vprintf JacHypCnt: "# Teichmueller lift of y computed, time %o\n",Cputime(T1);
   T1 := Cputime();

   // Substituting y in F(Y) in Qq, divide appropriately
   Fy := Matrix(Qq,2*g,2*g,[]); Ry := Evaluate(R,z); RyM := 1/Ry^M;
   for i := 1 to 2*g do  for j := 1 to 2*g do
      Fy[i,j] := Evaluate(FY[i,j],z) * RyM;
   end for; end for;
   vprintf JacHypCnt: "# F(y) computed, time %o\n",Cputime(T1);
   T1 := Cputime();

   // Computing F
   F := Transpose(SigmaPowMat(Transpose(Fy),2*g,a*n)); 
   vprintf JacHypCnt: "# F computed,    time %o\n\n",Cputime(T1);

   // Computing the characteristic polynomial as in Harrisons implementation
   N := N_0 + Valuation(Factorial(g),p); q := p^(a*n);
   Mm := Matrix(Qq,2*g,[ChangePrecision(Qq!x,N-Valuation(x)) : x in Eltseq(F)]);
   UCoeffs := UpperCoeffs(Mm,g,p^N_0,1);
   CharP := PolynomialRing(IntegerRing())!
                 ([UCoeffs[i]*q^(g+1-i): i in [1..g]] cat Reverse(UCoeffs));
   f0 := Parent(CharP)!Reverse(Coefficients(CharP));

   // Checking the result with the Jacobian
   T1 := Cputime();
   FqX := PolynomialRing(Fq); X := FqX.1;
   Qy := FqX!0; Qfc := Qfinchar; Rr := Parent(Qfinchar);
   for i := 0 to Degree(Qfc,Rr.1) do
      Qy := Qy + Evaluate(UnivariatePolynomial(Coefficient(Qfc,Rr.1,i)),y)*X^i;
   end for;
   J := Jacobian(HyperellipticCurve(Qy));
   O := Zero(J); order := Evaluate(f0,1);
   P := Random(J); fail := false;
   if (order*P ne O) then
      fail := true; vprint JacHypCnt: "Result not OK, trying M := 2*M";
      else vprint JacHypCnt: "Check OK, result is (presumably) correct";
   end if;
   vprintf JacHypCnt: "Time used to check result : %o\n\n",Cputime(T1);

   // Returning the result
   if (fail) then return -1, "M too small"; end if;
   result[k] := f0; text[k] := "All done";
   end for;
   return result, text;

end function;

////////////////// Intrinsics ///////////////////////////////////////

// Q = polynomial over finite field F in two variables, X and Y
//     monic of odd degree in X
//     F has odd characteristic
// y = (array of) non-zero element(s) of finite field Fq,
//     extension field of F
intrinsic EulerFactorsByDeformation(Q::RngMPolElt,Y::SeqEnum)->SeqEnum
{ For Q(x,z) a 2-variable polynomial over a finite field k of odd char.
  and Y a sequence of values in K, a finite extension of k, returns
  the sequence of Euler factors of the hyperelliptic curves
  y^2=Q(x,v) for v in Y.}

   T0 := Cputime();

   // Handling the presence of sequences
   require #Y gt 0:
	"Argument 2 must be a non-empty sequence";
   Fq := Universe(Y);

   // Creation of the induced input and checking of some conditions
   PQ := Parent(Q); Fp := BaseRing(PQ);
   p  := Characteristic(Fp);
   Kp := GF(p);
   require (Type(Fp) eq FldFin) and (Rank(PQ) eq 2):
      "Argument 1 must be a 2-variable polynomial over a finite field";
   require p ne 2:
      "Base field must not have characteristic 2.";
   require (Type(Fq) eq FldFin) and (p eq Characteristic(Fq)) and
   		IsDivisibleBy(Degree(Fq,Kp),Degree(Fp,Kp)):
      "Universe of argument 2 must be an extension field of ",
      "the base field of argument 1";
   require &and[y ne 0: y in Y]:
       "Argument 2 may not contain zero as a parameter value";
   require Degree(Fp,Kp) eq Degree(Fp):
    "Base field of argument 1 must be a simple extension of its prime field.";
   require IsOdd(Degree(Q,PQ.1)) and (Degree(Q,PQ.1) ge 3):
      "Argument 1 must be of odd degree >= 3 in its first variable.!";
   require LeadingCoefficient(Q,PQ.1) eq 1 :
      "Argument 1 must be monic in its first variable.";

   Embed(Fp,Fq);
   a  := Degree(Fp,FiniteField(p)); n := Degree(Fq,Fp); kappa := Degree(Q,PQ.2);
   g  := Integers()!((Degree(Q,PQ.1)-1)/2);

   // Trying over increasing M
   M := Ceiling(1.5*n)+10; M := Ceiling(M*(p/3)*g*a*(1+Floor(Log(20,n))/10)); factor := 1;
   repeat
      vprintf JacHypCnt: "Trying at precision %o\n",M;
      result, text := zetaFunctionDeformationInternal(Q,Y,p,Fq,a,n,g,kappa,M,factor);
      M := Ceiling(1.5*M); factor := 2;
   until (Category(result) eq SeqEnum);
   vprintf JacHypCnt: "Total time : %o seconds\n\n",Cputime(T0);

   return result;

end intrinsic;

intrinsic ZetaFunctionsByDeformation(Q::RngMPolElt,Y::SeqEnum)->SeqEnum
{ For Q(x,z) a 2-variable polynomial over a finite field k of odd char.
  and Y a sequence of values in K, a finite extension of k, returns
  the sequence of Zeta functions of the hyperelliptic curves
  y^2=Q(x,v) for v in Y.}

   efs := EulerFactorsByDeformation(Q,Y);
   q := #Universe(Y);
   den := (1-X)*(1-q*X) where X is Universe(efs).1;
   return [ef/den:ef in efs];

end intrinsic;

intrinsic JacobianOrdersByDeformation(Q::RngMPolElt,Y::SeqEnum)->SeqEnum
{ For Q(x,z) a 2-variable polynomial over a finite field k of odd char.
  and Y a sequence of values in K, a finite extension of k, returns
  the sequence of orders of the Jacobians of the hyperelliptic curves
  y^2=Q(x,v) for v in Y.}

   efs := EulerFactorsByDeformation(Q,Y);
   return [Evaluate(ef,1):ef in efs];

end intrinsic;
