///////////////////////////////////////////////
// This program is made by Hendrik Hubrechts //
// Postdoc F.W.O. at the K.U.Leuven, Belgium //
///////////////////////////////////////////////
// It computes the trace of Frobenius        //
//   (and hence the zeta function and order) //
// of any elliptic curve over a finite       //
// field                                     //
///////////////////////////////////////////////
// It uses Monsky-Washnitzer cohomology      //
// combined with deformation, as explained   //
// in "Quasi-quadratic point counting on     //
//    elliptic curves using rigid cohomology"//
///////////////////////////////////////////////
///////////////////////////////////////////////
// Use of the program: let E be an           //
// elliptic curve over a finite field        //
//   > t := ECDeformationTrace(E);           //
// returns                                   //
//   t as the trace of Frobenius             //
///////////////////////////////////////////////
// Under some conditions on the field        //
// (it has to be small) the built-in Magma   //
// algorithm is used                         //
///////////////////////////////////////////////
///////////////////////////////////////////////
freeze;




//////////////////////////////////////////////////////
//////////////////////////////////////////////////////
//////// Functions for Teichmuller arithmetic ////////
//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

function Frobp(z,R,n,Qq,p)
  // Computes Frobenius of z, where R is a Z/p^N[x], n is the
  // degree of the extension and Qq the quotient ring of degree n
  if (z eq 0) then return z; end if;
  z := Eltseq(z); F1 := [0 : i in [1..p*#z]];
  for i := 1 to #z do F1[p*i-(p-1)] := z[i]; end for;
  return Qq!F1;
end function;

function ASRoot(alpha,beta,gamma,N,p,ZX,ZNX,ZNXq,Fq,n,alphai,phi)
  // Conditions: ZX := Z[X]; ZNX := Z(p^N)[X]; ZNXq := Z(p^N)[X]/phi(X)
  // alpha, beta, gamma in ZNX, alpha unit, ord(beta)>0
  // Fq := finite field, n = extension degree
  // alphai = -1/alpha in Fq
  // Gives solution van alpha*sigma(x) + beta*x + gamma = 0 mod p^N
  // Based on code in Fré's thesis, originally by Harley
  if (N eq 1) then
    x := Fq!Eltseq(ZX!gamma)*alphai;
    x := Frobenius(x,-1);
    return ZNX!ZX!Eltseq(x);
  else
    N1 := Ceiling(N/2); M := N-N1;
    ZN1 := Integers(p^N1); ZN1X := PolynomialRing(ZN1); ZN1Xq := quo<ZN1X|phi>;
    x1 := ZNX!ASRoot(ZN1X!alpha,ZN1X!beta,ZN1X!gamma,N1,p,ZX,ZN1X,ZN1Xq,Fq,n,alphai,phi);
    x1sigma := ZNX!Frobp(x1,ZNX,n,ZNXq,p);
    gamma1 := ZNX![Integers()!i/p^N1 : i in Eltseq(ZNXq!(alpha*x1sigma+beta*x1+gamma))];
    Delta1 := ZNX!ASRoot(ZN1X!alpha,ZN1X!beta,ZN1X!gamma1,M,p,ZX,ZN1X,ZN1Xq,Fq,n,alphai,phi);
    return (x1+p^N1*Delta1);
  end if;
end function;

function NewtonII(A,B,C,D,X,N,n,p,Z,ZX,ZNX,ZNXq,Fq,Dyi,phi)
  // Newtonlifts a solution of
  //   A*x*xs + B*xs + C*x + D = 0 mod p^N, where xs = sigma(x), X is solution mod p
  // n = ext degree, p = prime, phi = Teichmuller modulus
  // ZX = Z[X], Fq  = finite field, Dyi = 1/Fq!(Ax+B)
  // Based on Fré's code in his thesis, originally by Harley
  if (N eq 1) then
    return X;
  else
    N1 := Ceiling(N/2);
    ZN1 := Integers(p^N1); ZN1X := PolynomialRing(ZN1); ZN1Xq := quo<ZN1X|phi>;
    x1 := ZNX!NewtonII(ZN1X!A,ZN1X!B,ZN1X!C,ZN1X!D,ZN1X!X,N1,n,p,Z,ZX,ZN1X,ZN1Xq,Fq,Dyi,phi);
    y1 := ZNX!Frobp(x1,ZNX,n,ZNXq,p);
    V  := ZN1X![Z!i/p^N1 : i in Eltseq(ZNXq!(A*x1*y1+B*y1+C*x1+D))];
    Dx := ZN1X!ZNXq!(A*y1+C);
    Dy := ZN1X!ZNXq!(A*x1+B);
    D1 := ZNX!ASRoot(Dy,Dx,V,N1,p,ZX,ZN1X,ZN1Xq,Fq,n,-Dyi,phi);
    return (x1 + p^N1*D1);
  end if;
end function;

// Internal function
function TeichmuellerLiftSST(a,Qq)
  Z := Integers(); p := Characteristic(Parent(a));
  ZX := PolynomialRing(Z); N := Precision(Qq);
  f := ZX!DefiningPolynomial(Qq); n := Degree(f);
  l := 4; // We take p^l at a time
  // If n/l eq 0 then t remains in ZX and the large power at the end consumes all memory
  if Floor(n/l) eq 0 then l := 1; end if;
  t := ZX!Eltseq(a);
  Precision := 1; 
  for i := 1 to Maximum(Floor(n/l),1) do
    Precision +:= l;
    Zi := Integers(p^Minimum(Precision,N)); ZiX := PolynomialRing(Zi);
    ZiXq := quo<ZiX|f>; t := ZiXq!ZiX!ZX!t;
    t := t^(p^l);
  end for; 
  t := t^(p^(n-l*Floor(n/l))); 
  t := ZX!Eltseq(t);
  return Qq!Eltseq(t);
end function;

// Computes the Teichmuller modulus lift of f (an inertial polynomial modulo p) with precision N.
// The polynomial f can be defined over Integers() or over GF(p).
// Uses the algorithm of Satoh, Skjernaa and Taguchi.
// The output is a polynomial over the Integers().
function TeichmullerModulusSST(f,N,p)
  ZNX := PolynomialRing(Integers(p^N)); ZX := PolynomialRing(Integers());
  f := ZX!f; R := quo<ZNX|f>; n := Degree(f);
  Qq := UnramifiedExtension(pAdicQuotientRing(p,N),f);
  Fq := ResidueClassField(Qq);
  psi := TeichmuellerLiftSST(Fq.1, Qq);
  A := ZNX!ZX!Eltseq(psi);
  G := f; i := 1;
  S := ZNX!ZX!Eltseq(Evaluate(Derivative(f),Fq.1)^(-1));
  F := ZNX!f; G := F; C := ZNX.1; dF := Derivative(F);
  ring1 := quo<ZNX|f>; A := ring1!A;
  while(i lt N) do
    V := Evaluate(G,A);
    ring := quo<ZNX|G>; C := ring!Eltseq(C); U := ZNX!Evaluate(V,C);
    G -:= U;
    ring := quo<ZNX|G>; C := ring!Eltseq(C); S := ring!Eltseq(S);
    S *:= 2-S*Evaluate(dF,C);
    C -:= Evaluate(F,C)*S;
    S *:= 2-S*Evaluate(dF,C);
  i *:= 2; end while;
  return ZX!G;
end function;





///////////////////////////////////////////////////////
///////////////////////////////////////////////////////
//////// Functions for p-adic norm computation ////////
///////////////////////////////////////////////////////
///////////////////////////////////////////////////////

// Gives [Trace(1),Trace(X),Trace(X^2),..]
function ComputeTraces(minPol,ZN)
  n := Degree(minPol); if n eq 1 then return [1]; end if;
  M := Eltseq(minPol); // M0,M1,M2,...,Mn
  trace := [ZN!n : i in [0..n-1]]; trace[1 +1] := -M[n-1 +1];
  for i := 2 to n-1 do
    trace[i +1] := -i*M[n-i +1] - &+[ trace[i-j +1]*M[n-j +1] : j in [1..i-1] ];
  end for;
  return trace;
end function;

// Gives exp(p) mod p^N
function ExponentialOfP(p,N)
  // Choose I such that I > N + I/(p-1), for p = 3, 5, 7
  I := Ceiling((p-1)*N/(p-2)); expP := 1; Z := Integers(); ZN := Integers(p^I);
  pI := 1; iFactorial := 1; 
  for i := 1 to I-1 do
    iFactorial := (i*iFactorial) mod p^I;
    if iFactorial eq 0 then break; end if;
    pI *:= p;
    expP +:= (ZN!(pI/iFactorial));
  end for;
  return (Z!expP) mod p^N;
end function;

// Gives exp(a) mod p^N, p|a is required
function Exponential(a,ep,p,N)
  return (Integers(p^N)!ep) ^ Integers()!(Integers()!a/p);
end function;

// Gives Log(a) mod p^N, where a=1 mod p, all over ZN[X]/minPol
function Logarithm(a,p,N,minPol)
  k := Ceiling(Sqrt(N)); ZN := Integers(p^N); ZNk := Integers(p^(N+k+2)); ZNX := PolynomialRing(ZN);
  ZNkX := PolynomialRing(ZNk); ZNkXq := quo<ZNkX | minPol>;
  a := ZNkXq!Eltseq(a); a := a^(p^k)-1;
  numerator := a; log := 0;
  for i := 1 to N+k do // Stops when 0 is reached
    temp := (-1)^(i-1) * ZNkX![ZNk!(Integers()!x/i) : x in Eltseq(numerator)];
    if temp eq 0 then break; end if;
    log +:= temp; numerator *:= a;
  end for;
  return ZNX![ZN!(Integers()!x/p^k) : x in Eltseq(log)];
end function;

// Computes the trace of a, given traces as above
function ComputeTrace(a,traces)
  a := Eltseq(a); return &+[a[i]*traces[i] : i in [1..#a]];
end function;

function TeichLiftInternal(X,N,n,p,Z,ZX,ZNX,ZNXq,Fq,Dyi,phi)
  if (N eq 1) then
    return X;
  else
    N1 := Ceiling(N/2); M := N1;
    ZN1 := Integers(p^N1); ZN1X := PolynomialRing(ZN1); ZN1Xq := quo<ZN1X|phi>;
    x1 := ZNX!TeichLiftInternal(ZN1X!X,N1,n,p,Z,ZX,ZN1X,ZN1Xq,Fq,Dyi,phi);
    y1 := ZNX!Frobp(x1,ZNX,n,ZNXq,p);
    x1p1 := ZNX!ZNXq!(x1^(p-1));
    V  := ZN1X![Z!i/p^N1 : i in Eltseq(ZNXq!(x1*x1p1-y1))];
    Dx := ZN1X!ZNXq!(p*x1p1);
    Dy := ZN1X!(-1);
    D1 := ZNX!ASRoot(Dy,Dx,V,M,p,ZX,ZN1X,ZN1Xq,Fq,n,-Dyi,phi);
    return (x1 + p^M*D1);
  end if;
end function;

// Gives Teichmuller lift of X in ZN[X]
function TeichLift(X,p,N,minPol,Fq)
  n := Degree(minPol); 
  Z := Integers(); ZX := PolynomialRing(Z);
  ZN := Integers(p^N); ZNX := PolynomialRing(ZN); ZNXq := quo<ZNX|minPol>;
  return TeichLiftInternal(X,N,n,p,Z,ZX,ZNX,ZNXq,Fq,-1,minPol);
end function;

// Computes the lift of a mod p^N, a in Z (or ZN)
function TeichLiftRational(a,p,N)
  a := Integers(p^N)!a;
  for i := 0 to Ceiling(Log(2,N)) do 
    y := a^(p-1); a := (p-1)*a*y/(p*y-1);
  end for;
  return a;
end function;

// The main function, norm à la SST
// INPUT:  a in Z[X]: p-adic number
//         minPol: Teichmuller modulus (in Z[X])
//         p,N: prime,accuracy
//         Fq : Finite field: Fp/minPol
// OUTPUT: N(a)
function pAdicNorm(a,p,N,minPol,Fq);
  Z := Integers(); ZN := Integers(p^N); ZNX := PolynomialRing(ZN);
  ZX := PolynomialRing(Z);
  traces := ComputeTraces(minPol,ZN); ep := ZN!ExponentialOfP(p,N);
  // Making 'a' close to unity (slowest step by far!!)
  aFF := Fq!Eltseq(ZX!a); 
  bFF := 1/aFF; b := TeichLift(ZNX!ZX!Eltseq(bFF),p,N,minPol,Fq);
  a := a*b;
  // Computing the norm of a  
  logarithmOfa := Logarithm(a,p,N,minPol);
  traceOfLog := ComputeTrace(ZNX!Eltseq(logarithmOfa),traces);
  n := Exponential(Z!traceOfLog,ep,p,N);
  // Dividing by the norm of b
  bFF := Norm(bFF);
  b := TeichLiftRational(Z!bFF,p,N);
  return ZN!(Z!n/Z!b);
end function;





///////////////////////////////////
///////////////////////////////////
//////// General functions ////////
///////////////////////////////////
///////////////////////////////////

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

function increaseField(f,n)
  // This method rewrites \prod(x-a_i) to \prod(x-a_i^n)
  // Use: rewrite a zeta function over F_q to one over F_(q^n)
  // Input : polynomial in Z[X], integer n > 0
  // Output: polynomial in Z[X]
  Z := Integers(); ZX := PolynomialRing(Integers());
  ZXY := PolynomialRing(Z,2);
  Ef := Eltseq(f);
  // Writing f(X) in ZXY
  f := &+[Ef[i]*ZXY.1^(i-1) : i in [1..#Ef]];
  // Computing the result result(Y) = \pm * Res_X(f(X), X^n - Y)
  return (-1)^(#Ef+1)*ZX!UnivariatePolynomial(Resultant(f,ZXY.1^n-ZXY.2,ZXY.1));
end function;

function isSquare(a)
  // Returns whether the finite field element a is a square
  // without computing its square root
  // Based on code in [Cohen, Frey e.a., (H)ECC, p. 235]
  F := Parent(a); Fp := PrimeField(F); p := #Fp;
  // Arbitrary choices...
  if (a in Fp) or (p eq 2) or (#F le 2^10) then ret := IsSquare(a); return ret; end if;
  m := DefiningPolynomial(F,Fp); Z := Integers();
  R := PolynomialRing(Fp); X:=R.1;
  f := R!Eltseq(a); k := 1;
  repeat
    if f eq 0 then return 1; end if;
    a := LeadingCoefficient(f);
    f /:= a;
    if (Degree(m) mod 2) eq 1 then k *:= LegendreSymbol(Z!a,p); end if;
    if (((p^Degree(m) mod 4) eq 3) and ((Degree(m)*Degree(f)) mod 2) eq 1) then k *:= -1; end if;
    r := f; f := m mod r; m := r;
  until Degree(m) eq 0;
  return k eq 1;
end function;





/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////
//////// Kedlaya'S algorithm (in odd characteristic) ////////
//////// By Mike Harrison.                           ////////
/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////

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
        vprintf SEA, 3:
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
    vprintf SEA, 2:
      "Computing (y^Frobenius)^-%o ...\n",cube select 3 else 1;
    tyme :=Cputime();
    x_pow := x^(p-1);
    difl := FrobYInv(PolynomialRing(R1)!poly,p,N,x_pow,S,cube)*x_pow;
    x_pow := x_pow*x;
    vprintf SEA, 2: "Expansion time: %o\n",Cputime(tyme);
    //Stage 2 - loop to calculate the rows of the Frobenius matrix
    vprint SEA, 2: "Reducing differentials ...";
    R1 := quo<Integers(K)|UniformizingElement(K)^N1>;
    M := RMatrixSpace(R1,d,d)!0;
    i := 1;
    boundu := p*N+(p div 2)-1;
    S1 := PolynomialRing(BaseRing(S));
    vtime SEA, 2:
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
    vprint SEA, 2: "Computing Frobenius matrix by powering ...";
    vtime SEA, 2:
    N2 := N1 + Valuation(Factorial(g),p);
    if N2 gt N then ChangePrecision(~K,N2); end if;
    M := Matrix(K,M);
    if N2 gt N1 then
      M := Matrix(K,d,[ChangePrecision(K!x,N2-Valuation(x)) : x in Eltseq(M)]);
    end if;
    return M;
end function;





//////////////////////////////////////////////////////
//////////////////////////////////////////////////////
//////// Functions for computing the matrices ////////
//////// in the differential equation.        ////////
//////////////////////////////////////////////////////
//////////////////////////////////////////////////////

function Frob0(Q,a,g,N,QpFinal,Fp)
   // Computing Q0
   Q0 := PolynomialRing(Fp)!UnivariatePolynomial(Evaluate(Q,Parent(Q).2,0));
   // Here we use Harrisons algorithm
   M00 := Kedl1(Q0,N,a,QpFinal);
   M0 := Matrix(QpFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      M0[i,j] := QpFinal!M00[i,j]; end for; end for;
   return Transpose(M0);
end function;

function matrixHinQ(Q,g,alpha,beta,Qp,QpYP,QpXYP)
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
       Half1 := ((m-2*g)/(m-3*g-1/2)*(X^m-X^(m-(2*g+1))*Q)); end if;
       Half2 := (1/(2*m-6*g-1)*((2*g+1)*X^m-X^(m-2*g)*Qq));
       NominatorH := ((NominatorH - LeadingTerm(NominatorH,X)) + lc*(Half1 - Half2));
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
   return h, H;
end function;

function FrobY1inQ(r,M,HH,h,F0,g,p,a,N_Y,Qp,QpFinal,QpYFinal,chi,N_1,N_2,N_0)
   // Idea: solve r*rsigma*dF/dY + (rsigma*H-M*rsigma*rdot)*F = r*F*Hsigma*p*Y^(p-1)
   // recursively. This F is r^M times the actual small Frobenius
   // 'Split' means a matrix of power series split up in an array of matrices
   // Computing rsigma and t := r*rsigma
   Q := Rationals();
   ZN := Integers(p^N_1); Z := Integers();
   r0M := Evaluate(r,0)^M;
   rsigma := [Q!0 : k in [0..p*Degree(r)]];
   for i := 0 to Degree(r) do rsigma[p*i+1] := Eltseq(r)[i+1]; end for;
   rsigma := Parent(r)!rsigma;
   t := r*rsigma; t1 := Degree(t);
   // Computing rsigmaH = rsigma*H, split
   temp1 := rsigma*HH - M*rsigma*Derivative(r);
   temp2 := Matrix(Q,2*g,2*g,[]); h1 := p*Degree(r)+Maximum(h,Degree(r)-1);
   rsigmaH := [temp2 : k in [0..h1]];
   for i := 1 to 2*g do  for j := 1 to 2*g do
      temp3 := Eltseq(temp1[i,j]);
      for k := 0 to Degree(temp1[i,j]) do
         rsigmaH[k+1][i,j] := temp3[k+1];
      end for; end for;
   end for;
   // Computing rHsigma = r*Hsigma, split
   for i := 1 to 2*g do for j := 1 to 2*g do
      temp1 := Eltseq(HH[i,j]); temp2 := [Q!0 : k in [0..p*Degree(HH[i,j])]];
      for k := 0 to Degree(HH[i,j]) do
        temp2[p*k+1] := temp1[k+1]; end for;
      HH[i,j] := r*Parent(HH[i,j])!temp2; end for; end for;
   h2 := Degree(r)+p*h; temp2 := Matrix(Q,2*g,2*g,[]);
   rHsigma := [temp2 : k in [0..h2]];
   for i := 1 to 2*g do  for j := 1 to 2*g do
      temp3 := Eltseq(HH[i,j]);
      for k := 0 to Degree(HH[i,j]) do
         rHsigma[k+1][i,j] := temp3[k+1];
      end for; end for;
   end for;
   // Computing F(Y), split, using recursion
   F := [temp2 : k in [0..N_Y-1]]; F[1] := F0*r0M;
   trow := Eltseq(t); t0 := trow[1]^(-1);
   // Finding the nonzero-values in the matrices, in order
   // to avoid running over all the zero values
   rHsigmaVals := [i : i in [0..h2] | not(IsZero(rHsigma[i +1]))];
   rsigmaHVals := [i : i in [0..h1] | not(IsZero(rsigmaH[i +1]))];
   trowVals    := [i : i in [1..t1] | not(IsZero(trow[i +1]))];
   // Start of the iterative computation
   for k := 0 to N_Y-2 do Ftemp1 := temp2; Ftemp2 := temp2; Ftemp3 := temp2;
      for j in rHsigmaVals do
         if j gt k-p+1 then continue j; end if;
         Ftemp1 +:= F[k-p-j+2]*rHsigma[j +1]; end for;
      for j in rsigmaHVals do
         if j gt k then continue j; end if;
         Ftemp2 +:= rsigmaH[j+1]*F[k-j+1]; end for;
      for j in trowVals do
         if j gt k then continue j; end if;
         Ftemp3 +:= trow[j+1]*(k-j+1)*F[k-j+2]; end for;
      for i := 1 to 2*g do  for j := 1 to 2*g do
         F[k+2][i,j] := ((p*Ftemp1[i,j]-Ftemp2[i,j]-Ftemp3[i,j])*t0/((k+1)));
         F[k+2][i,j] := Q!Z!ZN!F[k+2][i,j];
      end for; end for;
   end for;
      // Printing the valuation of the end result
      tempValue := Minimum([Valuation(x,p):x in Eltseq(F[N_Y])]);
      if tempValue gt N_0 then
        checkMinimum := true;
      else
        vprintf SEA: "  Convergence: valuation %o >? %o (is NOT OK)\n",tempValue,N_0;
        checkMinimum := false;
      end if;
   // Conversion of F(Y) to a matrix of power series
   Temp := [QpFinal!0 : k in [1..N_Y]]; Ff := [Temp : k in [1..4*g^2]];
   for i := 1 to N_Y do  for j := 1 to 4*g^2 do
      Ff[j][i] := QpFinal!F[i][((j-1) div (2*g))+1,((j-1) mod (2*g))+1]; end for; end for;
   F := Matrix(QpYFinal,2*g,2*g,[]);
   for i := 1 to 2*g do  for j := 1 to 2*g do
      F[i,j] := QpYFinal!Ff[2*g*(i-1)+j]; end for; end for;
   return F,checkMinimum;
end function;





////////////////////////////////////////
////////////////////////////////////////
//////// MAIN INTERNAL FUNCTION ////////
////////////////////////////////////////
////////////////////////////////////////

function computeZetaFunction(Qbar,Fq) T1 := Cputime();
// Computes the trace of Frobenius of the elliptic curve Y^2 = Qbar(X,Fq.1)

  T0 := Cputime(); y := Fq.1;
  Fp := PrimeField(Fq); p := #Fp; n := Degree(Fq,Fp); FpXY := Parent(Qbar);
  N := Ceiling(n/2+Log(p,4));
  vprint SEA: "Final p-adic precision:",N;
  Z := Integers(); ZX := PolynomialRing(Z);

  // M is the power such that we need r^M * Frobenius in the end
  M := Ceiling((Ceiling(1.5*n)+10)*(p/3)*(1+Floor(Log(20,n))/10));
  factor := 1;

  // Looping over M until we have convergence
  success := false;
  while not(success) do

  // Creating the p-adic structures
  // The accuracy-constants
  N_0 := N;
  N_Y := Ceiling(3*(M+2)*factor);
  N_b := (2*Ceiling(Log(p,N_Y))+Ceiling(Log(p,N_Y/p)));
  N_c := N_b div p + 1;
  N_2 := N_0 + Floor(Log(p,2*N_0))+1;
  N_1 := N_2 + N_b+N_c;
  // The fields and rings
  QQ := Rationals(); QQY := PolynomialRing(QQ); QQXY := PolynomialRing(QQ,2);
  Qp1   := pAdicField(p,N_1);     Zp1   := IntegerRing(Qp1);
  Qp1Y  := PolynomialRing(Qp1);   Zp1Y  := PolynomialRing(Zp1);
  Qp1XY := PolynomialRing(Qp1,2); Zp1XY := PolynomialRing(Zp1,2);
  Qp2 := ChangePrecision(Qp1, N_2); Qp2Y := PolynomialRing(Qp2);
  vprint SEA: "Initial p-adic precision:",N_1;

  // Lifting Q and computing the resultant
  Q := Zp1XY!0;
  for i := 0 to Degree(Qbar,FpXY.1) do for j := 0 to Degree(Qbar,FpXY.2) do
    Q +:= (Zp1!Eltseq(MonomialCoefficient(Qbar,FpXY.1^i*FpXY.2^j),Fp))*Zp1XY.1^i*Zp1XY.2^j;
  end for; end for;
  Res, alpha, beta := resultant(Q,1,Qp1,N_1,Zp1XY,Qp1XY);
  Q := Qp1XY!Q; Res := Zp1Y!UnivariatePolynomial(Res);
  // Lifting to Rationals()
  QinQ := QQXY!0;
  for i := 0 to Degree(Qbar,FpXY.1) do for j := 0 to Degree(Qbar,FpXY.2) do
    QinQ +:= (Integers()!Eltseq(MonomialCoefficient(Qbar,FpXY.1^i*FpXY.2^j),Fp))*QQXY.1^i*QQXY.2^j;
  end for; end for;
  ResInQ := QQY!Res; alphaInQ := QQXY!0;
  for i := 0 to Degree(alpha,Qp1XY.1) do for j := 0 to Degree(alpha,Qp1XY.2) do
      alphaInQ +:= (QQ!(MonomialCoefficient(alpha,Qp1XY.1^i*Qp1XY.2^j)))*QQXY.1^i*QQXY.2^j;
  end for; end for;
  betaInQ := QQXY!0;
  for i := 0 to Degree(beta,Qp1XY.1) do for j := 0 to Degree(beta,Qp1XY.2) do
      betaInQ +:= (QQ!(MonomialCoefficient(beta,Qp1XY.1^i*Qp1XY.2^j)))*QQXY.1^i*QQXY.2^j;
  end for; end for;

  // Creation of the matrices H and F0
  h, HPolyInQ := matrixHinQ(QinQ,1,alphaInQ,betaInQ,QQ,QQY,QQXY);
  N_bound := N_1; // Ad hoc convergence hack...
  if factor ne 1 then N_bound := N_1; end if;
  F0 := Frob0(Qbar,1,1,N_bound,Qp1,Fp);
  F0inQ := Matrix(QQ,2,2,Eltseq(F0));
  vprint SEA: "Time for computing differential equation:",Cputime()-T1; T1 := Cputime();

  // Computing the matrix F(Y) over Rationals()
  FY,checkMinimum := FrobY1inQ(ResInQ,M,HPolyInQ,h,F0inQ,1,p,1,N_Y,Qp1,Qp2,Qp2Y,1,N_1,N_2,N_0);
  vprint SEA: "Time for solving differential equation:",Cputime()-T1; T1 := Cputime();
  // If there is no convergence, we increase both M and factor, and restart
  if not(checkMinimum) then
    vprint SEA: "Matrix of Frobenius does not converge enough, restarting with M increased";
    M := Ceiling(1.5*M); factor := Minimum(2, factor+0.5) ; continue;
  end if;

  // Defining the field Qq
  minPol := TeichmullerModulusSST(DefiningPolynomial(Fq),N_1,p);
  Qq2 := UnramifiedExtension(Qp2, minPol mod p^N_2); Qq2Y := PolynomialRing(Qq2);
  // Changing Res from being defined over Qp to a definition over Qq
  Res := Qq2Y!Qp2Y!Res;
  vprint SEA: "Time for computing the Teichmueller modulus:",Cputime()-T1; T1 := Cputime();

  // Substituting y=Qq2.1 in F(Y), in Qq, divide appropriately
  Resy := Evaluate(Res,Qq2.1); RyM := 1/Resy^M;
  ZXmodpN := PolynomialRing(Integers(p^N_2));
  QasRing := quo<ZXmodpN|ZXmodpN!minPol>;
  Fy := Matrix(Qq2,2,2,[Qq2!Eltseq(x)*RyM : x in Eltseq(FY)]);
  vprint SEA: "Time for computing matrix of p-th power Frobenius:",Cputime()-T1; T1 := Cputime();

  // Now we have Fy, the matrix of the small Frobenius
  Fy := Transpose(Fy);
  // Some structures
  ZN := Integers(p^N_2); ZNX := PolynomialRing(ZN); ZNXq := quo<ZNX|minPol>;
  // Renaming the entries of the matrix
    FZX := [ZX!Eltseq(x) : x in Eltseq(Fy)]; FFq := [Fq!Eltseq(x) : x in Eltseq(FZX)]; FZNX := [ZNX!x : x in Eltseq(FZX)];
    // If necessary we take (a  1)^t instead of (1  a)^t
    if FFq[1] eq 0 and FFq[2] eq 0 then FZNX := Reverse(FZNX); FFq := Reverse(FFq); end if;
    f1 := FZX[1]; f2 := FZX[2]; f3 := FZX[3]; f4 := FZX[4]; f1b := FFq[1]; f2b := FFq[2]; f3b := FFq[3]; f4b := FFq[4];
  // Computing a solution modulo p of the equation
  xs := f2b ne 0 select f4b/f2b else f3b/f1b; x := Frobenius(xs,-1); sol := ZNX!ZX!Eltseq(x);
  // Lifting this solution to the 'eigenvector' V := (1  xlift)
  // This satisfies Fy * (1  xlift)^t = lambda*(1  sigma(xlift))^t
  xlift := NewtonII(f2,f1,-f4,-f3,sol,N_2,n,p,Z,ZX,ZNX,ZNXq,Fq,1/(f2b*x+f1b),minPol);
  // Lambda is then trivially recovered
  lambda := ZNXq!(f1 + xlift*f2);
  vprint SEA: "Time for computing eigenvalue of p-th power Frobenius:",Cputime()-T1; T1 := Cputime();
  // Next we need the norm of this eigenvalue
  normLambda := pAdicNorm(ZX!lambda,p,N,minPol,Fq);
  // Finally the trace of Frobenius is recovered, and compared to the Weil bound
  trace := Z!(normLambda) mod p^N_0;
  if (trace gt Floor(2*Sqrt(p^n))) then trace := trace - p^N_0; end if;
  vprint SEA: "Time for taking the norm of the eigenvalue:",Cputime()-T1; T1 := Cputime();

  success := true; end while; return trace;

end function;







////////////////////////////////////////
////////////////////////////////////////
//////// MAIN EXTERNAL FUNCTION ////////
////////////////////////////////////////
////////////////////////////////////////

intrinsic ECDeformationTrace(E::CrvEll[FldFin]) -> RngIntElt
{ Computes the trace of Frobenius of E over GF(p^n) by deformation
  methods on p-adic cohomology.}

   T := Cputime(); T1 := Cputime();

  // Basic constants
  Fq := BaseField(E); Fp := PrimeField(Fq); p := #Fp; n := Degree(Fq,Fp);
  require p gt 2 : "Characteristic must be odd for deformation mathod";

  // Computing Q(X) for E given as Y^2 = Q(X)
  Q,temp := HyperellipticPolynomials(E);
  if temp ne 0 then // If temp != 0 the equation does not have the form Y^2 = X^3+...
    E := SimplifiedModel(E); Q,_ := HyperellipticPolynomials(E); end if;

  // Putting the curve in a one parameter family Y^2 = Q(X,y)
  R<X,Z> := PolynomialRing(Fp,2); n := Degree(Fq,Fp);
  sign := 1; // At the end we return sign*trace, sign = (-1) ^ (number of twists)
  // We define Q(X) = X^3 + a X^2 + b X + c
  a := Coefficient(Q,2); b := Coefficient(Q,1); c := Coefficient(Q,0);
  b1 := b - a^2/3; c := c + 2*a^3/27 - a*b/3; b := b1;
  if (c eq 0) then Q := X^3 + (Z+1)*X; y := b-1;
  else
    repeat delta := Random(Fp); until ((delta ne 0) and (delta ne -Fp!27/4));
    Q := X^3 + (Z+delta)*X + Z + delta; y := b^3/c^2-delta;
    if not(isSquare(b/c)) then sign *:= -1; end if;
  end if;

  // Handling the field: curve becomes Y^2 = Q(X,Fq.1)
  minPol := MinimalPolynomial(y,Fp); m := Degree(minPol);
  // -----------------------------------------------------
  // mch - condition moved to main EC point counting function
  //if (m lt 40*Log(10,Log(10,p))+4) then
  //  return TraceOfFrobenius(E); end if;
  // -----------------------------------------------------
  Fq := ext<Fp|minPol : Optimize:=false>;

  // At this point we have Q(X,Y), y=Fq.1, rho
  vprint SEA:""; vprint SEA: "Family created in time:",Cputime()-T1;
  trace := computeZetaFunction(Q,Fq);

  // If y defined a smaller field than Fq, we restore the trace
  if (n gt m) then
    k := Integers()!(n/m);
    R := PolynomialRing(Integers()); TT := R.1;
    f := increaseField(p^m*TT^2 - trace*TT + 1,k);
    trace := -Coefficient(f,1);
  end if;

  // We return the trace with corrected sign
  return sign*trace;

end intrinsic;
