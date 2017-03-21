freeze;

function MySquarefreePart(f)

     if (Degree(f) eq 0) then
	 return f;
     end if;

     fder := Derivative(f);

     return f div GCD(f, fder);
	 
end function;

function NormalFormFiniteFieldChar2(C)

// transforms an hyperelliptic curve C into a standard form
// given by y^2 + h(x)y + f(x) = 0 where
// irreducible factors of h(x) divide f(x)

    K := BaseField(C);
    if not (Characteristic(K) eq 2 and IsFinite(K)) then
	error "Defining field has to be finite field of char 2";
    end if;
    
    boo, CC := IsHyperellipticCurve(C);  // checking if curve is hyperelliptic in the first place
    
    if not boo then
	error "Curve is not hyperelliptic";
    end if;
    
    f, h := HyperellipticPolynomials(CC);
    
    Polring := Parent(f);
    x := Polring.1;
    RF := RationalFunctionField(K);
    u := RF ! f/h^2;
    
    // now need to normalize
    // this is a simple loop over the partial fraction decomp, in general loop will be execute once
    // and then 1 time to check that indeed the form is correct
    
    stop := false;
    while (not stop) do
	
	changed := false;	
	PFD := PartialFractionDecomposition(u);
	
	u := RF ! 0;
	
	for i := 1 to #PFD do
	    
	    Ft := PFD[i];
	    if (Ft[1] eq 1) then  // looking at infinity here
		Pol := Ft[3];
		while (Degree(Pol) gt 1 and IsEven(Degree(Pol))) do
		    c := LeadingCoefficient(Pol);
		    Pol := Pol - LeadingTerm(Pol) + Sqrt(c)*x^(Degree(Pol) div 2);
		    changed := true;
		end while;
		u +:= Pol;
	    else  // other factors
		// check if this appears to higher degree
		if ((i lt #PFD) and (Ft[1] eq PFD[i+1][1])) then // leave this as is
		    u +:= Ft[3]/Ft[1]^Ft[2];
		else	
		    if IsEven(Ft[2]) then  // need to adjust
			if ((Degree(Ft[1]) eq 1) or (Degree(Ft[3]) lt 1)) then // no need to take extension
			    r := Sqrt(Ft[3]);
			    u +:= r/Ft[1]^(Ft[2] div 2);
			    changed := true;
			else  // here degree of Ft[3] is really > 1
			    F2ext := ext<K | Ft[1]>;
			    r := Polring ! Eltseq(Sqrt(F2ext ! Ft[3]));
			    q, rn := Quotrem(r^2, Ft[1]);
			    u +:= q/Ft[1]^(Ft[2]-1) + r/Ft[1]^(Ft[2] div 2);
			    changed := true;
			end if;
		    else
			u +:= Ft[3]/Ft[1]^Ft[2];
		    end if;
		end if;	
	    end if;
	end for;
	
	stop := not changed;
	
    end while;

    // deriving equation of the curve such that irreducible factors in h divide f
    
    N := Numerator(u);
    D := Denominator(u);
    
    a := LeadingCoefficient(N)/LeadingCoefficient(D);
    
    r := Polring ! (N div LeadingCoefficient(N));
    D := Polring ! (D div LeadingCoefficient(D));
    t := MySquarefreePart(D);
    t := t div LeadingCoefficient(t);    

    s := (D div t)/a;  
    
    // need to take square root of s
    
    s := Polring ! [ Sqrt(Coefficient(s,2*i)) : i in [0..(Degree(s) div 2)]];
    
    return HyperellipticCurve([r*t, s*t]);
    
end function;


function HyperellipticCurveChar2Type(f,h)  // assumes curve is in normal form as above

    // three types:
    // deg(f) > 2*deg(h) then imaginary  (iType = 1)
    // def(f) <= 2*deg(h) then real or unusual (iType = 2) or (iType = 3)
    
    sType := "";
    iType := 0;
    if Degree(f) gt 2*Degree(h) then
	sType := "Imaginary quadratic hyperelliptic curve of genus " cat IntegerToString(((Degree(f)-1) div 2));
	iType := 1;
    else
	g := Degree(h)-1;
	if (Degree(f) lt 2*g + 2) then
	    sType := "Real quadratic hyperelliptic curve of genus " cat IntegerToString(g);
	    iType := 2;
	else
	    if Trace(LeadingCoefficient(h)^(-1)) eq 0 then
		sType := "Real quadratic hyperelliptic curve of genus " cat IntegerToString(g);
		iType := 2;
	    else
		sType := "Unusual hyperelliptic curve of genus " cat IntegerToString(g);
		iType := 3;
	    end if;
	end if;
    end if;
	    
    return iType, sType;
    
end function;

function LiftFrobeniusOnyAs(m,c,f,N,R)  // only computes beta*y component of Frob(y), AS curves only

    vprintf JacHypCnt, 3: "Computing Frobenius on y with precision %o\n", N;
    
    T := N;
    S := Ceiling(Log(2,N)) + 1;
    Prec := [Integers() ! 0 : i in [1..S]]; 
    
    for i := S to 1 by -1 do
	Prec[i] := T;
	T := Ceiling(T/2);
    end for;
    
    LSR := LaurentSeriesRing(R);
    RR := BaseRing(LSR);
    x := LSR.1;
    flifted := LSR ! Eltseq(f);
    fsigma := Evaluate(LSR ! [GaloisImage(RR ! c, 1) : c in Eltseq(f) ], x^2);
    clifted := RR ! c;
    csigma := GaloisImage(RR ! c, 1);
    csigmainv := csigma^(-1);

    // solving the equation A*Z^2 + B*Z + C = 0

    A := 1 + 4*flifted*clifted^(-2)*x^(-2*m);
    B := -csigma*x^(2*m) - 4*csigma*flifted*clifted^(-2);
    C := flifted*csigma^2*x^(2*m)*clifted^(-2) - fsigma;

    // in the denominator then have Adenom*Zn + Bdenom
    // taken out factor csigma*x^(2*m)
    
    Bdenom := -B*csigma^(-1)*x^(-2*m);
    Adenom := -2*A*csigma^(-1)*x^(-2*m);
    
    LSR := LaurentSeriesRing(ChangePrecision(R,Prec[1])); 
    RR := BaseRing(LSR);
    x := LSR.1;
   
    alpha := LSR ! Eltseq(f);
    gamma :=  LSR ! 1;
    beta := LSR ! 0;
    
    for i := 2 to S do

	tyme := Cputime();
	
	// saving the old LSR for reuse
	
	LSRlow := LSR;
	RRlow := RR;
	xlow := x;
	
	LSR := LaurentSeriesRing(ChangePrecision(R,Prec[i]));   // changing precision in each step of the iteration
	RR := BaseRing(LSR);
	x := LSR.1;
	
	// rest of the iteration
	
	alpha := LSR ! alpha;

	mu := (RR ! csigmainv)*x^(-2*m)*(((LSR ! A)*alpha + (LSR ! B))*alpha + (LSR ! C));
	if (mu ne 0) then
	    mu := xlow^(Valuation(mu))*(LSRlow ! [ExactQuotient(c,2^(Prec[i-1])) : c in Coefficients(mu)]);
	else
	    mu := LSRlow ! mu;
	end if;    
	delta := gamma*mu;
	alpha := alpha + 2^(Prec[i-1])*(LSR ! delta);
	
	delete delta;
	delete mu;
	
	if (i lt S) then  // doing another inversion step

	    denom := (LSR ! Adenom)*alpha + (LSR ! Bdenom);
	    gamma := LSR ! gamma;

	    mu := (1 - denom*gamma);
	    if (mu ne 0) then
		mu := xlow^(Valuation(mu))*(LSRlow ! [ExactQuotient(c,2^(Prec[i-1])) : c in Coefficients(mu)]);
	    else
		mu := LSRlow ! 0;
	    end if;
	    delta := mu*(LSRlow ! gamma);

	    gamma := gamma + 2^(Prec[i-1])*(LSR ! delta);
	    
	end if;
	
	// check ....

//	 print (alpha)^2*(1 + 4*(LSR ! flifted)*x^(-2*m)*(RR ! clifted)^(-2)) + alpha*(-4*(RR ! csigma)*(LSR ! flifted)*(RR ! clifted)^(-2) - (RR ! csigma)*x^(2*m)) + (LSR ! flifted)*(RR ! csigma)^2*x^(2*m)*(RR ! clifted)^(-2) - (LSR ! fsigma);
	
       vprintf JacHypCnt, 3: "Reached precision %o   time = %o\n", Prec[i], Cputime(tyme);

       if (i eq S) then
	   beta := (RR ! csigma)*x^m*(RR ! clifted)^(-1) - 2*alpha*(RR ! clifted)^(-1)*x^(-m);
	   delete alpha;
       end if;
       
   end for;
   
   return beta;
   
end function;

function LiftFrobeniusOnyGeneral(Hlifted,hlifted,flifted,D,N,R) 
// only computes beta*y component of Frob(y), general curves, not AS see above

    vprintf JacHypCnt, 3: "Computing Frobenius on y with precision %o\n", N;
    
    T := N;
    S := Ceiling(Log(2,N)) + 1;
    Prec := [Integers() ! 0 : i in [1..S]]; 
    
    for i := S to 1 by -1 do
	Prec[i] := T;
	T := Ceiling(T/2);
    end for;

    LSR<Y> := LaurentSeriesRing(R);
    P1 := PolynomialRing(LSR); x := P1.1;
    LSRpolring<X> := quo<P1|(P1!Hlifted)-Y^-1>;
    
    fsigmaLSRP := LSRpolring ! (Evaluate(P1 ! [GaloisImage(c, 1) : c in Eltseq(flifted) ], x^2));
    hsigmaLSRP := LSRpolring ! (Evaluate(P1 ! [GaloisImage(c, 1) : c in Eltseq(hlifted) ], x^2));
    restinvhlifted := Hlifted^D div hlifted;  // hlifted = Hlifted^D / restinvhlifted
    hinvLSRP := LSRpolring ! ((P1 ! restinvhlifted)*Y^(D));
    hsqrinvLSRP := LSRpolring ! ((P1 ! restinvhlifted^2)*Y^(2*D));

    fliftedLSRP := LSRpolring ! (P1 ! flifted);
    hliftedLSRP := LSRpolring ! (P1 ! hlifted);

    // solving the equation A*Z^2 + B*Z + C = 0

    A := 1 + 4*fliftedLSRP*hsqrinvLSRP;
    B := -hsigmaLSRP - 4*hsigmaLSRP*fliftedLSRP*hsqrinvLSRP;
    C := fliftedLSRP*hsigmaLSRP^2*hsqrinvLSRP - fsigmaLSRP;
    
    // in the denominator then have Adenom*Zn + Bdenom
    // notice the minus signs, so we add in Newton iteration

    Bdenom := -B;
    Adenom := -2*A;
    
    LSR<Y> := LaurentSeriesRing(ChangePrecision(R,Prec[1])); 
    RR := BaseRing(LSR);
    P1 := PolynomialRing(LSR); x := P1.1;
    LSRpolring<X> := quo<P1|(P1!Hlifted)-Y^-1>;

    alpha := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(fliftedLSRP)];
    gamma :=  LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(hsqrinvLSRP)];
    beta := LSRpolring ! 0;
    
    Adenomn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(Adenom)];
    Bdenomn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(Bdenom)];

    for i := 2 to S do

	tyme := Cputime();
	
	// saving the old LSRpolring for reuse
	
	LSRlow := LSR;
	RRlow := RR;
	Ylow := Y;
	LSRpolringlow := LSRpolring;
	Xlow := X;

	LSR<Y> := LaurentSeriesRing(ChangePrecision(R,Prec[i])); 
	RR := BaseRing(LSR);
	P1 := PolynomialRing(LSR); x := P1.1;
	LSRpolring<X> := quo<P1|(P1!Hlifted)-Y^-1>;
	
	// rest of the iteration

	alpha := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(alpha)];
	An := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(A)];
	Bn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(B)];
	Cn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(C)];
	
	mu := (An*alpha + Bn)*alpha + Cn;

	if (mu ne 0) then  // getting out factor 2^Prec[i-1]
	    mu := LSRpolringlow ! [ LSRlow ! ((a eq 0) select 0 else Ylow^(Valuation(a))*(LSRlow ! [ExactQuotient(c,2^(Prec[i-1])) : c in Coefficients(a)])) : a in Coefficients(mu)];
	else
	    mu := LSRpolringlow ! 0;
	end if;    

	delta := gamma*mu;
	alpha := alpha + 2^(Prec[i-1])*(LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(delta)]);

	delete delta;
	delete mu;
	
	if (i lt S) then  // doing another inversion step

	    Adenomn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(Adenom)];
	    Bdenomn := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(Bdenom)];
	    
	    denom := Adenomn*alpha + Bdenomn;
	    gammaold := gamma;
	    gamma := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(gamma)];

	    mu := (1 - denom*gamma);
	    if (mu ne 0) then  // getting out factor 2^Prec[i-1]
		mu := LSRpolringlow ! [ LSRlow ! ((a eq 0) select  0 else Ylow^(Valuation(a))*(LSRlow ! [ExactQuotient(c,2^(Prec[i-1])) : c in Coefficients(a)])) : a in Coefficients(mu)];
	    else
		mu := LSRpolringlow ! 0;
	    end if;
	    delta := mu*gammaold;
	    
	    gamma := gamma + 2^(Prec[i-1])*(LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(delta)]);
	    delete gammaold;
	    delete delta;
	    
	end if;
	
	vprintf JacHypCnt, 3: "Reached precision %o   time = %o\n", Prec[i], Cputime(tyme);

	if (i eq S) then
	    beta := (LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(hinvLSRP)])*((LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(hsigmaLSRP)]) - 2*alpha);
	    delete alpha;

	    // check
	    /*
	    flifted := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(fliftedLSRP)];
	    hlifted := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(hliftedLSRP)];
	    fsigma := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(fsigmaLSRP)];
	    hsigma := LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(hsigmaLSRP)];

	    print (4*flifted + hlifted^2)*beta^2 - (4*fsigma + hsigma^2);
	    */
	    
	end if;
       
   end for;

   return beta;
   
end function;

function ReduceDifferentialAS(df,Md,m,c,f)  // reduction in cohomology for AS curves

    LSR := Parent(df);
    R := BaseRing(LSR);
    x := LSR.1;
    
    D := Degree(df);
    inv3 := (R ! 3)^(-1);

    flifted := LSR ! Eltseq(f);
    clifted := R ! c;
    fliftedder := Derivative(flifted);

    P1 := (2*fliftedder + m*clifted^2*x^(2*m-1));
    P2 := inv3*(4*flifted + clifted^2*x^(2*m));
   
    Res := df;
    
    for i := D to (Md+1) by -1 do 
	Coeffi := Coefficient(Res, i);
	if (Coeffi ne 0) then
	    j := i - Md;
	    Polred := x^j*P1 + P2*j*x^(j-1);
	    PolLeadCoef := Coefficient(Polred,i);
	    Res :=  Res - ExactQuotient(Coeffi,PolLeadCoef)*Polred;
	end if;
    end for;

    Coeffi := Coefficient(Res, Md);
    if (Coeffi ne 0) then
	Polred := P1;
	PolLeadCoef := Coefficient(Polred, Md);
	Res -:=  ExactQuotient(Coeffi,PolLeadCoef)*Polred;
    end if;

    V := Valuation(Res);

    for i := V to -1 do
	Coeffi := Coefficient(Res, i);
	if (Coeffi ne 0) then
	    Polred := x^i*P1 + i*x^(i-1)*P2;
	    PolLeadCoef := Coefficient(Polred,i);
	    Res :=  Res - ExactQuotient(Coeffi,PolLeadCoef)*Polred;
	end if;
    end for;
   
   return Res;

end function;

function PrecomputePowersFrobenius(K,U)  // in fact not needed further on
    // computes t^(sigma^2^i) for i := 0 to U

    Qp := BaseRing(K);
    QpT := PolynomialRing(Qp);
    Powers := [K ! 0 : i in [0..U]];
    t := K.1;
    Powers[1] := GaloisImage(t,1);
    for k := 2 to U+1 do
	Powers[k] := Evaluate(QpT ! Eltseq(Powers[k-1]), Powers[k-1]);
    end for;

    return Powers;
    
end function;

function NormOfMat(M,m,n) // norm of matrix 
    
    if n eq 1 then return M; end if; 
    bits := Intseq(n,2);
    R := CoefficientRing(M);
    t := R.1;
    Qp := BaseField(R);
    QpT := PolynomialRing(Qp);
    N := M;
    r := 1;
    prec := Precision(Parent(M[1][1]));
    tsigmapower := GaloisImage(t,1);
    tsigma := GaloisImage(t,1);
    for i := (#bits-1) to 1 by -1 do
	N := Matrix(m,[ Evaluate(QpT ! Eltseq(x), tsigmapower) : x in Eltseq(N)])*N;
	N := Matrix(Parent(M[1][1]), Nrows(N), Ncols(N), [ChangePrecision(a,prec) : a in Eltseq(N)]);
        tsigmapower := Evaluate(QpT ! Eltseq(tsigmapower), tsigmapower);
	if bits[i] eq 1 then
	    N := Matrix(m,[ Evaluate(QpT ! Eltseq(x), tsigma) : x in Eltseq(N)])*M;
	    N := Matrix(Parent(M[1][1]), Nrows(N), Ncols(N), [ChangePrecision(a,prec) : a in Eltseq(N)]);
	    tsigmapower := Evaluate(QpT ! Eltseq(tsigmapower), tsigma);
	end if;
    end for;
    return N;

end function;


function UpperCoeffs(M,g,ppow,e_val)  // adapted from Mike's code, tricking Magma with precision

    // Calcs the sequence of the upper coefficients (x^g,..x^(2g))
    // of CharPoly(M) using the trace method. The magma intrinsic
    // could be used but this is slightly more efficient as only
    // Trace(M),Trace(M^2),..Trace(M^g) need be calculated rather
    // than Trace(M),..,Trace(M^(2g)).
    // If Nrows(M) = 2*g+1 then the extra eigenvalue of M, e_val,
    // is discarded. (e_val = q in the real case or e_val = -q 
    // in the unusual case).
    // The sequence [r(v)] is returned where, for a p-adic int v,
    // r(v) is the integer n s.t.|n|<ppow/2 and n=v mod ppow.
    
    pAd := pAdicField(Parent(M[1,1]));
    prec := Precision(pAd);
    N := M;
    UCs := [pAd!1];   // coeffs (highest to lowest) of CharPoly(M)
    TrPows := [pAd|]; // [Trace(M),Trace(M^2),...]
    for i in [1..g] do
	Append(~TrPows,Eltseq(Trace(N))[1]);
        Append(~UCs, (- &+[TrPows[j]*UCs[i+1-j] : j in [1..i]])/i); 
        if i lt g then N := N*M; N := Matrix(Parent(M[1][1]), Nrows(N), Ncols(N), [ChangePrecision(a,prec) : a in Eltseq(N)]); end if;
    end for;
    if Nrows(M) ne 2*g then // original Q(x) of even degree
        for i in [1..g] do
            UCs[i+1] := UCs[i+1]+e_val*UCs[i];
        end for;
    end if;
    return [((2*uc gt ppow) select uc-ppow else uc) where uc is (IntegerRing()!x) mod ppow : x in UCs];
    
end function;

function KedlayaChar2AS(m,c,f)

    // computes matrix of Frobenius for curve y^2 + c*x^m*y + f(x) = 0
    // assumption is that f(0) = 0 if m > 0
    // also f should be monic, i.e. curve is in standard form
    
    Polring := Parent(f);
    BaseField := CoefficientRing(Polring);
    p := Characteristic(BaseField);
    n := Degree(BaseField);
    P := DefiningPolynomial(BaseField);  
    X := Polring.1;
    d := Degree(f);
    Md := 0;

    iType := HyperellipticCurveChar2Type(f,c*X^m);
    
    if (d gt 2*m) then
	g := (d-1) div 2;
	Md := 2*g;
    else
	g := (m-1);
	Md := 2*g+1;
    end if;
    
    epsilon := -Minimum([k - 3 - Floor(Log(2,2*k*Md + Md)) : k in [0..10]]);  // bound on valuation
    B := Ceiling(Log(p, 2*Binomial(2*g, g)) + n*g/2);  // bound on size of coefficients

    // for large geni switching to better bound

    B := Minimum(B, n*g + 1);
    
    vprintf JacHypCnt, 3: "Needed precision is %o\n", B;
    
    // determining correct precision N
    
    N := B + 3;
    while (N lt (B + 3 + Floor(Log(2,2*N*(Md+1) + g)))) do
	N := N + 1;
    end while;

    vprintf JacHypCnt, 3: "Working with precision %o\n", N;
    
    Qp := pAdicField(p,N+epsilon);
    //QpZ := PolynomialRing(Qp); Z := QpZ.1;
    K := UnramifiedExtension(Qp,n);//K := ext<Qp | QpZ ! Eltseq(P)>;
    R := quo<Integers(K)|UniformizingElement(K)^(N+epsilon)>;
    Embed(BaseField,ResidueClassField(R));
    
    LSR := LaurentSeriesRing(R);
    x := LSR.1;
    
    timelift := Cputime();
    beta := LiftFrobeniusOnyAs(m,c,f,N,ChangePrecision(R,N));  // lifting Frobenius to precision N
    beta := 2^(epsilon)*(LSR ! beta);  // fudge factor epsilon makes reduction integral
    vprintf JacHypCnt, 3: "Total time to lift Frobenius on y %o \n", Cputime(timelift);
    
    // need to reduce 2*x^(2*k+1)*beta*y dx for k = 0 .. Md-1

    M := RMatrixSpace(K,Md,Md)!0;
    
    vprintf JacHypCnt, 3: "Reducing %o differentials \n", Md;

    timediff := Cputime();
    for k := 0 to Md-1 do
	tyme := Cputime();
	rdiff := ReduceDifferentialAS(x^(2*k+1)*beta,Md,m,c,f);   // taken out factor 2 already, need to divide by 2^(epsilon-1)
	M[k+1] := RSpace(K,Md)! [ (K ! [Integers() ! c : c in Eltseq(Coefficient(rdiff,j))])/2^(epsilon-1) : j in [0..(Md-1)]];
	vprintf JacHypCnt, 3: "Reduced differential %o in time = %o\n", k+1, Cputime(tyme);
    end for;
    vprintf JacHypCnt, 3: "Total time to reduce differentials %o \n", Cputime(timediff);

    // at this point matrix M is matrix of Frobenius up to power 2^B, i.e. difference
    // with the correct one is multiple of 2^B (so not relative precision only)
    // we're leaving in N just not to lose anything
    
    // we need to trick Magma in forgetting about damned precision
    // so in norm computation precision is always reset to maximum
        
    timenorm := Cputime();
    NM := NormOfMat(M,Md,n);
    vprintf JacHypCnt, 3: "Total time to compute norm %o \n", Cputime(timenorm);
    
    // in the next step we could lose up to Valuation(g!,2)
    // to take care of non-integral entries in matrix, precision is always reset to max in UCoeffs
    
    Qp2 := pAdicField(p,N+Valuation(Factorial(g),2));
    //Qp2Z := PolynomialRing(Qp2); Z := Qp2Z.1;
    K2 := UnramifiedExtension(Qp2,n);//K2 := ext<Qp2 | Qp2Z ! Eltseq(P)>;
    M2 := Matrix(K2,Md,Md,[K2 ! [Rationals() ! c : c in Eltseq(a)] : a in Eltseq(NM)]);    
    tyme := Cputime();
    q := #ResidueClassField(Integers(K2));
    UCoeffs := UpperCoeffs(M2,g,p^B,(-1)^iType*q);
    CharP := PolynomialRing(IntegerRing())! ([UCoeffs[i]*q^(g+1-i): i in [1..g]] cat Reverse(UCoeffs));
    vprintf JacHypCnt,3: "Characteristic polynomial time: %o\n",Cputime(tyme);
    
    return Parent(CharP)!Reverse(Coefficients(CharP));
    
end function;

function SplitDifferential(differ)

    // splits differential up into positive terms and negative ones
    // now is polynomial ring over laurentseries ring
    // in reduction need the other way around
    
    MinVal := Minimum([(c eq 0) select 0 else Valuation(c) : c in Coefficients(differ)]);
    MaxDeg := Maximum([(c eq 0) select 0 else Degree(c) : c in Coefficients(differ)]);
    MaxDeg := Maximum([MaxDeg,1]);
    
    Polring := PolynomialRing(BaseRing(BaseRing(Parent(differ)))); X := Polring.1;

    negpowers := [Polring ! 0 : i in [0..-MinVal]];
    pospowers := [Polring ! 0 : i in [1..MaxDeg]];

    B := #Coefficients(differ);

    for i := 1 to B do
	C := Coefficient(differ,i-1);
	for j := MinVal to 0 do
	    negpowers[-j+1] +:= X^(i-1)*Coefficient(C,j);
	end for;
	for j := 1 to MaxDeg do
	    pospowers[j] +:= X^(i-1)*Coefficient(C,j);
	end for;
    end for;
    
    return negpowers, pospowers;
    
end function;


function integralXGCD(p1,p2,N)  // adapted from Mike's code

    // p1 and p2 are relatively prime integral polynomials over an
    // unramified pAdic field of bounded precision n.
    // It is assumed that the leading coeff of p1 is prime to p.
    // The function calculates and returns integral polynomials of
    // the same precision s.t. A*p1+B*p2 = 1 mod p^n.
    // Begins by lifting the Xgcd result over the Residue field and
    // iterates up mod p^i for 1 <= i <= n.
    R := Parent(p1);
    F,mp := ResidueClassField(BaseRing(R));
    S := PolynomialRing(F);
    p1r := S![mp(j) : j in Coefficients(p1)];
    p2r := S![mp(j) : j in Coefficients(p2)];
    _,Ar,Br := Xgcd(p1r,p2r);
    u := R!Ar; v := R!Br;
    A := u; B := v;
    delta := R!-1;
    p := Characteristic(F);
    for i in [1..N-1] do
        delta := ExactQuotient(delta+u*p1+v*p2,p);
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


function ReduceDifferentialGeneral(negpowers, pospowers, Hlifted, hlifted, flifted,Md,N)

    // reducing positive powers of X first, which corresponds to the elements in negpowers

    Res := Parent(negpowers[1]) ! 0;
    for i := #negpowers to 1 by -1 do
	Res := Res*Hlifted + negpowers[i]; 
    end for;
    
    inv3 := (BaseRing(Parent(Res)) ! 3)^(-1);
    P1 := (2*Derivative(flifted) + hlifted*Derivative(hlifted));
    P2 := inv3*(4*flifted + hlifted^2);
    x := Parent(Res).1;
        
    D := Degree(Res);
    
    for i := D to (Md+1) by -1 do 
	Coeffi := Coefficient(Res, i);
	if (Coeffi ne 0) then
	    j := i - Md;
	    Polred := x^j*P1 + P2*j*x^(j-1);
	    PolLeadCoef := Coefficient(Polred,i);
	    Res :=  Res - ExactQuotient(Coeffi,PolLeadCoef)*Polred;
	end if;
    end for;

    Coeffi := Coefficient(Res, Md);
    if (Coeffi ne 0) then
	Polred := P1;
	PolLeadCoef := Coefficient(Polred, Md);
	Res -:=  ExactQuotient(Coeffi,PolLeadCoef)*Polred;
    end if;

    // reducing negative powers of H(X), which corresponds to the elements in pospowers
    
    if ((#pospowers gt 1) or (pospowers[1] ne 0)) then
	PrevTerm := Parent(Res) ! 0;
	QF := flifted div Hlifted;
	QH := hlifted div Hlifted;

	GCDB := QF*Derivative(Hlifted);
	GA, GB := integralXGCD(Hlifted,GCDB,N);
	PP1 := inv3*QH^2*Derivative(Hlifted);
	PP2 := 2*Derivative(QF) + QH*Derivative(hlifted);
	PP3 := inv3*(4*QF + QH*hlifted);
	
	for k := #pospowers to 1 by -1 do
	    Coeff := pospowers[k];
	    Term := Coeff + PrevTerm;
	    
	    if (Term eq 0) then
		PrevTerm := Parent(Res) ! 0;
	    else
		// Getting out HH part if possible

		QT, RT := Quotrem(Term, Hlifted);
		Term := RT;
		PrevTerm := QT;      
		
		A := Term*GA;
		B := Term*GB;
		
		// Term = A*HH + B*QF*Derivative(HH)

		QB, RB := Quotrem(B, Hlifted);
		A := A + QB*GCDB;
		B := RB;
		
		// Now degrees are reduced
		
		PrevTerm := PrevTerm + A;    
		Scalar := 2*(1 - 2*k*inv3);
		ReductB := ExactQuotient(B*(k*PP1 - PP2) - Derivative(B)*PP3, Scalar);
		PrevTerm +:= ReductB; 
	    end if;
	end for;
	Res +:= PrevTerm;
    end if;
    
    return Res;

end function;
    
function KedlayaChar2General(h,f)
    
    // curve y^2 = h(x)y + f(x) where irreducible factors of h(x) divide f(x)
    // assumes curve comes out of NormalFormFiniteFieldChar2
    // also h(x) is not constant or power of linear term, use KedlayaChar2AS otherwise

    Polring := Parent(f);
    BaseField := CoefficientRing(Polring);
    p := Characteristic(BaseField);
    n := Degree(BaseField);
    P := DefiningPolynomial(BaseField);  
    X := Polring.1;
    d := Degree(f);
    Md := 0;
    m := Degree(h);

    iType := HyperellipticCurveChar2Type(f,h);
    
    if (d gt 2*m) then
	g := (d-1) div 2;
	Md := 2*g;
    else
	g := (m-1);
	Md := 2*g+1;
    end if;
    
    epsilon := -Minimum([k - 3 - Floor(Log(2, 2*k*Md + Md)) : k in [0..10]]);
    B := Ceiling(Log(p, 2*Binomial(2*g, g)) + n*g/2);

    // for large geni switching to better bound

    B := Minimum(B, n*g + 1);

    // Experimental bound

    B := Ceiling(n*g/2) + Ceiling(Log(2,g)) + 2;
    
    vprintf JacHypCnt, 3: "Needed precision is %o\n", B;
    
    // determining correct precision N
    
    N := B + 3;
    while (N lt (B + 3 + Floor(Log(2,2*N*(Md+1) + g)))) do
	N := N + 1;
    end while;

    vprintf JacHypCnt, 3: "Working with precision %o\n", N;

    Qp := pAdicField(p,N+epsilon);
    //QpZ := PolynomialRing(Qp); Z := QpZ.1;
    K := UnramifiedExtension(Qp,n);//K := ext<Qp | QpZ ! Eltseq(P)>;
    R := quo<Integers(K)|UniformizingElement(K)^(N+epsilon)>;
    Embed(BaseField,ResidueClassField(R));
    LiftedPolring := PolynomialRing(R);

    // Lifting curve

    c := LeadingCoefficient(h);
    F := Factorisation(h);
    D := Maximum([factor[2] : factor in F]);
    H := &*[factor[1] : factor in F];
    q := f div H;
    
    clifted := (R ! c);
    Hlifted := &*[LiftedPolring ! factor[1] : factor in F];
    hlifted := clifted*&*[(LiftedPolring ! factor[1])^factor[2] : factor in F];
    qlifted := LiftedPolring ! q;
    flifted := qlifted*Hlifted;
    
    LSR := LaurentSeriesRing(R);
    Y := LSR.1;  // this will equal 1/H(x)
    P1 := PolynomialRing(LSR);
    LSRpolring<X> := quo<P1|P1!Hlifted-Y^-1>;

    timelift := Cputime();
    beta := LiftFrobeniusOnyGeneral(Hlifted,hlifted,flifted,D,N,ChangePrecision(R,N));  // lifitng to precision N
    beta := 2^epsilon*(LSRpolring ! [BaseRing(LSRpolring) ! a : a in Coefficients(beta)]);  // fudge factor epsilon makes everything integral
    vprintf JacHypCnt, 3: "Total time to lift Frobenius on y %o \n", Cputime(timelift);
    
    // need to reduce 2*x^(2*k+1)*beta*y dx for k = 0 .. Md-1

    M := RMatrixSpace(K,Md,Md)!0;
    vprintf JacHypCnt, 3: "Reducing %o differentials \n", Md;
    timediff := Cputime();
    for k := 0 to Md-1 do
	tyme := Cputime();
	negpowers, pospowers := SplitDifferential(X^(2*k+1)*beta);
	rdiff := ReduceDifferentialGeneral(negpowers, pospowers, Parent(pospowers[1]) ! Hlifted, Parent(pospowers[1]) ! hlifted, Parent(pospowers[1]) ! flifted,Md,N+epsilon+1);
	M[k+1] := RSpace(K,Md)! [ (K ! [Integers() ! c : c in Eltseq(Coefficient(rdiff,j))])/2^(epsilon-1) : j in [0..(Md-1)]];
	vprintf JacHypCnt, 3: "Reduced differential %o in time = %o\n", k+1, Cputime(tyme);
    end for;
    vprintf JacHypCnt, 3: "Total time to reduce differentials %o \n", Cputime(timediff);

    // at this point matrix M is matrix of Frobenius up to power 2^B, i.e. difference
    // with the correct one is multiple of 2^B (so not relative precision only)
    // we're leaving in N just not to lose anything
    
    // we need to trick Magma in forgetting about damned precision
    // so in norm computation precision is always reset to maximum
        
    timenorm := Cputime();
    NM := NormOfMat(M,Md,n);
    vprintf JacHypCnt, 3: "Total time to compute norm %o \n", Cputime(timenorm);
    
    // in the next step we could lose up to Valuation(g!,2)
    // to take care of non-integral entries in matrix, precision is always reset to max in UCoeffs
    
    Qp2 := pAdicField(p,N+Valuation(Factorial(g),2));
    //QpZ2 := PolynomialRing(Qp2); Z := QpZ2.1;
    K2 := UnramifiedExtension(Qp2,n);//K2 := ext<Qp2 | QpZ2 ! Eltseq(P)>;
    M2 := Matrix(K2,Md,Md,[K2 ! [Rationals() ! c : c in Eltseq(a)] : a in Eltseq(NM)]);    
    tyme := Cputime();
    q := #ResidueClassField(Integers(K2));
    UCoeffs := UpperCoeffs(M2,g,p^B,(-1)^iType*q);
    CharP := PolynomialRing(IntegerRing())! ([UCoeffs[i]*q^(g+1-i): i in [1..g]] cat Reverse(UCoeffs));
    vprintf JacHypCnt,3: "Characteristic polynomial time: %o\n",Cputime(tyme);
    
    return Parent(CharP)!Reverse(Coefficients(CharP));

end function;


function KedlayaChar2(C)
     // takes in hyperelliptic curve C

    Cnorm := NormalFormFiniteFieldChar2(C);
    f, h := HyperellipticPolynomials(Cnorm);    
    Polring := Parent(f);
    X := Polring.1;

    iType, sType := HyperellipticCurveChar2Type(f,h);

    vprintf JacHypCnt,3: "Curve is of type: %o\n", sType;
    
    CharPol := 0;
    
    // see if this is AS case or not .....

    c := LeadingCoefficient(h);
    Fact := Factorisation(h);
    if (Degree(h) eq 0) or ((#Fact eq 1) and (Degree(Fact[1][1]) eq 1)) then
	// h is either constant or power of linear factor
	if (Degree(h) gt 0) then  // need to shift by root of h
	    r := Roots(Fact[1][1])[1][1];
	    h := Evaluate(h,X+r);
	    f := Evaluate(f,X+r);
	end if;

	CharPol := KedlayaChar2AS(Degree(h),LeadingCoefficient(h),f);
	
    else
	// general case, already normalised
	
	CharPol := KedlayaChar2General(h,f);
	
    end if;
	
    return CharPol;
    
end function;

function TestKedlaya(gL,gU,nL,nU,step,nr)
    // tests nr random curves of genus between gL and gU
    // over finite fields of extension degree between nL and nU going by step

    OK := true;
    
    for n := nL to nU by step do
	F2n := FiniteField(2,n);
	F2nX := PolynomialRing(F2n); X := F2nX.1;
	for g := gL to gU do
	    for i := 1 to nr do
		h := F2nX ! [Random(F2n) : i in [0..g]];
		f := X^(2*g+1) + F2nX ! [Random(F2n) : i in [0..2*g]];
		while not (IsHyperellipticCurve([f,h])) do
		    h := F2nX ! [Random(F2n) : i in [0..g]];
		    f := X^(2*g+1) + F2nX ! [Random(F2n) : i in [0..2*g]];
		end while;
		C := HyperellipticCurve([f,h]);
		time Pol := KedlayaChar2(C);
		J := Jacobian(C);
		P := Random(J);
		print Pol;
		if ((Evaluate(Pol,1)*P)[3] ne 0) then // test is nok
		    print F2n, f, h;
		    OK := false;
		else
		    print n, g, i;
		end if;
	    end for;
	end for;
    end for;

    return OK;
    
end function;


function DoCurve(f,h)

    C := HyperellipticCurve([f,h]);
    tyme := Cputime();
    A := ZetaFunction(C);
    timeMestre := Cputime(tyme);

    tyme := Cputime();
    A := KedlayaChar2(C);
    timeKedlaya := Cputime(tyme);

    return timeMestre, timeKedlaya;
    
end function;


function KedlayaVsMestre(BL,BU,step)

    // runs a test on genus 2 to 4 with all possibilities of 2-torsion
    
    for b := BL to BU by step do

	printf "\nb = %o ------------------------------------------------ \n\n", b;
	
	// genus 2: e = 1

	n := b div 2;
	F2n := FiniteField(2,n);
	F2nX := PolynomialRing(F2n); X := F2nX.1;

	h := Random(F2n)*(X + Random(F2n))*(X + Random(F2n));
	f := X^5 + F2nX ! [Random(F2n) : i in [0..4]];
	m, k := DoCurve(f,h);
	printf "g=2, e=1 %o,    %o \n", m, k;

	// genus 2: e = 2
	
	h := F2nX ! [Random(F2n) : i in [0..2]];
	while not(IsIrreducible(h)) do
	    h := F2nX ! [Random(F2n) : i in [0..2]];
	end while;
	f := X^5 + F2nX ! [Random(F2n) : i in [0..4]];
	m, k := DoCurve(f,h);
	printf "g=2, e=2 %o,    %o \n", m, k;

	// genus 3, e = 1

	n := b div 3;
	F2n := FiniteField(2,n);
	F2nX := PolynomialRing(F2n); X := F2nX.1;
	
	h := Random(F2n)*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n));
	f := X^7 + F2nX ! [Random(F2n) : i in [0..6]];
	m, k := DoCurve(f,h);
	printf "g=3, e=1 %o,    %o \n", m, k;
	
	// genus 3, e = 2

	hpart := F2nX ! [Random(F2n) : i in [0..2]];
	while not(IsIrreducible(hpart)) do
	    hpart := F2nX ! [Random(F2n) : i in [0..2]];
	end while;
	h := Random(F2n)*(X + Random(F2n))*hpart;
	f := X^7 + F2nX ! [Random(F2n) : i in [0..6]];
	m, k := DoCurve(f,h);
	printf "g=3, e=2 %o,    %o \n", m, k;

	// genus 3, e = 3

	h := F2nX ! [Random(F2n) : i in [0..3]];
	while not(IsIrreducible(h)) do
	    h := F2nX ! [Random(F2n) : i in [0..3]];
	end while;
	f := X^7 + F2nX ! [Random(F2n) : i in [0..6]];
	m, k := DoCurve(f,h);
	printf "g=3, e=3 %o,    %o \n", m, k;

	// genus 4, e = 1

	n := b div 4;
	F2n := FiniteField(2,n);
	F2nX := PolynomialRing(F2n); X := F2nX.1;
	
	h := Random(F2n)*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n));
	f := X^9 + F2nX ! [Random(F2n) : i in [0..8]];
	m, k := DoCurve(f,h);
	printf "g=4, e=1 %o,    %o \n", m, k;

	// genus 4, e = 2

	hpart1 := F2nX ! [Random(F2n) : i in [0..2]];
	while not(IsIrreducible(hpart1)) do
	    hpart1 := F2nX ! [Random(F2n) : i in [0..2]];
	end while;
	hpart2 := F2nX ! [Random(F2n) : i in [0..2]];
	while not(IsIrreducible(hpart2)) do
	    hpart2 := F2nX ! [Random(F2n) : i in [0..2]];
	end while;
	h := Random(F2n)*hpart2*hpart1;
	f := X^9 + F2nX ! [Random(F2n) : i in [0..8]];
	m, k := DoCurve(f,h);
	printf "g=4, e=2 %o,    %o \n", m, k;
	
	// genus 4, e = 3

	hpart1 := F2nX ! [Random(F2n) : i in [0..3]];
	while not(IsIrreducible(hpart1)) do
	    hpart1 := F2nX ! [Random(F2n) : i in [0..3]];
	end while;
	h := Random(F2n)*(X + Random(F2n))*hpart1;
	f := X^9 + F2nX ! [Random(F2n) : i in [0..8]];
	m, k := DoCurve(f,h);
	printf "g=4, e=3 %o,    %o \n", m, k;

	// genus 4, e = 4

	hpart1 := F2nX ! [Random(F2n) : i in [0..4]];
	while not(IsIrreducible(hpart1)) do
	    hpart1 := F2nX ! [Random(F2n) : i in [0..4]];
	end while;
	h := Random(F2n)*hpart1;
	f := X^9 + F2nX ! [Random(F2n) : i in [0..8]];
	m, k := DoCurve(f,h);
	printf "g=4, e=4 %o,    %o \n", m, k;

	// genus 5, e = 1

	n := b div 5;
	F2n := FiniteField(2,n);
	F2nX := PolynomialRing(F2n); X := F2nX.1;
	
	h := Random(F2n)*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n))*(X + Random(F2n));
	f := X^11 + F2nX ! [Random(F2n) : i in [0..10]];
	m, k := DoCurve(f,h);
	printf "g=5, e=1 %o,    %o \n", m, k;
	
    end for;
    
    return 0;
    
end function;


