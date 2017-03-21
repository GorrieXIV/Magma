freeze;

declare verbose resolvents, 4;

function EltSeq(f,D)
    if Type(f) eq RngUPolElt then
	F := Eltseq(f);
    else 
	F,v := Eltseq(f);
	for i in [1..v] do
	    Insert(~F,1,0);
	end for;
    end if;
    while #F le D do
	Append(~F,0);
    end while;
    return F;  
end function;

function rev(D,P)
    N:=Degree(P);
    L:=Eltseq(P);
    Reverse(~L);
    L := [0 : k in [1..D-N]] cat L;
    return Polynomial(CoefficientRing(Parent(P)),L);
end function;

intrinsic PolynomialToPowerSums(h::RngUPolElt, N::RngIntElt) -> SeqEnum
    {Given a polynomial, return the sequence of the first N power sums of the roots.}
    D := Degree(h);
    S := PowerSeriesRing(FieldOfFractions(CoefficientRing(h)),N+1);
    hd := Derivative(h);
    A := Evaluate(rev(D-1,hd),S.1);
    B := Evaluate(rev(D,h),S.1);
    //    L:= EltSeq(A/B,D);
    L:= EltSeq(A/B,N);
    Remove(~L,1);
    return L;
end intrinsic;

intrinsic PowerSumsToPolynomial(powers::SeqEnum) -> RngUPolElt
    {Compute the polynomial of degree n, when we know the first n power sums}
    if GetVerbose("resolvents") ge 4 then
     printf "Starting PowerSumsToPolynomial with %o coefficients.\n",#powers;
     lzc := 0; tzc := 0;
     while lzc lt #powers and powers[lzc+1] eq 0 do lzc := lzc + 1; end while;
     while tzc lt #powers and powers[#powers - tzc] eq 0 do tzc := tzc + 1; end while;
     printf "%o leading and %o trailing zeros\n",lzc,tzc;
    end if;
    D:=#powers;
    SS<T> := PowerSeriesRing(FieldOfFractions(Parent(Rep(powers))));
    S := SS ! powers; //exact: (Newton(h) - D)/T
    R := SS ! [1,-powers[1]]; // exact
    n := 2;
    while n le D do
	SS`DefaultPrecision:=Minimum(ShiftLeft(n,1)-1,D);
	RR := Derivative(R)/R;
	Md := -(RR + S);
	M := 1 + Integral(Md);
        if AbsolutePrecision(M) gt 2*n then
         ChangePrecision(~M,2*n);
        end if;
	R := R*M;
        
	vprintf resolvents,4: "Precision of R: %o\tvs. maximal needed:  %o\n",AbsolutePrecision(R),2*n;
	R := Truncate(R);
	n := ShiftLeft(n,1);
    end while;
    ChangePrecision(~R,D+1);
    return rev(D,R);
end intrinsic;

function ListOfPowers(m,D)
    a:=One(Parent(m));
    l:=[];
    for j in [0..D] do //power sums of x-m
	Append(~l,a);
	a *:= m;
    end for;
    return l;
end function;

intrinsic MSum(f::RngUPolElt,m::RngIntElt) -> RngUPolElt
    {Computes the polynomial which has alpha_(i_1)+..+alpha_(i_m) as roots}

    vprintf resolvents,1:"Enter 'MSum' with m = %o\n",m;
    IndentPush();
    if m eq 1 then
	vprint resolvents, 1: "Leaving...";
	IndentPop();
	return f;
    end if;
    L:=[f];
    for i in [2..m-1] do
	Append(~L,MSum(f,i));
    end for;
    
    D := Binomial(Degree(f),m);
    K:=FieldOfFractions(CoefficientRing(f));
    SS<T> := PowerSeriesRing(K,D+1);
    trry:=true;

    if trry then
	N:=Factorial(D+1);
	E:=[N];
	for k in [1..D] do
	    Append(~E,E[k] div k);
	end for;
	E := SS ! E;
	M := N^2;
    else
	E:=Exp(SS.1);
    end if;

    LL:=[];
    for i in [1..m-1] do
	powers:=PolynomialToPowerSums(L[i],D); 
	Insert(~powers,1,Degree(L[i]));
	F:=SS ! powers;
	Append(~LL, F);
    end for;//LL[i] contains the Newton series of f^{+i}

    if trry then
	res:=Laplace(Convolution(LL[1],E)*Convolution(LL[m-1],E)) div M;
    else
	res:=Laplace(Convolution(LL[1],E)*Convolution(LL[m-1],E));
    end if;

    H:=SS ! ListOfPowers(m,D);
    H:=Convolution(LL[1],H); //f . (T-m)
    vprintf resolvents, 4: "scalar multiplication 1... ";
    vtime resolvents, 4: res:=res + (-1)^(m+1)*H;
    for i in [2..m-1] do
	H := SS ! ListOfPowers(i,D);
	H := Convolution(LL[1],H); //f . (T-i)
	H := Convolution(H,E);
	F := Convolution(LL[m-i],E); // N(f^{m-i} . E
	if trry then 
	    H := Laplace(F*H) div M; // Umkehrung zu Punkt mit E
	else
	    H := Laplace(F*H); // Umkehrung zu Punkt mit E
	end if;
	res := res + (-1)^(i+1)*H;
    end for;
    vprintf resolvents, 4: "scalar division... ";
    vtime resolvents, 4: res := res/m;
    ll := EltSeq(res,D);
    Remove(~ll,1);
    vprint resolvents, 1: "Leaving...";
    IndentPop();
    return PowerSumsToPolynomial(ll);
end intrinsic;

intrinsic MSet(f::RngUPolElt,m::RngIntElt) -> RngUPolElt
    {Computes the polynomial which has alpha_(i_1)*..*alpha_(i_m) as roots}
    n:=Degree(f);
    N:=Binomial(n,m);
    NN:=N*m;
    L1:=PolynomialToPowerSums(f, NN);
    R:= Integers(CoefficientRing(f));
    L1:=[R ! x:x in L1];
    Insert(~L1,1,Degree(f));
    PP:=[L1];
    for i in [2..m] do
	l:=[];
	for k in [0..N] do
	    a:=Zero(R);
	    for h in [1..i-1] do
		a+:=(-1)^(h+1)*L1[k*h+1]*PP[i-h][k+1];        
	    end for;
	    a+:=(-1)^(i+1)*L1[k*i+1];
	    a:=a div i;
	    Append(~l,a);
	end for;
	Append(~PP,l);
    end for; 
    ll:=PP[m];  
    Remove(~ll,1);
    return PowerSumsToPolynomial(ll);
end intrinsic;

intrinsic MDiff2(f::RngUPolElt) -> RngUPolElt
    {Computes the polynomial which has alpha_i-alpha_j as roots}
    D:=Degree(f)*(Degree(f)-1);
    SS<x> := PowerSeriesRing(FieldOfFractions(CoefficientRing(f)),D+1);
    E:=Exp(x); 
    L1:=PolynomialToPowerSums(f, D); 
    Insert(~L1,1,Degree(f));
    L2:=L1; 
    i:=2;
    while i le #L2 do
	L2[i]:=-L2[i];
	i+:=2;
    end while;
    F1:=SS ! L1;
    FF1:=Convolution(F1,E);
    F2:=SS ! L2;
    FF2:=Convolution(F2,E);
    R:=FF1*FF2;
    R:=Laplace(R);
    ll:=EltSeq(R,D);
    Remove(~ll,1);
    return PowerSumsToPolynomial(ll);
end intrinsic;

intrinsic SumPoly(f::RngUPolElt,g::RngUPolElt) -> RngUPolElt
    {Computes the polynomial which has alpha_i+beta_j as roots}

    D:=Degree(f)*Degree(g);
    SS<x> := PowerSeriesRing(FieldOfFractions(CoefficientRing(f)),D+1);
    // SS<x> := PowerSeriesRing(RationalField(),D+1);
    E:=Exp(x); 
    L1:=PolynomialToPowerSums(f, D); 
    Insert(~L1,1,Degree(f));
    F:=SS ! L1;
    //F;
    L2:=PolynomialToPowerSums(g, D);
    Insert(~L2,1,Degree(g));
    G:=SS ! L2;
    //G;
    FF:=Convolution(F,E);
    //FF;
    GG:=Convolution(G,E);
    //GG;
    R:=Laplace(FF*GG);
    //R;
    ll:=EltSeq(R,D);
    Remove(~ll,1);
    return PowerSumsToPolynomial(ll);
end intrinsic;

///////////////////////////////////////////////////////////
// compute minimal polynomial using O_K basis and powersums
intrinsic MinimalPolynomialByTraces(a::FldElt)-> RngUPolElt
    {Computes the minimal polynomial of a over its basefield}
    K:=FieldOfFractions(Parent(a));
    require IsZero(Characteristic(K)) or (not IsDivisibleBy(Degree(K),Characteristic(K))): "char(K) must not divide Degree(K)"; 
    B:=[];
    c:=One(K);
    for k in [1..Degree(K)] do
	c*:=a;
	Append(~B,c);
    end for;
    D:=[ Trace(x) : x in B];
    R:=PolynomialRing(K);
    h:=R ! PowerSumsToPolynomial(D);
    Dh:=Derivative(h);
    f:=GCD(Dh,h);
    return h div f;
end intrinsic;
