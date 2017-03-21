
freeze;
declare attributes CrvEll: MS_ScalePlus,MS_ScaleMinus; /* MW 15 Nov 2010 */
declare verbose pAdicLSeries,1;

function get_period(E,A,T)
 a,b,c,d:=Explode(A); eps:=-RootNumber(E); N:=Conductor(E); S:=Sqrt(N);
 p1:=ComplexField(9)![c/d,1/d/S]; p2:=ComplexField(9)![b/d,1/d/S];
 p3:=ComplexField(9)![0,1/S]; R:=ModularParametrization(E,[p1,p2,p3]);
 return (1-eps)*R[3]+eps*R[1]-R[2]; end function;          

KS:=KroneckerSymbol;
function get_scaling(E,s,M,T) // are the Plus/Minus always the same ?
 if s eq 1 and assigned E`MS_ScalePlus then return E`MS_ScalePlus; end if;
 if s eq -1 and assigned E`MS_ScaleMinus then return E`MS_ScaleMinus; end if;
 N:=Conductor(E); eps:=RootNumber(E);
 if eps eq +1 and s eq 1 then r,Lv:=AnalyticRank(E : Precision:=5);
  if r eq 0 then rat:=BestApproximation(Lv/RealPeriod(E),100);
   v:=-Vector(Eltseq(Parent(M.1)!<1,[Infinity(),0]>))*T;
   vprintf pAdicLSeries: "Obtained scaling %o from curve directly\n",v[1]/rat;
   return v[1]/rat; end if; end if;
/*
 // Cremona's trick, but I don't use it except for checking when testing
 // only works with nonsquare conductor
 P:=[p : p in PrimesUpTo(100) | Gcd(p,2*N) eq 1 and KS(-N,p)*eps eq 1];
 if s eq 1 then P:=[p : p in P | p mod 4 eq 1];
  for p in P do Q:=MinimalModel(QuadraticTwist(E,p));
   assert RootNumber(Q) eq +1; r,Lv:=AnalyticRank(Q : Precision:=5);
   if r eq 0 then rat:=BestApproximation(Lv/RealPeriod(E)*Sqrt(p),100);
    v:=&+[KS(p,k)*Vector(Eltseq(Parent(M.1)!<1,[k/p,0]>))*T : k in [1..p-1]];
    vprintf pAdicLSeries: "Obtained scaling %o from twist by %o\n",v[1]/rat,p;
   return v[1]/rat; end if; end for; end if;
 if s eq -1 then P:=[p : p in P | p mod 4 eq 3];
  for p in P do Q:=MinimalModel(QuadraticTwist(E,-p));
   assert RootNumber(Q) eq +1; r,Lv:=AnalyticRank(Q : Precision:=5);
   if r eq 0 then r:=BestApproximation(Lv/Imaginary(Periods(E)[2])*Sqrt(p),99);
    v:=&+[KS(-p,k)*Vector(Eltseq(Parent(M.1)!<1,[k/p,0]>))*T : k in [1..p-1]];
    vprintf pAdicLSeries: "Obtained scaling %o from twist by %o\n",v[1]/r,-p;
   return v[1]/r; end if; end for; end if;
 */

 p:=2; num:=0;
 while true do num:=num+1; c:=Random([1..num]);
  while c*N mod p eq 0 do p:=NextPrime(p); end while;
  g,a,b:=XGCD(p,c*N); assert g eq 1;
  if s eq 1 then per:=RealPeriod(E); cp:=Real(get_period(E,[a,b,-c,p],[]));
  else per:=Imaginary(Periods(E)[2]);
       cp:=Imaginary(get_period(E,[a,b,-c,p],[])); end if;
  assert Determinant(Matrix(2,2,[a,b,-c*N,p])) eq 1;
  rat:=BestApproximation(cp/per,100); if rat eq 0 then continue; end if;
  v1:=Vector(Eltseq(Parent(M.1)!<1,[0,b/p]>))*T;
  if v1[1] eq 0 then continue; end if;
  vprintf pAdicLSeries: "Scaling %o from %o\n",v1[1]/rat,[a,b,-c*N,p];
  return v1[1]/rat; end while; end function;

function eval_ms(E,r : s:=1,M:=0,T:=0,D:=1) r:=Rationals()!r;
 if D ne 1 then
  return Sign(D)*&+[KroneckerSymbol(D,u)*eval_ms(E,r+u/D:s:=s,M:=M,T:=T) :
		    u in [1..Abs(D)] | Gcd(u,D) eq 1]; end if;
 if Type(M) ne ModSym then M:=ModularSymbols(E,s);
  T:=Transpose(Matrix(Basis(DualRepresentation(M)))); end if;
 r:=Rationals()!r; r:=r-Round(r);
 v1:=Vector(Eltseq(Parent(M.1)!<1,[r,Infinity()]>))*T;
 return v1[1]; end function;

function get_alpha(E,p,prec)
 ap:=FrobeniusTraceDirect(E,p); K:=pAdicField(p,prec);
 if Conductor(E) mod p eq 0 then return K!ap; end if;
 if ap mod p ne 0 then R:=Roots(Polynomial([p,-ap,1]),K);
  return [r[1] : r in R | Valuation(r[1]) lt 1][1];
 else assert false; E:=ext<K|Polynomial([p,0,1])>; // supersingular case
  return Roots(Polynomial([p,-ap,1],E))[1][1]; end if; end function;

function measure(E,p,a,n,alpha : M:=0,T:=0,D:=1)
 u:=KroneckerSymbol(D,p); eps:=Sign(D)*u^n;
 if Conductor(E) mod p eq 0 then
 return eps*eval_ms(E,a/p^n : s:=Sign(D),M:=M,T:=T,D:=D)/alpha^n; end if;
 z:=eps/alpha^n; w:=p^(n-1);
 return z*eval_ms(E,a/(p*w) : s:=Sign(D),M:=M,T:=T,D:=D)-
        u*(z/alpha)*eval_ms(E,a/w : s:=Sign(D),M:=M,T:=T,D:=D); end function;

function ChangeAbsolutePrecision(x,prec) K:=Parent(x); p:=K.1*Prime(K);
 u:=ChangePrecision(K.1,prec);
 q:=p^prec; q:=(q+u)-u; return (x+q)-q; end function;

function series(E,p,cprec,sprec,D,do_scale)
 _<T>:=PowerSeriesRing(Integers(),sprec+1);  
 V:=[Min([Valuation(Coefficient((1+T)^(p^cprec)-1,i),p) : i in [1..j]])
	: j in [1..sprec]]; MaxV:=Max(V);
 internal_coeff_prec:=cprec+MaxV+25; // can be increased with little loss
 R<T>:=PowerSeriesRing(Rationals(),sprec);
 gamma:=1+p; T1:=R!1; gammapow:=1; L:=0;
 TEICH:=TeichmuellerSystem(pAdicRing(p,internal_coeff_prec)) cat [0];
 alpha:=get_alpha(E,p,internal_coeff_prec);
 Msave:=ModularSymbols(E,Sign(D));
 Tsave:=Transpose(Matrix(Basis(DualRepresentation(Msave))));
 for j in [1..p^(cprec-1)] do s:=0;
  for a in [1..p-1] do b:=TEICH[a+1]*gammapow;
   meas:=measure(E,p,b,cprec,alpha : M:=Msave,T:=Tsave,D:=D); s:=s+meas;
   end for; L:=L+s*T1; T1:=T1*(1+T); gammapow:=gammapow*gamma; end for;
 if do_scale then rs:=0;
  if Sign(D) eq 1 then
   if assigned E`MS_ScalePlus then sc:=E`MS_ScalePlus;
   else sc:=get_scaling(E,+1,Msave,Tsave); E`MS_ScalePlus:=sc; end if;
   if D ne 1 then
    Q:=MinimalModel(QuadraticTwist(E,D));
    rat:=BestApproximation(RealPeriod(E)/RealPeriod(Q)/Sqrt(D),99);
    vprintf pAdicLSeries: "Rescaling factor from twisting is %o\n",rat;
   else rat:=1; end if;
   sc:=sc*rat;
  else if assigned E`MS_ScaleMinus then sc:=E`MS_ScaleMinus;
       else sc:=get_scaling(E,-1,Msave,Tsave); E`MS_ScaleMinus:=sc; end if;
   Q:=MinimalModel(QuadraticTwist(E,D));
   rat:=BestApproximation(RealPeriod(E)/Imaginary(Periods(Q)[2])/Sqrt(-D),99);
   vprintf pAdicLSeries: "Rescaling factor from twisting is %o\n",-rat;
   sc:=sc*-rat; end if;
 else m:=Min([Valuation(c) : c in Coefficients(L)]); rs:=0;
  if IsFinite(m) then sc:=p^m; rs:=m; else sc:=1; end if; end if;
 L:=L/sc; C:=Coefficients(L); V:=[0] cat V;
 C[1]:=ChangeAbsolutePrecision(C[1],internal_coeff_prec-2);
 for v in [2..#C] do
  C[v]:=ChangeAbsolutePrecision(C[v],cprec-1-MaxV+V[v]); end for;
 L:=Parent(L)!Polynomial(C); if Discriminant(E) gt 0 then L:=L/2; end if;
 return L; end function;

intrinsic pAdicLSeries
(E::CrvEll[FldRat],p::RngIntElt :
 CoefficientPrecision:=3,SeriesPrecision:=5,
 QuadraticTwist:=1,ProperScaling:=true) -> RngSerPowElt
{Given a good ordinary odd prime or one of multiplicative reduction,
 compute the p-adic L-function of the elliptic curve at that prime}
 require IsPrime(p) and p ne 2: "p must be an odd prime";
 require Valuation(Conductor(E),p) le 1: "Cannot have additive reduciton at p";
 require FrobeniusTraceDirect(E,p) mod p ne 0: "Prime cannot be supersingular";
 require QuadraticTwist eq 1 or IsFundamentalDiscriminant(QuadraticTwist):
 "QuadraticTwist must be a fundamental discrimtinant";
 require QuadraticTwist mod p ne 0: "QuadraticTwist must be coprime to p";
 require Gcd(QuadraticTwist,Conductor(E)) eq 1: "Gcd(QuadraticTwist,N) not 1";
 require CoefficientPrecision ge 1: "Coefficient precision must be positive";
 require SeriesPrecision ge 1: "Series precision must be positive";
 require IsMinimalModel(E): "Model must be minimal";
 return series(E,p,CoefficientPrecision+1,SeriesPrecision+1,
	       QuadraticTwist,ProperScaling); end intrinsic;
