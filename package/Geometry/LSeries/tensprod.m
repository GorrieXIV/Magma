
freeze;

import "Lseries.m" : MultiplicativityCheck,LocalFactorFun;
import "euler_factor.m" : CheckIsNewForm;
import "arithmetic.m" : SimplifyLProduct;

function TR(e,f) return Evaluate(f,e*Parent(f).1); end function;
function TensorRoots_dim1(L,f) return TR(-Coefficient(L,1),f); end function;

PSR:=PowerSeriesRing; Q:=Rationals();
function TensorRoots_general(f,g) // from Anton Mellit
 f:=PSR(FieldOfFractions(BaseRing(Parent(f))),AbsolutePrecision(f))!f;
 g:=PSR(FieldOfFractions(BaseRing(Parent(g))),AbsolutePrecision(g))!g;
 lf:=Coefficient(f,0); assert lf ne 0; df:=Derivative(Log(f/lf));
 lg:=Coefficient(g,0); assert lg ne 0; dg:=Derivative(Log(g/lg));
 return lf*lg*Exp(-Integral(Convolution(df,dg))); end function;

intrinsic TensorProduct(f::RngUPolElt,g::RngUPolElt) -> RngUPolElt
{Given two polynomials (over Q), take their tensor product.
 This has as roots alpha*beta where alpha,beta run over the roots of f,g}
 vf:=Valuation(f); vg:=Valuation(g); sc:=vf*Degree(g)+vg*Degree(f)-vf*vg;
 f:=f/Parent(f).1^vf; g:=g/Parent(g).1^vg; P:=PSR(Q,Degree(f)*Degree(g)+1);
 b1,f:=IsCoercible(P,f); b2,g:=IsCoercible(P,g);
 require b1 and b2: "Polynomials must coerce into Q";
 res:=Polynomial(Coefficients(TensorRoots_general(f,g)));
 res:=res*Parent(res).1^sc; return res; end intrinsic;

////////////////////////////////////////////////////////////////////////

AbsPrec:=Precision;
intrinsic TensorProduct
(L1::LSer, L2::LSer, ExcFactors::[<>] : Sign:=0, Precision:=0) -> LSer
{ For L-series L1=L(V1), L2=L(V2),
   associated to l-adic representations V1 and V2 (a la Serre),
   compute their tensor product L(V1 tensor V2).
  ExcFactors is a list of tuples, each of the form <p,v> or <p,v,F_p(x)>
   that give, for primes p where both L1 and L2 have bad reduction, the
   valuation v of the conductor of (V1 tensor V2) at p and the inverse
   local factor at p. If the data is not provided for such a prime p,
   e.g. if you call TensorProduct(L1,L2,[]), Magma will attempt to compute
   the local factors by assuming that the inertia invariants behave well at p,
    (V1 tensor V2)^(I_p) = V1^(I_p) tensor V2^(I_p).
  It will also compute the conductor exponents by predicting the tame
   and wild degrees from the degrees of the local factors [This is not
   guaranteed to work correctly, so use CheckFunctionalEquation to verify it.]
  You may provide the sign of L(V1 tensor V2) if you happen to know it.
   Note that it can not be determined from the respective signs of L1 and L2. }

  if Precision eq 0 then precision:=Min(L1`precision,L2`precision);
   else precision:=Precision; end if;
  if precision eq 0 then precision:=GetPrecision(1.2); end if;
  if L2`parent cmpeq Rationals() and #ExcFactors eq 0 then
   LSetPrecision(L1,precision); return L1; end if; // does nothing
  if L1`parent cmpeq Rationals() and #ExcFactors eq 0 then
   LSetPrecision(L2,precision); return L2; end if;
  if IsOne(L1) then return LSeries(1); end if; // tensoring with 1 works as 0
  if IsOne(L2) then return LSeries(1); end if;

  require Type(L1`weight) eq RngIntElt and L1`weight ge 0:
  "The first L-Series must have nonnegative integral weight";
  require Type(L2`weight) eq RngIntElt and L2`weight ge 0:
  "The second L-Series must have nonnegative integral weight";
  require &and[IsCoercible(Integers(),x) : x in L1`gamma cat L2`gamma]:
  "Hodge numbers must be integral";
  require MultiplicativityCheck(L1) and MultiplicativityCheck(L2):
    "L-Series does not appear to have multiplicative coefficients";

  b1,HS1:=HasHodgeStructure(L1); b2,HS2:=HasHodgeStructure(L2);
  require b1: "First L-Series has no Hodge structure";
  require b2: "Second L-Series has no Hodge structure";

  product:=((L1`prod cmpne false) or (L2`prod cmpne false))
            and IsEmpty(ExcFactors);
// hmm, should always decompose, can then use LSetCoefficients on the result?
// and put this first, then?

  if Type(L1`parent) eq ModFrmElt then CheckIsNewForm(L1`parent); end if;
  if Type(L2`parent) eq ModFrmElt then CheckIsNewForm(L2`parent); end if;

  d1:=Degree(L1); d2:=Degree(L2); c1:=L1`conductor; c2:=L2`conductor;
  sign:=Sign; poles:=[x+y-1: x in L1`lpoles, y in L2`lpoles]; // think OK
  C:=ComplexField(precision);
  S<x>:=PowerSeriesRing(C,40); // will handle correctly 2^40=10^12 coeffs

  excp:=[x[1] : x in ExcFactors];

  L1loc:=LocalFactorFun(L1,precision); L2loc:=LocalFactorFun(L2,precision);
  name:=<L1," tensor ",L2>; parent:=<L1`parent,"tensor",L2`parent>;
  conductor:=1; BOTH_ONE:=[Integers()|];
  if not product then
   for p in PrimeDivisors(c1*c2) do //prec d1,d2 can be high, user should say
    t1:=L1loc(p,d1); if t1 eq 1 then t1:=PolynomialRing(Integers())!1; end if;
    tame1:=d1-Degree(t1); wild1:=Valuation(c1,p)-tame1;
    t2:=L2loc(p,d2); if t2 eq 1 then t2:=PolynomialRing(Integers())!1; end if;
    tame2:=d2-Degree(t2); wild2:=Valuation(c2,p)-tame2;
    if tame1 eq 1 and Type(L1`parent) in {CrvEll,ModFrmElt}
     and tame2 eq 1 and Type(L2`parent) in {CrvEll,ModFrmElt}	
      then BOTH_ONE cat:=[p]; end if;
    if tame1 ne 0 and tame2 ne 0 and not (p in excp) then
     printf "WARNING: %o is ramified in each part of tensor prod\n",p; end if;
    if wild1 ne 0 and wild2 ne 0 and not (p in excp) then
     printf "WARNING: %o has wild ramification in tensor product\n",p; end if;
    val:=d1*d2-(d1-tame1)*(d2-tame2) + d1*wild2 + d2*wild1;
    conductor*:=p^val; end for; end if; // wild guess
  for t in ExcFactors do
   conductor*:=t[1]^(Integers()!t[2]-Valuation(conductor,t[1]));
   Exclude(~BOTH_ONE,t[1]); end for;
  conductor/:=&*BOTH_ONE; conductor:=Integers()!conductor;

  excp:=[x[1] : x in ExcFactors | #x gt 2];

  function FIX(f) C:=Coefficients(f);
   if not &and[IsCoercible(Integers(),c) : c in C] then return f; end if;
   C:=ChangeUniverse(C,Integers());
   if Type(f) eq RngUPolElt then return Polynomial(C); end if;
   assert Type(f) eq RngSerPowElt;
   PSR:=PowerSeriesRing(Integers(),AbsolutePrecision(f));
   return PSR!C; end function;

  function cf(p,d: Precision:=0)
   if p in excp then return ExcFactors[Index(excp,p)][3]; end if;
   L1loc:=LocalFactorFun(L1,Precision); l1:=L1loc(p,d);
   L2loc:=LocalFactorFun(L2,Precision); l2:=L2loc(p,d);
   if l1 eq 1 then l1:=PolynomialRing(Integers())!1; end if;
   if l2 eq 1 then l2:=PolynomialRing(Integers())!1; end if;
   l1:=FIX(l1); l2:=FIX(l2);
   BR1:=BaseRing(Parent(l1)); BR2:=BaseRing(Parent(l2));
   S1:=PowerSeriesRing(BR1); S2:=PowerSeriesRing(BR2);
   if Type(BR1) eq Type(BR2) then U:=S1.1; else U:=x; end if;
   if Type(BR1) in {FldRat,RngInt} and Type(BR2) in {FldRat,RngInt} then
    U:=PowerSeriesRing(Rationals()).1; end if;
   if (d eq 1) then
    return FIX(1-Coefficient(l1,1)*Coefficient(l2,1)*U+O(U^2)); end if;
   if p in BOTH_ONE then E:=1-Coefficient(l1,1)*Coefficient(l2,1)*U;
    return FIX(E*Evaluate(E,p*U)); end if;
   d1:=Degree(l1); d2:=Degree(l2);
   dmin:=Min(d1*d2,d); l1:=S1!l1+O(S1.1^(d+1)); l2:=S2!l2+O(S2.1^(d+1));
   if d1*d2 eq 0 then return FIX(1+O(U^(d+1))); end if;
   if d1 eq 1 then return FIX(TensorRoots_dim1(l1,l2)+O(U^(d+1))); end if;
   if d2 eq 1 then return FIX(TensorRoots_dim1(l2,l1)+O(U^(d+1))); end if;
   res:=TensorRoots_general(l1,l2)+O(U^(d+1));
   return FIX(res); end function;

  L:=LSeries(HS1*HS2,conductor,cf: Sign:=sign, Parent:=parent,
	     Precision:=precision, Poles:=poles, Residues:=[], Name:=name);
  if product then
   P1:=L1`prod cmpne false select L1`prod else [<L1,1>];
   P2:=L2`prod cmpne false select L2`prod else [<L2,1>];
   L`prod:=[<TensorProduct(F1[1],F2[1],[] : Precision:=precision),
	    F1[2]*F2[2]>: F1 in P1, F2 in P2]; SimplifyLProduct(~L); end if;
  return L; end intrinsic;

intrinsic TensorProduct
(L1::LSer,L2::LSer : Sign:=0,Precision:=0,BadPrimes:=[]) -> LSer {"}//"
 return TensorProduct(L1,L2,BadPrimes : Sign:=Sign, Precision:=Precision);
 end intrinsic;

////////////////////////////////////////////////////////////////////////

/*************************************************************************/

function HodgeStructureK(H,K) d:=Degree(K); IP:=InfinitePlaces(K);
 A:=SequenceToMultiset([Sort([h[1],h[2]]) : h in H]); B:=[* *];
 for e in Set(A) do m:=Multiplicity(A,e); assert m mod d eq 0;
  if e[1] eq e[2] then J:=[h : h in H | h[1] eq e[1] and h[2] eq e[2]];
   J3:=[j[3] : j in J]; CP:=[ip : ip in IP | not IsReal(ip)];
   C:=[* <[e[1],e[2],2],ip> : ip in CP *];
   for i in [1..#CP] do Exclude(~J3,0); Exclude(~J3,1); end for;
   RP:=[ip : ip in IP | IsReal(ip)];
   C cat:=[* <[e[1],e[2],J3[i]],RP[i]> : i in [1..#RP] *]; B cat:=C;
  else B cat:=[* <[e[1],e[2],2],ip> : i in [1..m div d], ip in IP *]; end if;
  end for; return B; end function;

function tens_prod_HSK(HS1,HS2,K) H:=[* *]; IP:=InfinitePlaces(K);
 for ip in IP do H1:=[* h[1] : h in HS1 | h[2] eq ip *];
  H2:=[* h[1] : h in HS2 | h[2] eq ip *];
  for h1 in H1, h2 in H2 do e:=2; v1:=h1[1]+h2[1]; v2:=h1[2]+h2[2];
   if v1 eq v2 then // unsure about some of this
    if h1[1] gt h2[1] then e:=1; elif h1[1] lt h2[1] then e:=0;
    else e:=(h1[3]+h2[3]) mod 2; end if; end if;
   H cat:=[* <[v1,v2,e],ip> *]; end for; end for; return H; end function;

function gamma_factorsK(wt,HS) G:=[]; // wt is unused?
 for h in HS do
  if IsReal(h[2]) then
   if h[1][1] eq h[1][2] then G cat:=[-h[1][1]+h[1][3]];
   elif h[1][1] lt h[1][2] then G cat:=[-h[1][1],-h[1][1]+1]; end if;
  else m:=Min(h[1][1],h[1][2]); G cat:=[-m,-m+1]; end if; end for;
  Sort(~G); return G; end function;
// not sure what is happening here?
// need to combine (p,q) and (q,p) in real case

intrinsic TensorProduct
(L1::LSer,L2::LSer,ExcFactors::[<>],K::FldNum : Sign:=0,Precision:=0) -> LSer
 { Same as TensorProduct, but with the Euler product over a number field }

  if Precision eq 0 then precision:=Max(L1`precision,L2`precision);
    else precision:=Precision; end if;
  if precision eq 0 then precision:=GetPrecision(1.2); end if;

  require Type(L1`weight) eq RngIntElt and L1`weight ge 0:
  "The first L-Series must have nonnegative integral weight";
  require Type(L2`weight) eq RngIntElt and L2`weight ge 0:
  "The second L-Series must have nonnegative integral weight";
  require &and[IsCoercible(Integers(),x) : x in L1`gamma cat L2`gamma]:
  "Hodge numbers must be integral";
  require MultiplicativityCheck(L1) and MultiplicativityCheck(L2):
    "L-Series does not appear to have multiplicative coefficients";

  require assigned L1`degreeK and L1`degreeK[2] eq K:
    "First L-series is not defined as an Euler product over K";
  require assigned L2`degreeK and L2`degreeK[2] eq K:
    "Second L-series is not defined as an Euler product over K";

  if Type(L1`parent) eq ModFrmElt then CheckIsNewForm(L1`parent); end if;
  if Type(L2`parent) eq ModFrmElt then CheckIsNewForm(L2`parent); end if;

  weight:=L1`weight+L2`weight-1;
  hodgeK:=tens_prod_HSK(L1`hodgeK,L2`hodgeK,K);
  gamma:=gamma_factorsK(weight-1,hodgeK);

  product:=((L1`prod cmpne false) or (L2`prod cmpne false))
            and IsEmpty(ExcFactors);
  if product and
   ((L1`prod cmpne false and
     not &and[assigned L[1]`degreeK and L[1]`degreeK[2] eq K : L in L1`prod])
    or
    (L2`prod cmpne false and
     not &and[assigned L[1]`degreeK and L[1]`degreeK[2] eq K : L in L2`prod]))
    then product:=false; end if;

// hmm, should always decompose, can then use LSetCoefficients on the result?
// and put this first, then?

  d1:=L1`degreeK[1]; d2:=L2`degreeK[1];
  sign:=Sign; poles:=[x+y-1: x in L1`lpoles, y in L2`lpoles]; // think OK
  C:=ComplexField(precision); S<x>:=PowerSeriesRing(C,40);
  name:=<L1," tensor ",L2," over ",K>; parent:=<L1`parent,"tensor",L2`parent>;
  OK:=IntegerRing(K); conductor:=1*OK;

  excp:=[x[1] : x in ExcFactors];

  if not product then
   for F in Factorization(L1`condK*L2`condK) do P:=F[1];
    t1:=L1`cffuncK(P,d1*Degree(P)); tame1P:=d1-Degree(t1) div Degree(P);
    t2:=L2`cffuncK(P,d2*Degree(P)); tame2P:=d2-Degree(t2) div Degree(P);
   if tame1P ne 0 and tame2P ne 0 and not (P in excp) then
     printf "WARNING: %o is ramified in each part of tensor prod\n",P; end if;
    w1P:=Valuation(L1`condK,P)-tame1P; w2P:=Valuation(L2`condK,P)-tame2P;
   if w1P ne 0 and w2P ne 0 and not (P in excp) then
    printf "WARNING: %o has wild ramification in tensor product\n",P; end if;
   val:= d1*d2 - (d1-tame1P)*(d2-tame2P) + d1*w2P + d2*w1P; conductor*:=P^val;
   end for; end if;
  for t in ExcFactors do
   conductor*:=t[1]^(Integers()!t[2]-Valuation(conductor,t[1])); end for;
  N:=Integers()!Norm(conductor/Gcd(conductor,Different(OK))*Discriminant(OK));

  excp:=[x[1] : x in ExcFactors | #x gt 2];

  function cffuncK(P,d : Precision:=precision)
   if P in excp then return ExcFactors[Index(excp,P)][3]; end if;
   ef1:=S!L1`cffuncK(P,d : Precision:=Precision)+O(x^(d+1));
   ef2:=S!L2`cffuncK(P,d : Precision:=Precision)+O(x^(d+1));
   ef1:=&+[Coefficient(ef1,i*Degree(P))*x^i : i in [0..d div Degree(P)]];
   ef2:=&+[Coefficient(ef2,i*Degree(P))*x^i : i in [0..d div Degree(P)]];
   if (d eq 1) then
    return 1-Coefficient(ef1,1)*Coefficient(ef2,1)*x^Degree(P)+O(x^2); end if;
   d1:=Degree(ef1); d2:=Degree(ef2);
   if d1*d2 eq 0 then return 1+O(x^(d+1)); end if;
   if d1 eq 1 then R:=TensorRoots_dim1(ef1,ef2)+O(x^(d+1)); end if;
   if d2 eq 1 then R:=TensorRoots_dim1(ef2,ef1)+O(x^(d+1)); end if;
   R:=TensorRoots_general(ef1,ef2)+O(x^(d+1));
   if Degree(P) ne 1 then R:=Evaluate(R,x^Degree(P)); end if;
   return R; end function;

  function cf(p,d : Precision:=precision)
   return &*[cffuncK(F[1],d : Precision:=Precision) :
		      F in Factorization(p*OK)]; end function;

  L:=LSeries(weight,gamma,N,cf: Sign:=sign, Parent:=parent,
	     Precision:=precision, Poles:=poles, Residues:=[], Name:=name);
  L`cffuncK:=cffuncK; L`degreeK:=<d1*d2,K>;
  L`hodgeK:=hodgeK; L`condK:=conductor;

  if product then
   P1:=L1`prod cmpne false select L1`prod else [<L1,1>];
   P2:=L2`prod cmpne false select L2`prod else [<L2,1>];
   L`prod:=[<TensorProduct(F1[1],F2[1],[],K),F1[2]*F2[2]>: F1 in P1, F2 in P2];
   SimplifyLProduct(~L); end if;
  return L; end intrinsic;

intrinsic TensorProduct
(L1::LSer,L2::LSer,K::FldNum : Sign:=0,Precision:=0,BadPrimes:=[])->LSer {"}//"
 return TensorProduct(L1,L2,BadPrimes,K : Sign:=Sign, Precision:=Precision);
 end intrinsic;

