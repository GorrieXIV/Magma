freeze;

import "Lseries.m" :
 ToSeries, MultiplicativityCheck, ExcludeList, LocalFactorFun;
lcf_list           := 0;
lcf_localfactors   := 1;
lcf_function       := 2;

function LSeriesParentCompare(P1,P2)
 if Type(P1) ne Type(P2) then return false; end if;
 if P1 cmpeq false or P2 cmpeq false then return false; end if;
 if Type(P1) eq ModFrmElt and Degree(BaseRing(P1)) ne 1
  then return false; end if;
 if Type(P2) eq ModFrmElt and Degree(BaseRing(P2)) ne 1
  then return false; end if;
 if Type(P1) eq CrvEll and
  BaseRing(P1) eq Rationals() and BaseRing(P2) eq Rationals() then
  b:=IsIsogenous(P1,P2); return b; end if; return P1 cmpeq P2; end function;

intrinsic 'eq'(L1::LSer, L2::LSer) -> BoolElt
{true iff L1 and L2 are L-series associated to the same object,
 except false for modular forms over number fields, and isogenous
 elliptic curves over Q are also checked}
  if (L1`prod cmpne false) or (L2`prod cmpne false) then
    P1:=L1`prod cmpne false select L1`prod else [<L1,1>];
    P2:=L2`prod cmpne false select L2`prod else [<L2,1>];
    return Set(P1) eq Set(P2); end if;
  if (L1`parent cmpeq false) and (L2`parent cmpeq false)
    then return false; // return L1 cmpeq L2;
  else return LSeriesParentCompare(L1`parent,L2`parent); end if; end intrinsic;

intrinsic 'ne'(L1::LSer, L2::LSer) -> BoolElt
{true iff L1 and L2 are not associated to the same object,
 except always true for modular forms over number fields,
 and isogenous elliptic curves over Q are always checked}
 return not (L1 eq L2); end intrinsic;

intrinsic IsOne(L:: LSer) -> BoolElt
{true iff the L-series was defined to be identically 1}
  return (L`parent cmpeq 1) or (L`prod cmpeq []); end intrinsic;

intrinsic LSeries(one:: RngIntElt: Precision:=0) -> LSer
{LSeries(1) returns the L-series which is identically 1}
 require one cmpeq 1: "Only LSeries(1) makes sense";
 L:=LSeries(1,[Integers()|],1,[1] : Parent:=1, Sign:=1, Precision:=Precision);
  L`prod:=[]; return L; end intrinsic;

function Lprodtermprint(L,n,star)
 if n eq 1 then return star select <"(",L,") * "> else <"(",L,")">;
 else return <"(",L,Sprintf(")^%o%o",n,star select " * " else "")>; end if;
end function;

declare attributes LSer : embed;
procedure SimplifyProduct(~P) n:=1;
 while n lt #P do ind:=[i: i in [1..#P] | P[i][1] eq P[n][1]];
//  if assigned P[n][1]`embed and P[n][1]`embed then ind:=[n]; end if;
  if #ind gt 1 then exponent:=&+[P[i][2]: i in ind]; P[ind[1]][2]:=exponent;
   if exponent eq 0 then n:=n-1; else Remove(~ind,1); end if;
   else ind:=[]; end if;
  for i in Reverse(ind) do Remove(~P,i); end for; n+:=1; end while;
end procedure;

procedure SimplifyLProduct(~L) // look for repeated factors
  if L`prod cmpeq false then return; end if;
  SimplifyProduct(~L`prod); P:=L`prod;
  if IsEmpty(P) then
    L`parent:=1; L`name:=1; L`conductor:=1; L`sign:=1; L`lpoles:=[]; return;
  end if;
  L`parent:=<<F[1]`parent,F[2]>: F in P>;
  L`name:=<Lprodtermprint(P[i,1],P[i,2],i ne #P): i in [1..#P]>;
  L`conductor:=&*[(F[1]`conductor)^F[2]: F in P];
  L`sign:=&*[(F[1]`sign)^F[2]: F in P]; L`lpoles:=&cat[F[1]`lpoles: F in P];
end procedure;

intrinsic '/'(L1::LSer, L2::LSer: Poles:=0, Residues:=[], Precision:=0) -> LSer
{Quotient of two L-series with weakly multiplicative coefficients, provided
 that this quotient makes sense and (this is not checked!) is again
 an L-series with finitely many poles. Specify poles and residues
 if you happen to know them}
 if IsOne(L2) then return L1; end if;
  require L1`weight cmpeq L2`weight:
    "Cannot divide L-series: different weights";
  if Precision eq 0 then precision:=Min(L1`precision,L2`precision);
   else precision:=Precision; end if;
  if precision eq 0 then precision:=GetPrecision(1.2); end if;
  if IsOne(L2) then LSetPrecision(L1,precision); return L1; end if;

  require MultiplicativityCheck(L1) and MultiplicativityCheck(L2):
    "L-Series does not appear to have multiplicative coefficients";
  weight:=L1`weight; conductor:=(L1`conductor/L2`conductor);
  if (Type(L1`conductor) cmpeq RngIntElt) and
     (Type(L2`conductor) cmpeq RngIntElt) then
       require L1`conductor mod L2`conductor eq 0:
         "Cannot divide L-series: Conductors do not divide one another";
     conductor:=Integers()!conductor; end if;
  require IsSubsequence(Sort(L2`gamma),Sort(L1`gamma): Kind:="Sequential"):
    "Cannot divide L-series: Gamma factors do not divide one another";
  gamma:=ExcludeList(L1`gamma,L2`gamma); poles:=Poles; residues:=Residues;

  function cffun(p,d: Precision:=0)
    L1loc:=LocalFactorFun(L1,Precision); L2loc:=LocalFactorFun(L2,Precision);
    return ToSeries(L1loc(p,d),d)/ToSeries(L2loc(p,d),d); end function;

  sign:=L2`sign eq 0 select 0 else L1`sign/L2`sign;
  name:=<L1," / ",L2>; parent:=<L1`parent,"/",L2`parent>;
  if poles cmpeq 0 then poles:=ExcludeList(L1`lpoles,L2`lpoles); end if;

  L:=LSeries(weight,gamma,conductor,cffun: Sign:=sign,
	     Precision:=precision, Poles:=poles, Residues:=residues,
	     Parent:=parent, Name:=name);
  fact1:=L1`prod cmpeq false select [<L1,1>] else L1`prod;
  fact2:=L2`prod cmpeq false select
                             [<L2,-1>] else [<x[1],-x[2]>: x in L2`prod];
  fact:=fact1 cat fact2; SimplifyProduct(~fact);
  if forall{x: x in fact | x[2] gt 0} then
   L`prod:=fact; SimplifyLProduct(~L); end if;
  return L; end intrinsic;


intrinsic '*'(L1::LSer, L2::LSer: Poles:=0, Residues:=[], Precision:=0) -> LSer
{Product of two L-series with weakly multiplicative coefficients.
 Specify poles and residues if you happen to know them}
  if Precision eq 0 then precision:=Min(L1`precision,L2`precision);
   else precision:=Precision; end if;
  if precision eq 0 then precision:=GetPrecision(1.2); end if;
  if IsOne(L1) then LSetPrecision(L2,precision); return L2; end if;
  if IsOne(L2) then LSetPrecision(L1,precision); return L1; end if;
  require L1`weight cmpeq L2`weight:
    "Cannot multiply L-series: different weights";
  require MultiplicativityCheck(L1) and MultiplicativityCheck(L2):
    "L-Series does not appear to have multiplicative coefficients";
  weight:=L1`weight; conductor:=L1`conductor*L2`conductor;
  gamma:=Sort(L1`gamma cat L2`gamma); sign:=L1`sign*L2`sign;
  poles:=Poles; residues:=Residues;

  function cffun(p,d: Precision:=0)
   L1loc:=LocalFactorFun(L1,Precision); L2loc:=LocalFactorFun(L2,Precision);
   return ToSeries(L1loc(p,d),d)*ToSeries(L2loc(p,d),d); end function;

  parent:=<L1`parent,"*",L2`parent>; name:=<L1," * ",L2>;
  if poles cmpeq 0 then poles:=L1`lpoles cat L2`lpoles; end if;
  require #Set(poles) eq #poles or true:
    "Product of the L-series has a multiple pole"; // why is this a problem ?
  L:=LSeries(weight,gamma,conductor,cffun: Sign:=sign,Precision:=precision,
	     Poles:=poles, Residues:=residues, Parent:=parent, Name:=name);
  L`prod:=Factorization(L1) cat Factorization(L2);
  SimplifyLProduct(~L); return L; end intrinsic;

intrinsic LProduct(A::SeqEnum[Tup] : Precision:=0) -> LSer 
{ Return the product of a sequence of L-series}
 require &and[#a eq 2 : a in A] and &and[Type(a[1]) eq LSer : a in A]
         and &and[Type(a[2]) eq RngIntElt and a[2] ge 0 : a in A]:
 "LProduct must be given an array of <L,n> pairs with n ge 0";
 if #A eq 0 then return LSeries(1 : Precision:=Precision); end if;
 precision:=Precision eq 0 select A[1][1]`precision else Precision;
 if precision eq 0 then precision:=GetPrecision(1.2); end if;
 if #A eq 1 then return '^'(A[1][1],A[1][2] : Precision:=Precision); end if;
 function coeff_func(p,d: Precision:=0)
  F:=[LocalFactorFun(a[1],Precision) : a in A];
  return &*[ToSeries(F[i](p,d),d)^A[i][2] : i in [1..#A]]; end function;
// hmm, this does more than is strictly necessary -- gives a deg d factor
// also, should try to make this K-compatible
 M:=LSeries(A[1][1]`weight,&cat[&cat[a[1]`gamma : i in [1..a[2]]] : a in A],
	    &*[a[1]`conductor^a[2] : a in A],coeff_func :
	    Sign:=&*[a[1]`sign^a[2] : a in A], Precision:=precision);
 M`prod:=&cat[[<x[1],x[2]*a[2]> : x in Factorization(a[1])] : a in A];
 SimplifyLProduct(~M); return M; end intrinsic;

intrinsic LProduct(L::SeqEnum[LSer] : Precision:=0) -> LSer 
{ Return the product of a sequence of L-series}
 return LProduct([<a,1> : a in L]); end intrinsic;

intrinsic // poles and residues could be obsolete, in the future
 '^'(L::LSer, n::RngIntElt : Poles:=[], Residues:=[], Precision:=0) -> LSer
{Take a power of an L-series}
 require n ge 0: "Power of L-Series must be nonnegative";
 precision:=Precision eq 0 select L`precision else Precision;
 if precision eq 0 then precision:=GetPrecision(1.2); end if;
 if n eq 0 then return LSeries(1 : Precision:=precision); end if;
 if n eq 1 then LSetPrecision(L,precision); return L; end if;
 if IsOne(L) then LSetPrecision(L,precision); return L; end if;
 function coeff_func(p,d: Precision:=0)
  return ToSeries(LocalFactorFun(L,Precision)(p,d),d)^n; end function;
 M:=LSeries(L`weight,&cat[L`gamma : i in [1..n]],L`conductor^n,coeff_func :
	    Sign:=L`sign^n, Precision:=precision,
	    Poles:=Poles, Residues:=Residues);
 if L`prod cmpeq false then M`prod:=[<L,n>];
 else M`prod:=[<a[1],a[2]*n> : a in L`prod]; end if;
 SimplifyLProduct(~M); return M; end intrinsic;

intrinsic Factorization(L::LSer) -> SeqEnum[Tup]
{If an L-series is known to be a product of other L-series,
 return them and their exponents [<L1,n1>,...]. Otherwise returns [<L,1>]}
  return L`prod cmpeq false select [<L,1>] else L`prod; end intrinsic;

////////////////////////////////////////////////////////////////////////

function detect_poles(L : limit:=1000)
 C:=LGetCoefficients(L,limit); wt:=L`weight-1;
 V:=[C[p]/(p^(wt/2)) : p in [1..#C] | IsPrime(p)];
 // sum should be near an integer, make it, say, within 10%
 sum:=(&+V)/#V; a:=Abs(sum); r:=Round(a); c:=Abs(r-a);
 if c gt 0.1 or Abs(Imaginary(sum)) gt 0.1 then
  return detect_poles(L : limit:=(181*limit) div 128); end if; // sqrt(2)
 norm:=(&+[Abs(V[i]-r)^2 : i in [1..#V]])/#V;
 if Abs(Round(norm)-norm) gt 0.1 then
  return detect_poles(L : limit:=(181*limit) div 128); end if; // sum,norm;
 return r,Round(norm); end function;

intrinsic ArithmeticLSeries(L::LSer : Limit:=1000) -> LSer, RngIntElt
{ Given an LSeries of "arithmetic" type, attempt to factor off zeta-factors
  and determine whether it is primitive}
 a,b:=detect_poles(L : limit:=Limit);
 if a ne 0 then T:=Translate(RiemannZeta(),(L`weight-1)/2);
                L:=LProduct([<L/T^a,1>,<T,a>]); end if;
 return L,b; end intrinsic;

intrinsic MomentData(L::LSer,P::SeqEnum[RngIntElt],n::RngIntElt :
		     Twist:=1)
-> RngIntElt,SeqEnum, RngIntElt
{Given an L-series and a set of primes, compute the moment data up to n.
 Returned as the mean, and then an array of even powers up to n, and the
 proportion of prime coefficients that are zero}
 require IsSelfDual(L): "L-function must be self-dual"; wt:=MotivicWeight(L);
 m:=Max(P); C:=LGetCoefficients(L,m); A:=AssociativeArray();
 RF5:=RealField(5); C:=[RF5!Real(x) : x in C];
 for p in P do
  if not IsPrime(p) or Valuation(Conductor(L),p) gt 0 then continue; end if;
 A[p]:=KroneckerCharacter(Twist)(p)*C[p]; end for;
 K:=#Keys(A); m1:=&+[A[p]/p^(wt/2)*1.0 : p in Keys(A)]/K;
 M:=[&+[A[p]^u/p^(wt*u/2)*1.0 : p in Keys(A)]/K : u in [2..n by 2]];
 perc:=#[A[p] : p in Keys(A) | A[p] eq 0]/K;
 return m1,M,perc*RF5!1.0; end intrinsic;

intrinsic InnerProduct(L1::LSer,L2::LSer,P::SeqEnum[RngIntElt]) -> FldReElt
{Given two L-series and a set of primes, compute the inner product on them}
 require IsSelfDual(L1) and IsSelfDual(L2): "L-functions must be self-dual";
 wt1:=MotivicWeight(L1); wt2:=MotivicWeight(L2); A:=AssociativeArray();
 m:=Max(P); C1:=LGetCoefficients(L1,m); C2:=LGetCoefficients(L2,m);
 RF5:=RealField(5); C1:=[RF5!Real(x) : x in C1]; C2:=[RF5!Real(x) : x in C2];
 J:=Conductor(L1)*Conductor(L2);
 for p in P do if not IsPrime(p) or Valuation(J,p) gt 0 then continue; end if;
  A[p]:=C1[p]*C2[p]/p^((wt1+wt2)/2); end for;
 K:=Keys(A); return &+[A[p] : p in K]/#K; end intrinsic;

////////////////////////////////////////////////////////////////////////

hasprecpar:=func<f|Position(Sprint(f),"[ Precision ]") ne 0>;

intrinsic ChangeEulerFactor(L::LSer,p::RngIntElt,f::RngUPolElt) -> LSer
{Given an L-series, a prime, and a polynomial,
 create an L-function with the given Euler factor at said prime.}
 require L`cftype eq lcf_localfactors: "L-function must be from local factors";
 return ChangeLocalInformation(L,p,Valuation(Conductor(L),p),f); end intrinsic;

intrinsic ChangeLocalInformation
(L::LSer,p::RngIntElt,d::RngIntElt,f::RngUPolElt) -> LSer
{Given an L-series, a prime, the new local conductor, and a polynomial,
 create an L-function with the given Euler factor at said prime.}
 require L`cftype eq lcf_localfactors: "L-function must be from local factors";
 return ChangeLocalInformation(L,[*<p,d,f>*]); end intrinsic;

intrinsic ChangeLocalInformation(L::LSer,bp::List) -> LSer
{Given an L-series and local information <p,f,eul>, create a new L-function.}
 require L`cftype eq lcf_localfactors: "L-function must be from local factors";
 BAD:=AssociativeArray(); for b in bp do BAD[b[1]]:=b[3]; end for;
 function local_func(q,e : Precision:=L`precision)
  if IsDefined(BAD,q) then return BAD[q]; end if;
  if hasprecpar(L`cffun) then return L`cffun(q,e : Precision:=Precision);
  else return L`cffun(q,e); end if; end function;
 C:=Conductor(L);C:=Integers()!(C*&*[b[1]^(b[2]-Valuation(C,b[1])) : b in bp]);
 M:=LSeries(HodgeStructure(L),C,local_func : Poles:=L`lpoles,Parent:=L`parent,
	    Name:=L`name,Precision:=L`precision);
 if assigned L`cfvec then M`cfvec:=L`cfvec; N:=#M`cfvec;
  for b in bp do p:=b[1]; d:=Ilog(p,N); A:=[* 0 : i in [1..d] *];
   S:=1/ToSeries(b[3],d); for j in [1..d] do A[j]:=Coefficient(S,j); end for;
   for k in [1..d] do pk:=p^k; for j in [1..Floor(N/pk)] do
    if j mod p eq 0 then continue; end if;
    M`cfvec[j*pk]:=M`cfvec[j]*A[k]; end for; end for; end for; end if;
 return M; end intrinsic;
// should also have some saving of Mellin weightings for a given conductor?

intrinsic BadPrimeData(L::LSer) -> SeqEnum
{Given an L-series, return an array of its bad prime data}
 C:=Conductor(L); P:=PrimeFactors(Conductor(L));
 return [<p,Valuation(C,p),EulerFactor(L,p)> : p in P]; end intrinsic;

intrinsic CopyCoefficients(L::LSer,M::LSer)
{Given two L-series the first with stored coefficients,
 copy them from the first to the second}
 require assigned L`cfvec: "L has no coeffs stored";
 if not assigned M`cfvec then M`cfvec:=[* *]; end if;
 M`cfvec:=L`cfvec cat M`cfvec[#L`cfvec+1..#M`cfvec]; end intrinsic;
