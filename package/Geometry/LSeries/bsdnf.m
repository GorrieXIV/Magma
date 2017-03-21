/*******************************************************
Implements BSD-related functions for elliptic curves
over number fields:
  ConjecturalRegulator, AnalyticRank, ConjecturalSha
Tim & Vladimir Dokchitser Aug 2010
*******************************************************/


freeze;


Z:=Integers();
Q:=Rationals();


function cross(z1,z2)
  a:=Real(z1);
  b:=Imaginary(z1);
  c:=Real(z2);
  d:=Imaginary(z2);
  return a*d-b*c;
end function;


IsCloseToReal:=func<x,prec|Abs(Imaginary(x)) lt 10^(2-prec)>;


function RealPeriod(p1,p2)
  prec:=Precision(p1);
  if IsCloseToReal(p1,prec) then return p1; end if;
  if IsCloseToReal(p2,prec) then return p2; end if;
  q:=BestApproximation(Imaginary(p1)/Imaginary(p2),10^((prec-2) div 2));
  num:=Numerator(q);
  den:=Denominator(q);
  assert IsCloseToReal(p1*den-p2*num,prec);
  return p1*den-p2*num;
end function;


function BSDEasyTerms(E: Precision:=6)

  K:=BaseField(E);
  r1,r2:=Signature(K);
  inf:=InfinitePlaces(K);
  P:=Periods(E: Precision:=Max(Precision,20));
  dsc:=Discriminant(E);
  C:=ComplexField(Precision);
  realpers:=&*[C| RealPeriod(P[i][1],P[i][2]): i in [1..r1+r2] | IsReal(inf[i])];
  realcorr:=&*[Z| d lt 0 select 1 else 2: d in RealEmbeddings(dsc)];
  complpers:=&*[C| cross(P[i][1],P[i][2]): i in [1..r1+r2] | not IsReal(inf[i])];
  complcorr:=2^r2;
  omegas:=Abs(realpers*realcorr*complpers*complcorr);

  // Torsion
  tors:=#TorsionSubgroup(E);

  // Discriminant of O_K
  dK:=Abs(Discriminant(IntegerRing(K)));

  // Tamagawa numbers * Omega contribution
  loc:=LocalInformation(E);
  tam:=&*[Z| l[4]: l in loc];
  disc:=Discriminant(E);
  om:=&*[Q| Norm(l[1])^((Valuation(disc,l[1])-l[2]) div 12): l in loc];
  C:=tam*om;

  return C * omegas / Sqrt(dK) / tors^2;
end function;


function OrderOfVanishing(L,tolerance)
  w:=Sign(L);
  if w in [1,-1] 
    then der:=w gt 0 select -2 else -1; step:=2;
    else der:=-1; step:=1; 
  end if;
  repeat
    der+:=step;
    vprint LSeries,1: "Computing "*Sprint(der)*"th derivative of",L;
    lval:=Evaluate(L,1: Derivative:=der, Leading:=true)/Factorial(der);
  until Abs(lval) ge tolerance;
  return der,lval; 
end function;


intrinsic AnalyticRank(E::CrvEll[FldNum] : Precision:=8) -> RngIntElt, FldReElt
{Computes the analytic rank of E, assuming the conjectural functional equation
for its L-function. Returns the analytic rank and the leading derivative
of the L-function at s=1. Uses Precision to determine whether a given
derivative is 0.}
  K:=BaseField(E);
  if &and[IsCoercible(Rationals(),x) : x in Coefficients(E)] then
   L:=LSeries(ChangeRing(E,Rationals()),K : Precision:=Precision);
  else L:=LSeries(E: Precision:=Precision); end if;
  P:=L`prod;
  prec:=L`precision;
  tolerance:=prec le 8 select 1E-4 else 10^-(prec div 2);
  if P cmpeq false then return OrderOfVanishing(L,tolerance); end if;
  ord:=0;
  lead:=1;
  
  PF:=[* F[1]`parent: F in P *];
  oper:=["compute": F in P];
  if forall{F: F in PF | (Type(F) eq Tup) and (#F eq 3) and (F[2] cmpeq "tensor") and
     (Type(F[1]) eq CrvEll) and (Type(F[3]) eq ArtRep) and (F[1] cmpeq PF[1][1])} then 
    for i:=1 to #PF do
      F:=PF[i];       
      ch:=Character(F[3]);
      if IsReal(ch) then continue; end if;
      if exists{j: j in [1..i-1] | Character(PF[j][3]) eq ComplexConjugate(ch)} 
        then oper[i]:="skip"; else oper[i]:="andconjugate";
      end if;
    end for;   
  end if;
  for i in [1..#P] do
    F:=P[i];
    o:=oper[i];
    if o eq "skip" then continue; end if;
    fctord,fctlead:=OrderOfVanishing(F[1],tolerance);   
    ord+:=fctord*F[2];
    lead*:=fctlead^F[2];
    if o eq "andconjugate" then
      ord+:=fctord*F[2];
      lead*:=ComplexConjugate(fctlead)^F[2];
    end if;
  end for;
  return ord,Real(lead);
end intrinsic;


intrinsic ConjecturalRegulator(E::CrvEll[FldNum] : Precision:=10) 
  -> FldReElt, RngIntElt
{For an elliptic curve over a number field, this returns 
(approximately) the conjectural value of Regulator*|Sha|
according to the Birch-Swinnerton-Dyer conjecture.
The analytic rank is also returned.   
'Precision' is used to decide which derivatives are zero 
(in determining the rank)}
  r,lead:=AnalyticRank(E: Precision:=Precision);
  R := lead/BSDEasyTerms(E: Precision:=Precision)
           /Degree(BaseField(E),Q)^r;
  return R, r;
end intrinsic;


intrinsic ConjecturalSha(E::CrvEll[FldNum], pts::Setq[PtEll] : Precision:=6)
  -> FldReElt
{For an elliptic curve over a number field K, this returns 
an approximate value for #Sha(E) computed analytically, 
assuing the Birch-Swinnerton-Dyer conjecture and assuming
that the given points generate E(K) modulo torsion. 
(More precisely: returns 0 if the subgroup <pts> has rank 
smaller than the analytic rank, otherwise returns #Sha(E)/I^2
where I is the index of <pts> as a subgroup of E(K)/E_tors.}

  K:=BaseField(E);

  pts:=IndependentGenerators([E| p : p in pts]);

  // regulator
  if IsEmpty(pts) then reg:=1; else 
    reg:=Determinant(HeightPairingMatrix(pts: Precision:=Precision))
      * Degree(K,Q)^#pts;
    assert reg ne 0;
  end if;

  // lvalue
  L:=LSeries(E: Precision:=Precision);
  lval:=Evaluate(L,1: Derivative:=#pts)/Factorial(#pts);

  return lval/reg/BSDEasyTerms(E: Precision:=Precision);
end intrinsic;

