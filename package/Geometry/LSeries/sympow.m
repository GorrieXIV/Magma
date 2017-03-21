
freeze;

import "sympow_ec.m" : sympow_ec;
import "hodge.m" : split_up; // for [2,2] case

import "sympow_formulas.m" : coeff_sym2_deg3;
import "sympow_formulas.m" : coeff_sym3_deg3;
import "sympow_formulas.m" : coeff_sym21_deg3;
import "sympow_formulas.m" : coeff_sym11_deg4;
import "sympow_formulas.m" : coeff_sym2_deg4;
import "sympow_formulas.m" : coeff_sym22_deg4;
import "sympow_formulas.m" : coeff_sym11_deg5;
import "sympow_formulas.m" : euler_d3_symk;

function TBIN(a,b) x:=Binomial(a-b+1,b)-Binomial(a-b-1,b-2);
                   if b mod 2 eq 1 then x:=-x; end if; return x; end function;

DS:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;
function NS(S) return DS(Sprint(S)); end function;
function myNS(S) u:=DS(Sprint(S));
 u:=&*[e eq "[" select "{" else e : e in Eltseq(u)];
 u:=&*[e eq "]" select "}" else e : e in Eltseq(u)]; return u; end function;

function de_pole(L,z) if z eq 0 then return L; end if; wt:=MotivicWeight(L);
 Q:=Translate(RiemannZeta(:Precision:=L`precision),wt div 2)^z;
 return (L/Q)*Q; end function;

function euler_d2_symk(ef,m)
 ap:=-Coefficient(ef,1); pk:=Coefficient(ef,2); x:=Parent(ef).1;
 if m eq 0 then return (1-x); end if; s:=m; s2:=s div 2;
 ti:=&+[Parent(ap) | TBIN(s,s2-k)*ap^(2*k)*pk^(s2-k) : k in [0..s2]];
 if s mod 2 eq 1 then ti:=ti*ap; end if;
 return (1-ti*x+pk^m*x^2); end function;

function generic_deg2_symk(L,m,BP,prec,pole)
 if m eq 0 then return true,RiemannZeta(:Precision:=prec); end if;
 if m eq 1 then return true,L; end if; A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<m+1,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); x:=Parent(ef).1; pk:=Coefficient(ef,2);
  return &*[Evaluate(euler_d2_symk(ef,m-u),x*pk^(u div 2)) : u in [0..m by 2]];
  end function;
 LS:=LSeries(SymmetricPower(HodgeStructure(L),m),N,cf : Precision:=prec);
 if m mod 10 eq 1 then STR:="st "; elif m mod 10 eq 2 then STR:="nd ";
 elif m mod 10 eq 3 then STR:="rd "; else STR:="th "; end if;
 if IsOrthogonal(L : AssumeFalse) and IsEven(m) and pole le 1
  then pole:=1; end if;
 LS`name:=<m,STR*"symmetric power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<m,STR*"symmetric power of ",L>; return true,LS; end function;

function sympow_deg2(L,S,BP,prec,pole) assert #S eq 1;
 return generic_deg2_symk(L,S[1],BP,prec,pole); end function;

function sympow_d3alt11(L,BP,u,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<3,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for; wt:=MotivicWeight(L);
 DL:=Determinant(L:Precision:=u); DL:=Translate(DL,-(MotivicWeight(DL) div 2));
 TP:=TensorProduct(L,DL : BadPrimes:=BP,Precision:=u);
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(TP,p); x:=Parent(ef).1;
  return Evaluate(ef,p^(wt div 2)*x); end function;
 HS:=HodgeStructure(TP); CTP:=Conductor(TP);
 LS:=LSeries(TateTwist(HS,-wt div 2),CTP,cf : Precision:=u);
 LS`name:=<"{1,1}-symmetrization of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"{1,1}-symmetrization of ",L>; return true,LS; end function;

function sympow_d3sym2(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<6,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym2_deg3(L,ef,p,d); end function;
 HL:=HodgeStructure(L); DL:=Determinant(HL); HS:=HL*HL-DL/HL;
 LS:=LSeries(HS,N,cf : Precision:=prec);
 if IsSelfDual(L) and pole le 1 then pole:=1; end if;
 LS`name:=<"2nd symmetric power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"2nd symmetric power of ",L>; return true,LS; end function;

function sympow_d3sym3(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<10,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym3_deg3(L,ef,p,d); end function;
 HL:=HodgeStructure(L); DL:=Determinant(HL);
 HS:=HL^3-2*(HL*Dual(HL)*DL-DL); LS:=LSeries(HS,N,cf : Precision:=prec);
 if IsSelfDual(L) then LS`name:=<"3rd symmetric power of ",L>;
  LT:=Translate(L,MotivicWeight(L)); LS:=(LS/LT)*LT; end if; // unsure else
 LS`name:=<"3rd symmetric power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"3rd symmetric power of ",L>; return true,LS; end function;

function sympow_d3alt21(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<8,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym21_deg3(L,ef,p,d); end function;
 HL:=HodgeStructure(L); DL:=Determinant(HL); HS:=HL*Dual(HL)*DL-DL;
 LS:=LSeries(HS,N,cf : Precision:=prec);
 if IsSelfDual(L) then LS`name:=<"{2,1}-symmetrization of ",L>;
  LT:=Translate(L,MotivicWeight(L)); LS:=(LS/LT)*LT; end if; // unsure else
 LS`name:=<"{2,1}-symmetrization of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"{2,1}-symmetrization of ",L>; return true,LS; end function;

function sympow_deg3(L,S,BP,prec,pole)
 if not S in {[2],[1,1],[3],[2,1]} then return false,_; end if;
 if S eq [1,1] then return sympow_d3alt11(L,BP,prec,pole); end if;
 if S eq [2,1] then return sympow_d3alt21(L,BP,prec,pole); end if;
 if S eq [2] then return sympow_d3sym2(L,BP,prec,pole); end if;
 if S eq [3] then return sympow_d3sym3(L,BP,prec,pole); end if; end function;

function sympow_d4alt11(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<6,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym11_deg4(L,ef,p,d); end function;
 LS:=LSeries(AlternatingSquare(HodgeStructure(L)),N,cf : Precision:=prec);
 if IsSymplectic(L : AssumeFalse) and pole le 1 then pole:=1; end if;
 LS`name:=<"{1,1}-symmetrization of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"{1,1}-symmetrization of ",L>; return true,LS; end function;

function sympow_d4sym2(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<10,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym2_deg4(L,ef,p,d); end function;
 LS:=LSeries(SymmetricPower(HodgeStructure(L),2),N,cf : Precision:=prec);
 if IsOrthogonal(L : AssumeFalse) and pole le 1 then pole:=1; end if;
 LS`name:=<"2nd symmetric power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"2nd symmetric power of ",L>; return true,LS; end function;

function sympow_deg4(L,S,BP,prec,pole)
 if not S in {[2],[1,1]} then return false,_; end if;
 if S eq [1,1] then return sympow_d4alt11(L,BP,prec,pole); end if;
 if S eq [2] then return sympow_d4sym2(L,BP,prec,pole); end if; end function;

function sympow_d5alt11(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<10,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)];
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); return coeff_sym11_deg5(L,ef,p,d); end function;
 LS:=LSeries(AlternatingSquare(HodgeStructure(L)),N,cf : Precision:=prec);
 LS`name:=<"{1,1}-symmetrization of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"{1,1}-symmetrization of ",L>; return true,LS; end function;

function sympow_deg5(L,S,BP,prec,pole)
 if not S in {[1,1]} then return false,_; end if;
 return sympow_d5alt11(L,BP,prec,pole); end function;

////////////////////////////////////////////////////////////////////////

intrinsic IsReal(L::LSer : NumCoeff:=20) -> BoolElt
{Whether L is real (self-dual)}
 return IsSelfDual(L : NumCoeff:=NumCoeff); end intrinsic;

intrinsic IsSelfDual(L::LSer : NumCoeff:=20) -> BoolElt
{Whether L is real (self-dual)}
 C:=LGetCoefficients(L,NumCoeff); prec:=L`precision; CF:=ComplexField(prec);
 return &and[Abs(Imaginary(CF!c)) le 10*10^(-prec)*Abs(CF!c) : c in C];
 end intrinsic;

intrinsic IsSymplectic(L::LSer : AssumeTrue:=false,AssumeFalse:=false)->BoolElt
{Whether L is symplectic. If L is self-dual and even degree and weight,
 then either AssumeTrue or AssumeFalse should be set to avoid an error.}
 if not HasHodgeStructure(L) then return false; end if;
 if not IsSelfDual(L) then return false; end if;
 if IsOdd(Degree(L)) then return false; end if;
 if IsOdd(MotivicWeight(L)) then return true; end if;
 require Type(AssumeTrue) eq BoolElt: "AssumeTrue must be a boolean";
 require Type(AssumeFalse) eq BoolElt: "AssumeFalse must be a boolean";
 if AssumeTrue and AssumeFalse then error "Contrary assumption"; end if;
 if AssumeTrue then return true; end if;
 if AssumeFalse then return false; end if;
 error "Not yet determined"; end intrinsic;

intrinsic IsOrthogonal(L::LSer : AssumeTrue:=false,AssumeFalse:=false)->BoolElt
{Whether L is orthogonal. If L is self-dual and even degree and weight,
 then either AssumeTrue or AssumeFalse should be set to avoid an error.}
 if not HasHodgeStructure(L) then return false; end if;
 if not IsSelfDual(L) then return false; end if;
 if IsOdd(Degree(L)) then return true; end if;
 if IsOdd(MotivicWeight(L)) then return false; end if;
 require Type(AssumeTrue) eq BoolElt: "AssumeTrue must be a boolean";
 require Type(AssumeFalse) eq BoolElt: "AssumeFalse must be a boolean";
 if AssumeTrue and AssumeFalse then error "Contrary assumption"; end if;
 if AssumeTrue then return true; end if;
 if AssumeFalse then return false; end if;
 error "Not yet determined"; end intrinsic;

APC:=AssociatedPrimitiveCharacter;
APG:=AssociatedPrimitiveGrossencharacter;
TRANS:=Translate;
intrinsic Determinant(L::LSer : Precision:=L`precision,Translate:=true) -> LSer
{Given an L-series, return its determinant (highest wedge product)}
 wt2:=(MotivicWeight(L)*Degree(L)) div 2;
 if IsSelfDual(L) and IsOdd(MotivicWeight(L)) then
  return TRANS(RiemannZeta(:Precision:=Precision),wt2); end if;
 C:=Conductor(L); p:=1; DATA:=[* *];
 while true do p:=NextPrime(p); if C mod p eq 0 then continue; end if;
  u:=LeadingCoefficient(EulerFactor(L,p))*(-1)^(Degree(L))/p^wt2;
  if Type(u) in {FldReElt,FldComElt} then CF:=ComplexField();
   frac:=BestApproximation(Real(Log(u)/2/Pi(CF)/CF.1),C);
   u:=Integers(Denominator(frac))!Numerator(frac); end if;
  DATA:=DATA cat [* <p,u> *];
  chi,K:=DirichletCharacter
          (C*Integers(QNF()),<d : d in DATA> : RequireGenerators:=false);
  if #K eq 1 then break; end if; end while;
 LS:=LSeries(APC(DirichletCharacterOverQ(chi)) : Precision:=Precision);
 if wt2 ne 0 and Translate then LS:=TRANS(LS,wt2); end if;
 return LS; end intrinsic; // could special case GrpDrchElt, ArtRep

intrinsic Symmetrization
(L::LSer,S::SeqEnum : BadPrimes:=[],Precision:=L`precision,
                      PoleOrder:=0,Induction:=true) -> LSer
{ Given an L-series L and a partition S, return the symmetrization L^S}
 require Universe(S) cmpeq Integers(): "Sequence must be integral";
 while 0 in S do Exclude(~S,0); end while; S:=Reverse(Sort(S));
 require &and[p ge 1 : p in S]: "Partition must be nonnegative";
 require Type(PoleOrder) eq RngIntElt and PoleOrder ge 0: "PoleOrder invalid";
 require HasHodgeStructure(L): "L does not seem to have a Hodge structure?";
 prec:=Precision; if IsOne(L) then return L; end if;
 if #S eq 0 then return RiemannZeta( : Precision:=prec); end if;
 if Degree(L) lt #S then return LSeries(1 : Precision:=prec); end if;
 ////////////////////////////////////////////////////////////////////////
 if Type(L`parent) eq ArtRep then return
  LSeries(Symmetrization(L`parent,S) : Precision:=prec); end if;
 if Degree(L) eq 1 then D:=Determinant(L : Precision:=prec,Translate:=false);
  if D eq RiemannZeta() then D`parent:=KroneckerCharacter(1); end if;
  LS:=LSeries(APC(D`parent^S[1]) : Precision:=prec);
  return Translate(LS,MotivicWeight(L) div 2); end if;
 if Type(L`parent) eq GrpDrchElt then return LSeries(1); end if;
 if Induction and Type(L`parent) in {GrpHeckeElt,GrossenChar} then // GL(1)
 if #S gt 1 then return LSeries(1 : Precision:=prec); end if;
  if Type(L`parent) eq GrpHeckeElt then
   return LSeries(APC(L`parent^S[1]) : Precision:=prec); end if;
  if Type(L`parent) eq GrossenChar then
   return LSeries(APG(L`parent^S[1]) : Precision:=prec); end if; end if;
 if Type(L`parent) eq CrvEll and BaseRing(L`parent) eq Rationals() then
  if #S eq 1 then return sympow_ec(L,S[1],prec); end if;
  return Translate(sympow_ec(L,S[1]-S[2],prec),S[2]); end if; // rename?
 ////////////////////////////////////////////////////////////////////////
 if Degree(L) eq #S then m:=Min(S); S2:=[s-m : s in S]; // wedge prod case
  A:=AssociativeArray(); for z in BadPrimes do A[z[1]]:=<z[2],z[3]>; end for;
  LS:=Symmetrization(L,S2 : BadPrimes:=BadPrimes,Precision:=prec,
		     PoleOrder:=PoleOrder,Induction:=Induction);
  T:=Translate(TensorProduct(LS,Symmetrization(Determinant(L),[m])),m);
  T`name:=<myNS(S)*"-symmetrization of ",L>; Tcf:=T`cffun;
  function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
   return Tcf(p,d); end function;
  T`cffun:=cf; return de_pole(T,PoleOrder); end if;
 ////////////////////////////////////////////////////////////////////////
 if Degree(L) eq 2 then b,R:=sympow_deg2(L,S,BadPrimes,prec,PoleOrder);
  if b then return R; end if; end if;
 if Degree(L) eq 3 then b,R:=sympow_deg3(L,S,BadPrimes,prec,PoleOrder);
  if b then return R; end if; end if;
 if Degree(L) eq 4 then b,R:=sympow_deg4(L,S,BadPrimes,prec,PoleOrder);
  if b then return R; end if; end if;
 if Degree(L) eq 5 then b,R:=sympow_deg5(L,S,BadPrimes,prec,PoleOrder);
  if b then return R; end if; end if;
 error "Not implemented"; end intrinsic; 
// try to handle deg4,[2] case when induced?

intrinsic SymmetricPower
(L::LSer,m::RngIntElt : BadPrimes:=[], BadEulerFactors:=[], Induction:=true,
                        Precision:=L`precision, PoleOrder:=0) -> LSer
{ Given an L-series, return the L-series for the m-th symmetric power of it.}
 require m ge 0: "Symmetric power must be nonnegative";
 if BadPrimes eq [] then BadPrimes:=BadEulerFactors; end if;
 return Symmetrization(L,[m] : BadPrimes:=BadPrimes,PoleOrder:=PoleOrder,
		               Precision:=Precision,Induction:=Induction);
 end intrinsic;

////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

function ortho_deg2_symk(L,m,BP,prec,pole) wt:=MotivicWeight(L);
 if m eq 0 then return true,RiemannZeta(:Precision:=prec); end if;
 if m eq 1 then return true,L; end if; A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do
  A[p]:=<Valuation(C,p),Evaluate(EulerFactor(L,p),Polynomial([0,p^wt]))>;
  end for; for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)]; wm:=(wt*m) div 2;
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); x:=Parent(ef).1; pk:=Coefficient(ef,2);
  if pk lt 0 and Coefficient(ef,1) eq 0 then return (1-p^wm*x)*(1+p^wm*x);
  else return euler_d2_symk(ef,m); end if; end function;
 HS:=HodgeStructure(L);
 HS:=SymmetricPower(HS,m)-TateTwist(SymmetricPower(HS,m-2),-MotivicWeight(L));
 LS:=LSeries(HS,N,cf : Precision:=prec);
 if m mod 10 eq 1 then STR:="st "; elif m mod 10 eq 2 then STR:="nd ";
 elif m mod 10 eq 3 then STR:="rd "; else STR:="th "; end if;
 LS`name:=<m,STR*"orthogonal power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<m,STR*"orthogonal power of ",L>; return LS; end function;

function ortho_deg3_symk(L,m,BP,prec,pole) wt:=MotivicWeight(L);
 if m eq 0 then return true,RiemannZeta(:Precision:=prec); end if;
 if m eq 1 then return true,L; end if; A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<2*m+1,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)]; wm:=wt;
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p); x:=Parent(ef).1; pk:=Coefficient(ef,2);
  f:=euler_d3_symk(L,ef,p,d,m); Pf:=Parent(f); BR:=BaseRing(Pf);
  g:=Evaluate(euler_d3_symk(L,ef,p,d,m-2),p^wm*x); g:=Pf!g;
  if not IsExact(BR) then Pf:=PowerSeriesRing(BR,Max(d+1,2*m+2));
   return (Pf!f)/(Pf!g); end if; return Parent(f)!(f/g); end function;
 HS:=HodgeStructure(L);
 HS:=SymmetricPower(HS,m)-TateTwist(SymmetricPower(HS,m-2),-MotivicWeight(L));
 LS:=LSeries(HS,N,cf : Precision:=prec);
 if m mod 10 eq 1 then STR:="st "; elif m mod 10 eq 2 then STR:="nd ";
 elif m mod 10 eq 3 then STR:="rd "; else STR:="th "; end if;
 LS`name:=<m,STR*"orthogonal power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<m,STR*"orthogonal power of ",L>; return LS; end function;

function ortho_deg4_sym2(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<9,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)]; wt2:=MotivicWeight(L);
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p);
  f:=coeff_sym2_deg4(L,ef,p,d); Pf:=Parent(f); BR:=BaseRing(Pf);
  g:=Pf!Polynomial([1,-p^wt2]);
  if not IsExact(BR) then Pf:=PowerSeriesRing(BR,Max(d+1,10));
   return (Pf!f)/(Pf!g); end if; return Pf!(f/g); end function;
 HS:=SymmetricPower(HodgeStructure(L),2)-
     TateTwist(HodgeStructure(RiemannZeta()),-wt2);
 LS:=LSeries(HS,N,cf : Precision:=prec);
 LS`name:=<"2nd orthogonal power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"2nd orthogonal power of ",L>; return LS; end function;

function ortho_deg4_sym22(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<10,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)]; wt2:=MotivicWeight(L);
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p);
  f:=coeff_sym22_deg4(L,ef,p,d); g:=coeff_sym2_deg4(L,ef,p,d);
  Pf:=Parent(f); BR:=BaseRing(Pf); g:=Pf!Evaluate(g,p^wt2*Parent(g).1);
  if not IsExact(BR) then Pf:=PowerSeriesRing(BR,Max(d+1,11));
   return (Pf!f)/(Pf!g); end if; return Parent(f)!(f/g); end function;
 HSL:=HodgeStructure(L); Y,Z:=Explode(split_up(HSL));
 A2Y:=AlternatingSquare(Y);  A2Z:=AlternatingSquare(Z); 
 HS:=Y*Z*(A2Y+A2Z)+A2Y^2+A2Z^2+SymmetricPower(Y,2)*SymmetricPower(Z,2)+A2Y*A2Z;
 HS:=HS-TateTwist(SymmetricPower(HSL,2),-Weight(HSL));
 LS:=LSeries(HS,N,cf : Precision:=prec);
 LS`name:=<"[2,2]-orthogonal power of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"[2,2]-orthogonal power of ",L>; return LS; end function;

intrinsic OrthogonalSymmetrization
(L::LSer,S::SeqEnum : BadPrimes:=[],Precision:=L`precision,
                      PoleOrder:=0) -> LSer
{Given an L-series L and partition S, return the orthogonal symmetrization L^S}
 require Universe(S) cmpeq Integers(): "Sequence must be integral";
 while 0 in S do Exclude(~S,0); end while; S:=Reverse(Sort(S));
 require &and[p ge 1 : p in S]: "Partition must be nonnegative";
 require Type(PoleOrder) eq RngIntElt and PoleOrder ge 0: "PoleOrder invalid";
 require HasHodgeStructure(L): "L does not seem to have a Hodge structure?";
 require IsOrthogonal(L : AssumeTrue): "L-function must be orthogonal";
 ////////////////////////////////////////////////////////////////////////
 pole:=PoleOrder; prec:=Precision; BP:=BadPrimes;
 if S eq [1] then return L; end if;
 if #S eq 0 then return RiemannZeta( : Precision:=prec); end if;
 require Degree(L) ge 2*#S: "Invalid partition for orthogonalization";
 if Degree(L) eq 2 then return ortho_deg2_symk(L,S[1],BP,prec,pole); end if;
 if Degree(L) eq 3 then require S[1] le 4: "Partition is too large";
  return ortho_deg3_symk(L,S[1],BP,prec,pole); end if;
 if Degree(L) eq 4 then
  require S eq [2] or S eq [2,2]: "Partition type not implemented";
  if S eq [2] then return ortho_deg4_sym2(L,BP,prec,pole); end if;
  return ortho_deg4_sym22(L,BP,prec,pole); end if;
 error "Degree not implemented"; end intrinsic; 

function symplectic_d4_sym11(L,BP,prec,pole) A:=AssociativeArray();
 C:=Conductor(L); BAD:=Sort([b[1] : b in BP]); PF:=PrimeFactors(C);
 if not PF subset BAD then "WARNING: Some bad primes are unspecified"; end if;
 for p in PF do A[p]:=<5,Polynomial([1])>; end for;
 for bp in BP do A[bp[1]]:=<bp[2],bp[3]>; end for;
 N:=&*[Integers()|p^A[p][1] : p in Keys(A)]; wt2:=MotivicWeight(L);
 function cf(p,d) if IsDefined(A,p) then return A[p][2]; end if;
  ef:=EulerFactor(L,p);
  f:=coeff_sym11_deg4(L,ef,p,d); Pf:=Parent(f); BR:=BaseRing(Pf);
  g:=Pf!Polynomial([1,-p^wt2]);
  if not IsExact(BR) then Pf:=PowerSeriesRing(BR,Max(d+1,6));
   return (Pf!f)/(Pf!g); end if; return Parent(f)!(f/g); end function;
 HS:=AlternatingSquare(HodgeStructure(L))-
     TateTwist(HodgeStructure(RiemannZeta()),-wt2);
 LS:=LSeries(HS,N,cf : Precision:=prec);
 LS`name:=<"<1,1>-symplectic symmetrization of ",L>; LS:=de_pole(LS,pole);
 LS`name:=<"<1,1>-symplectic symmetrization of ",L>; return LS; end function;

intrinsic SymplecticSymmetrization
(L::LSer,S::SeqEnum : BadPrimes:=[],Precision:=L`precision,
                      PoleOrder:=0) -> LSer
{Given an L-series L and partition S, return the symplectic symmetrization L^S}
 require Universe(S) cmpeq Integers(): "Sequence must be integral";
 while 0 in S do Exclude(~S,0); end while; S:=Reverse(Sort(S));
 require &and[p ge 1 : p in S]: "Partition must be nonnegative";
 require Type(PoleOrder) eq RngIntElt and PoleOrder ge 0: "PoleOrder invalid";
 require HasHodgeStructure(L): "L does not seem to have a Hodge structure?";
 require IsSymplectic(L : AssumeTrue): "L-function must be symplectic";
 ////////////////////////////////////////////////////////////////////////
 pole:=PoleOrder; prec:=Precision; BP:=BadPrimes;
 if #S eq 0 then return RiemannZeta( : Precision:=prec); end if;
 if #S eq 1 then
  return Symmetrization(L,S : BadPrimes:=BadPrimes,Precision:=Precision,
			      PoleOrder:=PoleOrder); end if;
 require Degree(L) eq 4 and S eq [1,1]: "Not implemented (degree too large)";
 return symplectic_d4_sym11(L,BP,prec,pole); end intrinsic; 

/*
> Lf:=LSeries(Newforms(ModularForms(25,4))[1][1]);
> S:=Symmetrization(Lf,[3,1] : BadPrimes:=[<5,2,1+5^7*x>]); CFENew(S);
> S:=Symmetrization(Lf,[3] : BadPrimes:=[<5,4,1>]); CFENew(S);
> S:=Symmetrization(Lf,[4] : BadPrimes:=[<5,4,1-125^2*x>]); CFENew(S);
> sig:=ArtinRepresentations(NumberField(x^4+x+1))[5];
> S2:=Symmetrization(LSeries(sig),[2] : BadPrimes:=[<229,2,1-2*x+2*x^3-x^4>]);
> LSetPrecision(S2,10);
> CFENew(S2);
> H:=HypergeometricData([2,2,2],[1,1,1]);
> L := LSeries(H,1/2 : BadPrimes:=[<2,8,1>],Precision:=20);
> S21 := Symmetrization(L,[2,1] : BadPrimes:=[<2,20,1>]); // deg 8
> CFENew(S21);


> H:=HypergeometricData([4,4],[1,1,2,2]); // using EC to compute
> L:=LSeries(H,2 : BadPrimes:=[<2,16,1>],Precision:=10); CFENew(L);
> S:=Symmetrization(L,[1,1] : BadPrimes:=[<2,16,1-2*x>]); CFENew(S);
> H:=HypergeometricData([8],[1,2,4]); // using ArtRep to compute
> L:=LSeries(H,-1 : BadPrimes:=[<2,16,1>],Precision:=10); CFENew(L);
> S:=Symmetrization(L,[1,1] : BadPrimes:=[<2,23,1>]); CFENew(S);

> f:=Newforms(CuspForms(FullDirichletGroup(13).1^2,2))[1][1];
> L:=LSeries(f : Embedding:=func<x|Conjugates(x)[1]>);
> BP:=[<13,2,Polynomial([1,-Coefficient(EulerFactor(L,13),1)^2])>];
> S:=Symmetrization(L,[2] : BadPrimes:=BP); CFENew(S);

> A:=ArtinRepresentations(NumberField(x^3+x+1))[3];
> L:=LSeries(A); TL:=Translate(L,1);
> O2:=OrthogonalSymmetrization(TL,[4] : BadPrimes:=[<31,1,1-31^4*x>]);
> CFENew(O2);
> O2:=OrthogonalSymmetrization
>     (TL,[6] : BadPrimes:=[<31,1,1-31^6*x>],PoleOrder:=1);
> CFENew(O2);

> H:=HypergeometricData([2,2,2],[1,1,1]);
> L:=LSeries(H,2);
> O2:=OrthogonalSymmetrization(L,[2] : BadPrimes:=[<2,10,1>],Precision:=10);
> CFENew(O2);
> L:=LSeries(H,-1);
> BP:=[<2,6,(1-16*x^2)*(1-4*x)*(1-4*x)>];
> O2:=Symmetrization(L,[2] : BadPrimes:=BP,Precision:=10,PoleOrder:=2);
> CFENew(O2);
> BP:=[<2,6,(1-16*x^2)*(1-4*x)>];
> O2:=OrthogonalSymmetrization
      (L,[2] : BadPrimes:=BP,Precision:=10,PoleOrder:=1);
> CFENew(O2);
> H:=HypergeometricData([2,2,2],[1,1,1]);
> L:=LSeries(H,-1);
> O3:=OrthogonalSymmetrization(L,[3] : BadPrimes:=[<2,17,1>],Precision:=10);
> CFENew(O3); // same works with Translate(L,1)
> H:=HypergeometricData([2,2,2],[1,1,1]);
> L:=LSeries(H,-1);
> BP:=[<2,12,(1-16*x)^3*(1+16*x)^2>];
> O4:=OrthogonalSymmetrization(L,[4]:BadPrimes:=BP,PoleOrder:=1,Precision:=10);
> CFENew(O4);
> H := HypergeometricData([2,2,2],[1,1,1]);
> L := LSeries(H,2 : BadPrimes:=[<2,9,1>],Precision:=5);
> BP := [<2,18,1-16*x>];
> O4 := OrthogonalSymmetrization(L,[4] : BadPrimes:=BP);
> CFENew(O4);

*/

/*
function general_sympow(ef,part,deg)
 Se:=SFAElementary(Integers()); Sh:=SFA(Integers());
 C:=[Coefficient(ef,i)*(-1)^(i*(deg-1)) : i in [1..deg]];
 chi:=CharacterTable(CyclicGroup(1))[1];
 num:=Integers()!Symmetrization(deg*chi,part)[1];
 for c in [1..num
  R:=RestrictParts(Se!(Se.[c]~Sh.part),deg);
 // In general, use SFAElementary()!SFA.part
// > Se!(Se.[3]~Sh.[2]); // throw out parts bigger than 3
// > RestrictParts(Se!(Se.[coeff]~Sh.part),degree);
// too slow for Se!(Se.[10]~Sh.[3]) already : use func eq?
 end function;
*/
