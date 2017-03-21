freeze;

/* Euler factors, split by MW, Oct 2014 */

lcf_list           := 0;
lcf_localfactors   := 1;
lcf_function       := 2;

procedure CheckIsNewForm(f) // ModFrmHilElt does not have is_newform
 if not assigned f`ef_warning then f`ef_warning:=true;
  if not assigned f`is_newform or not f`is_newform then
  "WARNING: Modular form is not known to be a newform";
 end if; end if; end procedure;

function function_varargs(f)
 S:=Sprint(f); ok,_,matches:=Regexp("\\\[ (.*) \\\]", S);
 if not ok then return [ Strings()| ];
 else return matches; end if; end function;

function function_call_string(f, fname, args, varargs)
 validargs:=function_varargs(f);
 varlist:=[ arg : arg in varargs | arg[1] in validargs ];
 if #varlist eq 0 then varstr:="";
 else
  varstr:=&cat[Sprintf(",%o:=%o",arg[1],arg[2]) : arg in varlist];
  varstr:=":" cat varstr[2..#varstr]; end if;
 return Sprintf("%o(%o%o)", fname, args, varstr); end function;

function FIX(f) C:=Coefficients(f);
 if not &and[IsCoercible(Integers(),c) : c in C] then return f; end if;
 C:=ChangeUniverse(C,Integers());
 if Type(f) eq RngUPolElt then return Polynomial(C); end if;
 assert Type(f) eq RngSerPowElt;
 PSR:=PowerSeriesRing(Integers(),AbsolutePrecision(f));
 return PSR!C; end function;

FCS:=function_call_string; ITS:=IntegerToString;

function get_euler_factor(L,p,d,prec)
 if L`cftype eq lcf_localfactors then
  fu:=L`cffun; A:=[<"Precision",ITS(prec)>];
  f:=eval FCS(fu,"fu",ITS(p)*","*ITS(d),A); end if;
 if L`cftype eq lcf_function then
  fu:=L`cffun; A:=[<"Precision",ITS(prec)>];
  if Type(L`parent) eq ModFrmElt then
   F:=PowerSeriesRing(Parent(eval FCS(fu,"fu","1",A)),d+1);
   c:=DirichletCharacter(L`parent)(p); R:=BaseRing(F);
   f:=F!([1,-eval FCS(fu,"fu",ITS(p),A),R!c*p^(Weight(L`parent)-1)]);
  else // not a ModFrmElt
   F:=PowerSeriesRing(Parent(eval FCS(fu,"fu","1",A)),d+1);
   f:=1/F!([1] cat [eval FCS(fu,"fu",ITS(p^k),A) : k in [1..d]]); end if;
  end if;
 if L`cftype eq lcf_list then // ignore Precision
  error if p^d gt #L`cffun, "Not enough coefficients in list";
  F:=PowerSeriesRing(Parent(L`cffun[1]),d+1);
  f:=1/F!([1] cat [L`cffun[p^k] : k in [1..d]]); end if;
 return f; end function;

PREC:=Precision;

intrinsic EulerFactor(Q::FldRat,p::RngIntElt) -> . {Return 1-x}
 return Polynomial([1,-1]); end intrinsic;

intrinsic EulerFactor(K::FldNum,p::RngIntElt) -> .
{Given a number field and a (rational) prime, return the Euler factor}
 R:=PermutationCharacter(K); return EulerFactor(R,p); end intrinsic;
// maybe allow user to compute w/o using Artin decomposition?

intrinsic EulerFactor
(L::LSer,p::RngIntElt : Degree:=0,Precision:=0,Integral:=false) -> .
{Given an L-series, return the pth Euler factor for p prime.}
 require p ge 1: "p must be positive"; require IsPrime(p): "p must be prime";
 if Degree eq 0 then d:=#L`gamma; else d:=Degree; end if;
 if Precision eq 0 then prec:=PREC(RealField()); else prec:=Precision; end if;
 if Type(L`parent) eq ModFrmElt then CheckIsNewForm(L`parent); end if;
 if ISA(Type(L`parent),FldNum) then return EulerFactor(L`parent,p); end if;
 // maybe check if L is using Artin reps?
 if L`prod cmpne false then // should not pass Integral!
  E:=&*[EulerFactor(F[1],p : Degree:=Degree,Precision:=Precision)^F[2]
	: F in L`prod];
  if ISA(Type(L`parent),FldNum) or Integral then
   E:=Polynomial([Round(Real(x)) : x in Coefficients(E)]); end if;
  return E; end if;
 LOOKUP:=false; ef:=0;
 if IsDefined(L`known_ef,p) then ef:=L`known_ef[p]; OK:=true;
  if Type(ef) eq RngSerPowElt then OK:=AbsolutePrecision(ef) gt d; end if;
  BR:=BaseRing(Parent(ef));
  if Type(BR) eq FldCom and PREC(BR) lt prec then OK:=false; end if;
  if OK then LOOKUP:=true; end if; end if;
 if LOOKUP then f:=ef; else f:=get_euler_factor(L,p,d,prec); end if;
 if Type(f) eq RngIntElt then f:=Polynomial([1]); end if;
 if Degree ne 0 then f:=PowerSeriesRing(BaseRing(Parent(f)),d+1)!f;
 else f:=Polynomial(Coefficients(f)); end if;
 f:=FIX(f);
 if Integral then
  if Type(BaseRing(Parent(f))) in {FldRat,RngInt} then
   f:=ChangeRing(Polynomial(Coefficients(f)),Integers());
  else f:=Polynomial([Round(Real(x)) : x in Coefficients(f)]); end if; end if;
 if p lt L`EF_SAVE_LIM then L`known_ef[p]:=f; end if; return f; end intrinsic;

DEG:=Degree;
intrinsic EulerFactor(L::LSer,P::RngOrdIdl : Degree:=0,Precision:=0) -> .
{Given an L-series over K and a prime ideal of K, return the Euler factor}
 require IsPrime(P): "The ideal must be prime";
 K:=NumberField(Order(P));
 require assigned L`degreeK and L`degreeK[2] eq K:
  "L-function must have an Euler product over the field of the ideal";
 if Precision eq 0 then prec:=GetPrecision(1.2); else prec:=Precision; end if;
 if Degree eq 0 then d:=L`degreeK[1]*DEG(P); else d:=Degree; end if;
 return L`cffuncK(P,d : Precision:=prec); end intrinsic;
