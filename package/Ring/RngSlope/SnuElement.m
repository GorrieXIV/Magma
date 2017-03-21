
freeze;

//Copyright (c) 2011-13, Xavier Caruso and David Lubicz, Mark Watkins
//All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
//   * Redistributions of source code must retain the above copyright notice,
// this list of conditions and the following disclaimer.
//   * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
// TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

////////////////////////////////////////////////////////////////////////

/* Mark's setup for user-defined types */

intrinsic Normalize(f::RngSerPowElt) -> RngSerPowElt
{Given a power series ring element (over an inexact ring),
 remove the lower coefficients that are weakly zero.}
 if IsWeaklyZero(f) then return f; end if;
 A,v:=Coefficients(f); t:=AbsolutePrecision(f); P:=Parent(f);
 if t eq Infinity() then ERR:=0; else ERR:=O(P.1^t); end if;
 while #A ge 0 do e:=A[1]; if not IsWeaklyZero(e) then break; end if;
  Exclude(~A,e); v:=v+1; end while;
 if t eq Infinity() then return (P!A)*P.1^v;
 else return (P!A)*P.1^v+O(P.1^t); end if; end intrinsic;

intrinsic Normalize(f::RngSerLaurElt) -> RngSerPowElt
{Given a Laurent series ring element (over an inexact ring),
 remove the lower coefficients that are weakly zero.}
 if IsWeaklyZero(f) then return f; end if;
 A,v:=Coefficients(f); t:=AbsolutePrecision(f); P:=Parent(f);
 if t eq Infinity() then ERR:=0; else ERR:=O(P.1^t); end if;
 while #A ge 0 do e:=A[1]; if not IsWeaklyZero(e) then break; end if;
  Exclude(~A,e); v:=v+1; end while;
 if t eq Infinity() then return (P!A)*P.1^v;
 else return (P!A)*P.1^v+O(P.1^t); end if; end intrinsic;

////////////////////////////////////////////////////////////////////////

declare type SnuRng[SnuElement];

declare attributes SnuRng: R,nu,var_name; // the power series Ring
declare attributes SnuElement: f,S; // the power series

intrinsic SnuRing(R::FldPad,nu::FldRatElt : Precision:=Infinity()) -> SnuRng
{Given a p-adic field/ring and a (rational) slope, return the S^nu slope ring}
 S:=New(SnuRng); S`nu:=nu;
 if Precision eq Infinity() then S`R:=PowerSeriesRing(R);
 else S`R:=PowerSeriesRing(R,Precision); end if; return S; end intrinsic;

intrinsic SnuRing(R::RngPad,nu::FldRatElt : Precision:=Infinity()) -> SnuRng
{"}//"
 return SnuRing(FieldOfFractions(R),nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(R::RngPad,nu::RngIntElt : Precision:=Infinity()) -> SnuRng
{"}//"
 return SnuRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(R::FldPad,nu::RngIntElt : Precision:=Infinity()) -> SnuRng
{"}//"
return SnuRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(R::RngPad : Precision:=Infinity(),nu:=0) -> SnuRng
{Given a p-adic field/ring, return the S^nu slope ring where nu is a vararg}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SnuRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(R::FldPad : Precision:=Infinity(),nu:=0) -> SnuRng
{"}//"
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SnuRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(p::RngIntElt : Precision:=Infinity(),nu:=0) -> SnuRng
{Given a prime p, construct the S^nu slope ring over Q_p (nu is a vararg)}
 require IsPrime(p): "p must be prime";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p); return SnuRing(K,nu : Precision:=Precision); end intrinsic;

intrinsic SnuRing(p::RngIntElt,e::RngIntElt : Precision:=Infinity(),nu:=0)
 -> SnuRng
{Given a prime p and a precision e, construct the S^nu slope ring over
    Q_p with p-adic precision e (nu is a vararg)}
 require IsPrime(p): "p must be prime"; require e ge 1: "e must be at least 1";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p,e); return SnuRing(K,nu :Precision:=Precision); end intrinsic;

intrinsic SnuRing(S::RngSerPow,nu::FldRatElt) -> SnuRng
{Given a p-adic power series ring and a (rational) slope,
 construct the S^nu slope ring}
 require Type(BaseRing(S)) in {RngPad,FldPad}: "Ring must be over p-adics";
 return SnuRing(BaseRing(S),nu : Precision:=Precision(S)); end intrinsic;

intrinsic SnuRing(S::RngSerPow,nu::RngIntElt) -> SnuRng
{"}//"
 return SnuRing(S,Rationals()!nu); end intrinsic;

intrinsic SnuRing(S::RngSerPow : nu:=0) -> SnuRng
{Given a p-adic power series ring, return the S^nu slope ring (nu is a vararg)}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SnuRing(S,nu); end intrinsic;

intrinsic SnuRing(S::SpRng) -> SnuRng
{Given a S^nu_p ring, return the associated S^nu ring}
 return SnuRing(S`R,S`nu); end intrinsic;
intrinsic SnuRing(S::SuRng) -> SnuRng
{Given a S^nu_u ring, return the associated S^nu ring}
 return SnuRing(IntegerRing(S`R),S`nu); end intrinsic;

intrinsic 'eq'(S1::SnuRng,S2::SnuRng) -> BoolElt {Whether inputs are equal}
 return S1`R eq S2`R and S1`nu eq S2`nu; end intrinsic;
intrinsic 'ne'(S1::SnuRng,S2::SnuRng) -> BoolElt {Whether inputs are unequal}
 return not (S1 eq S2); end intrinsic;

intrinsic Slope(S::SnuRng) -> FldRatElt
{The slope of a S^nu slope ring} return S`nu; end intrinsic;

intrinsic Precision(S::SnuRng) -> RngIntElt
{The u-precision of the power series ring associated to a S^nu slope ring}
 return Precision(S`R); end intrinsic;

intrinsic CoefficientRing(S::SnuRng) -> RngIntElt
{The p-adic coefficient ring associated to a S^nu slope ring}
 return CoefficientRing(S`R); end intrinsic;

intrinsic PrintNamed(S::SnuRng,level::MonStgElt,name::MonStgElt)
{Print SnuRing}
 printf "Slope ring of slope %o given by %o",S`nu,S`R; end intrinsic;

intrinsic '.'(S::SnuRng,w::RngIntElt) -> SnuElement {The i-th generator (i=1)}
 require w eq 1: "Only first generator makes sense";
 return S!((S`R).1); end intrinsic;

intrinsic AssignNames(~S::SnuRng,str::[MonStgElt]) {}
 require #str eq 1: "Length of variable names for slope-ring must be 1";
 S`var_name:=str[1]; end intrinsic;

intrinsic Name(S::SnuRng,i::RngIntElt) -> SnuElement {The i-th name (i is 1)}
 require i eq 1: "Only 1st Name for SnuRng"; return S.1; end intrinsic;

forward valuation_and_degree;

NORMAL:=Normalize;

intrinsic IsCoercible(S::SnuRng,y::.) -> BoolElt,SnuElement {}
 if Type(y) in {RngIntElt,FldRatElt,FldPadElt,RngPadElt} then
  return true,S!(S`R)!y; end if;
 if Type(y) in {SnuElement,SpElement,SuElement} then
  try x:=S!y`f; return true,x;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 if Type(y) in {RngSerPowElt} then
  try r:=NORMAL((S`R)!y); v,d:=valuation_and_degree(r,S`nu);
   if v lt 0 then return false,"Slope too small for valid coercion"; end if;
   g:=New(SnuElement); g`f:=r; g`S:=S; return true,g;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 return false,"Improper type in slope-ring coercion attempt"; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Parent(f::SnuElement) -> SnuRng {The parent ring}
 return f`S; end intrinsic;

intrinsic '+'(x::SnuElement,y::SnuElement) -> SnuElement {Sum of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SnuElement); z`f:=NORMAL(x`f+y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '+'(x::SnuElement,y::.) -> SnuElement {Generic add (tries coercion)}
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(y::.,x::SnuElement) -> SnuElement {"}//"
 return x+(x`S)!y; end intrinsic;

intrinsic '-'(x::SnuElement) -> SnuElement {Negation of input}
 z:=New(SnuElement); z`f:=-x`f; z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SnuElement,y::SnuElement) -> SnuElement {Difference of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SnuElement); z`f:=NORMAL(x`f-y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SnuElement,y::.) -> SnuElement {Generic sub (tries coercion}
 return x-(x`S)!y; end intrinsic;
intrinsic '-'(y::.,x::SnuElement) -> SnuElement {"}//"
 return ((x`S)!y)-x; end intrinsic;

intrinsic '*'(x::SnuElement,y::SnuElement) -> SnuElement {Product of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SnuElement); z`f:=NORMAL(x`f*y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '*'(x::SnuElement,y::.) -> SnuElement {Generic mult (tries coercion)}
 return x*(x`S)!y; end intrinsic;
intrinsic '*'(y::.,x::SnuElement) -> SnuElement {"}//"
 return ((x`S)!y)*x; end intrinsic;

intrinsic '/'(x::SnuElement,y::SnuElement) -> SnuElement {Quotient of inputs}
 require x`S eq y`S: "x and y must have same parent";
 require not IsWeaklyZero(y): "Cannot divide by 0";
 f:=NORMAL(x`f/y`f); v,d:=valuation_and_degree(f,x`S`nu);
 require v ge 0 and d ge 0: "Division is not possible in S_nu";
 z:=New(SnuElement); z`f:=f; z`S:=x`S; return z; end intrinsic;
intrinsic '/'(x::SnuElement,y::.) -> SnuElement {Generic div (tries coercion)}
 return x/(x`S)!y; end intrinsic;
intrinsic '/'(y::.,x::SnuElement) -> SnuElement {"}//"
 return ((x`S)!y)/x; end intrinsic;

intrinsic '^'(x::SnuElement,n::RngIntElt) -> SnuElement {The n-th power of x};
 return (x`S)!(x`f^n); end intrinsic;

intrinsic 'eq'(x::SnuElement,y::SnuElement) -> BoolElt {Equality of inputs}
 require x`S eq y`S: "x and y must have same parent";
 return IsWeaklyZero(x-y); end intrinsic;
intrinsic 'eq'(x::SnuElement,y::.) -> BoolElt {Generic equals (tries coercion)}
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(y::.,x::SnuElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;

intrinsic 'ne'(x::SnuElement,y::SnuElement) -> BoolElt {Nonequality of inputs}
 return not (x eq y); end intrinsic;
intrinsic 'ne'(x::SnuElement,y::.) ->BoolElt {Generic unequal (tries coercion)}
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(y::.,x::SnuElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;

intrinsic NumericalPrecision(R::SnuRng) -> RngIntElt
{The effective power series precision of the input ring}
 if Precision(R) ne Infinity() then return Precision(R); end if;
 return RelativePrecision((1/(1+R.1))`f); end intrinsic;

intrinsic PrintNamed(x::SnuElement,level::MonStgElt,name::MonStgElt)
{Print SnuElement}
 if assigned x`S`var_name then str:=x`S`var_name;
  else str:="$.1"; end if; C,v:=Coefficients(x); first:=true;
 for c in [1..#C] do if IsWeaklyZero(C[c]) then continue; end if;
  if not first then printf " + "; else first:=false; end if;
  if c-1+v eq 0 then printf "%o",C[c]; continue; end if;
  if IsWeaklyZero(C[c]-1) then
   if c-1+v eq 1 then printf "%o",str; else printf "%o^%o",str,c-1+v; end if;
   continue; end if;
  if c-1+v eq 1 then printf "(%o)*%o",C[c],str; continue; end if;
  printf "(%o)*%o^%o",C[c],str,c-1+v; end for;
 if not first then printf " + "; end if;
 if AbsolutePrecision(x`f) ne Infinity() then
  printf "O(%o^%o)",str,AbsolutePrecision(x`f);
 else printf "O(%o^%o)",str,NumericalPrecision(x`S); end if; end intrinsic;

intrinsic LeadingTerm(x::SnuElement) -> RngSerPowElt
{The leading term in the power series expansion of a S^nu element}
 A,b,c:=Coefficients(x); w:=1; R:=x`S`R; p:=NumericalPrecision(x`S);
 for i in [1..#A] do
  if IsWeaklyZero(A[i]) then w:=w+1; b:=b+1; else break; end if; end for;
 if w gt #A then return O(R.1^p); end if; return A[w]*R.1^b; end intrinsic;

intrinsic WeierstrassTerm(x::SnuElement) -> RngSerPowElt
{The term corresponding to the Weierstrass degree (it has smallest valuation)}
 d:=WeierstrassDegree(x); R:=x`S`R; A,b,c:=Coefficients(x);
 if d eq -Infinity() or 1+d-b gt #A then p:=NumericalPrecision(x`S);
  return O(R.1^p); end if;
 if 1+d-b le #A then return A[1+d-b]*R.1^d; end if; end intrinsic;

intrinsic IsWeaklyZero(a::SnuElement) -> BoolElt {True if input is weakly zero}
 return &and[IsWeaklyZero(c) : c in Coefficients(a`f)]; end intrinsic;

intrinsic Coefficients(x::SnuElement) -> SeqEnum,RngIntElt,RngIntElt
{The coefficients of the underlying power series, with valuation shift}
 return Coefficients(x`f); end intrinsic;

intrinsic O(x::SnuElement) -> BoolElt {Returns O(x)}
 return Parent(x)!O(x`f); end intrinsic;

////////////////////////////////////////////////////////////////////////

function valuation_and_degree(f,nu)
 coef,pow:=Coefficients(f); val:=0; deg:=pow-1; vadd:=pow*nu;
 for i:=1 to #coef do
  if RelativePrecision(coef[i]) eq 0 then vadd:=vadd+nu; continue; end if;
  v:=Valuation(coef[i])+vadd;
  if deg lt pow or v lt val then val:=v; deg:=pow+i-1; end if;
  vadd:=vadd+nu; end for;
 if deg lt pow then return Infinity(),-Infinity();
 else return val,deg; end if; end function;

intrinsic GaussValuation(f::SnuElement) -> FldRatElt
{Return the Gauss valuation of the element f in its parent S^nu
 Returns Precision(Parent(f))+1 for 0}
 v,d:=valuation_and_degree(f`f,f`S`nu); if d ge 0 then return v; end if;
 return Precision(Parent(f))+1; end intrinsic;

intrinsic WeierstrassDegree(f::SnuElement) -> FldRatElt
{Return the Weierstrass degree of the element f in S^nu}
 v,d:=valuation_and_degree(f`f,f`S`nu);
 if d eq -1 then d eq -Infinity(); end if; return d; end intrinsic;

intrinsic IsDistinguished(f::SnuElement) -> BoolElt,RngIntElt
{Test if f is distinguished and returns its Weierstrass degree.}
 v,d:=valuation_and_degree(f`f,f`S`nu);
 if v eq 0 then return true,d; else return false, _; end if; end intrinsic;

////////////////////////////////////////////////////////////////////////

function higher_terms(f,n) P:=Parent(f); a,b:=Eltseq(f);
 a:=a[[Max(n+1-b,1)..#a]]; if b-n-1 ge 0 then return P!a*P.1^(b-n); end if;
 return P!a; end function;

function lower_terms(f,n) P:=Parent(f); a,b:=Eltseq(f);
 if n-b ge 1 then a:=a[[1..Min(n-b,#a)]]; return P!a*P.1^b; end if;
 return 0; end function;

function quot_rem_old(A,B,d,piprec,nu)
 S:=Parent(A); uprec:=d*(piprec+1); if d eq 0 then return A/B,S!0; end if;
 ChangePrecision(~B,uprec); ChangePrecision(~A,uprec); ERR:=O(S.1^uprec);
 Blow:=lower_terms(B,d); Bhiinv:=higher_terms(B,d)^-1; Q:=ERR;
 while true do Alow:=lower_terms(A,d)+ERR; Ahi:=higher_terms(A,d)+ERR;
  if valuation_and_degree(Ahi,nu) ge piprec then break; end if;
   Qadd:=Ahi*Bhiinv; Q:=Q+Qadd; A:=Alow-Blow*Qadd; uprec:=uprec-d; end while;
  // at end of loop? ChangePrecision(~A,uprec); ChangePrecision(~Q,uprec);
 return Q,A; end function; // this loses precision

function quot_rem(A,B,d,piprec,nu)
 S:=Parent(A); if d eq 0 then return A/B,S!0; end if; ERR:=O(S.1^piprec);
 Blow:=lower_terms(B,d); Bhiinv:=higher_terms(B,d)^-1; Q:=ERR;
 while true do Alow:=lower_terms(A,d)+ERR; Ahi:=higher_terms(A,d)+ERR;
  if valuation_and_degree(Ahi,nu) ge piprec then break; end if;
   Qadd:=Ahi*Bhiinv; Q:=Q+Qadd; A:=Alow-Blow*Qadd; end while;
 return Q,A; end function; // this loses precision

intrinsic Quotrem
(A::SnuElement,B::SnuElement) -> SnuElement,SnuElement
{Given A and B with v(A) >= v(B) returns Q,R such that A = B*Q + R with R
 a polynomial with degree less than the Weierstrass degree of B.
 We suppose that A and B have infinite u-precision (i.e are polynomials)
 and ensure that Q and R are known up to padic-precision piprec }
 require A`S eq B`S: "A and B must have same parent ring";
 require GaussValuation(A) ge GaussValuation(B): "Val(A) must be >= Val(B)";
 piprec:=Min(AbsolutePrecision(A`f),AbsolutePrecision(B`f));
 piprec:=Min(piprec,Precision(CoefficientRing(Parent(A`f))));
 if piprec eq Infinity() then piprec:=NumericalPrecision(A`S); end if;
 Q,R:=quot_rem(A`f,B`f,WeierstrassDegree(B),piprec,A`S`nu);
 return A`S!Q,A`S!R; end intrinsic;
// could assert answer is correct

intrinsic WeierstrassPreparation(f::SnuElement) -> SnuElement,SnuElement
{Let f be a distinguished element of S_nu  (i.e. whose Gauss valuation is 0)
 with Weierstrass degree d. Write f = UP where U is invertible in S^nu
 and P is a polynomial of degree d.}
 b,d:=IsDistinguished(f); require b: "f must be distinguished";
 prec:=Min(RelativePrecision(f`f),Precision(CoefficientRing(f`S`R)));
 if prec eq Infinity() then prec:=NumericalPrecision(f`S); end if;
 nu:=f`S`nu; xd:=f`S`R.1^d; q,r:=quot_rem(xd,f`f,d,prec,nu);
 pi:=UniformizingElement(CoefficientRing(f`S`R));
 dnu:=d*nu; assert IsIntegral(dnu); dnu:=Integers()!dnu;
 return f`S!f`S`R!(pi^dnu*q^(-1)),f`S!f`S`R!((xd-r)/pi^dnu); end intrinsic;
 // could assert answer is correct

function ext_gcd_snu(a,b,v,piprec,nu) pi:=[0,0]; flag:=2;
 S:=Parent(a); vv,d:=valuation_and_degree(b,nu);
 uprec:=d*(piprec+1); ERR:=O(S.1^uprec);
 Ma:=Matrix(S,1,2,[1+ERR,ERR]); Mb:=Matrix(S,1,2,[ERR,1+ERR]);
 while true do vv,d:=valuation_and_degree(b,nu); flag:=3-flag;
  // unsure what pi is, really
  if d lt 0 or vv+pi[flag] gt v then break; end if;
  q,r:=quot_rem(a,b,d,piprec,nu);
  a:=b; b:=-r; Mx:=Ma; Ma:=Mb; Mb:=-Mx+q*Mb; end while;
 return a,b,Ma[1,1],Ma[1,2],Mb[1,1],Mb[1,2]; end function;

intrinsic ExtendedGcd(a::SnuElement,b::SnuElement)
 -> SnuElement,SnuElement,SnuElement,SnuElement,SnuElement,SnuElement
{Given A and B with v(A)>=v(B) this returns G,H,w,x,y,z with Aw+Bx=G 
 where v(G)=v(B) and Ay+Bz=H with v(H)>v(A) and wz-xy=1. The fact that
 H need not be 0 in all cases is due to the non-Euclidean nature of S^nu.}
 require a`S eq b`S: "a and b must have same parent ring"; S:=a`S;
 if GaussValuation(a) lt GaussValuation(b) then
  G,H,x,w,z,y:=ExtendedGcd(b,a); H:=-H; z:=-z; y:=-y;
  assert w*z-x*y eq 1; assert a*w+b*x eq G; assert a*y+b*z eq H;
  return G,H,w,x,y,z; end if;
 piprec:=Min(AbsolutePrecision(a`f),AbsolutePrecision(b`f));
 piprec:=Min(piprec,Precision(CoefficientRing(Parent(a`f))));
 if piprec eq Infinity() then piprec:=NumericalPrecision(a`S); end if;
 G,H,w,x,y,z:=ext_gcd_snu(a`f,b`f,GaussValuation(b),piprec,S`nu);
 G:=S!G; H:=S!H; w:=S!w; x:=S!x; y:=S!y; z:=S!z;
 assert w*z-x*y eq 1; assert a*w+b*x eq G; assert a*y+b*z eq H;
 return G,H,w,x,y,z; end intrinsic;
