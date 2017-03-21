
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

import "SnuElement.m": valuation_and_degree;
import "SnuElement.m" : quot_rem;

declare type SpRng[SpElement];

declare attributes SpRng: R,nu,var_name; // the power series Ring
declare attributes SpRng: A,B; // Associative arrays for R^n and R^(m,n)
declare attributes SpElement: f,S; // the power series

intrinsic SpRing(R::FldPad,nu::FldRatElt : Precision:=Infinity()) -> SpRng
{Given a p-adic ring/field and a (rational) slope, return the S^nu_p ring}
 S:=New(SpRng); S`nu:=nu; S`A:=AssociativeArray(Integers());
 S`B:=AssociativeArray(CartesianProduct(Integers(),Integers()));
 if Precision eq Infinity() then S`R:=PowerSeriesRing(R);
 else S`R:=PowerSeriesRing(R,Precision); end if; return S; end intrinsic;

intrinsic SpRing(R::RngPad,nu::FldRatElt : Precision:=Infinity()) -> SpRng
{"}//"
 return SpRing(FieldOfFractions(R),nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(R::RngPad,nu::RngIntElt : Precision:=Infinity()) -> SpRng
{"}//"
 return SpRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(R::FldPad,nu::RngIntElt : Precision:=Infinity()) -> SpRng
{"}//"
 return SpRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(R::RngPad : Precision:=Infinity(),nu:=0) -> SpRng
{Given a p-adic ring/field, return the S^nu_p slope ring (nu is a vararg)}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SpRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(R::FldPad : Precision:=Infinity(),nu:=0) -> SpRng {"}//"
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SpRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(p::RngIntElt : Precision:=Infinity(),nu:=0) -> SpRng
{Given a prime p, get the S^nu_p slope ring over Q_p (nu is a vararg)}
 require IsPrime(p): "p must be prime";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p); return SpRing(K,nu : Precision:=Precision); end intrinsic;

intrinsic SpRing(p::RngIntElt,e::RngIntElt : Precision:=Infinity(),nu:=0)
  -> SpRng
{Given a prime p and a precision e, construct the S^nu_p slope
 ring over Q_p with p-adic precision e (nu is a vararg)}
 require IsPrime(p): "p must be prime"; require e ge 1: "e must be at least 1";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p,e); return SpRing(K,nu :Precision:=Precision); end intrinsic;

intrinsic SpRing(S::RngSerPow,nu::FldRatElt) -> SpRng
{Given a p-adic power series ring and a (rational) slope,
 construct the associated S^nu_p slope ring}
 require Type(BaseRing(S)) in {RngPad,FldPad}: "Ring must be over p-adics";
 return SpRing(BaseRing(S),nu : Precision:=Precision(S)); end intrinsic;
 
intrinsic SpRing(S::RngSerPow,nu::RngIntElt) -> SpRng {"}//"
 return SpRing(S,Rationals()!nu); end intrinsic;

intrinsic SpRing(S::RngSerPow : nu:=0) -> SpRng
{Given a p-adic power series ring, get the S^nu_p slope ring (nu is a vararg)}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SpRing(S,nu); end intrinsic;

intrinsic SpRing(S::SnuRng) -> SpRng
{Given a S^nu slope ring, construct the associated S^nu_p localization}
 return SpRing(S`R,S`nu); end intrinsic;

intrinsic 'eq'(S1::SpRng,S2::SpRng) -> BoolElt {Whether two Sp rings are equal}
 return S1`R eq S2`R and S1`nu eq S2`nu; end intrinsic;
intrinsic 'ne'(S1::SpRng,S2::SpRng) -> BoolElt {Whether 2 Sp rings are unequal}
 return not (S1 eq S2); end intrinsic;

intrinsic Precision(S::SpRng) -> RngIntElt
{The u-precision of the power series ring associated to a S^nu_p slope ring}
 return Precision(S`R); end intrinsic;

intrinsic Slope(S::SpRng) -> FldRatElt {The slope of a S^nu_p slope ring}
 return S`nu; end intrinsic;

intrinsic CoefficientRing(S::SpRng) -> RngIntElt
{The p-adic coefficient ring of a S^nu_p slope ring}
 return CoefficientRing(S`R); end intrinsic;

intrinsic PrintNamed(S::SpRng,level::MonStgElt,name::MonStgElt) {Print SpRng}
 printf "Sp-slope ring of slope %o given by %o",S`nu,S`R; end intrinsic;

 intrinsic '.'(S::SpRng,w::RngIntElt) -> SpElement {The i-th generator (i=1)}
 require w eq 1: "Only first generator makes sense";
 return S!((S`R).1); end intrinsic;

intrinsic AssignNames(~S::SpRng,str::[MonStgElt]) {}
 require #str eq 1: "Length of variable names for slope-ring must be 1";
 S`var_name:=str[1]; end intrinsic;

intrinsic Name(S::SpRng,i::RngIntElt) -> SpElement {The i-th name (i is 1)}
 require i eq 1: "Only 1st Name for SpRng"; return S.1; end intrinsic;

NORMAL:=Normalize;

intrinsic IsCoercible(S::SpRng,y::.) -> BoolElt,SpElement {}
 if Type(y) in {RngIntElt,FldRatElt,FldPadElt,RngPadElt} then
  return true,S!(S`R)!y; end if;
 if Type(y) in {SnuElement,SpElement} then
  try x:=S!y`f; return true,x;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 if Type(y) in {RngSerPowElt} then
  try r:=NORMAL((S`R)!y); g:=New(SpElement); g`f:=r; g`S:=S; return true,g;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 return false,"Improper type in slope-ring coercion attempt"; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Parent(f::SpElement) -> SpRng {The parent Sp ring of an element}
 return f`S; end intrinsic;

intrinsic '+'(x::SpElement,y::SpElement) -> SpElement {The sum of the inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SpElement); z`f:=NORMAL(x`f+y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '+'(x::SpElement,y::.) -> SpElement {Generic add (tries coercion)}
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(y::.,x::SpElement) -> SpElement {"}//"
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(x::SpElement,y::SnuElement) -> SpElement {"}//"
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(y::SnuElement,x::SpElement) -> SpElement {"}//"
 return x+(x`S)!y; end intrinsic;

intrinsic '-'(x::SpElement) -> SpElement {Negation of the input} // negation
 z:=New(SpElement); z`f:=-x`f; z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SpElement,y::SpElement) -> SpElement {Difference of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SpElement); z`f:=NORMAL(x`f-y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SpElement,y::.) -> SpElement {Generic sub (tries coercion)}
 return x-(x`S)!y; end intrinsic;
intrinsic '-'(y::.,x::SpElement) -> SpElement {Generic sub (tries coercion)}
 return ((x`S)!y)-x; end intrinsic;
intrinsic '-'(x::SpElement,y::SnuElement) -> SpElement {"}//"
 return x-(x`S)!y; end intrinsic;
intrinsic '-'(y::SnuElement,x::SpElement) -> SpElement {"}//"
 return ((x`S)!y)-x; end intrinsic;

intrinsic '*'(x::SpElement,y::SpElement) -> SpElement {Product of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SpElement); z`f:=NORMAL(x`f*y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '*'(x::SpElement,y::.) -> SpElement {Generic mult (tries coercion)}
 return (x`S)!(x`f*(x`S`R)!y); end intrinsic;
intrinsic '*'(y::.,x::SpElement) -> SpElement {"}//"
 return (x`S)!(x`f*(x`S`R)!y); end intrinsic;
intrinsic '*'(x::SpElement,y::SnuElement) -> SpElement {"}//"
 require x`S`R eq y`S`R: "x and y must have compatible p-adic rings";
 return x`S!(x`f*y`f); end intrinsic;
intrinsic '*'(y::SnuElement,x::SpElement) -> SpElement {"}//"
 return x*y; end intrinsic;

intrinsic '/'(x::SpElement,y::SpElement) -> SpElement {Quotient of inputs}
 require x`S eq y`S: "x and y must have same parent";
 require not IsWeaklyZero(y): "Cannot divide by 0";
 if IsWeaklyZero(x) then return x`S!0; end if;
 f:=NORMAL(x`f/y`f); require Degree(f) ge 0: "Division is not possible in Sp";
 z:=New(SpElement); z`f:=f; z`S:=x`S; return z; end intrinsic;
intrinsic '/'(x::SpElement,y::.) -> SpElement {Generic div (tries coercion)}
 return (x`S)!(x`f/((x`S`R)!y)); end intrinsic;
intrinsic '/'(y::.,x::SpElement) -> SpElement {"}//"
 return (x`S)!(((x`S`R)!y)/(x`f)); end intrinsic;
intrinsic '/'(x::SpElement,y::SnuElement) -> SpElement {"}//"
 require not IsWeaklyZero(y): "y cannot be zero";
 require x`S`R eq y`S`R: "x and y must have compatible p-adic rings";
 return x`S!(x`f/y`f); end intrinsic;
intrinsic '/'(y::SnuElement,x::SpElement) -> SpElement {"}//"
 require not IsWeaklyZero(x): "x cannot be zero";
 require x`S`R eq y`S`R: "x and y must have compatible p-adic rings";
 return x`S!(x`f/y`f); end intrinsic;

intrinsic '^'(x::SpElement,n::RngIntElt) -> SpElement {The n-th power of x};
 return x`S!((x`f)^n); end intrinsic;

intrinsic 'eq'(x::SpElement,y::SpElement) -> BoolElt {Whether inputs are equal}
 require x`S eq y`S: "x and y must have same parent";
 return IsWeaklyZero(x-y); end intrinsic; 
intrinsic 'eq'(x::SpElement,y::.) -> BoolElt {Generic equals (tries coercion)}
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(y::.,x::SpElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(x::SpElement,y::SnuElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(y::SnuElement,x::SpElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;

intrinsic 'ne'(x::SpElement,y::SpElement) -> BoolElt {Nonequality of inputs}
 require x`S eq y`S: "x and y must have same parent";
 return not (x eq y); end intrinsic; 
intrinsic 'ne'(x::SpElement,y::.) -> BoolElt {Generic unequal (tries coercion)}
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(y::.,x::SpElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(x::SpElement,y::SnuElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(y::SnuElement,x::SpElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;

intrinsic NumericalPrecision(R::SpRng) -> RngIntElt
{The effective power series precision of the input ring}
 if Precision(R) ne Infinity() then return Precision(R); end if;
 return RelativePrecision((1/(1+R.1))`f); end intrinsic;

intrinsic PrintNamed(x::SpElement,level::MonStgElt,name::MonStgElt)
{Print SpElement}
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

intrinsic LeadingTerm(x::SpElement) -> RngSerPowElt
{The leading term of the power series expansion of an S^nu_p element}
 A,b,c:=Coefficients(x); w:=1; R:=x`S`R; p:=NumericalPrecision(x`S);
 for i in [1..#A] do
  if IsWeaklyZero(A[i]) then w:=w+1; b:=b+1; else break; end if; end for;
 if w gt #A then return O(R.1^p); end if; return A[w]*R.1^b; end intrinsic;

intrinsic WeierstrassTerm(x::SpElement) -> RngSerPowElt
{The Weierstrass term of a S^nu_p element}
 d:=WeierstrassDegree(x); R:=x`S`R; A,b,c:=Coefficients(x);
 if d eq -Infinity() or 1+d-b gt #A then p:=NumericalPrecision(x`S);
  return O(R.1^p); end if;
 if 1+d-b le #A then return A[1+d-b]*R.1^d; end if; end intrinsic;

intrinsic IsWeaklyZero(a::SpElement) -> BoolElt {True if input is weakly zero}
 return &and[IsWeaklyZero(c) : c in Coefficients(a`f)]; end intrinsic;

intrinsic O(x::SpElement) -> BoolElt {Returns O(x)}
 return Parent(x)!O(x`f); end intrinsic;

intrinsic Coefficients(x::SpElement) -> SeqEnum,RngIntElt,RngIntElt
{The coefficients of the underlying power series, with valuation shift}
 return Coefficients(x`f); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic GaussValuation(f::SpElement) -> FldRatElt
{Return the Gauss valuation of the element f in its parent S^nu_p
 Returns Precision(Parent(f))+1 for 0}
 v,d:=valuation_and_degree(f`f,f`S`nu); if d ge 0 then return v; end if;
 return Precision(Parent(f))+1; end intrinsic;

intrinsic WeierstrassDegree(f::SpElement) -> FldRatElt
{Return the Weierstrass degree of the element f in S^nu_p}
 v,d:=valuation_and_degree(f`f,f`S`nu);
 if d eq -1 then d eq -Infinity(); end if; return d; end intrinsic;

intrinsic Quotrem(A::SpElement,B::SpElement) -> SpElement,SpElement
{Given A and B returns Q,R such that A = B*Q + R with R a polynomial
 whose degree is less than the Weierstrass degree of B}
 require A`S eq B`S: "A and B must have same parent ring";
 require not IsWeaklyZero(B): "Cannot take quotient by zero element";
 AR:=A`S; P:=UniformizingElement(CoefficientRing(AR`R));
 s:=0; vB:=GaussValuation(B);
 if vB lt 0 then s:=Ceiling(-vB); B:=B*P^s; vB:=vB+s; end if;
 t:=0; vA:=GaussValuation(A);
 if vA lt 0 then t:=Ceiling(-vA); A:=A*P^t; vA:=vA+t; end if;
 if vA lt vB then c:=Ceiling(vB-vA); t:=t+c; A:=A*P^c; end if;
 S:=SnuRing(A`S`R,A`S`nu); Q,R:=Quotrem(S!A,S!B);
 Q:=AR!Q; R:=AR!R; Q:=Q*P^(s-t); R:=R/P^t; return Q,R; end intrinsic;

function extended_gcd_sp(a,b,v,piprec,nu)
 S:=Parent(a); Ma:=Matrix(S,1,2,[1,0]); Mb:=Matrix(S,1,2,[0,1]);
 while true do if IsWeaklyZero(b) then break; end if;
  vv,d:=valuation_and_degree(b,nu); q,r:=quot_rem(a,b,d,piprec,nu);
  a:=b; b:=-r; Mx:=Ma; Ma:=Mb; Mb:=-Mx+q*Mb; end while;
 return a,b,Ma[1,1],Ma[1,2],Mb[1,1],Mb[1,2]; end function;

intrinsic ExtendedGcd(a::SpElement,b::SpElement)
 -> SpElement,SpElement,SpElement,SpElement,SpElement,SpElement
{Given A and B with v(A)>=v(B) this returns G,H,w,x,y,z with Aw+Bx=G
 where v(G)=v(B) and Ay+Bz=H and wz-xy=1. Here H will always be 0,
 since S_p^nu is Euclidean.}
 require a`S eq b`S: "a and b must have same parent ring"; S:=a`S;
 if GaussValuation(a) lt GaussValuation(b) then
  G,H,x,w,z,y:=ExtendedGcd(b,a); H:=-H; z:=-z; y:=-y;
  assert w*z-x*y eq 1; assert a*w+b*x eq G; assert a*y+b*z eq H;
  assert H eq 0; return G,H,w,x,y,z; end if;
 piprec:=Precision(CoefficientRing(Parent(a`f)));
 G,H,w,x,y,z:=extended_gcd_sp(a`f,b`f,GaussValuation(b),piprec,S`nu);
 G:=S!G; H:=S!H; w:=S!w; x:=S!x; y:=S!y; z:=S!z;
 assert w*z-x*y eq 1; assert a*w+b*x eq G; assert a*y+b*z eq H;
 assert H eq 0; return G,H,w,x,y,z; end intrinsic;

