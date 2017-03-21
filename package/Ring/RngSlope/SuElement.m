
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

declare type SuRng[SuElement];

declare attributes SuRng: R,nu,var_name; // the power series Ring
declare attributes SuRng: A,B; // Associative arrays for R^n and R^(m,n)
declare attributes SuElement: f,S; // the power series

intrinsic SuRing(R::FldPad,nu::FldRatElt : Precision:=Infinity()) -> SuRng
{Given a p-adic ring/field and a (rational) slope, return the S^nu_u ring}
 S:=New(SuRng); S`nu:=nu; S`A:=AssociativeArray(Integers());
 S`B:=AssociativeArray(CartesianProduct(Integers(),Integers()));
 if Precision eq Infinity() then S`R:=LaurentSeriesRing(R);
 else S`R:=LaurentSeriesRing(R,Precision); end if; return S; end intrinsic;

intrinsic SuRing(R::RngPad,nu::FldRatElt : Precision:=Infinity()) -> SuRng
{"}//"
 return SuRing(FieldOfFractions(R),nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(R::RngPad,nu::RngIntElt : Precision:=Infinity()) -> SuRng
{"}//"
 return SuRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(R::FldPad,nu::RngIntElt : Precision:=Infinity()) -> SuRng
{"}//"
 return SuRing(R,Rationals()!nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(R::RngPad : Precision:=Infinity(),nu:=0) -> SuRng
{Given a p-adic ring/field, return the S^nu_u slope ring (nu is a vararg)}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SuRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(R::FldPad : Precision:=Infinity(),nu:=0) -> SuRng {"}//"
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SuRing(R,nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(p::RngIntElt : Precision:=Infinity(),nu:=0) -> SuRng
{Given a prime p, get the S^nu_u slope ring over Q_p (nu is a vararg)}
 require IsPrime(p): "p must be prime";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p); return SuRing(K,nu : Precision:=Precision); end intrinsic;

intrinsic SuRing(p::RngIntElt,e::RngIntElt : Precision:=Infinity(),nu:=0)
 -> SuRng
{Given a prime p and a precision e, construct the S^nu_u slope
 ring over Q_p with p-adic precision e (nu is a vararg)}
 require IsPrime(p): "p must be prime"; require e ge 1: "e must be at least 1";
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 K:=pAdicField(p,e); return SuRing(K,nu :Precision:=Precision); end intrinsic;

intrinsic SuRing(S::RngSerLaur,nu::FldRatElt) -> SuRng
{Given a p-adic power/Laurent series ring and a (rational) slope,
 construct the associated S^nu_u slope ring}
 require Type(BaseRing(S)) in {RngPad,FldPad}: "Ring must be over p-adics";
 return SuRing(BaseRing(S),nu : Precision:=Precision(S)); end intrinsic;
intrinsic SuRing(S::RngSerLaur,nu::RngIntElt) -> SuRng {"}//"
 return SuRing(S,Rationals()!nu); end intrinsic;

intrinsic SuRing(S::RngSerPow,nu::FldRatElt) -> SuRng {"}//"
 require Type(BaseRing(S)) in {RngPad,FldPad}: "Ring must be over p-adics";
 return SuRing(BaseRing(S),nu : Precision:=Precision(S)); end intrinsic;
 intrinsic SuRing(S::RngSerPow,nu::RngIntElt) -> SuRng {"}//"
 return SuRing(S,Rationals()!nu); end intrinsic;

intrinsic SuRing(S::RngSerLaur : nu:=0) -> SuRng
{Given a p-adic power/Laurent series ring,
 construct the S^nu_u slope ring (nu is a vararg)}
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SuRing(S,nu); end intrinsic;
intrinsic SuRing(S::RngSerPow : nu:=0) -> SuRng {"}//"
 b,q:=IsCoercible(Rationals(),nu); require b: "nu must be rational";
 return SuRing(S,nu); end intrinsic;

intrinsic SuRing(S::SnuRng) -> SpRng
{Given a S^nu slope ring, construct the associated S^nu_u localization}
 return SuRing(S`R,S`nu); end intrinsic;

intrinsic 'eq'(S1::SuRng,S2::SuRng) -> BoolElt {Whether two Su rings are equal}
 return S1`R eq S2`R and S1`nu eq S2`nu; end intrinsic;
intrinsic 'ne'(S1::SuRng,S2::SuRng) -> BoolElt {Whether 2 Su rings are unequal}
return not (S1 eq S2); end intrinsic;

intrinsic Precision(S::SuRng) -> RngIntElt
{The u-precision of the power series ring associated to a S^nu_u slope ring}
 return Precision(S`R); end intrinsic;

intrinsic Slope(S::SuRng) -> FldRatElt {The slope of a S^nu_u slope ring}
 return S`nu; end intrinsic;

intrinsic CoefficientRing(S::SuRng) -> RngIntElt
{The p-adic coefficient ring of a S^nu_u slope ring}
 return CoefficientRing(S`R); end intrinsic;

intrinsic PrintNamed(S::SuRng,level::MonStgElt,name::MonStgElt) {Print SuRng}
 printf "Su-slope ring of slope %o given by %o",S`nu,S`R; end intrinsic;

intrinsic '.'(S::SuRng,w::RngIntElt) -> SuElement {The i-th generator (i is 1)}
 require w eq 1: "Only first generator makes sense";
 return S!((S`R).1); end intrinsic;

intrinsic AssignNames(~S::SuRng,str::[MonStgElt]) {}
 require #str eq 1: "Length of variable names for slope-ring must be 1";
 S`var_name:=str[1]; end intrinsic;

intrinsic Name(S::SuRng,i::RngIntElt) -> SuElement {The i-th name (i is 1)}
 require i eq 1: "Only 1st Name for SuRng"; return S.1; end intrinsic;

NORMAL:=Normalize;

intrinsic IsCoercible(S::SuRng,y::.) -> BoolElt,SuElement {}
 if Type(y) in {RngIntElt,FldRatElt,FldPadElt,RngPadElt} then
  return true,S!(S`R)!y; end if;
 if Type(y) in {SnuElement,SuElement} then
  try x:=S!y`f; return true,x;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 if Type(y) in {RngSerLaurElt,RngSerPowElt} then
  try r:=NORMAL((S`R)!y); v:=valuation_and_degree(r,S`nu);
   if v lt 0 then return false,"Slope too small for valid coercion"; end if;
   g:=New(SuElement); g`f:=r; g`S:=S; return true,g;
  catch e return false,"Cannot coerce y into slope ring"; end try; end if;
 return false,"Improper type in slope-ring coercion attempt"; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Parent(f::SuElement) -> SuRng {} return f`S; end intrinsic;

intrinsic '+'(x::SuElement,y::SuElement) -> SuElement {Sum of the inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SuElement); z`f:=NORMAL(x`f+y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '+'(x::SuElement,y::.) -> SuElement {Generic add (tries coercion)}
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(y::.,x::SuElement) -> SuElement {"}//"
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(x::SuElement,y::SnuElement) -> SuElement {"}//"
 return x+(x`S)!y; end intrinsic;
intrinsic '+'(y::SnuElement,x::SuElement) -> SuElement {"}//"
 return x+(x`S)!y; end intrinsic;

intrinsic '-'(x::SuElement) -> SuElement {Negation of the input} // negation
 z:=New(SuElement); z`f:=-x`f; z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SuElement,y::SuElement) -> SuElement {Difference of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SuElement); z`f:=NORMAL(x`f-y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '-'(x::SuElement,y::.) -> SuElement {Generic sub (tries coercion)}
 return x-(x`S)!y; end intrinsic;
intrinsic '-'(y::.,x::SuElement) -> SuElement {"}//"
 return ((x`S)!y)-x; end intrinsic;
intrinsic '-'(x::SuElement,y::SnuElement) -> SuElement {"}//"
 return x-(x`S)!y; end intrinsic;
intrinsic '-'(y::SnuElement,x::SuElement) -> SuElement {"}//"
 return ((x`S)!y)-x; end intrinsic;

intrinsic '*'(x::SuElement,y::SuElement) -> SuElement {Product of inputs}
 require x`S eq y`S: "x and y must have same parent";
 z:=New(SuElement); z`f:=NORMAL(x`f*y`f); z`S:=x`S; return z; end intrinsic;
intrinsic '*'(x::SuElement,y::.) -> SuElement {Generic mult (tries coercion)}
 return (x`S)!(x`f*(x`S`R)!y); end intrinsic;
intrinsic '*'(y::.,x::SuElement) -> SuElement {"}//"
 return (x`S)!(x`f*(x`S`R)!y); end intrinsic;
intrinsic '*'(x::SuElement,y::SnuElement) -> SuElement {"}//"
 return x`S!(x`f*y`f); end intrinsic;
intrinsic '*'(y::SnuElement,x::SuElement) -> SuElement {"}//"
 return x*y; end intrinsic;

intrinsic '/'(x::SuElement,y::SuElement) -> SuElement {Quotient of inputs}
 require x`S eq y`S: "x and y must have same parent";
 require not IsWeaklyZero(y): "Cannot divide by 0";
 if IsWeaklyZero(x) then return x`S!0; end if; f:=NORMAL(x`f/y`f);
 require valuation_and_degree(f,x`S`nu) ge 0: "Division is not possible in Su";
 z:=New(SuElement); z`f:=f; z`S:=x`S; return z; end intrinsic;
intrinsic '/'(x::SuElement,y::.) -> SuElement {Generic div (tries coercion)}
 return (x`S)!(x`f/((x`S`R)!y)); end intrinsic;
intrinsic '/'(y::.,x::SuElement) -> SuElement {"}//"
 return (x`S)!(((x`S`R)!y)/(x`f)); end intrinsic;
intrinsic '/'(x::SuElement,y::SnuElement) -> SuElement {"}//"
 require not IsWeaklyZero(y): "y cannot be zero";
 return (x`S)!(x`f/y`f); end intrinsic;
intrinsic '/'(y::SnuElement,x::SuElement) -> SuElement {"}//"
 require not IsWeaklyZero(x): "x cannot be zero";
 return (x`S)!(x`f/y`f); end intrinsic;

intrinsic '^'(x::SuElement,n::RngIntElt) -> SuElement {The n-th power of x};
 return (x`S)!(x`f^n); end intrinsic;

intrinsic 'eq'(x::SuElement,y::SuElement) -> BoolElt {Equality of inputs}
 require x`S eq y`S: "x and y must have same parent";
 return IsWeaklyZero(x-y); end intrinsic; 
intrinsic 'eq'(x::SuElement,y::.) -> BoolElt {Generic equals (tries coercion)}
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(y::.,x::SuElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(x::SuElement,y::SnuElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;
intrinsic 'eq'(y::SnuElement,x::SuElement) -> BoolElt {"}//"
 return x eq x`S!y; end intrinsic;

intrinsic 'ne'(x::SuElement,y::SuElement) -> BoolElt {Nonequality of inputs}
 require x`S eq y`S: "x and y must have same parent";
 return not (x eq y); end intrinsic; 
intrinsic 'ne'(x::SuElement,y::.) -> BoolElt {Generic unequal (tries coercion)}
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(y::.,x::SuElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(x::SuElement,y::SnuElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;
intrinsic 'ne'(y::SnuElement,x::SuElement) -> BoolElt {"}//"
 return x ne x`S!y; end intrinsic;

intrinsic NumericalPrecision(R::SuRng) -> RngIntElt
{The effective power series precision of the input ring}
 if Precision(R) ne Infinity() then return Precision(R); end if;
 return RelativePrecision((1/(1+R.1))`f); end intrinsic;

intrinsic PrintNamed(x::SuElement,level::MonStgElt,name::MonStgElt)
{Print SuElement}
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

intrinsic LeadingTerm(x::SuElement) -> RngSerLaurElt
{The leading term of the Laurent series expansion of an S^nu_u element}
 A,b,c:=Coefficients(x); w:=1; R:=x`S`R; p:=NumericalPrecision(x`S);
 for i in [1..#A] do
  if IsWeaklyZero(A[i]) then w:=w+1; b:=b+1; else break; end if; end for;
 if w gt #A then return O(R.1^p); end if; return A[w]*R.1^b; end intrinsic;

intrinsic WeierstrassTerm(x::SuElement) -> RngSerLaurElt
{The Weierstrass term of a S^nu_u element}
 d:=WeierstrassDegree(x); R:=x`S`R; A,b,c:=Coefficients(x);
 if d eq -Infinity() or 1+d-b gt #A then p:=NumericalPrecision(x`S);
  return O(R.1^p); end if;
 if 1+d-b le #A then return A[1+d-b]*R.1^d; end if; end intrinsic;

intrinsic IsWeaklyZero(a::SuElement) -> BoolElt {True if input is weakly zero}
 return &and[IsWeaklyZero(c) : c in Coefficients(a`f)]; end intrinsic;

intrinsic O(x::SuElement) -> BoolElt {Returns O(x)}
 return Parent(x)!O(x`f); end intrinsic;

intrinsic Coefficients(x::SuElement) -> SeqEnum,RngIntElt,RngIntElt
{The coefficients of the underlying power series, with valuation shift}
 return Coefficients(x`f); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic CanonicalElement(S::SuRng,v::FldRatElt) -> SuElement
{The canonical element of a given valuation in an Su ring}
 L:=Denominator(v); nu:=S`nu;
 for y in [0..L-1] do if not IsIntegral(y*nu-v) then continue; end if;
  z:=Integers()!(v-y*nu); u:=S.1^y*UniformizingElement(CoefficientRing(S`R))^z;
  assert GaussValuation(u) eq v; return u; end for; assert 0; end intrinsic;

intrinsic CanonicalElement(S::SuRng,v::RngIntElt) -> SuElement {"}//"
 return CanonicalElement(S,Rationals()!v); end intrinsic;

intrinsic GaussValuation(f::SuElement) -> FldRatElt
{Return the Gauss valuation of the element f in its parent S^nu_u.
 Returns Precision(Parent(f))+1 for 0}
 v,d:=valuation_and_degree(f`f,f`S`nu);
 if d ne -Infinity() then return v; end if;
 return Precision(Parent(f))+1; end intrinsic;

intrinsic WeierstrassDegree(f::SuElement) -> FldRatElt
{Return the Weierstrass degree of the element f in S^nu_u}
 v,d:=valuation_and_degree(f`f,f`S`nu); return d; end intrinsic;

intrinsic Quotrem(A::SuElement,B::SuElement) -> SuElement,SuElement
{Given A and nonzero B returns Q,R such that A = B*Q + R. Since Su is
 a valuation ring, when v(A)<v(B) we take Q=0,R=A and else Q=A/B,R=0.}
 require A`S eq B`S: "A and B must have same parent ring";
 require not IsWeaklyZero(B): "Cannot take quotient by zero element";
 vA:=GaussValuation(A); vB:=GaussValuation(B);
 if vB gt vA then return Parent(A)!0,A; end if;
 return A/B,Parent(A)!0; end intrinsic;

intrinsic ExtendedGcd(a::SuElement,b::SuElement)
 -> SuElement,SuElement,SuElement,SuElement,SuElement,SuElement
{Given A and B with this returns G,H,w,x,y,z with Aw+Bx=G where
 v(G)=min(v(B),v(A)) and Ay+Bz=H=0 and wz-xy=1. Since Su is a DVR,
 we can just take G to be CanonicalElement of appropriate valuation.}
 require a`S eq b`S: "a and b must have same parent ring"; S:=a`S;
 v:=GaussValuation(a); w:=GaussValuation(b);
 if v lt w then g:=CanonicalElement(S,v); A:=g/a; B:=S!0; D:=a/g; C:=(-D*b)/a;
 else g:=CanonicalElement(S,w); A:=S!0; B:=g/b; C:=-b/g; D:=(-C*a)/b; end if;
 assert A*D-B*C eq 1; assert A*a+B*b eq g; assert C*a+D*b eq 0;
 return g,_,A,B,C,D; end intrinsic;


