freeze;
 
declare verbose QuarticReduce,2;

import "utils.m" : PolynomialApplyDegree;

function roots_deflated_cubic(a,b,p) F:=ComplexField(p+10);
 if a eq 0 then u:=(F!-b)^(1/3); r:=(-1+Sqrt(F!-3))/2;
  return [u,r*u,r^2*u]; end if;
 C:=-108*b+12*Sqrt(F!12*a^3+81*b^2); C:=C^(1/3);
 C6:=C/6; aC2:=2*a/C; r1:=C/6-aC2; im:=C6+aC2; s3:=Sqrt(F!-3/4);
 B:=im*s3; r12:=-r1/2; return [r1,r12+B,r12-B]; end function;

function roots_cubic(f,p)
 d,c,b,a:=Explode(Coefficients(f)); s:=1/a; b*:=s; c*:=s; d*:=s;
 b3:=b/3; B:=b3*b; R:=roots_deflated_cubic(c-B,d-b3*c+2*B*b3/3,p);
 return [ComplexField(p)!r-b3 : r in R]; end function;

function roots_quartic(f,p : IisZero:=false, RisZero:=false)
 I:=QuarticIInvariant(f); J:=QuarticJInvariant(f);
 if IisZero then I:=0; end if;
 ROO:=roots_deflated_cubic(-3*I,J,p);
 a:=LeadingCoefficient(f); H:=QuarticHSeminvariant(f);
 Z:=[Sqrt((4*a*r-H)/3) : r in ROO]; inv:=1/(4*a); b:=Coefficient(f,3);
 if RisZero then Sort(~Z,func<x,y|Norm(y)-Norm(x)>); Prune(~Z);
  return [(+Z[1]+Z[2]-b)*inv,(+Z[1]-Z[2]-b)*inv,
	  (-Z[1]-Z[2]-b)*inv,(-Z[1]+Z[2]-b)*inv]; end if;
 R:=QuarticRSeminvariant(f);
 if Abs(Arg(&*Z/R)) lt 0.1 then Z[3]:=-Z[3]; end if;
 return [(+Z[1]+Z[2]+Z[3]-b)*inv,(+Z[1]-Z[2]-Z[3]-b)*inv,
	 (-Z[1]+Z[2]-Z[3]-b)*inv,(-Z[1]-Z[2]+Z[3]-b)*inv]; end function;

intrinsic FastRoots(f::RngUPolElt : IisZero:=false, RisZero:=false) -> SeqEnum
{Compute roots over C using Cardano/Ferrari for degrees up through 4}
 require Degree(f) le 4: "Degree must be less than 4"; T:=Type(BaseRing(f));
 require T eq FldCom or T eq FldRe: "Field must be real or complex";
 f:=ChangeRing(f,ComplexField(Precision(BaseRing(f))));
 if Degree(f) eq 0 then return []; end if;
 if Degree(f) eq 1 then return [-Coefficient(f,0)/Coefficient(f,1)]; end if;
 if Degree(f) eq 2 then c,b,a:=Explode(Coefficients(f)); s:=Sqrt(b^2-4*a*c);
  r:=1/(2*a); return [(-b+s)*r,(-b-s)*r]; end if;
 prec:=Precision(BaseRing(f));
 if Degree(f) eq 3 then
 if IisZero or QuarticIInvariant(f) eq 0 then
  return roots_deflated_cubic(0,ConstantCoefficient(f),prec); end if;
 return roots_cubic(f,prec); end if;
 return roots_quartic(f,prec :
		      IisZero:=IisZero or QuarticIInvariant(f) eq 0,
		      RisZero:=RisZero or QuarticRSeminvariant(f) eq 0);
 end intrinsic;

function QuarticType(q)
 a:=QuarticNumberOfRealRoots(q); if (a eq 0) then return 1; end if;
 if (a eq 4) then return 2; end if; if (a eq 2) then return 3; end if;
end function;

function QuarticResolvantCubic(q) P:=PolynomialRing(Integers());
 return P.1^3-3*QuarticIInvariant(q)*P.1+QuarticJInvariant(q); end function;

function QuarticTypes12Quadratic(q,phis,type)
 a:=LeadingCoefficient(q); phis:=Sort([Real(t): t in phis]);
 if type eq 1 then if a gt 0 then phi:=phis[1]; else phi:=phis[3]; end if;
 else phi:=phis[2]; end if; // Construct the H1 quadratic
 PR:=PolynomialRing(Parent(phis[1]));
 H1:=PR!Derivative(QuarticG4Covariant(q),2);
 H1+:=(4*PR!Derivative(q,2))*phi+8*(QuarticIInvariant(q)-phi^2);
 H1:=H1/36; return type eq 1 select -H1 else H1; end function;

function QuarticType3Quadratic(q,phis)
 a:=LeadingCoefficient(q); b:=Coefficient(q,3);
 Sort(~phis,func<x,y|Abs(Imaginary(x))-Abs(Imaginary(y))>);
 rp:=Real(phis[1]); cp:=phis[2];
 wr:=Sqrt(Parent(cp)!(4*a*rp-QuarticHSeminvariant(q))/3);
 wc:=Sqrt((4*a*cp-QuarticHSeminvariant(q))/3);
 if (not IsReal(wr)) then wr:=0; else wr:=Real(wr); end if;
 wr:=wr*Sign(wr)*Sign(QuarticRSeminvariant(q));
 t12:=Abs(Imaginary(wc))*Abs((wr+wc)^2);
 t22:=Abs(Imaginary(wc))*Abs((wr-wc)^2); u2:=Abs(Real(wc))*Abs(wc^2-wr^2);
 alpha1:=(-b-wr+2*Real(wc))/(4*a); alpha2:=(-b-wr-2*Real(wc))/(4*a);
 beta:=(-b+wr+2*Imaginary(wc)*Parent(cp).1)/(4*a);
 x:=PolynomialRing(Parent(cp)).1; xr:=PolynomialRing(Parent(rp)).1;
 rq:=t12*(x-alpha1)^2+t22*(x-alpha2)^2;
 rq+:=2*u2*(x-beta)*(x-ComplexConjugate(beta));
 return &+[Real(Coefficient(rq,n))*xr^n : n in [0..2]]; end function;

function QuarticQuadratic(q,phis,pr)
 phis:=[ComplexField(pr)!x : x in phis]; type:=QuarticType(q);
 if (type ne 3) then return QuarticTypes12Quadratic(q,phis,type);
 else return QuarticType3Quadratic(q,phis); end if; end function;

function CubicQuadratic(q,R,pr) /* q roots are 1/3 those of ResCubic */
 r1,r2,r3:=Explode([ComplexField(pr)!r/3 : r in R]);
 r12:=Abs(r1-r2); r13:=Abs(r1-r3); r23:=Abs(r2-r3);
 c2:=r12+r13+r23; c1:=-2*(Real(r1)*r23+Real(r2)*r13+Real(r3)*r12);
 c0:=Norm(r1)*r23+Norm(r2)*r13+Norm(r3)*r12+r12*r13*r23;
 return PolynomialRing(RealField(pr))!Reverse([c2,c1,c0]); end function;

function QuarticReduceInternal(q,R : extra_prec:=0 )
 d:=Degree(q)+1; qs:=[1+Ilog(10,1+Abs(x)) : x in Coefficients(q)];
 pr:=Ceiling(Max([2*Sqrt(qs[1])] cat [1+(1+qs[i]-qs[d])/(d-i):i in [1..d-1]]));
 pr:=Max(20,Ceiling(1.1*pr)+5)+(extra_prec div 2);
 vprintf QuarticReduce,1: "QuarticReduce prec %o\n",2*pr+4;
 if R eq [] or 2*pr+4 gt Precision(R[1]) then
  if Degree(q) eq 4 then R:=roots_cubic(QuarticResolvantCubic(q),2*pr+4);
  else R:=[3*r : r in roots_cubic(q,2*pr+4)]; end if; end if;
 if Degree(q) eq 4 then qq:=QuarticQuadratic(q,R,2*pr+4);
  else qq:=CubicQuadratic(q,R,2*pr+4); end if;
 if Degree(q) eq 3 then R:=[]; end if; // Bug fix from TAF, May 3 2011
 vprintf QuarticReduce,2: "Covariant is %o\n",qq;
 c,b,a:=Explode(Coefficients(qq)); M:=DiagonalMatrix([1,1]);
 pt:=(-b+Sqrt(ComplexField(2*pr+4)!(b^2-4*a*c)))/2/a;
 if Imaginary(pt) gt 1+10^(-pr) then
  if Abs(Real(pt)) lt 0.5+10^(-pr) then k:=0; else k:=Round(Real(pt)); end if;
  M*:=Matrix(2,2,[1,k,0,1]);
  if Abs(b^2-4*a*c)*2^pr lt Max(b^2,Abs(4*a*c)) then
   return false,PolynomialApplyDegree(4,M,q),M,R;
  else return true,PolynomialApplyDegree(4,M,q),M,R; end if; end if;
 if Norm(pt) gt 1/(1-10^(-pr))
  then pt:=-1/pt; M*:=Matrix(2,2,[0,-1,1,0]); end if;
 while true do
  if Norm(pt) eq 0 then return false,PolynomialApplyDegree(4,M,q),M,R; end if;
  if Norm(pt) lt 1-10^(-pr) then pt:=-1/pt; M*:=Matrix(2,2,[0,-1,1,0]);
  else
   if M ne -DiagonalMatrix([1,1]) and M ne DiagonalMatrix([1,1]) then
    return false,PolynomialApplyDegree(4,M,q),M,R; end if;
   return true,PolynomialApplyDegree(4,M,q),M,R; end if;
  if Abs(Real(pt)) lt 0.5+10^(-pr) then k:=0; else k:=Round(Real(pt)); end if;
  pt:=pt-k; M*:=Matrix(2,2,[1,k,0,1]);
  if Abs(Max(Eltseq(M))) gt 10^pr then
   return false,PolynomialApplyDegree(4,M,q),M,R; end if;
  end while; end function;

intrinsic QuarticReduce(q::RngUPolElt) -> RngUPolElt,AlgMatElt
{Reduce a quartic f over Z by reducing its covariant quadratic form.
 Returns g and M such that f*M=g; }
 require BaseRing(q) eq Integers(): "Must be over Z";
 require Degree(q) eq 3 or Degree(q) eq 4: "Degree must be 3 or 4";
 ok:=false; M:=One(MatrixAlgebra(Integers(),2)); R:=[]; q0:=q; SET:={};
 while not ok do ok,q,T,R:=QuarticReduceInternal(q,R); M:=M*T;
  if q in SET then break; else Include(~SET,q); end if; end while;
 if Degree(q0) ne 3 then assert q0^M eq q;
 elif Degree(q) ne 3 then assert q0 eq q^(M^(-1)); end if; // May 3 2011
 return q,M; end intrinsic;
