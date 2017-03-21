freeze;

import "../Clstr/ratpoints.m" : BaseRingIsQorZ;

function jacobian_plane_cubic(v) // From GP code of FRV
 q0,r0,q1,s0,r1,q2,t0,s1,r2,q3:=Explode(v);
 a1:=r1; a2:=-(s0*q2+s1*q1+r0*r2);
 a3:=(9*t0*q0-s0*r0)*q3+((-t0*q1-s1*r0)*q2+(-s0*r2*q1-s1*r2*q0));
 a4:=((-3*t0*r0+s0^2)*q1+(-3*s1*s0*q0+s1*r0^2))*q3
      +(t0*r0*q2^2+(s1*s0*q1+((-3*t0*r2+s1^2)*q0+s0*r0*r2))*q2
	+(t0*r2*q1^2+s1*r0*r2*q1+s0*r2^2*q0));
 a6:=(-27*t0^2*q0^2+(9*t0*s0*r0-s0^3)*q0-t0*r0^3)*q3^2+
     (((9*t0^2*q0-t0*s0*r0)*q1+((-3*t0*s0*r1+(3*t0*s1*r0 +2*s1*s0^2))*q0
				+(t0*r0^2*r1-s1*s0*r0^2)))*q2
      +(-t0^2*q1^3+(t0*s0*r1+(2*t0*s1*r0-s1*s0^2))*q1^2
	+((3*t0*s0*r2+(-3*t0*s1*r1+2*s1^2*s0))*q0+
	  ((2*t0*r0^2-s0^2*r0)*r2+(-t0*r0*r1^2+s1*s0*r0*r1-s1^2*r0^2)))*q1
	+((9*t0*s1*r2-s1^3)*q0^2+(((-3*t0*r0+s0^2)*r1-s1*s0*r0)*r2
				  + (t0*r1^3-s1*s0*r1^2+s1^2*r0*r1))*q0)))*q3
 +(-t0^2*q0*q2^3+(-t0*s1*r0*q1+
		  ((2*t0*s0*r2+(t0*s1*r1-s1^2*s0))*q0-t0*r0^2*r2))*q2^2
   +(-t0*s0*r2*q1^2+(-t0*s1*r2*q0+(t0*r0*r1-s1*s0*r0)*r2)*q1
     +((2*t0*r0-s0^2)*r2^2 +(-t0*r1^2 + s1*s0*r1 - s1^2*r0)*r2)*q0)*q2
   +(-t0*r0*r2^2*q1^2 + (t0*r1 - s1*s0)*r2^2*q0*q1 -t0*r2^3*q0^2));
 return EllipticCurve([a1,a2,a3,a4,a6]); end function;

intrinsic IsCubicModel(X::Sch) -> BoolElt
{Returns whether a scheme is a projective ternary plane cubic}
 if not IsProjective(X) then return false; end if;
 if Dimension(Ambient(X)) ne 2 then return false; end if;
 D:=DefiningEquations(X); if #D ne 1 then return false; end if;
 if TotalDegree(D[1]) ne 3 then return false; end if;
 return true; end intrinsic;

intrinsic PointsCubicModel
(C::Crv,H::RngIntElt : ExactBound:=false,OnlyOne:=false) -> SeqEnum
{Compute the points on a ternary cubic up to a bound}
 require IsCubicModel(C) : "Curve must be a cubic model";
 require IsEmpty(SingularPoints(C)) : "Cubic Model is singular";
 require IsIrreducible(C) : "Cubic Model is reducible";
 require BaseRingIsQorZ(C) : "Base ring must be Q or Z";
 require H ge 1: "Bound must be at least 1";
 f:=DefiningEquation(C); ZZ:=Integers();
 R<X,Y,Z>:=PolynomialRing(Integers(),3);
 d:=LCM([Denominator(Rationals()!x) : x in Coefficients(f)]);
 f:=R!(d*f); p:=Floor(H/2); if p lt 10 then p:=10; end if; p:=NextPrime(p);
 X3:=ZZ!Coefficient(f,X,3);
 X2Y:=ZZ!Coefficient(Coefficient(f,X,2),Y,1);
 X2Z:=ZZ!Coefficient(Coefficient(f,X,2),Z,1);
 XY2:=ZZ!Coefficient(Coefficient(f,X,1),Y,2);
 XYZ:=ZZ!Coefficient(Coefficient(Coefficient(f,X,1),Y,1),Z,1);
 XZ2:=ZZ!Coefficient(Coefficient(f,X,1),Z,2);
 Y3:=ZZ!Coefficient(f,Y,3);
 Y2Z:=ZZ!Coefficient(Coefficient(f,Y,2),Z,1);
 YZ2:=ZZ!Coefficient(Coefficient(f,Y,1),Z,2);
 Z3:=ZZ!Coefficient(f,Z,3);
 v:=[X3,X2Y,X2Z,XY2,XYZ,XZ2,Y3,Y2Z,YZ2,Z3];
 D:=Discriminant(jacobian_plane_cubic(v));
 while p mod 4 eq 1 or Valuation(D,p) ne 0 do p:=NextPrime(p); end while;
 PTS:=InternalCMSearch(v,H,p : OnlyOne:=OnlyOne,ExactBound:=ExactBound);
 P:=[C!x : x in PTS]; if OnlyOne and #P gt 1 then P:=[P[1]]; end if;
 return P; end intrinsic;



