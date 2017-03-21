freeze;

import "utils.m": QFFromMatrix;

intrinsic QuarticIInvariant(A::RngUPolElt) -> RngIntElt
{ The I invariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if;
 return 12*t[1]*t[5]-3*t[2]*t[4]+t[3]^2; end intrinsic;

intrinsic QuarticJInvariant(A::RngUPolElt) -> RngIntElt
{ The J invariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if;
 return 72*t[1]*t[3]*t[5]+9*t[2]*t[3]*t[4]-2*t[3]^3
        -27*(t[1]*t[4]^2+t[5]*t[2]^2); end intrinsic;

intrinsic QuarticHSeminvariant(A::RngUPolElt) -> RngIntElt
{ The H seminvariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if;
 return 8*t[5]*t[3]-3*t[4]^2; end intrinsic;

intrinsic QuarticPSeminvariant(A::RngUPolElt) -> RngIntElt
{ The P invariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if;
 return 3*t[4]^2-8*t[5]*t[3]; end intrinsic;

intrinsic QuarticQSeminvariant(A::RngUPolElt) -> RngIntElt
{ The Q seminvariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if; e,d,c,b,a:=Explode(t);
 return 3*b^4-16*a*b^2*c+16*a^2*c^2+16*a^2*b*d-64*a^3*e; end intrinsic;

intrinsic QuarticRSeminvariant(A :: RngUPolElt) -> RngIntElt
{ The R seminvariant of the quartic A }
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if;
 return t[4]^3+8*t[5]^2*t[2]-4*t[5]*t[4]*t[3]; end intrinsic;

intrinsic QuarticNumberOfRealRoots(A::RngUPolElt) -> RngIntElt
{ Returns the number of real roots of a real quartic polynomial.
The polynomial must have non-zero discriminant }
 require Degree(A) eq 4: "Polynomial must have degree 4";
 require Type(BaseRing(A)) in {FldRat,RngInt,FldRe} :
  "Polynomial must be coercible into reals";
 d:=Discriminant(A); require d ne 0: "Quartic must have non-zero discriminant";
 if (d lt 0) then return 2; end if;
 if (d gt 0) then
  if (QuarticHSeminvariant(A) lt 0 and QuarticQSeminvariant(A) gt 0) then
  return 4; end if; return 0; end if; end intrinsic;

intrinsic QuarticG4Covariant(A::RngUPolElt) -> RngUPolElt
{ The G4 covariant of a quartic}
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if; e,d,c,b,a:=Explode(t);
 x:=Parent(A).1;
 return (3*b^2-8*a*c)*x^4+4*(b*c-6*a*d)*x^3+
  2*(2*c^2-24*a*e-3*b*d)*x^2+4*(c*d-6*b*e)*x+(3*d^2-8*c*e); end intrinsic;

intrinsic QuarticG6Covariant(A::RngUPolElt) -> RngUPolElt
{ The G6 covariant of a quartic}
 require Degree(A) eq 3 or Degree(A) eq 4: "Polynomial must have degree 3-4";
 t:=Coefficients(A); if #t eq 4 then t[5]:=0; end if; e,d,c,b,a:=Explode(t);
 x:=Parent(A).1;
 return
 (b^3 + 8*a^2*d - 4*a*b*c)*x^6 +
  2*(16*a^2*e + 2*a*b*d - 4*a*c^2 + b^2*c)*x^5 +
  5*(8*a*b*e + b*b*d - 4*a*c*d)*x^4 +
  20*(b^2*e-a*d^2)*x^3 - 5*(8*a*d*e + b*d^2 - 4*b*c*e)*x^2 -
  2*(16*a*e^2+2*b*d*e-4*c^2*e+c*d^2)*x - (d^3+8*b*e^2-4*c*d*e); end intrinsic;

function QuarticVariants(C) c:=Coefficient; d:=DefiningPolynomial(C);
 br:=BaseRing(Parent(d)); P := PolynomialRing(br); t := P.1;
 qq:=&+[-t^i * br!c(c(c(d,1,i),2,0),3,4-i) : i in [0..4]];
 return QuarticIInvariant(qq),QuarticJInvariant(qq),
        QuarticG4Covariant(qq),QuarticG6Covariant(qq); end function;

intrinsic AssociatedEllipticCurve(C::CrvHyp : E:=0 ) -> CrvEll, MapSch
{ given a hyperelliptic curve, return the map to the associated EC}

 // Call Tom's code when necessary (TO DO: in all cases?)
 if E cmpne 0 then 
   modelC, _, modelCtoE:=nCovering(GenusOneModel(C) : E:=E);
 elif ISA(Type(BaseRing(C)), FldAlg) then
   modelC, E, modelCtoE:=nCovering(GenusOneModel(C) : E:=E);
 end if;
 if assigned modelC then
   xC,yC,zC:=Explode([Ambient(C).i : i in [1,2,3]]);
   CtoE:=map<C->E| [Evaluate(eqn,[xC,zC,yC]) : 
		    eqn in DefiningEquations(modelCtoE)] : Check:=false>;
   return E, CtoE; 
 end if;

 require Genus(C) eq 1: "Hyperelliptic curve must be genus 1";
 f,h:=HyperellipticPolynomials(C); require h eq 0: "Must be in form y^2=f(x)";
 if Degree(f) eq 3 then
  if ConstantCoefficient(f) eq 0 then C2,m2:=Transformation(C,[1,1,0,1]);
   else C2,m2:=Transformation(C,[0,1,1,0]); end if;
  A,m:=AssociatedEllipticCurve(C2); return A,m2*m; end if;
 I,J,g4,g6:=QuarticVariants(C); E0:=EllipticCurve([0,0,0,-27*I,-27*J]);
 Emin,minimise:=MinimalModel(E0); ECspace:=Ambient(E0); LHSspace:=Ambient(C);
 g4:=&+[Coefficient(g4,i)*LHSspace.1^i*LHSspace.3^(4-i) : i in [0..4]];
 g6:=&+[Coefficient(g6,i)*LHSspace.1^i*LHSspace.3^(6-i) : i in [0..6]];
 y:=LHSspace.2; map1:=map<C->E0|[3*g4/(4*y^2),27*g6/(8*y^3),1] : Check:=false>;
 map1:=map1*minimise; return Emin,map1; end intrinsic;

intrinsic AssociatedEllipticCurve(A::RngUPolElt : E:=0 ) -> CrvEll, MapSch
{ Given a quartic, return the associated elliptic curve and a map}
 require Degree(A) eq 4 : "Polynomial must be quartic";
 return AssociatedEllipticCurve(HyperellipticCurve(A) : E:=E ); end intrinsic;

intrinsic AssociatedEllipticCurve(C::Crv : E:=0 ) -> CrvEll, MapSch
{ Given an intersection of quadrics, return the associated elliptic curve }
 bool, C_hyp := IsHyperellipticCurve(C);
 if bool then return AssociatedEllipticCurve(C_hyp : E:=E ); end if;
 require IsQuadricIntersection(C) : 
   "\nThe given curve must be either a 2-covering of some elliptic curve, " cat 
   "given as a hyperelliptic curve y^2 = quartic(x), or else a 4-covering " cat
   "given as an intersection of two quadrics";
 H,m1:=AssociatedHyperellipticCurve(C);
 E,m2:=AssociatedEllipticCurve(H : E:=E ); return E,m1*m2; end intrinsic;

function AQDirect(A) P:=PolynomialRing(BaseRing(A[1])); R:=MatrixAlgebra(P,4);
 DD:=Determinant(R!A[1]*P.1+R!A[2]); return DD; end function;

function FourDCov_internal(C,M)
 M1,M2:=Explode(M); BR:=BaseRing(M1); P := PolynomialRing(BR); x := P.1;
 Q<t1,t2,t3,t4>:=PolynomialRing(BR,4); v:=[t1,t2,t3,t4];
 M1i:=Adjoint(M1); M2i:=Adjoint(M2);
 f1:=QFFromMatrix(v,M1); f2:=QFFromMatrix(v,M2);
 M3:=M1*M2i*M1; M4:=M2*M1i*M2; f3:=QFFromMatrix(v,M3); f4:=QFFromMatrix(v,M4);
 G:=Determinant(JacobianMatrix([f1,f2,f3,f4])) div 16; f4i:=1/f4;
 H:=HyperellipticCurve(AQDirect(M));
 m:=map<C->H | [-f3*f4i,G*f4i^2,1] : Check:=false>; return H,m; end function;

intrinsic AssociatedHyperellipticCurve(C::Crv : C2:=0 ) -> CrvHyp,MapSch
{ The associated hyperelliptic curve for a quadric intersection,
 and the covering map between them.}
 if C2 cmpne 0 then _,_,CtoC2:=FourToTwoCovering(C : C2:=C2);
  return C2,CtoC2; end if;
 b,A:=IsQuadricIntersection(C); require b: "Not an intersection of quadrics";
 require not IsSingular(C) : "Curve must be non-singular";
 return FourDCov_internal(C,A); end intrinsic;

intrinsic QuadricIntersection(S::Prj,F::[AlgMatElt]) -> Crv
{Write two symmetric 4x4 matrices as a quadric intersection}
 require Dimension(S) eq 3: "Dimension of projective space must be 3";
 require Type(F[1]) eq AlgMatElt and NumberOfRows(F[1]) eq 4
         and IsSymmetric(F[1]): "First argument is not a symmetric 4x4 matrix";
 require Type(F[2]) eq AlgMatElt and NumberOfRows(F[2]) eq 4
        and IsSymmetric(F[2]): "Second argument is not a symmetric 4x4 matrix";
 return Curve(S,[QFFromMatrix([S.1,S.2,S.3,S.4],t) : t in F]); end intrinsic;

intrinsic QuadricIntersection(F::[AlgMatElt]) -> Crv
{Write two symmetric 4x4 matrices as a quadric intersection}
 S:=ProjectiveSpace(FieldOfFractions(BaseRing(F[1])),3);
 return Curve(S,[QFFromMatrix([S.1,S.2,S.3,S.4],t) : t in F]); end intrinsic;

function Elift(f,xv,yv) // U:=FieldOfFractions(Parent(xv));
 U:=Rationals(); P := PolynomialRing(U); x := P.1;
 E,m:=AssociatedEllipticCurve(f); DE:=DefiningEquations(m);
 t:=Evaluate(DE[1]/DE[3],3,1); LHS:=Numerator(t);
 L:=&+[U!Coefficient(Coefficient(LHS,1,i),2,0)*x^i : i in [0..4]]
     +U!Coefficient(LHS,2,2)*P!f;
 C:=PolynomialRing(U); R:=Roots(C!L-xv*C!f);
 q:=PolynomialRing(U,3)!DE[1]; ans:=[]; q2:=PolynomialRing(U,3)!DE[2];
 for r in R do x:=r[1]; b,y:=IsSquare(Evaluate(ChangeRing(f,U),x));
  if b then yp:=U!Evaluate(Evaluate(Evaluate(q2,1,x),2,y),3,1)/y^3;
  ym:=U!-Evaluate(Evaluate(Evaluate(q2,1,x),2,-y),3,1)/y^3;
  if Abs(yv-yp) gt Abs(yv-ym) then y:=-y; end if;
  ans:=ans cat [[x,y,1]]; end if; end for; return ans; end function;

function UN(f,i) F:=BaseRing(Parent(f)); G := PolynomialRing(F); x := G.1;
 if Degree(f,i) eq -1 then return G!0; end if;
 return &+[F!Coefficient(f,i,d)*x^d : d in [0..Degree(f,i)]]; end function;

function roots(f)
 if f eq 0 then return []; end if; return Roots(f); end function;

function Dlift1(M1,M2,xv,yv) U:=FieldOfFractions(Parent(xv));
 A:=MatrixAlgebra(U,4); P4<a,b,c,d>:=PolynomialRing(U,4); v:=[a,b,c,d];
 M1:=A!M1; M2:=A!M2; M3:=M1*M2^(-1)*M1; M4:=M2*M1^(-1)*M2;
 q1:=Evaluate(QFFromMatrix(v,M1),1,1); q2:=Evaluate(QFFromMatrix(v,M2),1,1);
 q3:=QFFromMatrix(v,M3)*Determinant(M2)/Determinant(M1)+xv*QFFromMatrix(v,M4);
 q3:=Evaluate(q3,1,1); R1:=Resultant(q1,q2,2); R2:=Resultant(q1,q3,2);
 res:=Resultant(R1,R2,3); ans:=[];
 for R in roots(UN(res,4)) do r:=R[1]; p3:=Evaluate(R2,4,r);
  for S in roots(UN(p3,3)) do s:=S[1]; p2:=Evaluate(Evaluate(q1,4,r),3,s);
   for T in roots(UN(p2,2)) do t:=T[1];
    e1:=U!Evaluate(Evaluate(Evaluate(q1,4,r),3,s),2,t);
    e2:=U!Evaluate(Evaluate(Evaluate(q2,4,r),3,s),2,t);
    e3:=U!Evaluate(Evaluate(Evaluate(q3,4,r),3,s),2,t);
    if e1 eq 0 and e2 eq 0 and e3 eq 0 then ans cat:=[[1,t,s,r]]; end if;
    end for; end for; end for; return ans; end function;

function Dlift0(QI,xv,yv) _,M:=IsQuadricIntersection(QI);
 M1,M2:=Explode(M); return Dlift1(M2,M1,xv,yv); end function;
function Dlift(QI,xv,yv) _,M:=IsQuadricIntersection(QI);
 M1,M2:=Explode(M); return Dlift1(M1,M2,xv,yv); end function;

intrinsic
 TwoCoverPullback(H::CrvHyp[FldRat],pt::PtEll[FldRat]) -> SeqEnum[PtHyp]
{Given a two-covering and a point on the corresponding elliptic curve,
 find the pre-images of the point on the two-covering (faster than @@)}
 H2,mH:=SimplifiedModel(H); E2,m:=AssociatedEllipticCurve(H2); E:=Curve(pt);
 b,t:=IsIsomorphic(E,E2); require b: "Curve must cover Parent of the point";
 f:=HyperellipticPolynomials(H2); PT:=t(pt);
 hpts:=Elift(f,PT[1]/PT[3],PT[2]/PT[3]);
 b,r:=IsSquare(LeadingCoefficient(f)); if b then
  if m(H2![1,r,0]) eq PT then hpts cat:=[[1,r,0]]; end if;
  if m(H2![1,-r,0]) eq PT then hpts cat:=[[1,-r,0]]; end if; end if;
 b,r:=IsSquare(Coefficient(f,0)); if b then
  if m(H2![0,r,1]) eq PT then hpts cat:=[[0,r,1]]; end if;
  if m(H2![0,-r,1]) eq PT then hpts cat:=[[0,-r,1]]; end if; end if;
 return [Inverse(mH)(H2!Eltseq(p)) : p in hpts]; end intrinsic;

intrinsic
 TwoCoverPullback(f::RngUPolElt[FldRat],pt::PtEll[FldRat]) -> SeqEnum[PtHyp]
{Given a two-covering quartic and a point on the corresponding elliptic curve,
 find the pre-images of the point on the two-covering (faster than @@)}
 return TwoCoverPullback(HyperellipticCurve(f),pt); end intrinsic;

intrinsic FourCoverPullback(C::Crv[FldRat],pt::PtEll[FldRat]) -> SeqEnum[Pt]
{Given a four-covering and a point on the corresponding elliptic curve,
 find the pre-images of the point on the four-covering (faster than @@)}
 require IsQuadricIntersection(C): "Must be a quadric intersection";
 T:=AssociatedHyperellipticCurve(C); Tpts:=TwoCoverPullback(T,pt);
 Tpts1:=[x : x in Tpts | x[3] ne 0]; Tpts0:=[x : x in Tpts | x[3] eq 0];
 return
  &cat[[C!Eltseq(x) : x in Dlift(C,t[1]/t[3],t[2]/t[3]^2) ] : t in Tpts1] cat
  &cat[[C!Eltseq(x) : x in Dlift0(C,t[3]/t[1],t[2]/t[1]^2) ] : t in Tpts0];
 end intrinsic;

intrinsic FourCoverPullback(C::Crv[FldRat],pt::PtHyp[FldRat]) -> SeqEnum[Pt]
{Given a four-covering and a point on the corresponding two-covering,
 find the pre-images of the point on the four-covering (faster than @@)}
 require IsQuadricIntersection(C): "Must be a quadric intersection";
 T:=AssociatedHyperellipticCurve(C); b,t:=IsIsomorphic(Curve(pt),T);
 require b: "Curve must cover Parent of the point"; u:=t(pt);
 if u[3] eq 0 then return [C!Eltseq(x) : x in Dlift0(C,u[3]/u[1],u[2]/u[1]^2)];
 else return [C!Eltseq(x) : x in Dlift(C,u[1]/u[3],u[2]/u[3]^2)]; end if;
 end intrinsic;
