freeze;

import "../../Clstr/ratpoints.m" : BaseRingIsQorZ;

/* Rewritten by Mark Watkins, Aug 2004, Feb 2005 */

iQISearch:=InternalQISearch;

function Pencilise(A)
 while Determinant(A[1]) eq 0 do A[1]:=A[1]+A[2]; end while;
 while Determinant(A[2]) eq 0 do A[2]:=A[1]+A[2]; end while; return A;
end function;

function GetLocalSolutionQI(M,N,p,H,EB : xvalue:=1)
 x:=xvalue; OK:=false; S:=[];
 _<T,U>:=PolynomialRing(GF(p),2); VV := PolynomialRing(GF(p)); V := VV.1; Z:=Integers();
 while (not OK) do
  c:=M[1][1]+2*M[1][2]*x+M[2][2]*x^2;
  y:=2*M[1][3]+2*M[2][3]*x; z:=2*M[1][4]+2*M[2][4]*x;
  p1:=c+y*T+z*U+2*M[3][4]*T*U+M[3][3]*T^2+M[4][4]*U^2;
  c:=N[1][1]+2*N[1][2]*x+N[2][2]*x^2;
  y:=2*N[1][3]+2*N[2][3]*x; z:=2*N[1][4]+2*N[2][4]*x;
  p2:=c+y*T+z*U+2*N[3][4]*T*U+N[3][3]*T^2+N[4][4]*U^2;
  R:=Resultant(p1,p2,T); d:=Degree(R,U); rp:=0;
  for i in [0..d] do rp:=rp+V^i*Integers()!Coefficient(R,U,i); end for;
  if rp ne 0 then roo:=Roots(VV!rp); else roo:=[]; end if;
  if not IsEmpty(roo) then OK:=true; else x:=x+1; end if; end while;
 OK:=false;
 for L in roo do
  z:=Z!L[1];
  p3:=M[3][3]*V^2+V*(2*M[1][3]+2*M[2][3]*x+2*M[3][4]*z)+
      M[1][1]+2*M[1][2]*x+2*M[1][4]*z+2*M[2][4]*x*z+M[2][2]*x^2+M[4][4]*z^2;
  if p3 ne 0 then roo2:=Roots(VV!p3); else roo2:=[]; end if;
  for L2 in roo2 do
   r:=Z!L2[1];
   t:=N[3][3]*r^2+r*(2*N[1][3]+2*N[2][3]*x+2*N[3][4]*z)+
      N[1][1]+2*N[1][2]*x+2*N[1][4]*z+2*N[2][4]*x*z+N[2][2]*x^2+N[4][4]*z^2;
   if (t mod p) eq 0 then
    if (not OK) then OK:=true; ys:=r; zs:=z;
    else S:=S cat iQISearch(M,N,[1,x,r,z],p,H : Direct:=true,ExactBound:=EB);
    end if; end if;  end for; end for;
 if not OK then return GetLocalSolutionQI(N,M,p,H,EB : xvalue:=x+1); end if;
 vprintf QISearch,1:
 "Local Solution: %o %o %o %o\n",1,x,ys,zs; return [1,x,ys,zs],S; end function;

function Find01yzSolutions(M,N,bound,p,EB)
 A:=Matrix
 ([[M[2][2],M[1][2],M[2][3],M[2][4]],[M[2][1],M[1][1],M[1][3],M[1][4]],
   [M[3][2],M[3][1],M[3][3],M[3][4]],[M[4][2],M[4][1],M[4][3],M[4][4]]]);
 B:=Matrix
 ([[N[2][2],N[1][2],N[2][3],N[2][4]],[N[2][1],N[1][1],N[1][3],N[1][4]],
   [N[3][2],N[3][1],N[3][3],N[3][4]],[N[4][2],N[4][1],N[4][3],N[4][4]]]);
 _<Y,Z>:=PolynomialRing(GF(p),2);
 p1:=A[1][1]+2*A[1][3]*Y+2*A[1][4]*Z+A[3][3]*Y^2+2*A[3][4]*Y*Z+A[4][4]*Z^2;
 p2:=B[1][1]+2*B[1][3]*Y+2*B[1][4]*Z+B[3][3]*Y^2+2*B[3][4]*Y*Z+B[4][4]*Z^2;
 VV := PolynomialRing(GF(p)); V := VV.1; AR:=[];
 RZ:=Resultant(p1,p2,Y); d:=Degree(RZ,Z); P:=0;
 for i in [0..d] do P:=P+V^i*Integers()!Coefficient(RZ,Z,i); end for;
 if d gt 0 then rz:=Roots(VV!P); else rz:=[]; end if;
 RY:=Resultant(p1,p2,Z); d:=Degree(RY,Y); P:=0;
 for i in [0..d] do P:=P+V^i*Integers()!Coefficient(RY,Y,i); end for;
 if d gt 0 then ry:=Roots(VV!P); else ry:=[]; end if;
 for r in ry do y:=Integers()!r[1]; for s in rz do z:=Integers()!s[1];
  T:=A[3][3]*y^2+y*(2*A[1][3]+2*A[3][4]*z)+A[1][1]+2*A[1][4]*z+A[4][4]*z^2;
  U:=B[3][3]*y^2+y*(2*B[1][3]+2*B[3][4]*z)+B[1][1]+2*B[1][4]*z+B[4][4]*z^2;
  if (T mod p) eq 0 and (U mod p) eq 0 then
   AR:=AR cat iQISearch(A,B,[1,0,y,z],p,bound: Direct:=true,ExactBound:=EB);
  end if; end for; end for;
 for i in [1..#AR] do
  temp:=AR[i][1]; AR[i][1]:=AR[i][2]; AR[i][2]:=temp; end for;
 return AR; end function;

function Find001zSolutions(M,N,bound,p,EB)
 A:=Matrix
 ([[M[3][3],M[3][2],M[1][3],M[3][4]],[M[2][3],M[2][2],M[2][1],M[2][4]],
   [M[3][1],M[1][2],M[1][1],M[1][4]],[M[4][3],M[4][2],M[4][1],M[4][4]]]);
 B:=Matrix
 ([[N[3][3],N[3][2],N[1][3],N[3][4]],[N[2][3],N[2][2],N[2][1],N[2][4]],
   [N[3][1],N[1][2],N[1][1],N[1][4]],[N[4][3],N[4][2],N[4][1],N[4][4]]]);
 VV := PolynomialRing(GF(p)); V := VV.1; AR:=[]; poly:=A[4][4]*V^2+2*A[4][1]*V+A[1][1];
 if Degree(poly) gt 0 then roo:=Roots(VV!poly); else roo:=[]; end if;
 for r in roo do
  z:=Integers()!r[1]; T:=B[4][4]*z^2+2*B[4][1]*z+B[1][1];
  if (T mod p) eq 0 then
   AR:=AR cat iQISearch(A,B,[1,0,0,z],p,bound: Direct:=true,ExactBound:=EB);
  end if; end for;
 for i in [1..#AR] do
  temp:=AR[i][1]; AR[i][1]:=AR[i][3]; AR[i][3]:=temp; end for;
 return AR; end function;

function Find0001Solutions(M,N,bound,p,EB)
 A:=Matrix
 ([[M[4][4],M[4][2],M[4][3],M[4][1]],[M[2][4],M[2][2],M[2][3],M[2][1]],
   [M[3][4],M[3][2],M[3][3],M[3][1]],[M[1][4],M[1][2],M[1][3],M[1][1]]]);
 B:=Matrix
 ([[N[4][4],N[4][2],N[4][3],N[4][1]],[N[2][4],N[2][2],N[2][3],N[2][1]],
   [N[3][4],N[3][2],N[3][3],N[3][1]],[N[1][4],N[1][2],N[1][3],N[1][1]]]);
 if ((A[1][1] mod p) eq 0) and ((B[1][1] mod p) eq 0) then
  AR:=iQISearch(A,B,[1,0,0,0],p,bound:Direct:=true,ExactBound:=EB);
  for i in [1..#AR] do
  temp:=AR[i][1]; AR[i][1]:=AR[i][4]; AR[i][4]:=temp; end for;
 else AR:=[]; end if; return AR; end function;

intrinsic PointsQI
(X::Crv,B::RngIntElt : OnlyOne:=false, ExactBound:=false) -> SeqEnum
{Find points on a quadric intersection using the Elkies ANTS-IV method}
 require BaseRingIsQorZ(X) : "Base Ring must be Q or Z";
 require B ge 1: "Bound must be at least 1";
 b,F:=IsQuadricIntersection(X); require b: "Not an intersection of quadrics";
 require not IsSingular(X) : "Quadric intersection must be non-singular";
 x := PolynomialRing(Integers()).1;
 l:=LCM([Denominator(u) : u in Eltseq(F[1]) cat Eltseq(F[2])]);
 F:=[MatrixAlgebra(Integers(),4)!(u*l) : u in F]; F:=Pencilise(F);
 F_rat:=[MatrixAlgebra(Rationals(),4)!(u*l) : u in F];
 disc:=Discriminant(Determinant(F[1]+F[2]*x)); // this does not always catch
                                               // all primes where the QI has 
                                               // singular reduction   -- Steve
 disc_steve:=Numerator(Discriminant(GenusOneModel(F_rat)));
 p:=NextPrime(Floor(B^(2/3))); if p le 10 then p:=11; end if;
 while ((p mod 4 ne 3) or (disc mod p eq 0) or (disc_steve mod p eq 0)) do 
   p:=NextPrime(p); end while;
 vprintf QISearch,1: "Prime to be used: %o\n",p;
 l,S:=GetLocalSolutionQI(F[1],F[2],p,B,ExactBound);
 if #S eq 0 or not OnlyOne then
  S cat:=iQISearch(F[1],F[2],l,p,B : OnlyOne:=OnlyOne,ExactBound:=ExactBound);
 end if;
 S cat:=Find01yzSolutions(F[1],F[2],B,p,ExactBound);
 S cat:=Find001zSolutions(F[1],F[2],B,p,ExactBound);
 S cat:=Find0001Solutions(F[1],F[2],B,p,ExactBound);
 if OnlyOne and #S gt 1 then S:=[S[1]]; end if;
 S:=[X!p : p in S]; return S; end intrinsic;

