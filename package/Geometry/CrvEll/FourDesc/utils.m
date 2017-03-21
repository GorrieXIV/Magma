freeze;
 
function QFFromMatrix(Coords, M)
    return &+[Coords[i]*Coords[j]*M[i,j] : i in [1..4], j in [1..4]];
end function;

function MatrixFromQF(Q)// Construct a 4x4 symmetric matrix from Q
 m:=[[2,0,0,0],[1,1,0,0],[1,0,1,0],[1,0,0,1],[0,2,0,0],[0,1,1,0],
	      [0,1,0,1],[0,0,2,0],[0,0,1,1],[0,0,0,2]];
 T:=[MonomialCoefficient(Q, Monomial(Parent(Q),r)) : r in m];
 for i in [2,3,4,6,7,9] do T[i]/:=2; end for;
 Reordering:=[1,2,5,3,6,8,4,7,9,10]; S:=SymmetricMatrix(T[Reordering]);
 return S*LCM([Denominator(Rationals()!x) : x in Eltseq(S)]); end function;

function QFToMatrix(Q)
 Q:=PolynomialRing(FieldOfFractions(CoefficientRing(Parent(Q))),4)!Q;
 if CoefficientRing(Parent(Q)) cmpeq RationalField() then
  return MatrixFromQF(Q); end if;
 if Characteristic(CoefficientRing(Parent(Q))) eq 2 then return 0; end if;
 m:=[[2,0,0,0],[1,1,0,0],[1,0,1,0],[1,0,0,1],[0,2,0,0],[0,1,1,0],
	       [0,1,0,1],[0,0,2,0],[0,0,1,1],[0,0,0,2]];
 T:=[MonomialCoefficient(Q, Monomial(Parent(Q),r)) : r in m];
 for i in [1,5,8,10] do T[i] *:= 2; end for;
 Reordering:=[1,2,5,3,6,8,4,7,9,10];
 return SymmetricMatrix(T[Reordering]); end function;


function IsLinear(p) // is a multivariate polynomial linear?
 return &and[&+Exponents(t) eq 1 : t in Terms(p)]; end function;

function LinearFactors(p)
 return [t[1] : t in Factorisation(p) | IsLinear(t[1])]; end function;

function FirstNonZeroElt(a)
 if (&and[u eq 0 : u in a]) then return 0,1; end if;
 return a[b],b where b is Min([t : t in [1..#a] | a[t] ne 0]); end function;

fnz:=FirstNonZeroElt;

function IsIntegralFD(A)
 if Category(BaseRing(Parent(A[1]))) eq RngInt then return true; end if;
 ee:=Eltseq(A[1]) cat Eltseq(A[2]);
 ff:=&and [Denominator(e) eq 1 : e in ee]; return ff; end function;

function SL2Apply(m,A)
 return [m[1,1]*A[1] + m[2,1]*A[2], m[1,2]*A[1]+m[2,2]*A[2]]; end function;

function ApplyMatrix(mat,fd) // Act on a four-covering fd by mat in SL4(Z)
 m2:=[mat*t*Transpose(mat) : t in fd];
 if Category(BaseRing(m2[1])) eq FldRat then
  if LCM(&cat[[Denominator(t) : t in Eltseq(m)]:m in m2]) ne 1 then
   error "Impossible transform",mat,fd,m2; end if;
  m2:=[MatrixAlgebra(Integers(),4)!m : m in m2]; end if;
 assert IsIntegralFD(m2); return m2; end function;

function ApplyTransform(T,fc) // Apply T to the four-covering fc
 return SL2Apply(T[1],ApplyMatrix(T[2],fc)); end function;

function PolynomialApplyDegree(deg, M, q)// subst x = ax+by, y = cx+dy in q
 b:=BaseRing(Parent(q)); pq:=Parent(q); p:=PolynomialRing(b,2); X:=p.1; Y:=p.2;
 newX:=M[1,1]*p.1+M[1,2]*p.2; newY:=M[2,1]*p.1+M[2,2]*p.2;
 t:=&+[Coefficient(q,n)*newX^n*newY^(deg-n): n in [0..deg]];
 return hom<p->pq | pq.1,1>(t); end function;

function PolynomialApply(M,q)
 return PolynomialApplyDegree(Degree(q),M,q); end function;

intrinsic '^'(f::RngUPolElt, M::Mtrx : Deg:=Degree(f)) -> RngUPolElt
{Transform a univariate polynomial by an element of GL_2 in the standard way
 (by making the linear substitution on the homogenization of f)}
  return PolynomialApplyDegree(Deg,M,f);
end intrinsic;
function ExtendToUnimodular(cc)
 vv:=[[Integers()!wi : wi in Eltseq(w)] : w in cc];
 v,_,u:=SmithForm(Matrix(vv)); u:=u^(-1); return u; end function;

intrinsic QuadricIntersection(E::CrvEll) -> Crv,MapIsoSch
{Write an elliptic curve as a QuadricIntersection with map to E}
 a1,a2,a3,a4,a6:=Explode(aInvariants(E));
 F<A,B,C,D>:=ProjectiveSpace(BaseField(E),3);
 f1:=(D^2+a1*B*D+a3*C*D)-(A*B+a2*B^2+a4*B*C+a6*C^2); f2:=A*C-B^2;
 S:=Curve(F,[f1,f2]); P<x,y,z>:=Ambient(E);
 g1:=A^2*D+(-a2^2+a4)*A*C*D-a1*A*D^2+(-a2*a4+a6)*B*C*D+(a1*a2-a3)*B*D^2
     -a2*a6*C^2*D+a2*a3*C*D^2+a2*D^3;
 g2:=A^3-2*a1*A^2*D+(-a2^4+3*a2^2*a4-2*a2*a6-a4^2)*A*C^2
     +(-a1*a2^2+2*a2*a3)*A*C*D+(a1^2+2*a2)*A*D^2
     +(-a2^3*a4+a2^2*a6+2*a2*a4^2-2*a4*a6)*B*C^2
     +(a1*a2^3-2*a1*a2*a4-a2^2*a3+2*a3*a4)*B*C*D
     +(-a2^2+2*a4)*B*D^2+(-a2^3*a6+2*a2*a4*a6-a6^2)*C^3
     +(a2^3*a3-2*a2*a3*a4+2*a3*a6)*C^2*D
     +(a2^3-2*a2*a4-a3^2+2*a6)*C*D^2-2*a3*D^3; g3:=D^3;
 m:=map<S->E|[[g1,g2,g3],[B,D,C]],[x^2,x*z,z^2,y*z] : Check:=false >;
 return S,m; end intrinsic;

intrinsic QuadricIntersection(H::CrvHyp) -> Crv,MapIsoSch
{Write a genus 1 hyperelliptic curve as a QuadricIntersection with map to H}
 require Degree(H) eq 4 : "CrvHyp must be of degree 4";
 P<x,y,z>:=Ambient(H); DE:=DefiningEquation(H);
 a,b,c,d,e:=Explode
       ([BaseField(H)!-Coefficient(Coefficient(DE,x,4-i),z,i) : i in [0..4]]);
 F<A,B,C,D>:=ProjectiveSpace(BaseField(H),3);
 f1:=D^2-(a*A^2+b*A*B+c*A*C+d*B*C+e*C^2); f2:=A*C-B^2; S:=Curve(F,[f1,f2]);
 m:=map<S->H|[[B,C*D,C],[A,A*D,B]],[x^2,x*z,z^2,y] : Check:=false >;
 return S,m; end intrinsic;

intrinsic IsQuadricIntersection(X::Sch) -> BoolElt,SeqEnum[AlgMatElt]
{Determine if a scheme in P^3 is an intersection of 2 quadrics (poss. sing.)}
 if not IsProjective(X) then return false,_; end if;
 if Dimension(Ambient(X)) ne 3 then return false,_; end if;
 D:=DefiningEquations(X); if #D ne 2 then return false,_; end if;
 if TotalDegree(D[1]) ne 2 or TotalDegree(D[2]) ne 2
  then return false,_; end if;
 if Dimension(X) ne 1 then return false,_; end if;
 return true,[QFToMatrix(x) : x in D]; end intrinsic;

intrinsic Transformation(F::[AlgMatElt],T::Tup)->SeqEnum
{Apply the transformation T to the four-covering F}
 require IsIntegralFD(F): "F must be an integral four-covering";
 return ApplyTransform(T,F); end intrinsic;

intrinsic IsEquivalent(f1::RngUPolElt,f2::RngUPolElt) -> BoolElt
{Determine if two quartics are equivalent over their common base field}
 require Degree(f1) eq 4 and Degree(f2) eq 4:
 "The given polynomials must have degree 4";
 require BaseRing(f1) eq BaseRing(f2):
 "The given polynomials should have the same base ring";
 K:=FieldOfFractions(BaseRing(f1)); L := PolynomialRing(K); u := L.1;
 Ii:=QuarticIInvariant(f1); Ji:=QuarticJInvariant(f2);
 if Ii ne QuarticIInvariant(f2) then return false; end if;
 if Ji ne QuarticJInvariant(f2) then return false; end if;
 a1:=LeadingCoefficient(f1); a2:=LeadingCoefficient(f2);
 p1:=QuarticPSeminvariant(f1); p2:=QuarticPSeminvariant(f2);
 r1:=QuarticRSeminvariant(f1); r2:=QuarticRSeminvariant(f2);
 p:=(32*a1*a2*Ii+p1*p2)/3; r:=r1*r2;
 s:=(64*Ii*(a1^2*p2^2+a2^2*p1^2+a1*a2*p1*p2)
     -256*a1*a2*Ji*(a1*p2+a2*p1)-p1^2*p2^2)/27;
 R:=Roots(u^4-2*p*u^2-8*r*u+s); if #R eq 0 then return false; end if;
 return true; end intrinsic;
