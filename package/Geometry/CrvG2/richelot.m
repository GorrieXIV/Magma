freeze;

/*****************************************************************************
 *
 * richelot.m
 *
 * date:   11/11/2010
 * author: Nils Bruin
 *
 * routines to compute with Richelot Isogenies on Jacobians of Genus 2 curves.
 *
 * Main interface routines:
 *   RichelotIsogenousSurface(J::JacHyp, ker::RngUPolElt[RngUPolRes])
 *   RichelotIsogenousSurfaces(J::JacHyp : Kernels:=false)
 *
 * BACKGROUND THEORY:
 * Let J be the Jacobian of a genus 2 curve C: y^2=f(x) [so, odd characteristic]
 * Then J[2] can be expressed as divisor classes of differences of Weierstrass
 * points [(theta_i,0)-(theta_j,0)]. A maximal isotropic subgroup corresponds to
 * splitting the 6 roots of f(x) in three groups of 2. This means writing
 * f/lc(f) as the norm of a quadratic polynomial over a cubic algebra.
 * The following pseudocode shows the requirements for ker to describe a
 * valid kernel.
 *
 * J:=Jacobian(HyperellipticCurve(f));
 * P<x>:=PolynomialRing(k) and f in P
 * assert h in P and Degree(h) eq 3;
 * A<alpha>:= quo<P|h>
 * AX := PolynomialRing(A); X := AX.1;
 * assert ker in AX and degree(ker) eq 2;
 * assert Norm(swp(ker)) eq f/LeadingCoefficient(f)
 *                          where _,swp:=SwapExtension(AX);
 *
 * RETURN TYPES:
 * The codomain of a richelot isogeny is a principally polarized surface. This
 * can be of the following types:
 *
 *  (a) A Jacobian of a genus 2 curve
 *  (b) A product of elliptic curves
 *  (c) A Weil restriction of an elliptic curve over a quadratic extension.
 *
 * Type (a) is represented by a Jacobian of type JacHyp.
 * Type (b) is represented by a Cartesian product of two elliptic curves, of
 *    type SetCart
 * Type (c) is represented by the elliptic curve over the quadratic extension,
 *    of type CrvEll (but defined over a field that is a quadratic extension)
 *****************************************************************************/
 
function padseq(L,n)
  return L cat [0: i in [#L+1..n]];
end function;

function sing_rich_codomain(f,Q:r:=false)
  //INPUT:  f - degree 5 or 6 polynomial
  //        Q - monic quadratic over degree 2 or 3 algebra
  //        r - base field element (optional)
  //
  //RESTRICTIONS:
  // if f is quintic then Q must be over a degree 2 algebra and r must be specified and
  // C: y^2 = f(x) = c (x-r) Norm(Q) [for some c]
  // if f is sextic then Q must be over a degree 3 algebra and r must not be given and
  // C: y^2 = f(x) = c Norm(Q) [for some c]
  //
  //OUTPUT: A cartesian product of elliptic curves or an elliptic curve over a
  // quadratic extension (representing its weil restriction), giving the codomain
  // of the richelot isogeny on Jac(C) described by the splitting given by the specified data.

  R:=BaseRing(Q);
  k:=BaseRing(f);
  assert BaseRing(R) eq k;
  x:=PolynomialRing(k).1;
  P<a,b,c,d>:=PolynomialRing(R,4);
  PX := PolynomialRing(P); XP := PX.1;
  H:=Evaluate(Q,XP);
  TH:=Numerator(Evaluate(Q,(a*XP+b)/(c*XP+d)));
  L:=Eltseq(LeadingCoefficient(H)*TH-LeadingCoefficient(TH)*H);
  rng,swp:=SwapExtension(P);
  _<aa,bb,cc,dd>:=BaseRing(rng);
  E:=&cat[Eltseq(swp(l)):l in L];
  if r cmpne false then
    E cat:=[cc*r+dd,aa-cc*r];
  end if;
  V:=[l: p in RationalPoints(Scheme(Proj(Universe(E)),E))| l ne [1,0,0,1] where l:=Eltseq(p)];
  assert #V eq 1;
  m:=Matrix(2,2,V[1]);
  L:=Eltseq(m^2);
  assert L[2] eq 0 and L[3] eq 0 and L[1] eq L[4];
  bl,lambda:=IsSquare(L[1]);
  if bl then
    A:=Matrix([Basis(Eigenspace(m,lambda))[1],Basis(Eigenspace(m,-lambda))[1]])^(-1);
    Lf:=padseq(Eltseq(f),7);
    F:=&+[Lf[i+1]*(A[2,1]*x+A[2,2])^(6-i)*(A[1,1]*x+A[1,2])^i: i in [0..6]];
    assert Eltseq(F)[[2,4,6]] eq [0,0,0];
    e1:=Parent(F)!Eltseq(F)[[1,3,5,7]];
    E1:=EllipticCurve(lc^2*Evaluate(e1,x/lc) where lc:=LeadingCoefficient(e1));
    e2:=Parent(F)!Eltseq(F)[[7,5,3,1]];
    E2:=EllipticCurve(lc^2*Evaluate(e2,x/lc) where lc:=LeadingCoefficient(e2));
    return CartesianProduct(E1,E2);
  else
    K:=ext<BaseRing(f)|x^2-L[1]>;
    PK:=PolynomialRing(K);X:=PK.1;
    f:=Polynomial(K,f);
    m:=ChangeRing(m,K);
    bl,lambda:=IsSquare(K!L[1]);
    assert bl;
    A:=Matrix([Basis(Eigenspace(m,lambda))[1],Basis(Eigenspace(m,-lambda))[1]])^(-1);
    Lf:=padseq(Eltseq(f),7);
    F:=&+[Lf[i+1]*(A[2,1]*X+A[2,2])^(6-i)*(A[1,1]*X+A[1,2])^i: i in [0..6]];
    assert Eltseq(F)[[2,4,6]] eq [0,0,0];
    e1:=Parent(F)!Eltseq(F)[[1,3,5,7]];
    E1:=EllipticCurve(lc^2*Evaluate(e1,X/lc) where lc:=LeadingCoefficient(e1));
    return E1;
  end if;
end function;

function rich_codomain_deg5(r,Q)
  //INPUT:  Q - monic quadratic over a quadratic etale algebra
  //        r - a base field element, not a root of Q
  //
  //OUTPUT: g - polynomial over base field. If g !=0 then
  //        the curve D: v^2=g(u) has Jac(D) Richelot-isogenous to
  //        Jac(C), where C: y^2=(x-r)*Norm(Q).
  //        If g=0, the richelot isogeny is singular.
  
  RX:=Parent(Q);
  R:=BaseRing(RX);
  h:=Modulus(R);
  h:=h/LeadingCoefficient(h);
  k:=BaseRing(R);
  h0,h1:=Explode(Eltseq(h));
  QL:=Eltseq(Q);
  q00,q01:=Explode(padseq(Eltseq(QL[1]),3));
  q10,q11:=Explode(padseq(Eltseq(QL[2]),3));
  /**********************************************************************************
  //we can determine a model for the curve D generically with the following code.
  //computing D is simply a matter of specializing.
  //our curve is specified by:
  //
  //alpha^2+h1*alpha+h0=0
  //f(X)=(X-r)* Norm(X^2+(q11*alpha+q10)*X+(q01*alpha+q00))
  
  k0<r,h1,h0,q11,q10,q01,q00>:=RationalFunctionField(Rationals(),7);
  k0X := PolynomialRing(k0); X := k0X.1;
  h:=X^2+h1*X+h0;
  dsc:=Discriminant(h);
  k1<alpha>:=quo<k0X|h>;
  k1Y := PolynomialRing(k1); Y := k1Y.1;
  alphas:=[a[1]: a in Roots(Polynomial(k1,h))];
  sigmas:=[hom<k1->k1| alphas[i]>: i in [1..2]];
  F1:=Y^2+(q11*alpha+q10)*Y+(q01*alpha+q00);
  Fi:=[Y-r] cat [k1Y![s(c): c in Eltseq(F1)]: s in sigmas];
  LF:=Eltseq(&*Fi);
  padseq:=func<L,n|L cat [0: i in [#L+1 .. n]]>;
  delta:=Determinant(Matrix([padseq(Eltseq(f),3): f in Fi]));
  Gfunc:=func<f,g|Determinant(Matrix([[Derivative(f),Derivative(g)],[f,g]]))/delta>;
  Gi:=[Gfunc(Fi[i[1]],Fi[i[2]]): i in [[2,3],[3,1],[1,2]]];
  G:=dsc*&*Gi;
  LG:=[(r*q11 + q01)^4*b : b in &cat[Eltseq(v): v in Eltseq(G)]];
  **********************************************************************************/

  LG:=[
    -r^3*h1*q11^3*q10*q00 + r^3*h1*q11^2*q10^2*q01 + r^3*h0*q11^4*q00 - 
        r^3*h0*q11^3*q10*q01 + r^3*q11^2*q10^2*q00 - r^3*q11*q10^3*q01 - 
        r^2*h1*q11^3*q00^2 - r^2*h1*q11^2*q10*q01*q00 + 2*r^2*h1*q11*q10^2*q01^2
        + 3*r^2*h0*q11^3*q01*q00 - 3*r^2*h0*q11^2*q10*q01^2 + 
        2*r^2*q11^2*q10*q00^2 - r^2*q11*q10^2*q01*q00 - r^2*q10^3*q01^2 - 
        2*r*h1*q11^2*q01*q00^2 + r*h1*q11*q10*q01^2*q00 + r*h1*q10^2*q01^3 + 
        3*r*h0*q11^2*q01^2*q00 - 3*r*h0*q11*q10*q01^3 + r*q11^2*q00^3 + 
        r*q11*q10*q01*q00^2 - 2*r*q10^2*q01^2*q00 - h1*q11*q01^2*q00^2 + 
        h1*q10*q01^3*q00 + h0*q11*q01^3*q00 - h0*q10*q01^4 + q11*q01*q00^3 - 
        q10*q01^2*q00^2,
    -2*r^3*h1*q11^3*q00 + 4*r^3*h1*q11^2*q10*q01 - 2*r^3*h0*q11^3*q01 + 
        4*r^3*q11^2*q10*q00 - 6*r^3*q11*q10^2*q01 - 2*r^2*h1*q11^2*q01*q00 + 
        8*r^2*h1*q11*q10*q01^2 - 6*r^2*h0*q11^2*q01^2 + 4*r^2*q11^2*q00^2 - 
        4*r^2*q11*q10*q01*q00 - 6*r^2*q10^2*q01^2 + 2*r*h1*q11*q01^2*q00 + 
        4*r*h1*q10*q01^3 - 6*r*h0*q11*q01^3 + 2*r*q11*q01*q00^2 - 
        8*r*q10*q01^2*q00 + 2*h1*q01^3*q00 - 2*h0*q01^4 - 2*q01^2*q00^2,
    r^3*h1*q11^3*q10 + 4*r^3*h1*q11^2*q01 - r^3*h0*q11^4 - r^3*q11^2*q10^2 + 
        4*r^3*q11^2*q00 - 12*r^3*q11*q10*q01 + 2*r^2*h1*q11^3*q00 + 
        r^2*h1*q11^2*q10*q01 + 8*r^2*h1*q11*q01^2 - 3*r^2*h0*q11^3*q01 - 
        4*r^2*q11^2*q10*q00 + r^2*q11*q10^2*q01 - 4*r^2*q11*q01*q00 - 
        12*r^2*q10*q01^2 + 4*r*h1*q11^2*q01*q00 - r*h1*q11*q10*q01^2 + 
        4*r*h1*q01^3 - 3*r*h0*q11^2*q01^2 - 3*r*q11^2*q00^2 - 
        2*r*q11*q10*q01*q00 + 2*r*q10^2*q01^2 - 8*r*q01^2*q00 + 
        2*h1*q11*q01^2*q00 - h1*q10*q01^3 - h0*q11*q01^3 - 3*q11*q01*q00^2 + 
        2*q10*q01^2*q00,
    2*r^3*h1*q11^3 - 4*r^3*q11^2*q10 - 8*r^3*q11*q01 + 2*r^2*h1*q11^2*q01 - 
        8*r^2*q11^2*q00 + 4*r^2*q11*q10*q01 - 8*r^2*q01^2 - 2*r*h1*q11*q01^2 - 
        4*r*q11*q01*q00 + 8*r*q10*q01^2 - 2*h1*q01^3 + 4*q01^2*q00,
    -4*r^3*q11^2 - r^2*h1*q11^3 + 2*r^2*q11^2*q10 + 4*r^2*q11*q01 - 
        2*r*h1*q11^2*q01 + 3*r*q11^2*q00 + r*q11*q10*q01 + 8*r*q01^2 - 
        h1*q11*q01^2 + 3*q11*q01*q00 - q10*q01^2,
    4*r^2*q11^2 + 2*r*q11*q01 - 2*q01^2,
    -r*q11^2 - q11*q01];
  return Polynomial(k,LG);
end function;
 
function rich_codomain_deg6(Q)
  //INPUT:  Q - monic quadratic over a cubic etale algebra
  //
  //OUTPUT: g - polynomial over base field. If g !=0 then
  //        the curve D: v^2=g(u) has Jac(D) Richelot-isogenous to
  //        Jac(C), where C: y^2=Norm(Q).
  //        If g=0, the richelot isogeny is singular.

  RX:=Parent(Q);
  R:=BaseRing(RX);
  h:=Modulus(R);
  h:=h/LeadingCoefficient(h);

  k:=BaseRing(R);
  h0,h1,h2:=Explode(Eltseq(h));
  QL:=Eltseq(Q);
  q00,q01,q02:=Explode(padseq(Eltseq(QL[1]),3));
  q10,q11,q12:=Explode(padseq(Eltseq(QL[2]),3));
  
  /********************************************************************************
  //we can determine a model for the curve D generically with the following code.
  //computing D is simply a matter of specializing.
  //our curve is specified by:
  //
  //alpha^3+h2*alpha^2+h1*alpha+h0=0
  //f(X)=Norm(X^2+(q12*alpha^2+q11*alpha+q10)*X+(qq02*alpha^2+01*alpha+q00))

  k0<h2,h1,h0,q12,q11,q10,q02,q01,q00>:=RationalFunctionField(Rationals(),9);
  q2:=1;
  k0X := PolynomialRing(k0); X := k0X.1;
  dsc:=Discriminant(X^3+h2*X^2+h1*X+h0);
  k1<DELTA>:=quo<k0X|X^2-dsc>;
  k1Y := PolynomialRing(k1); Y := k1Y.1;
  h:=Y^3+h2*Y^2+h1*Y+h0;
  k2<alpha>:=quo<k1Y|h>;
  alphas:=[a[1]: a in Roots(Polynomial(k2,h))];
  k2x := PolynomialRing(k2); x := k2x.1;
  sigmas:=[hom<k2->k2| alphas[i]>: i in [1..3]];
  F1:=q2*x^2+(q12*alpha^2+q11*alpha+q10)*x+(q02*alpha^2+q01*alpha+q00);
  Fi:=[k2x![s(c): c in Eltseq(F1)]: s in sigmas];
  LF:=&cat[Eltseq(a): a in &cat[Eltseq(a): a in Eltseq(&*Fi)]];
  delta:=Determinant(Matrix([Eltseq(f): f in Fi]));
  Gfunc:=func<f,g|Determinant(Matrix([[Derivative(f),Derivative(g)],[f,g]]))/delta>;
  Gi:=[Gfunc(Fi[i[1]],Fi[i[2]]): i in [[2,3],[3,1],[1,2]]];
  G:=dsc*&*Gi;
  LG:=[(q12*q01 - q11*q02)^4*q2^4*b : b in &cat[Eltseq(a): a in &cat[Eltseq(a): a in Eltseq(G)]]];
  *********************************************************************************/
  LG:=[
    h2^2*q12^3*q11*q01*q00^3-h2^2*q12^3*q10*q01^2*q00^2-
        h2^2*q12^2*q11^2*q02*q00^3-h2^2*q12^2*q11*q10*q02*q01*q00^2+
        2*h2^2*q12^2*q10^2*q02*q01^2*q00+2*h2^2*q12*q11^2*q10*q02^2*q00^2-
        h2^2*q12*q11*q10^2*q02^2*q01*q00-h2^2*q12*q10^3*q02^2*q01^2-
        h2^2*q11^2*q10^2*q02^3*q00+h2^2*q11*q10^3*q02^3*q01-
        h2*h1*q12^4*q01*q00^3+h2*h1*q12^3*q11*q02*q00^3-
        h2*h1*q12^3*q11*q01^2*q00^2+3*h2*h1*q12^3*q10*q02*q01*q00^2+
        h2*h1*q12^3*q10*q01^3*q00+2*h2*h1*q12^2*q11^2*q02*q01*q00^2-
        3*h2*h1*q12^2*q11*q10*q02^2*q00^2-h2*h1*q12^2*q11*q10*q02*q01^2*q00-
        3*h2*h1*q12^2*q10^2*q02^2*q01*q00-h2*h1*q12^2*q10^2*q02*q01^3-
        h2*h1*q12*q11^3*q02^2*q00^2-h2*h1*q12*q11^2*q10*q02^2*q01*q00+
        3*h2*h1*q12*q11*q10^2*q02^3*q00+2*h2*h1*q12*q11*q10^2*q02^2*q01^2+
        h2*h1*q12*q10^3*q02^3*q01+h2*h1*q11^3*q10*q02^3*q00-
        h2*h1*q11^2*q10^2*q02^3*q01-h2*h1*q11*q10^3*q02^4+
        h2*h0*q12^4*q01^2*q00^2-2*h2*h0*q12^3*q11*q02*q01*q00^2+
        h2*h0*q12^3*q11*q01^3*q00-2*h2*h0*q12^3*q10*q02*q01^2*q00-
        h2*h0*q12^3*q10*q01^4+h2*h0*q12^2*q11^2*q02^2*q00^2-
        3*h2*h0*q12^2*q11^2*q02*q01^2*q00+4*h2*h0*q12^2*q11*q10*q02^2*q01*q00 
       +3*h2*h0*q12^2*q11*q10*q02*q01^3+h2*h0*q12^2*q10^2*q02^2*q01^2+
        3*h2*h0*q12*q11^3*q02^2*q01*q00-2*h2*h0*q12*q11^2*q10*q02^3*q00-
        3*h2*h0*q12*q11^2*q10*q02^2*q01^2-2*h2*h0*q12*q11*q10^2*q02^3*q01-
        h2*h0*q11^4*q02^3*q00+h2*h0*q11^3*q10*q02^3*q01+
        h2*h0*q11^2*q10^2*q02^4-2*h2*q12^2*q11^2*q01*q00^3+
        4*h2*q12^2*q11*q10*q01^2*q00^2-2*h2*q12^2*q10^2*q01^3*q00+
        2*h2*q12*q11^3*q02*q00^3-2*h2*q12*q11^2*q10*q02*q01*q00^2-
        2*h2*q12*q11*q10^2*q02*q01^2*q00+2*h2*q12*q10^3*q02*q01^3-
        2*h2*q11^3*q10*q02^2*q00^2+4*h2*q11^2*q10^2*q02^2*q01*q00-
        2*h2*q11*q10^3*q02^2*q01^2+h1^2*q12^4*q01^2*q00^2-
        2*h1^2*q12^3*q11*q02*q01*q00^2-2*h1^2*q12^3*q10*q02*q01^2*q00+
        h1^2*q12^2*q11^2*q02^2*q00^2+4*h1^2*q12^2*q11*q10*q02^2*q01*q00+
        h1^2*q12^2*q10^2*q02^2*q01^2-2*h1^2*q12*q11^2*q10*q02^3*q00-
        2*h1^2*q12*q11*q10^2*q02^3*q01+h1^2*q11^2*q10^2*q02^4-
        2*h1*h0*q12^4*q01^3*q00+6*h1*h0*q12^3*q11*q02*q01^2*q00+
        2*h1*h0*q12^3*q10*q02*q01^3-6*h1*h0*q12^2*q11^2*q02^2*q01*q00-
        6*h1*h0*q12^2*q11*q10*q02^2*q01^2+2*h1*h0*q12*q11^3*q02^3*q00+
        6*h1*h0*q12*q11^2*q10*q02^3*q01-2*h1*h0*q11^3*q10*q02^4+
        h1*q12^3*q11*q01*q00^3-h1*q12^3*q10*q01^2*q00^2-
        h1*q12^2*q11^2*q02*q00^3+h1*q12^2*q11^2*q01^2*q00^2-
        h1*q12^2*q11*q10*q02*q01*q00^2-2*h1*q12^2*q11*q10*q01^3*q00+
        2*h1*q12^2*q10^2*q02*q01^2*q00+h1*q12^2*q10^2*q01^4-
        2*h1*q12*q11^3*q02*q01*q00^2+2*h1*q12*q11^2*q10*q02^2*q00^2+
        4*h1*q12*q11^2*q10*q02*q01^2*q00-h1*q12*q11*q10^2*q02^2*q01*q00-
        2*h1*q12*q11*q10^2*q02*q01^3-h1*q12*q10^3*q02^2*q01^2+
        h1*q11^4*q02^2*q00^2-2*h1*q11^3*q10*q02^2*q01*q00-
        h1*q11^2*q10^2*q02^3*q00+h1*q11^2*q10^2*q02^2*q01^2+
        h1*q11*q10^3*q02^3*q01+h0^2*q12^4*q01^4-4*h0^2*q12^3*q11*q02*q01^3+
        6*h0^2*q12^2*q11^2*q02^2*q01^2-4*h0^2*q12*q11^3*q02^3*q01+
        h0^2*q11^4*q02^4+h0*q12^4*q01*q00^3-h0*q12^3*q11*q02*q00^3-
        3*h0*q12^3*q11*q01^2*q00^2-3*h0*q12^3*q10*q02*q01*q00^2+
        3*h0*q12^3*q10*q01^3*q00+6*h0*q12^2*q11^2*q02*q01*q00^2+
        3*h0*q12^2*q11*q10*q02^2*q00^2-3*h0*q12^2*q11*q10*q02*q01^2*q00+
        3*h0*q12^2*q10^2*q02^2*q01*q00-3*h0*q12^2*q10^2*q02*q01^3-
        3*h0*q12*q11^3*q02^2*q00^2-3*h0*q12*q11^2*q10*q02^2*q01*q00-
        3*h0*q12*q11*q10^2*q02^3*q00+6*h0*q12*q11*q10^2*q02^2*q01^2-
        h0*q12*q10^3*q02^3*q01+3*h0*q11^3*q10*q02^3*q00-
        3*h0*q11^2*q10^2*q02^3*q01+h0*q11*q10^3*q02^4+q12*q11^3*q01*q00^3-
        3*q12*q11^2*q10*q01^2*q00^2+3*q12*q11*q10^2*q01^3*q00-
        q12*q10^3*q01^4-q11^4*q02*q00^3+3*q11^3*q10*q02*q01*q00^2-
        3*q11^2*q10^2*q02*q01^2*q00+q11*q10^3*q02*q01^3,
   -2*h2^2*q12^3*q01^2*q00^2-2*h2^2*q12^2*q11*q02*q01*q00^2+
        8*h2^2*q12^2*q10*q02*q01^2*q00+4*h2^2*q12*q11^2*q02^2*q00^2-
        4*h2^2*q12*q11*q10*q02^2*q01*q00-6*h2^2*q12*q10^2*q02^2*q01^2-
        4*h2^2*q11^2*q10*q02^3*q00+6*h2^2*q11*q10^2*q02^3*q01+
        6*h2*h1*q12^3*q02*q01*q00^2+2*h2*h1*q12^3*q01^3*q00-
        6*h2*h1*q12^2*q11*q02^2*q00^2-2*h2*h1*q12^2*q11*q02*q01^2*q00-
        12*h2*h1*q12^2*q10*q02^2*q01*q00-4*h2*h1*q12^2*q10*q02*q01^3-
        2*h2*h1*q12*q11^2*q02^2*q01*q00+12*h2*h1*q12*q11*q10*q02^3*q00+
        8*h2*h1*q12*q11*q10*q02^2*q01^2+6*h2*h1*q12*q10^2*q02^3*q01+
        2*h2*h1*q11^3*q02^3*q00-4*h2*h1*q11^2*q10*q02^3*q01-
        6*h2*h1*q11*q10^2*q02^4-4*h2*h0*q12^3*q02*q01^2*q00-
        2*h2*h0*q12^3*q01^4+8*h2*h0*q12^2*q11*q02^2*q01*q00+
        6*h2*h0*q12^2*q11*q02*q01^3+4*h2*h0*q12^2*q10*q02^2*q01^2-
        4*h2*h0*q12*q11^2*q02^3*q00-6*h2*h0*q12*q11^2*q02^2*q01^2-
        8*h2*h0*q12*q11*q10*q02^3*q01+2*h2*h0*q11^3*q02^3*q01+
        4*h2*h0*q11^2*q10*q02^4+8*h2*q12^2*q11*q01^2*q00^2-
        8*h2*q12^2*q10*q01^3*q00-4*h2*q12*q11^2*q02*q01*q00^2-
        8*h2*q12*q11*q10*q02*q01^2*q00+12*h2*q12*q10^2*q02*q01^3-
        4*h2*q11^3*q02^2*q00^2+16*h2*q11^2*q10*q02^2*q01*q00-
        12*h2*q11*q10^2*q02^2*q01^2-4*h1^2*q12^3*q02*q01^2*q00+
        8*h1^2*q12^2*q11*q02^2*q01*q00+4*h1^2*q12^2*q10*q02^2*q01^2-
        4*h1^2*q12*q11^2*q02^3*q00-8*h1^2*q12*q11*q10*q02^3*q01+
        4*h1^2*q11^2*q10*q02^4+4*h1*h0*q12^3*q02*q01^3-
        12*h1*h0*q12^2*q11*q02^2*q01^2+12*h1*h0*q12*q11^2*q02^3*q01-
        4*h1*h0*q11^3*q02^4-2*h1*q12^3*q01^2*q00^2-
        2*h1*q12^2*q11*q02*q01*q00^2-4*h1*q12^2*q11*q01^3*q00+
        8*h1*q12^2*q10*q02*q01^2*q00+4*h1*q12^2*q10*q01^4+
        4*h1*q12*q11^2*q02^2*q00^2+8*h1*q12*q11^2*q02*q01^2*q00-
        4*h1*q12*q11*q10*q02^2*q01*q00-8*h1*q12*q11*q10*q02*q01^3-
        6*h1*q12*q10^2*q02^2*q01^2-4*h1*q11^3*q02^2*q01*q00-
        4*h1*q11^2*q10*q02^3*q00+4*h1*q11^2*q10*q02^2*q01^2+
        6*h1*q11*q10^2*q02^3*q01-6*h0*q12^3*q02*q01*q00^2+
        6*h0*q12^3*q01^3*q00+6*h0*q12^2*q11*q02^2*q00^2-
        6*h0*q12^2*q11*q02*q01^2*q00+12*h0*q12^2*q10*q02^2*q01*q00-
        12*h0*q12^2*q10*q02*q01^3-6*h0*q12*q11^2*q02^2*q01*q00-
        12*h0*q12*q11*q10*q02^3*q00+24*h0*q12*q11*q10*q02^2*q01^2-
        6*h0*q12*q10^2*q02^3*q01+6*h0*q11^3*q02^3*q00-
        12*h0*q11^2*q10*q02^3*q01+6*h0*q11*q10^2*q02^4-
        6*q12*q11^2*q01^2*q00^2+12*q12*q11*q10*q01^3*q00-6*q12*q10^2*q01^4+
        6*q11^3*q02*q01*q00^2-12*q11^2*q10*q02*q01^2*q00+
        6*q11*q10^2*q02*q01^3,
   -3*h2^2*q12^3*q11*q01*q00^2+2*h2^2*q12^3*q10*q01^2*q00+
        3*h2^2*q12^2*q11^2*q02*q00^2+2*h2^2*q12^2*q11*q10*q02*q01*q00-
        2*h2^2*q12^2*q10^2*q02*q01^2+8*h2^2*q12^2*q02*q01^2*q00-
        4*h2^2*q12*q11^2*q10*q02^2*q00+h2^2*q12*q11*q10^2*q02^2*q01-
        4*h2^2*q12*q11*q02^2*q01*q00-12*h2^2*q12*q10*q02^2*q01^2+
        h2^2*q11^2*q10^2*q02^3-4*h2^2*q11^2*q02^3*q00+
        12*h2^2*q11*q10*q02^3*q01+3*h2*h1*q12^4*q01*q00^2-
        3*h2*h1*q12^3*q11*q02*q00^2+2*h2*h1*q12^3*q11*q01^2*q00-
        6*h2*h1*q12^3*q10*q02*q01*q00-h2*h1*q12^3*q10*q01^3-
        4*h2*h1*q12^2*q11^2*q02*q01*q00+6*h2*h1*q12^2*q11*q10*q02^2*q00+
        h2*h1*q12^2*q11*q10*q02*q01^2+3*h2*h1*q12^2*q10^2*q02^2*q01-
        12*h2*h1*q12^2*q02^2*q01*q00-4*h2*h1*q12^2*q02*q01^3+
        2*h2*h1*q12*q11^3*q02^2*q00+h2*h1*q12*q11^2*q10*q02^2*q01-
        3*h2*h1*q12*q11*q10^2*q02^3+12*h2*h1*q12*q11*q02^3*q00+
        8*h2*h1*q12*q11*q02^2*q01^2+12*h2*h1*q12*q10*q02^3*q01-
        h2*h1*q11^3*q10*q02^3-4*h2*h1*q11^2*q02^3*q01-12*h2*h1*q11*q10*q02^4
       -2*h2*h0*q12^4*q01^2*q00+4*h2*h0*q12^3*q11*q02*q01*q00-
        h2*h0*q12^3*q11*q01^3+2*h2*h0*q12^3*q10*q02*q01^2-
        2*h2*h0*q12^2*q11^2*q02^2*q00+3*h2*h0*q12^2*q11^2*q02*q01^2-
        4*h2*h0*q12^2*q11*q10*q02^2*q01+4*h2*h0*q12^2*q02^2*q01^2-
        3*h2*h0*q12*q11^3*q02^2*q01+2*h2*h0*q12*q11^2*q10*q02^3-
        8*h2*h0*q12*q11*q02^3*q01+h2*h0*q11^4*q02^3+4*h2*h0*q11^2*q02^4+
        6*h2*q12^2*q11^2*q01*q00^2-8*h2*q12^2*q11*q10*q01^2*q00+
        2*h2*q12^2*q10^2*q01^3-8*h2*q12^2*q01^3*q00-6*h2*q12*q11^3*q02*q00^2
       +4*h2*q12*q11^2*q10*q02*q01*q00+2*h2*q12*q11*q10^2*q02*q01^2-
        8*h2*q12*q11*q02*q01^2*q00+24*h2*q12*q10*q02*q01^3+
        4*h2*q11^3*q10*q02^2*q00-4*h2*q11^2*q10^2*q02^2*q01+
        16*h2*q11^2*q02^2*q01*q00-24*h2*q11*q10*q02^2*q01^2-
        2*h1^2*q12^4*q01^2*q00+4*h1^2*q12^3*q11*q02*q01*q00+
        2*h1^2*q12^3*q10*q02*q01^2-2*h1^2*q12^2*q11^2*q02^2*q00-
        4*h1^2*q12^2*q11*q10*q02^2*q01+4*h1^2*q12^2*q02^2*q01^2+
        2*h1^2*q12*q11^2*q10*q02^3-8*h1^2*q12*q11*q02^3*q01+
        4*h1^2*q11^2*q02^4+2*h1*h0*q12^4*q01^3-6*h1*h0*q12^3*q11*q02*q01^2+
        6*h1*h0*q12^2*q11^2*q02^2*q01-2*h1*h0*q12*q11^3*q02^3-
        3*h1*q12^3*q11*q01*q00^2+2*h1*q12^3*q10*q01^2*q00+
        3*h1*q12^2*q11^2*q02*q00^2-2*h1*q12^2*q11^2*q01^2*q00+
        2*h1*q12^2*q11*q10*q02*q01*q00+2*h1*q12^2*q11*q10*q01^3-
        2*h1*q12^2*q10^2*q02*q01^2+8*h1*q12^2*q02*q01^2*q00+4*h1*q12^2*q01^4
       +4*h1*q12*q11^3*q02*q01*q00-4*h1*q12*q11^2*q10*q02^2*q00-
        4*h1*q12*q11^2*q10*q02*q01^2+h1*q12*q11*q10^2*q02^2*q01-
        4*h1*q12*q11*q02^2*q01*q00-8*h1*q12*q11*q02*q01^3-
        12*h1*q12*q10*q02^2*q01^2-2*h1*q11^4*q02^2*q00+
        2*h1*q11^3*q10*q02^2*q01+h1*q11^2*q10^2*q02^3-4*h1*q11^2*q02^3*q00+
        4*h1*q11^2*q02^2*q01^2+12*h1*q11*q10*q02^3*q01-3*h0*q12^4*q01*q00^2 
       +3*h0*q12^3*q11*q02*q00^2+6*h0*q12^3*q11*q01^2*q00+
        6*h0*q12^3*q10*q02*q01*q00-3*h0*q12^3*q10*q01^3-
        12*h0*q12^2*q11^2*q02*q01*q00-6*h0*q12^2*q11*q10*q02^2*q00+
        3*h0*q12^2*q11*q10*q02*q01^2-3*h0*q12^2*q10^2*q02^2*q01+
        12*h0*q12^2*q02^2*q01*q00-12*h0*q12^2*q02*q01^3+
        6*h0*q12*q11^3*q02^2*q00+3*h0*q12*q11^2*q10*q02^2*q01+
        3*h0*q12*q11*q10^2*q02^3-12*h0*q12*q11*q02^3*q00+
        24*h0*q12*q11*q02^2*q01^2-12*h0*q12*q10*q02^3*q01-
        3*h0*q11^3*q10*q02^3-12*h0*q11^2*q02^3*q01+12*h0*q11*q10*q02^4-
        3*q12*q11^3*q01*q00^2+6*q12*q11^2*q10*q01^2*q00-
        3*q12*q11*q10^2*q01^3+12*q12*q11*q01^3*q00-12*q12*q10*q01^4+
        3*q11^4*q02*q00^2-6*q11^3*q10*q02*q01*q00+3*q11^2*q10^2*q02*q01^2-
        12*q11^2*q02*q01^2*q00+12*q11*q10*q02*q01^3,
    4*h2^2*q12^3*q01^2*q00+4*h2^2*q12^2*q11*q02*q01*q00-
        8*h2^2*q12^2*q10*q02*q01^2-8*h2^2*q12*q11^2*q02^2*q00+
        4*h2^2*q12*q11*q10*q02^2*q01-8*h2^2*q12*q02^2*q01^2+
        4*h2^2*q11^2*q10*q02^3+8*h2^2*q11*q02^3*q01-
        12*h2*h1*q12^3*q02*q01*q00-2*h2*h1*q12^3*q01^3+
        12*h2*h1*q12^2*q11*q02^2*q00+2*h2*h1*q12^2*q11*q02*q01^2+
        12*h2*h1*q12^2*q10*q02^2*q01+2*h2*h1*q12*q11^2*q02^2*q01-
        12*h2*h1*q12*q11*q10*q02^3+8*h2*h1*q12*q02^3*q01-2*h2*h1*q11^3*q02^3
       -8*h2*h1*q11*q02^4+4*h2*h0*q12^3*q02*q01^2-
        8*h2*h0*q12^2*q11*q02^2*q01+4*h2*h0*q12*q11^2*q02^3-
        16*h2*q12^2*q11*q01^2*q00+8*h2*q12^2*q10*q01^3+
        8*h2*q12*q11^2*q02*q01*q00+8*h2*q12*q11*q10*q02*q01^2+
        16*h2*q12*q02*q01^3+8*h2*q11^3*q02^2*q00-16*h2*q11^2*q10*q02^2*q01-
        16*h2*q11*q02^2*q01^2+4*h1^2*q12^3*q02*q01^2-
        8*h1^2*q12^2*q11*q02^2*q01+4*h1^2*q12*q11^2*q02^3+
        4*h1*q12^3*q01^2*q00+4*h1*q12^2*q11*q02*q01*q00+4*h1*q12^2*q11*q01^3
       -8*h1*q12^2*q10*q02*q01^2-8*h1*q12*q11^2*q02^2*q00-
        8*h1*q12*q11^2*q02*q01^2+4*h1*q12*q11*q10*q02^2*q01-
        8*h1*q12*q02^2*q01^2+4*h1*q11^3*q02^2*q01+4*h1*q11^2*q10*q02^3+
        8*h1*q11*q02^3*q01+12*h0*q12^3*q02*q01*q00-6*h0*q12^3*q01^3-
        12*h0*q12^2*q11*q02^2*q00+6*h0*q12^2*q11*q02*q01^2-
        12*h0*q12^2*q10*q02^2*q01+6*h0*q12*q11^2*q02^2*q01+
        12*h0*q12*q11*q10*q02^3-8*h0*q12*q02^3*q01-6*h0*q11^3*q02^3+
        8*h0*q11*q02^4+12*q12*q11^2*q01^2*q00-12*q12*q11*q10*q01^3-
        8*q12*q01^4-12*q11^3*q02*q01*q00+12*q11^2*q10*q02*q01^2+
        8*q11*q02*q01^3,
    3*h2^2*q12^3*q11*q01*q00-h2^2*q12^3*q10*q01^2-3*h2^2*q12^2*q11^2*q02*q00
       -h2^2*q12^2*q11*q10*q02*q01-8*h2^2*q12^2*q02*q01^2+
        2*h2^2*q12*q11^2*q10*q02^2+4*h2^2*q12*q11*q02^2*q01+
        4*h2^2*q11^2*q02^3-3*h2*h1*q12^4*q01*q00+3*h2*h1*q12^3*q11*q02*q00-
        h2*h1*q12^3*q11*q01^2+3*h2*h1*q12^3*q10*q02*q01+
        2*h2*h1*q12^2*q11^2*q02*q01-3*h2*h1*q12^2*q11*q10*q02^2+
        12*h2*h1*q12^2*q02^2*q01-h2*h1*q12*q11^3*q02^2-
        12*h2*h1*q12*q11*q02^3+h2*h0*q12^4*q01^2-2*h2*h0*q12^3*q11*q02*q01+
        h2*h0*q12^2*q11^2*q02^2-6*h2*q12^2*q11^2*q01*q00+
        4*h2*q12^2*q11*q10*q01^2+8*h2*q12^2*q01^3+6*h2*q12*q11^3*q02*q00-
        2*h2*q12*q11^2*q10*q02*q01+8*h2*q12*q11*q02*q01^2-
        2*h2*q11^3*q10*q02^2-16*h2*q11^2*q02^2*q01+h1^2*q12^4*q01^2-
        2*h1^2*q12^3*q11*q02*q01+h1^2*q12^2*q11^2*q02^2+
        3*h1*q12^3*q11*q01*q00-h1*q12^3*q10*q01^2-3*h1*q12^2*q11^2*q02*q00+
        h1*q12^2*q11^2*q01^2-h1*q12^2*q11*q10*q02*q01-8*h1*q12^2*q02*q01^2-
        2*h1*q12*q11^3*q02*q01+2*h1*q12*q11^2*q10*q02^2+
        4*h1*q12*q11*q02^2*q01+h1*q11^4*q02^2+4*h1*q11^2*q02^3+
        3*h0*q12^4*q01*q00-3*h0*q12^3*q11*q02*q00-3*h0*q12^3*q11*q01^2-
        3*h0*q12^3*q10*q02*q01+6*h0*q12^2*q11^2*q02*q01+
        3*h0*q12^2*q11*q10*q02^2-12*h0*q12^2*q02^2*q01-3*h0*q12*q11^3*q02^2 
       +12*h0*q12*q11*q02^3+3*q12*q11^3*q01*q00-3*q12*q11^2*q10*q01^2-
        12*q12*q11*q01^3-3*q11^4*q02*q00+3*q11^3*q10*q02*q01+
        12*q11^2*q02*q01^2,
   -2*h2^2*q12^3*q01^2-2*h2^2*q12^2*q11*q02*q01+4*h2^2*q12*q11^2*q02^2+
        6*h2*h1*q12^3*q02*q01-6*h2*h1*q12^2*q11*q02^2+8*h2*q12^2*q11*q01^2-
        4*h2*q12*q11^2*q02*q01-4*h2*q11^3*q02^2-2*h1*q12^3*q01^2-
        2*h1*q12^2*q11*q02*q01+4*h1*q12*q11^2*q02^2-6*h0*q12^3*q02*q01+
        6*h0*q12^2*q11*q02^2-6*q12*q11^2*q01^2+6*q11^3*q02*q01,
   -h2^2*q12^3*q11*q01+h2^2*q12^2*q11^2*q02+h2*h1*q12^4*q01-
        h2*h1*q12^3*q11*q02+2*h2*q12^2*q11^2*q01-2*h2*q12*q11^3*q02-
        h1*q12^3*q11*q01+h1*q12^2*q11^2*q02-h0*q12^4*q01+h0*q12^3*q11*q02 
       -q12*q11^3*q01+q11^4*q02 ];
  return Polynomial(k,LG);
end function;  

function linear_interpolate(Qs)
  //INPUT:  A sequence of n polynomials
  //OUTPUT: A polynomial over a split etale degree n algebra that
  //        specializes to each of the polynomials given.
  k:=BaseRing(Universe(Qs));
  KX:=PolynomialRing(k);
  pt:=[k| i : i in [0..#Qs-1]];
  h:=&*[KX.1-r: r in pt];
  A<alpha>:=quo<KX|h>;
  AX := PolynomialRing(A); XA := AX.1;
  L:=[Eltseq(Q): Q in Qs];
  d:=Maximum([#l: l in L]);
  L:=[padseq(l,d): l in L];
  return AX![Evaluate(Interpolation(pt,[l[i]:l in L]),alpha): i in [1..#L[1]]];
end function;

function CRT_interpolate(Q1,Q2)
  //INPUT:  Q1 - over base field k
  //        Q2 - a polynomial over an etale algebra of degree n over k
  //OUTPUT: A polynomial over a degree n+1 etale algebra that specializes
  //        to Q1 and Q2.
  k:=BaseRing(Q1);
  L2:=BaseRing(Q2);
  h2:=Modulus(L2);
  Pk:=Parent(Q1);
  assert BaseRing(L2) eq k;
  x1:=0;
  while Evaluate(h2,x1) eq 0 do
    x1+:=1;
  end while;
  h1:=Parent(h2).1-x1;
  one,S,T:=ExtendedGreatestCommonDivisor(h1,h2);
  r1:=T*h2;
  r2:=S*h1;
  assert one eq 1 and r1+r2 eq 1;
  d:=Maximum(Degree(Q1),Degree(Q2))+1;
  Q1L:=padseq(Eltseq(Q1),d);
  Q2L:=padseq([Pk!l: l in Eltseq(Q2)],d);
  A<alpha>:=quo<Pk|h1*h2>;
  AX := PolynomialRing(A); XA := AX.1;
  return AX![Evaluate(r1*Q1L[i]+r2*Q2L[i],alpha): i in [1..d]];
end function;

function irreducible_norm_decompositions(f)
  k:=BaseRing(f);
  error if Degree(f) notin {4,6}, "Only implemented for degree 4 and 6"; //only case tested
  if ISA(Type(k),FldFin) then
    L:=ext<k|Degree(f) div 2>;
    fct:=Factorisation(Polynomial(L,f));
    assert forall{c: c in fct | c[2] eq 1 and Degree(c[1]) eq 2};
    return [*fct[1][1]*];
  else
    //This is the more direct method, but subfields is not implemented for
    //all field types (in particular, not for relative number fields)

    //d:=ExactQuotient(Degree(f),2);
    //Kf:=ext<k|f>;
    //S:=Subfields(Kf,d);
    //res:=[* *];
    //for s in S do
    //  Append(~res,MinimalPolynomial(Kf.1,s[1]));
    //end for;
    //return res;

    d:=ExactQuotient(Degree(f),2);
    g:=MSetPolynomial(f,2);
    //we need an element in k of large enough additive order
    //so in a characteristic 0 field, 1 will do. We have already dealt
    //with finite fields above, so we assume that the generator of k does not have
    //finite additive order. That assumption need not hold, because someone could
    //adjoin a root of x^2+x+1 to FunctionField(GF(2)), for instance. In such a rare
    //situation, the code below might go into an infinite loop.
    inc:=Characteristic(k) eq 0 select 1 else k.1;
    x:=Parent(f).1;
    ft:=f;
    while not IsSquarefree(g) do
      ft:=Evaluate(ft,x+inc);
      g:=MSetPolynomial(ft,2);
    end while;
    Fg:=Factorisation(g);
    assert forall{c: c in Fg | c[2] eq 1 and Degree(c[1]) ge d};
    Fg:=[c[1]: c in Fg | Degree(c[1]) eq d];
    res:=[* *];
    for h in Fg do
      fct:=Factorisation(Polynomial(ext<k|h>,f));
      assert forall{c: c in fct | c[2] eq 1 and Degree(c[1]) ge 2};
      //A priori, one could get multiple candidates here and a priori, they may
      //lead to different norm decompositions. For degree 4, we'll always find
      //two degree 2 factors here and they clearly lead to the same decomposition
      //(they are just conjugate)
      //For degree 6, the only transitive Galois action that admits multiple
      //distinct norm decompositions is S3 acting transitively. Indeed, passing to
      //one of the cubic subfields lets f split in 3 quadratics, but they all have
      //the same splitting field and hence lead to equivalent norm decompositions
      //so the right thing to do is pick one representative for each cubic subfield
      //that we have found from degree 3 factors from MSetPolynomial(f,2).
      cnd:=[c[1]: c in fct | Degree(c[1]) eq 2];
      Append(~res, cnd[1]);
    end for;
    return res;
  end if;
end function;

function deg4_quadratic_norm_decompositions(f)
  //INPUT:  f - monic square free degree 4 polynomial
  //OUTPUT: List of monic quadratic polynomials Q over quadratic etale algebras such that
  //        f=Norm(Q). All decomposition classes are represented in the output.
  
  fct:=Factorisation(f);
  assert Degree(f) eq 4 and IsMonic(f) and forall{l: l in fct | l[2] eq 1};
  fct:=[v[1]: v in fct];
  case {*Degree(l): l in fct*}:
    when {* 1^^4 *}:
      return [*linear_interpolate([fct[v[1]]*fct[v[2]],fct[v[3]]*fct[v[4]]]) : v in [[1,2,3,4],[1,3,2,4],[1,4,2,3]]*];
    when {* 2^^2 *}:
      if IsSquare(Discriminant(fct[1])*Discriminant(fct[2])) then
        A<alpha>:=quo<Parent(fct[1])|fct[1]>;
        AX := PolynomialRing(A); XA := AX.1;
        return [* linear_interpolate([fct[1],fct[2]]) *] cat [* (XA-alpha)*(XA-r[1]): r in  Roots(Polynomial(A,fct[2])) *];
      else
        return [* linear_interpolate([fct[1],fct[2]]) *];
      end if;
    when {* 1^^2, 2 *}:
      bl:=exists(Q2){Q: Q in fct | Degree(Q) eq 2};
      assert bl;
      return [* linear_interpolate([&*[L: L in fct | Degree(L) eq 1],Q2]) *];
    when {* 1, 3 *}:
      return [* *];
    when {* 4 *}:
      Kf:=ext<BaseRing(f)| f>;
      S:=irreducible_norm_decompositions(f);
      res:=[* *];
      for h in S do
        s:=BaseRing(h);
        A<alpha>:=quo<Parent(f)| DefiningPolynomial(s)>;
        AX := PolynomialRing(A); XA := AX.1;
        stoA:=hom<s ->A | A.1>;
        Append(~res, AX![stoA(l): l in Eltseq(h)]);
      end for;
      return res;
    else
      error "Unrecognised factorisation type";
  end case;
end function; 

function deg5_cubic_norm_decompositions(f)
  //INPUT:  f - monic square free degree 5 polynomial
  //OUTPUT: f is assumed to represent a degree 6 form with a root at infinity. The
  //        list returned consists of pair <r,Q>, where r is a root of f in the ground field
  //        and Q is quadratic over a quadratic etale algebra such that
  //        f = (x-r)*Norm(Q)
  //        This data is equivalent to specifying a cubic norm decomposition of a sextic form.
  fct:=Factorisation(f);
  assert Degree(f) eq 5 and IsMonic(f) and forall{l: l in fct | l[2] eq 1};
  fct:=[v[1]: v in fct];

  //The degree 5 case is actually easy:
  //infty has to pair up with a rational root of f and we are left with finding
  //the quadratic norm decompositions of the quartic cofactor.
    res:=[* *];
  for i in [1..#fct] do
    if Degree(fct[i]) eq 1 then
      r:= - Eltseq(fct[i])[1];
      g:= &*[fct[j]: j in [1..#fct] | j ne i];
      res cat:=[* <r,Q>: Q in deg4_quadratic_norm_decompositions(g) *];
    end if;
  end for;
  return res;
end function;
  
function deg6_cubic_norm_decompositions(f)
  //INPUT:  f - monic square free degree 5 or 6 polynomial
  //OUTPUT: List of monic quadratic polynomials Q over cubic etale algebras such that
  //        f=Norm(Q). All decomposition classes are represented in the output.
  
  fct:=Factorisation(f);
  assert Degree(f) eq 6 and IsMonic(f) and forall{l: l in fct | l[2] eq 1};
  fct:=[v[1]: v in fct];

  case {*Degree(l): l in fct*}:
    when {* 1^^6 *}:  // subgroup 1
      //15 quadratic splittings possible, simply by pairing up all orbits
      return [*linear_interpolate([fct[v[1]]*fct[v[2]],fct[v[3]]*fct[v[4]],fct[v[5]]*fct[v[6]]]) : v in
               [[1,2,3,4,5,6],[2,3,4,5,1,6],[1,3,2,6,4,5],[1,3,2,4,5,6],[2,4,3,5,1,6],
                [1,4,2,3,5,6],[3,5,4,6,1,2],[2,6,1,4,3,5],[2,5,3,4,1,6],[1,5,4,6,2,3],
                [2,5,1,3,4,6],[3,6,1,2,4,5],[1,5,2,6,3,4],[3,6,1,5,2,4],[3,6,2,5,1,4]]*];
    when {* 1^^4, 2 *}: // subgroup 2
      bl:=exists(Q2){l: l in fct | Degree(l) eq 2};
      fct:=[l: l in fct | Degree(l) eq 1];
      return [*linear_interpolate([fct[v[1]]*fct[v[2]],fct[v[3]]*fct[v[4]],Q2]) : v in [[1,2,3,4],[1,3,2,4],[1,4,2,3]]*];
    when {* 2^^3 *}: // subgroups 3, 9, 14, 24
      dscs:=[Discriminant(f): f in fct];
      if exists(i){i: i in [[2,3,1],[1,3,2],[1,2,3]] |
               not(IsSquare(dscs[i[1]]*dscs[i[3]])) and not(IsSquare(dscs[i[2]]*dscs[i[3]]))} then
        Q1:=fct[i[3]];
        return [*CRT_interpolate(Q1, Q2): Q2 in deg4_quadratic_norm_decompositions(fct[i[1]]*fct[i[2]])*];
      else
        A<alpha>:=quo<Parent(fct[1])|fct[1]>;
        AX := PolynomialRing(A); XA := AX.1;
        rts:=[[r[1]: r in Roots(AX!g)]:g in fct];
        assert forall{l:l in rts | #l eq 2};
        res:=[*linear_interpolate(fct) *];
        for i in [[1,2,3],[2,3,1],[3,1,2]] do
          Append(~res,CRT_interpolate(fct[i[1]],(XA-rts[i[2]][1])*(XA-rts[i[3]][1])));
          Append(~res,CRT_interpolate(fct[i[1]],(XA-rts[i[2]][1])*(XA-rts[i[3]][2])));
        end for;
        return res;
      end if;
    when {* 1^^2, 2^^2 *}: //subgroups 4, 11
      Q1:=&*[h: h in fct | Degree(h) eq 1];
      Quar:=&*[h: h in fct | Degree(h) eq 2];
      return [*CRT_interpolate(Q1, Q2):Q2 in deg4_quadratic_norm_decompositions(Quar)*];
    when {* 1^^3, 3 *}: //subgroups 5, 15
      return [* *];
    when {* 3^^2 *}: //subgroups 6, 19, 21, 34, 36, 45
      A<alpha>:=quo<Parent(fct[1])|fct[1]>;
      AX := PolynomialRing(A); XA := AX.1;
      return [*(XA-A.1)*(XA-r[1]): r in Roots(AX!fct[2])*];
    when {* 1, 5 *}: //subgroups 7, 22, 37, 49, 54
      return [* *];
    when {* 1^^2, 4 *}: //subgroups 8, 13, 26, 31, 40
      Q1:=&*[h: h in fct | Degree(h) eq 1];
      bl:=exists(Quar){Quar: Quar in fct | Degree(Quar) eq 4};
      return [*CRT_interpolate(Q1, Q2):Q2 in deg4_quadratic_norm_decompositions(Quar)*];      
    when {* 2, 4 *}: //subgroups 10, 12, 23, 25, 27, 28, 29, 38, 41, 42, 51
      bl:=exists(Q1){Q1: Q1 in fct | Degree(Q1) eq 2};
      bl:=exists(Quar){Quar: Quar in fct | Degree(Quar) eq 4};
      return [*CRT_interpolate(Q1, Q2):Q2 in deg4_quadratic_norm_decompositions(Quar)*];      
    when {* 6 *}: //subgroups 16, 18, 30, 33, 35, 39, 43, 44, 46, 47, 48, 50, 52, 53, 55, 56
      S:=irreducible_norm_decompositions(f);
      res:=[* *];
      for h in S do
        s:=BaseRing(h);
        A<alpha>:=quo<Parent(f)| DefiningPolynomial(s)>;
        AX := PolynomialRing(A); XA := AX.1;
        stoA:=hom<s ->A | A.1>;
        Append(~res, AX![stoA(l): l in Eltseq(h)]);
      end for;
      return res;
    when {* 1, 2, 3 *}: //subgroups 17, 20, 32
      return [* *];
    else
      error "Unrecognised factorisation type";
  end case;
end function;
  
intrinsic RichelotIsogenousSurfaces(C::CrvHyp:Kernels:=false)->List,List
{}
  f:=HyperellipticPolynomials(SimplifiedModel(C));
  lc:=LeadingCoefficient(f);
  fmonic:=f/lc;
  if Degree(f) eq 5 then
    if Kernels then
      codomain:=[* *];
      splittings:=[* *];
      x:=Parent(f).1;
      for v in deg5_cubic_norm_decompositions(fmonic) do
        Append(~codomain,
                g eq 0 select 
                        sing_rich_codomain(f,v[2]:r:=v[1])
                       else HyperellipticCurve(lc*g) where g:=rich_codomain_deg5(v[1],v[2]));
        Append(~splittings,CRT_interpolate(x-v[1],v[2]));
      end for;
      return codomain,splittings;
    else
      return [* g eq 0 select 
                        sing_rich_codomain(f,v[2]:r:=v[1])
                       else HyperellipticCurve(lc*g) where g:=rich_codomain_deg5(v[1],v[2]):
                v in deg5_cubic_norm_decompositions(fmonic) *];
    end if;
  elif Degree(f) eq 6 then
    if Kernels then
      codomains:=[* *];
      splittings:=[* *];
      x:=Parent(f).1;
      for Q in deg6_cubic_norm_decompositions(fmonic) do
        Append(~codomains,
                g eq 0 select 
                        sing_rich_codomain(f,Q)
                       else HyperellipticCurve(lc*g) where g:=rich_codomain_deg6(Q));
        Append(~splittings,Q);
      end for;
      return codomains,splittings;
    else
      return [* g eq 0 select 
                         sing_rich_codomain(f,Q)
                       else HyperellipticCurve(lc*g) where g:=rich_codomain_deg6(Q):
                Q in deg6_cubic_norm_decompositions(fmonic) *];
    end if;
  else
    require Degree(f) in {5,6}: "C must be a genus 2 curve";
  end if;
end intrinsic;

intrinsic RichelotIsogenousSurfaces(J::JacHyp:Kernels:=false)->List,List
{Given a Jacobian of a genus 2 curve compute all (2,2)-isogenous abelian
surfaces.}
  if Kernels then
    codomains,splittings:=RichelotIsogenousSurfaces(Curve(J):Kernels);
    return [* ISA(Type(r),CrvHyp) select Jacobian(r) else r: r in codomains *], splittings;
  else
    return [* ISA(Type(r),CrvHyp) select Jacobian(r) else r: r in RichelotIsogenousSurfaces(Curve(J)) *];
  end if;
end intrinsic;

intrinsic RichelotIsogenousSurface(C::CrvHyp, kernel::RngUPolElt[RngUPolRes])->.
{}
  R:=BaseRing(kernel);
  f,g:=HyperellipticPolynomials(C);
  require g eq 0 and Degree(f) in {5,6}:
    "Only implemented for Jacobians of genus 2 curves with model y^2=f(x)";
  require BaseRing(R) eq BaseRing(f):
    "Kernel must be defined over the same base field as the Jacobian";
  h:=Modulus(R);
  require Degree(kernel) eq 2 and Degree(h) eq 3:
    "Kernel must be a quadratic polynomial defined over a cubic algebra";
  lc:=LeadingCoefficient(f);
  fmonic:=f/LeadingCoefficient(f);
  _,swp:=SwapExtension(Parent(kernel));
  require Norm(swp(kernel)) eq fmonic: "Invalid quadratic splitting, i.e., Norm(Q) not equal to f/LC(f)";
  if Degree(f) eq 5 then
    x:=Parent(h).1;
    LCQ:=LeadingCoefficient(kernel);
    bl:=exists(r){r[1]: r in Roots(h) | Evaluate(LCQ,r[1]) eq 0};
    assert bl;
    hquad:=ExactQuotient(h,x-r);
    A<alpha>:=quo<Parent(h)|hquad>;
    QA:=Polynomial(A,[Evaluate(l,alpha): l in Eltseq(kernel)]);
    return g eq 0 select 
                     sing_rich_codomain(f,QA:r:=r)
                  else HyperellipticCurve(lc*g) where g:=rich_codomain_deg5(r,QA);
  else
     return g eq 0 select 
                     sing_rich_codomain(f,kernel)
                  else HyperellipticCurve(lc*g) where g:=rich_codomain_deg6(kernel);
  end if;
end intrinsic;

intrinsic RichelotIsogenousSurface(J::JacHyp, kernel::RngUPolElt[RngUPolRes])->.
{Given a Jacobian of a genus 2 curve together with a description of a
 maximal isotropic exponent 2 kernel, return a description of the codomain.
 This can be again a Jacobian of a genus 2 curve, a product of elliptic curves
 or an elliptic curve over quadratic extension, representing its weil
 restriction to the ground field.
 See documentation for a description of how to describe a kernel.}
  D:=RichelotIsogenousSurface(Curve(J),kernel);
  return ISA(Type(D),CrvHyp) select Jacobian(D) else D;
end intrinsic;

/* For reference, the group numbers in deg5_6_cubic_norm_decompositions return to the
 * following representation of the subgroup lattice of Sym(6) (they are really just sorted
 * by orbit type in the routine)
lat6:=SubgroupLattice([<PermutationGroup<6|>,1,1,[]>,
<PermutationGroup<6|\[1,3,2,4,5,6]>,2,15,[1]>,
<PermutationGroup<6|\[2,1,5,6,3,4]>,2,15,[1]>,
<PermutationGroup<6|\[1,2,6,5,4,3]>,2,45,[1]>,
<PermutationGroup<6|\[1,4,2,3,5,6]>,3,20,[1]>,
<PermutationGroup<6|\[3,4,6,5,2,1]>,3,20,[1]>,
<PermutationGroup<6|\[1,5,4,2,6,3]>,5,36,[1]>,
<PermutationGroup<6|\[1,2,4,3,6,5],\[1,2,6,5,4,3]>,4,15,[4]>,
<PermutationGroup<6|\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,4,15,[4]>,
<PermutationGroup<6|\[3,2,1,4,6,5],\[5,4,6,2,3,1]>,4,45,[4]>,
<PermutationGroup<6|\[1,3,2,4,5,6],\[1,2,3,4,6,5]>,4,45,[2,4]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[2,1,4,3,6,5]>,4,45,[3,4]>,
<PermutationGroup<6|\[1,2,5,3,6,4],\[1,2,6,5,4,3]>,4,45,[4]>,
<PermutationGroup<6|\[1,2,4,3,6,5],\[2,1,3,4,5,6]>,4,45,[2,3,4]>,
<PermutationGroup<6|\[1,3,2,4,5,6],\[1,3,4,2,5,6]>,6,20,[2,5]>,
<PermutationGroup<6|\[2,1,5,6,3,4],\[6,5,1,2,4,3]>,6,20,[3,6]>,
<PermutationGroup<6|\[1,3,2,4,6,5],\[1,3,4,2,5,6]>,6,60,[4,5]>,
<PermutationGroup<6|\[2,1,4,3,6,5],\[6,5,1,2,4,3]>,6,60,[3,6]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[6,5,1,2,4,3]>,6,60,[4,6]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,3,4,2,5,6]>,6,60,[2,5]>,
<PermutationGroup<6|\[3,6,4,1,2,5],\[1,5,3,4,6,2]>,9,10,[5,6]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[1,3,5,6,4,2]>,10,36,[4,7]>,
<PermutationGroup<6|\[2,1,4,3,6,5],\[1,2,6,5,4,3],\[1,2,4,3,6,5]>,8,15,[8,12,14]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,8,15,[9,11,14]>,
<PermutationGroup<6|\[2,1,4,3,6,5],\[2,1,6,5,3,4],\[1,2,4,3,6,5]>,8,45,[10,13,14]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,2,6,5,4,3],\[1,2,4,3,6,5]>,8,45,[8,11,13]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,8,45,[8,9,10]>,
<PermutationGroup<6|\[1,2,6,5,3,4],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,8,45,[9,12,13]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[5,4,6,2,1,3],\[3,2,1,4,6,5]>,8,45,[10,11,12]>,
<PermutationGroup<6|\[6,5,1,2,4,3],\[2,1,3,4,6,5],\[1,2,4,3,6,5]>,12,15,[6,9]>,
<PermutationGroup<6|\[1,3,4,2,5,6],\[3,4,1,2,5,6],\[2,1,4,3,5,6]>,12,15,[5,8]>,
<PermutationGroup<6|\[1,3,2,4,5,6],\[1,2,3,4,6,5],\[1,4,2,3,5,6]>,12,60,[11,15,17,20]>,
<PermutationGroup<6|\[2,1,4,3,6,5],\[1,2,6,5,4,3],\[3,4,6,5,2,1]>,12,60,[12,16,18,19]>,
<PermutationGroup<6|\[1,2,4,3,6,5],\[4,5,1,3,6,2],\[1,6,3,4,2,5]>,18,10,[17,19,21]>,
<PermutationGroup<6|\[5,4,6,2,1,3],\[4,5,1,3,6,2],\[1,5,3,4,6,2]>,18,20,[16,18,21]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,6,3,4,2,5],\[3,2,4,1,5,6]>,18,20,[15,20,21]>,
<PermutationGroup<6|\[1,5,2,3,4,6],\[1,4,5,2,3,6],\[1,5,4,2,6,3]>,20,36,[13,22]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,2,6,5,4,3],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,16,45,[23,24,25,26,27,28,29]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[3,4,6,5,2,1],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,24,15,[19,27,30]>,
<PermutationGroup<6|\[1,3,2,4,5,6],\[1,4,2,3,5,6],\[2,1,4,3,5,6],\[4,3,2,1,5,6]>,24,15,[15,26,31]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,4,2,3,5,6],\[2,1,4,3,5,6],\[4,3,2,1,5,6]>,24,15,[20,23,31]>,
<PermutationGroup<6|\[1,3,2,4,6,5],\[1,4,2,3,5,6],\[2,1,4,3,5,6],\[4,3,2,1,5,6]>,24,15,[17,27,31]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[3,4,6,5,2,1],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,24,15,[18,24,30]>,
<PermutationGroup<6|\[1,2,6,5,3,4],\[3,4,6,5,2,1],\[2,1,4,3,5,6],\[1,2,4,3,6,5]>,24,15,[16,28,30]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,2,4,3,6,5],\[4,2,1,3,5,6],\[1,5,3,4,6,2]>,36,10,[32,34,36]>,
<PermutationGroup<6|\[5,4,6,2,1,3],\[1,2,4,3,6,5],\[4,2,1,3,5,6],\[1,5,3,4,6,2]>,36,10,[33,34,35]>,
<PermutationGroup<6|\[5,4,6,2,3,1],\[1,2,4,3,6,5],\[4,2,1,3,5,6],\[1,5,3,4,6,2]>,36,10,[10,34]>,
<PermutationGroup<6|\[6,5,3,4,2,1],\[4,5,1,3,6,2]>,60,6,[19,22,30]>,
<PermutationGroup<6|\[1,6,5,4,3,2],\[1,2,6,3,5,4]>,60,6,[17,22,31]>,
<PermutationGroup<6|\[1,2,6,5,4,3],\[6,5,1,2,4,3],\[1,2,3,4,6,5],\[1,2,4,3,5,6],\[2,1,3,4,5,6]>,48,15,[33,38,39,43,44]>,
<PermutationGroup<6|\[1,3,2,4,5,6],\[1,3,4,2,5,6],\[2,1,4,3,5,6],\[4,3,2,1,5,6],\[1,2,3,4,6,5]>,48,15,[32,38,40,41,42]>,
<PermutationGroup<6|\[4,2,3,1,5,6],\[5,4,6,2,1,3],\[4,6,3,1,5,2],\[4,2,1,3,5,6],\[1,5,3,4,6,2]>,72,10,[29,45,46,47]>,
<PermutationGroup<6|\[2,1,4,3,6,5],\[3,4,2,6,1,5]>,120,6,[33,37,44,48]>,
<PermutationGroup<6|\[1,2,3,4,6,5],\[1,6,4,5,3,2]>,120,6,[32,37,40,49]>,
<PermutationGroup<6|\[1,2,4,3,6,5],\[5,6,4,2,1,3]>,360,1,[39,42,47,48,49]>,
<PermutationGroup<6|\[2,3,4,5,6,1],\[2,1,3,4,5,6]>,720,1,[50,51,52,53,54,55]>]);*/
