freeze;

/*************************************************************\
*  cbrank - A program for bounding the rank of an elliptic    *
*           curve over Q with a rational 2-torsion point      *
*  Author: T. Fisher                                          *
*  This version: 27/08/2014                                   *
*                                                             *
*  Our algorithm extends that used by Cassels and Bremner     *
*  to find points of infinite order on the elliptic curves    *
*  y^2 = x^3 + p x for p a prime with p = 5 (mod 8).          *
\*************************************************************/

// TO DO (maybe): use StoredPoints, set/use MWRankBounds ?

declare verbose cbrank, 3;

import "8descent.m"
// import "/home/fisher/Magma/package/Geometry/CrvEll/8descent.m"
// import "/magma/shared/magma/package/Geometry/CrvEll/8descent.m"
    : HasRealPoint,MakeIntegral,ImageOfOneLocalPoint;

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
KM := KernelMatrix;
SymMat := SymmetricMatrix;
Det := Determinant;

GF2 := GF(2);
QQ  := Rationals();
ZZ  := Integers();
Z8  := Integers(8);

CoveringData := recformat<
   data0 : Tup, xi1 : ZZ,
   data1 : Tup, xi2 : ZZ,
   data2 : Tup, xi3 : ZZ,
   data3 : Tup, xi4 : ZZ,
   data4 : Tup >;

TABLE8 := [
   [GF2| 0,0,0],
   [],
   [GF2| 0,1,1],
   [],
   [GF2| 0,0,1],
   [],
   [GF2| 0,1,0]
];

function LocalModSquares(x,p)
  assert x ne 0;
  if p eq -1 then 
    return x lt 0 select [GF2|1] else [GF2|0];
  end if;
  x := QQ! x;
  v := Valuation(x,p);
  x := x / p^v;
  if p gt 2 then 
    x := ZZ! Integers(p)! x;
    return [GF2| v, LegendreSymbol(x,p) eq 1 select 0 else 1];
  else
    l := TABLE8[ ZZ! Z8! x ];
    l[1] := v;
    return l;
  end if;
end function;

function LocalModSquaresZ(x,p)
  assert x ne 0;
  if p eq -1 then 
    return x lt 0 select [GF2|1] else [GF2|0];
  end if;
  v := Valuation(x,p);
  x := x div p^v;
  if p gt 2 then 
    return [GF2| v, LegendreSymbol(x,p) eq 1 select 0 else 1];
  else
    l := TABLE8[ x mod 8 ];
    l[1] := v;
    return l;
  end if;
end function;

function LocalModSquaresMatrix(S,p)
  assert 0 notin S;

  if p eq -1 then 
    return Matrix(1, [GF2| x gt 0 select 0 else 1 : x in S]);
  end if;

  S := ChangeUniverse(S, ZZ);

  if p gt 2 then
    M := RMatrixSpace(GF2, #S, 2) ! 0;
    for i := 1 to #S do
      x := S[i];
      v := Valuation(x,p);
      x := x div p^v;
      M[i,1] := v;
      M[i,2] := LegendreSymbol(x,p) eq 1 select 0 else 1;
    end for;
    return M;

  else // p = 2
    M := RMatrixSpace(GF2, #S, 3) ! 0;
    for i := 1 to #S do
      x := S[i];
      v := Valuation(x,p);
      x := x div p^v;
      M[i,1] := v;
      case x mod 8 :
      when 1 : 
        M[i,2] := 0;
        M[i,3] := 0;
      when 3 : 
        M[i,2] := 1;
        M[i,3] := 1;
      when 5 : 
        M[i,2] := 0;
        M[i,3] := 1;
      when 7 : 
        M[i,2] := 1;
        M[i,3] := 0;
      end case;
    end for;
    return M;

  end if;
end function;

IM1 := MatrixRing(GF2,1)!1;
IM2 := MatrixRing(GF2,2)!1;
IM3 := MatrixRing(GF2,3)!1;
NM1 := Matrix(1,[GF2|]);
NM2 := Matrix(2,[GF2|]);
NM3 := Matrix(3,[GF2|]);

HNRS2     := Matrix(3,[GF2|0,0,1,0,1,0,1,0,0]);
HNRS1mod4 := Matrix(2,[GF2|0,1,1,0]);
HNRS3mod4 := Matrix(2,[GF2|1,1,1,0]);

function HNRS(p)
  if p eq -1 then 
    return IM1;
  elif p eq 2 then 
    return HNRS2;
  elif p mod 4 eq 1 then
    return HNRS1mod4;
  else
    return HNRS3mod4;
  end if;
end function;

/*
function MyPrimeDivisors(x,pp)
  assert IsIntegral(x);
  S := [];
  for p in pp do
    v := Valuation(x,p);
    if v gt 0 then  
      x := x/p^v;
      S cat:= [p];
    end if;
  end for;
  T := PrimeDivisors(Integers()!x);
  return Sort(S cat T);
end function;
*/

function IsSupportedOnModSquares(S,x)
  x := Rationals()!x;
  if x eq 0 then return false; end if;
  for p in S do
    if p eq -1 then 
      x := Abs(x);
    else
      x /:= p^Valuation(x,p);
    end if;
  end for;
  return IsSquare(x);
end function; 

function EllChangeCurve(urst,E)
  u,r,s,t := Explode(urst);
  Weqn := Equation(E);
  R<x,y,z> := Parent(Weqn);
  mons := [x*y*z,x^2*z,y*z^2,x*z^2,z^3];
  Weqn2 := (1/u^6)*Evaluate(Weqn,[u^2*x+r*z,u^3*y+u^2*s*x+t*z,z]);
  a1,ma2,a3,ma4,ma6 := Explode([MC(Weqn2,mon): mon in mons]);
  return EllipticCurve([a1,-ma2,a3,-ma4,-ma6]);
end function;

function EllChangePoint(urst,pt);
  u,r,s,t := Explode(urst);
  pt := Eltseq(pt);
  x := pt[1]/pt[3];
  y := pt[2]/pt[3];
  x1 := (1/u^2)*(x - r); 
  y1 := (1/u^3)*(y - u^2*s*x1 - t); 
  return [x1,y1];
end function;

function MyDegree(QI,f)
  error "This routine only used in testing";
  R := PolynomialRing(QI);
  assert Parent(f) eq R;
  X := Scheme(Proj(R),Equations(QI) cat [f]);
  J := Radical(Ideal(X));
  Xred := Scheme(Proj(R),Basis(J));
  return Degree(Xred);
end function;

function MyDouble(QI,R);
  MM := [ChangeRing(M,R): M in Matrices(QI)];
  f := Det(R.1*MM[1] + R.2*MM[2]);
  return GenusOneModel(f);
end function;

function SmallPointSearch(Q)
  L := StandardLattice(4);
  found := false;
  for N in [1..10] do 
    SV := ShortVectors(L, N, N);
    for tup in SV do 
      soln := Eltseq(tup[1]);
      if Evaluate(Q,soln) eq 0 then
        found := true; 
        break N;
      end if;
    end for;
  end for;
  return found,soln;
end function;

function SolveQuadraticForm(Q)
  R := Parent(Q);
  assert BaseRing(R) eq Rationals();
  Q /:= RationalGCD(Coefficients(Q));
  n := Rank(R);
  assert n in {3,4};
  assert Det(SymMat(Q)) ne 0;
  vprint cbrank, 3 : "Solving quadratic form of rank",n;
  vprint cbrank, 3 : "Q =",Q;
  case n :
    when 3 :
      C := Conic(Proj(R),Q);
      soln := Eltseq(RationalPoint(C));
    when 4 :
      found,soln := SmallPointSearch(Q);
      if not found then
        V := IsotropicSubspace(Q);
        soln := Eltseq(Basis(V)[1]);
      end if;
      size := Maximum([Log(Abs(x)): x in soln | x ne 0]);
      if size gt 50 then 
        vprintf cbrank,3 : "Solution: %o\n",soln;
        vprint cbrank,3 : "Looking for a smaller solution"; 
//                         but not in an intelligent way!
        for ctr in [1..10] do
          T := RandomSLnZ(4,10,5);
          TT := ChangeRing(T,Rationals());
          V := IsotropicSubspace(Q^TT);
          soln1 := Eltseq(Basis(V)[1]*(Transpose(T)));
          size1 := Maximum([Log(Abs(x)): x in soln1 | x ne 0]);
          if size1 lt size then 
   	    soln := soln1;
            size := size1;
            if size lt 20 then break; end if;
          end if;
        end for;
      end if;
  end case;
  d := RationalGCD(soln);
  soln := [x/d : x in soln];
  assert Evaluate(Q,soln) eq 0;
  vprintf cbrank,3 : "Solution: %o\n",soln;
  return soln;
end function;

function MySquareFree(x)
  x := Rationals()!x;
  if x eq 0 then return 0,_; end if;
  return PowerFreePart(x,2);
end function;

function Delta(f)
  R<x,y> := Parent(f);
  coeffs := [MC(f,mon): mon in [x^2,x*y,y^2]];
  a,b,c := Explode(coeffs);
  return b^2 - 4*a*c;
end function;

function ReductionMatrix(f)
  R<x,y> := Parent(f);
  coeffs := [Integers()|MC(f,mon): mon in [x^2,x*y,y^2]];
  a,b,c := Explode(coeffs);
  D := b^2 - 4*a*c;
  if IsSquare(D) then return 0; end if;
  if a lt 0 and D lt 0 then 
    Q := BinaryQuadraticForms(D)![-a,-b,-c];
  else
    Q := BinaryQuadraticForms(D)![a,b,c];
  end if;
  _,mat := Reduction(Q);
  return ChangeRing(mat,Rationals());
end function;

function SimonLevel(Q,ff)
  R2<x,y> := Universe(ff);
  R3<X,Y,Z> := Parent(Q);
  mons := [x^2,x*y,y^2];
  q := Matrix(3,3,[MC(f,mon): mon in mons,f in ff]);
  Q := SymmetricMatrix(Q);
  Q0 := SymmetricMatrix(Y^2 - X*Z);
  detQ := Determinant(Q);
  detq := Determinant(q);
  mu_squared := (Transpose(q)*Q*q)[2,2]/(-4*detQ);
  mu_cubed := Determinant(q)/(-4*detQ);
  mu := mu_cubed/mu_squared;
  assert Transpose(q)*Q*q eq (-4*detQ)*mu^2*Q0;
  assert Determinant(q) eq (-4*detQ)*mu^3;
  Qstar := Adjoint(Q);
  for i in [1..3] do
    assert Delta(ff[i]) eq -4*Qstar[i,i]*mu^2;
  end for;
  return mu;
end function;

function SimonParametrisation(Q,soln:
    R := PolynomialRing(Rationals(),2))
  R3<X,Y,Z> := Parent(Q);
  assert BaseRing(R3) eq Rationals();
  assert forall{x : x in Coefficients(Q) | IsIntegral(x)};
  soln := Eltseq(soln);
  d := RationalGCD(soln);
  soln := [x/d : x in soln];  
  mat := Matrix(Integers(),1,3,soln);
  _,_,T := SmithForm(mat);
  T := ChangeRing(Transpose(Adjoint(T)),Rationals());
  assert Determinant(T) eq 1;
  Q1 := Q^T;
  mons := [X^2,X*Y,X*Z,Y^2,Y*Z,Z^2];
  _,a,b,c,d,e := Explode([MC(Q1,mon): mon in mons]);
  q := T*Matrix(3,3,[c,d,e,-a,-b,0,0,-a,-b]);
  mons := [R.1^2,R.1*R.2,R.2^2];
  ff := [&+[q[i,j]*mons[j]: j in [1..3]]: i in [1..3]];
  for k in [3,1,2] do
    mat := ReductionMatrix(ff[k]);
    if mat ne 0 then 
      ff := [f^mat : f in ff];
      break;
    end if;
  end for;
  assert SimonLevel(Q,ff) eq 1;
  return ff;
end function;

function NiceRepForPoint(pt,prec)
  L<delta> := Universe(pt);
  d := Integers()!(L.1^2);
  OL := RingOfIntegers(L);
  I := ideal<OL|pt>;
  RR := RealField(prec);
  elts := [L| x : x in Basis(I)];
  mymat := Matrix(RR,2,2,
    [[Eltseq(x)[1],Eltseq(x)[2]*Sqrt(RR!Abs(d))]: x in elts]);
  _,T := LLL(mymat);
  kk := [&+[T[i,j]*elts[j]: j in [1..2]]: i in [1..2]];
  pt := [x/kk[1]: x in pt];    
  return pt;
end function;

function NiceMatrix(pt,prec)
  L<delta> := Universe(pt);
  d := Integers()!(L.1^2);
  OL := RingOfIntegers(L);
  I := ideal<OL|pt>;
  RR := RealField(prec);
  elts := [L| x : x in Basis(I)];
  mymat := Matrix(RR,2,2,
    [[Eltseq(x)[1],Eltseq(x)[2]*Sqrt(RR!Abs(d))]: x in elts]);
  _,T := LLL(mymat);
  kk := [&+[T[i,j]*elts[j]: j in [1..2]]: i in [1..2]];
  pt := [x/kk[1]: x in pt];    
  a,b,c := Explode(pt);
  I := ideal<OL|a,b>;
  elts := [L| x : x in Basis(I)];
  a1,a2 := Explode(Eltseq(a));
  b1,b2 := Explode(Eltseq(b));
  k1,k2 := Explode(Eltseq(elts[1]));
  mm := Matrix(2,4,[a1,d*a2,b1,d*b2,a2,a1,b2,b1]);
  rr := RationalGCD(Eltseq(mm) cat [k1,k2]);
  mat := ChangeRing(mm/rr,Integers());
  vec := Vector(Integers(),2,[2*k1/rr,2*k2/rr]);
  soln := Eltseq(Solution(Transpose(mat),vec));
  r := soln[1]+delta*soln[2];
  s := soln[3]+delta*soln[4];
  k := r*a + s*b;
  J := ideal<OL|k,c>;
  elts := [L| x : x in Basis(J)];
  a1,a2 := Explode(Eltseq(k));
  b1,b2 := Explode(Eltseq(c));
  k1,k2 := Explode(Eltseq(elts[1]));
  mm := Matrix(2,4,[a1,d*a2,b1,d*b2,a2,a1,b2,b1]);
  rr := RationalGCD(Eltseq(mm) cat [k1,k2]);
  mat := ChangeRing(mm/rr,Integers());
  vec := Vector(Integers(),2,[2*k1/rr,2*k2/rr]);
  soln := Eltseq(Solution(Transpose(mat),vec));
  t := soln[1]+delta*soln[2];
  u := soln[3]+delta*soln[4];
  one := t*k + u*c;
  MM := Matrix(3,3,[a,b,c,-s,r,0,-u*a/k,-u*b/k,t]);
  assert Determinant(MM) eq one;
  return Transpose(MM);
end function;

function ApproxSimonParam(Q,pt)
  T := NiceMatrix(pt,2000);
  L := Universe(pt);
  R := PolynomialRing(L,2);
  R3<X,Y,Z> := Parent(Q);
//  print "Determinant(T) =",Determinant(T);
  Q1 := Q^T;
  assert MC(Q1,X^2) eq 0;
  mons := [X^2,X*Y,X*Z,Y^2,Y*Z,Z^2];
  _,a,b,c,d,e := Explode([MC(Q1,mon): mon in mons]);
  q := T*Matrix(3,3,[c,d,e,-a,-b,0,0,-a,-b]);
  mons := [R.1^2,R.1*R.2,R.2^2];
  ff := [&+[q[i,j]*mons[j]: j in [1..3]]: i in [1..3]];
//  print "Simon Level =",SimonLevel(Q,ff);
  return ff;
end function;

function MyPreImage(ff,soln)
  R<x,y> := Universe(ff);
  mons := [x^2,x*y,y^2];
  mat := Matrix(3,3,[MC(f,mon): f in ff,mon in mons]);
  soln := Solution(mat,Vector(3,Eltseq(soln)));
  pt := [soln[1],soln[2]];
  if pt[1] eq 0 then 
    pt := [soln[2],soln[3]];
  end if;
  d := RationalGCD(&cat[Eltseq(x): x in pt]);
  pt := [x/d: x in pt];
  if pt[1] eq 0 then pt := [0,1]; end if;
  if pt[2] eq 0 then pt := [1,0]; end if;
  return pt;
end function;

function MyPolarise(f,xx,yy)
  Df := [Evaluate(Derivative(f,i),xx): i in [1..2]];
  return (1/2)*&+[Df[i]*yy[i]: i in [1..#yy]];
end function;

function MyRowReduce(mat)
  Q := Rationals();
  L := PureLattice(Lattice(mat));
  return LLL(Matrix(Q,[Eltseq(x): x in Basis(L)]));
end function;

function MinRedPolys(ff,d)
  R := Universe(ff);
  mons := MD(R,d);
  mat := Matrix(#ff,#mons,[MC(f,mon): mon in mons,f in ff]);
  mat := MyRowReduce(mat);
  n := Nrows(mat);
  ff := [&+[mat[i,j]*mons[j]: j in [1..#mons]]: i in [1..n]];
  return ff;
end function;

function MyRatio(QI,f,g)
  R := PolynomialRing(QI);
  assert Parent(f) eq R;
  assert Parent(g) eq R;
  assert TotalDegree(f) eq 2;
  assert TotalDegree(g) eq 2;
  mons := MD(R,2);
  qq := Equations(QI) cat [g];
  mat := Matrix(#qq,#mons,[MC(q,mon): mon in mons,q in qq]);
  vec := Vector(#mons,[MC(f,mon): mon in mons]);
  soln := Solution(mat,vec);
  return Eltseq(soln)[3];
end function;

function IsScalarMultiple(QI,f,g)
  R := PolynomialRing(QI);  
  assert Parent(f) eq R;
  assert Parent(g) eq R;
  assert TotalDegree(f) eq 2;
  assert TotalDegree(g) eq 2;
  mons := MD(R,2);
  qq := Equations(QI) cat [f,g];
  mat := Matrix(#qq,#mons,[MC(q,mon): mon in mons,q in qq]);
  km := KernelMatrix(mat);
  if Nrows(km) ne 1 or km[1,3] eq 0 or km[1,4] eq 0 then 
    return false,_;
  else
    return true,-km[1,4]/km[1,3];
  end if;
end function;

function ComplementaryQuadric(QI,ff);
  R := PolynomialRing(QI);
  assert Universe(ff) eq R;
  qq := Equations(QI);
  mons := MD(R,2);
  Z := Integers();
  mat1 := Matrix(Z,3,10,[MC(f,mon): mon in mons,f in ff]);
  mat2 := Matrix(Z,2,10,[MC(q,mon): mon in mons,q in qq]);
  soln := Solution(mat1,mat2);
  mat := ChangeRing(soln,Integers());
  _,_,T := SmithForm(mat);
  T := T^(-1);
  return &+[T[3,i]*ff[i]: i in [1..3]];
end function;
  
function MinRedQuadric(QI,f)
  assert forall{x : x in Eltseq(QI) | IsIntegral(x)};
  R := PolynomialRing(QI);
  assert Parent(f) eq R;
  eqns := Equations(QI);
  ff := MinRedPolys(eqns cat [f],2);
  g := ComplementaryQuadric(QI,ff);
  return MyRatio(QI,f,g)*g;
end function;

function MinRed(g1m)
  n := Degree(g1m);
  R := PolynomialRing(g1m);
  vprint cbrank,3 : "Minimising";
  g1min,tr1 := Minimise(g1m);
  vprint cbrank,3 : "Reducing";
//  vprint cbrank,3 : Eltseq(g1min);
  g1red,tr2 := Reduce(g1min);
  g1red := GenusOneModel(n,Eltseq(g1red):PolyRing:=R);
  return g1red,tr2*tr1;
end function;

function ConvertQuadrics(QI1,QI2,qq1,qq2,ff)
  assert forall{x : x in Eltseq(QI1) | IsIntegral(x)};
  assert forall{x : x in Eltseq(QI2) | IsIntegral(x)};
  R := PolynomialRing(QI1);
  mons := MD(R,2);
  qq := qq2 cat Equations(QI2);
  mat1 := Matrix(#qq,#mons,[MC(q,mon): mon in mons,q in qq]);
  mat2 := Matrix(#ff,#mons,[MC(q,mon): mon in mons,q in ff]);
  soln := Solution(mat1,mat2);
  gg := [&+[soln[i,j]*qq1[j]: j in [1..8]]: i in [1..#ff]];
  return [MinRedQuadric(QI1,g): g in gg];
end function;

function OddQuadrics(QI,evenquads,oddq,ff)
  R := PolynomialRing(QI);
  mons2 := MD(R,2);
  mons4 := MD(R,4);
  qq := Equations(QI) cat [oddq];
  qq := [mon*q : mon in mons2,q in qq];
  mat1 := Matrix(#qq,#mons4,[MC(q,mon): mon in mons4,q in qq]);
  ff := [Evaluate(f,evenquads): f in ff];
  mat2 := Matrix(#ff,#mons4,[MC(f,mon): mon in mons4,f in ff]);
  soln := Solution(mat1,mat2);
  gg := [&+[soln[i,20+j]*mons2[j]: j in [1..10]]: i in [1..4]];
  return [MinRedQuadric(QI,g): g in gg];
end function;

function MyComponents(f,RQ)
  RL := Parent(f);
  L := BaseRing(RL);
  d := Degree(L);
  assert Rank(RQ) eq Rank(RL);
  coeffs := [Eltseq(x): x in Coefficients(f)];
  mons := ChangeUniverse(Monomials(f),RQ); 
  ff := [&+[coeffs[i][j]*mons[i]: i in [1..#mons]]: j in [1..d]];
  bb := Basis(L);
  assert f eq &+[bb[i]*(RL!ff[i]): i in [1..d]];
  return ff;
end function;

function MyRestrictScalars(f,RQ)
  RL := Parent(f);
  L := BaseRing(RL);
  n := Rank(RL);
  d := Degree(L);
  S := PolynomialRing(L,n*d);
  bb := Basis(L);
  subst := [&+[bb[j]*S.(i*d + j) : j in [1..d]]: i in [0..n-1]];
  f := Evaluate(f,subst);
  return MyComponents(f,RQ);
end function;

function TangentCoefficients(ff,pt)
  R := Universe(ff);
  mons := MD(R,2);
  mat := Matrix(3,3,[MC(f,mon): mon in mons,f in ff]);
  lambda := pt[2]*R.1 - pt[1]*R.2;
  vec := Vector(3,[MC(lambda^2,mon): mon in mons]);
  aa := Eltseq(Solution(mat,vec));
  assert &+[aa[i]*ff[i]: i in [1..3]] eq lambda^2;
  return aa;
end function;

function MyNormEquation(L,b)
  R3<X,Y,Z> := PolynomialRing(Rationals(),3);
  a := Rationals()!(L.1^2);
  Q := X^2 - a*Y^2 - b*Z^2;
  soln := SolveQuadraticForm(Q);
  x,y,z := Explode(soln);
  pi := (x + y*L.1)/z;
  assert Norm(pi) eq b;
  return pi;
end function;

function NewQuadricIntersection(QI,BQF,f)

// QI is a quadric intersection in P^3 with "doubling" 
// y^2 = g(x,z) where g is a binary quartic.
// BQF is a binary quadratic form that is a factor of g.
// The roots of BQF correspond to a pair of singular
// quadratic forms Q_1 and Q_2 in the pencil defining QI.
// These are either defined over the rationals, or
// over a quadratic field, depending whether or not the
// discriminant of BQF is a square.
// The third argument is a quadratic form on P^3 that
// (modulo the ideal of QI) is the product of two linear
// forms l_1 and l_2, where l_i is the equation of a tangent
// plane to Q_i (at a smooth rational point on Q_i).
//
// This function returns a new quadric intersection QInew,
// a sequence of 4 quadrics qq (defining a morphism of degree 2
// from QInew to QI), and a quadric g such that f ( qq ) = g^2 
// modulo the ideal of QInew.

  R2<x,y> := Parent(BQF);
  BQF /:= RationalGCD(Coefficients(BQF));
  mons := [x^2,x*y,y^2];
  a,b,c := Explode([MC(BQF,m): m in mons]);
  d,e := MySquareFree(b^2 - 4*a*c);
  R4<x1,x2,x3,x4> := PolynomialRing(QI);
  MM := Matrices(QI) cat [2*SymMat(f)];
  if d ne 1 then 
    L := QuadraticField(Integers()!d); delta := L.1;
    conjL := hom<L->L|-delta>;
    R3L<u1,u2,u3> := PolynomialRing(L,3);
    R4L<z1,z2,z3,z4> := PolynomialRing(L,4);
    MM := [ChangeRing(M,L): M in MM];
    M0 := (-b + e*delta)*MM[1] + 2*a*MM[2];
    assert Rank(M0) eq 3;
    _,_,T := SmithForm(KernelMatrix(M0));
    linforms := [&+[T[i,j]*R4L.i: i in [1..4]]: j in [2..4]];
    MM := [U*M*Transpose(U): M in MM] where U is T^(-1);
    M0 := (-b + e*delta)*MM[1] + 2*a*MM[2];
    eqn_conic := &+[M0[i+1,j+1]*R3L.i*R3L.j: i,j in [1..3]];
    C := Conic(Proj(R3L),eqn_conic);
    J := ideal<R4L|[&+[M[i,j]*R4L.i*R4L.j: i,j in [1..4]]: M in MM]>;
    JJ := EliminationIdeal(J,{z2,z3,z4});
    X := Scheme(Proj(R3L),[Evaluate(f,[0,u1,u2,u3]): f in Basis(JJ)]);
    solns := Points(X);
    assert #solns ge 1;
    pt := Eltseq(solns[1]);
    QQ := ApproxSimonParam(eqn_conic,pt);
    assert Evaluate(eqn_conic,QQ) eq 0;
    nu := 0;
    for soln in solns do
      pt := MyPreImage(QQ,Eltseq(soln));
      pt := NiceRepForPoint(ChangeUniverse(pt,L),2000);
      aa := TangentCoefficients(QQ,pt);
      elts := [Basis(L)[i]*a: a in aa,i in [1..2]];
      mat := Matrix(6,2,[Eltseq(e): e in elts]);
      b := L!(Eltseq(LLL(mat)[1]));
      ell1 := &+[aa[i]*linforms[i]: i in [1..3]];
      ell2 := &+[conjL(MC(ell1,R4L.i))*R4L.i: i in [1..4]];
      ff := R4!(ell1*ell2);
      flag,nu := IsScalarMultiple(QI,f,ff);
      if flag then break; end if;
    end for;
    assert nu ne 0;
    R2L<la,mu> := Universe(QQ);
    w := pt[2]*la - pt[1]*mu;
    assert &+[aa[i]*QQ[i]: i in [1..3]] eq w^2;
    pi := (1/b)*MyNormEquation(L,nu*Norm(b));
    QQ := [(1/pi)*Q : Q in QQ];
    LHS := &cat[MyComponents(l,R4): l in linforms];
    RHS := &cat[MyRestrictScalars(Q,R4): Q in QQ];
  else
    R3<u1,u2,u3> := PolynomialRing(Rationals(),3);
    R2Z := PolynomialRing(Integers(),2);
    factBQF := Factorization(R2Z!BQF);
    aa,bb := Explode([R2|p[1]: p in factBQF]);
    M1 := MC(aa,y)*MM[1] - MC(aa,x)*MM[2];
    M2 := MC(bb,y)*MM[1] - MC(bb,x)*MM[2];
    M3 := MM[3];
    assert Rank(M1) eq 3;
    assert Rank(M2) eq 3;
    gg := [];
    hh := [];
    LHS := [];
    RHS := [];
    MM := [M1,M2,M3];
    for ctr in [1,2] do
      _,_,T := SmithForm(KernelMatrix(MM[1]));
      linforms := [&+[T[i,j]*R4.i: i in [1..4]]: j in [2..4]];
      MM := [U*M*Transpose(U): M in MM] where U is T^(-1);
      eqn_conic := &+[MM[1][i+1,j+1]*R3.i*R3.j: i,j in [1..3]];
      J := ideal<R4|[&+[M[i,j]*R4.i*R4.j: i,j in [1..4]]: M in MM]>;
      JJ := EliminationIdeal(J,{x2,x3,x4});
      X := Scheme(Proj(R3),[Evaluate(f,[0,u1,u2,u3]): f in Basis(JJ)]);
      solns := Points(X);
      assert #solns ge 1;      
      QQ := SimonParametrisation(eqn_conic,solns[1]:R:=R2);
      assert Evaluate(eqn_conic,QQ) eq 0;
      pts := [MyPreImage(QQ,soln): soln in solns];
      aaa := [TangentCoefficients(QQ,pt): pt in pts];
      subst := ctr eq 1 select [x1,x2] else [x3,x4];
      gg cat:= [[&+[aa[i]*linforms[i]: i in [1..3]]: aa in aaa]];
      hh cat:= [[pt[2]*x - pt[1]*y: pt in pts]];
      LHS cat:= linforms;
      RHS cat:= [Evaluate(Q,subst): Q in QQ];
      MM := [M2,M1,M3];
    end for;
    nu := 0;
    for i in [1..#gg[1]] do
      for j in [1..#gg[2]] do
	ff := gg[1][i]*gg[2][j];
        flag,nu := IsScalarMultiple(QI,f,ff);
        if flag then 
  	  w1 := hh[1][i];
          w2 := hh[2][j];
          break i; 
        end if;
      end for;
    end for;
    assert nu ne 0;
    for i in [4..6] do RHS[i] /:= nu; end for;
  end if;
  mat := Matrix(6,4,[MC(l,R4.i): i in [1..4],l in LHS]);
  _,T,_ := SmithForm(mat);
  LHS := [&+[T[i,j]*LHS[j]: j in [1..6]]: i in [1..6]];
  assert LHS eq [x1,x2,x3,x4,0,0];
  RHS := [&+[T[i,j]*RHS[j]: j in [1..6]]: i in [1..6]];
  QInew := GenusOneModel([RHS[5],RHS[6]]);
  if d ne 1 then 
    ell1 := Evaluate(w,[z1 + delta*z2,z3 + delta*z4]);
    ell2 := &+[conjL(MC(ell1,R4L.i))*R4L.i: i in [1..4]];
    g := R4!(ell1*ell2);
  else
    g := Evaluate(w1,[x1,x2])*Evaluate(w2,[x3,x4]);
  end if;
  QInew,tr := MinRed(QInew);
  qq := [RHS[i]^Transpose(tr`Matrix): i in [1..4]];
  g := g^Transpose(tr`Matrix);
  qq := [MinRedQuadric(QInew,f): f in qq];
  d := RationalGCD(&cat[Coefficients(f): f in qq]);
  qq := [(1/d)*f : f in qq];
  g := (1/d)*g;
  I := Ideal(Curve(QInew));
  eqn1,eqn2 := Explode(Equations(QI));
  assert Evaluate(eqn1,qq) in I;
  assert Evaluate(eqn2,qq) in I;
  assert Evaluate(f,qq) - g^2 in I;
  return QInew,qq,g;
end function;

function TangentForm(Q,soln)
  R4 := Parent(Q);
  assert Evaluate(Q,soln) eq 0; 
  coeffs := [Evaluate(Derivative(Q,i),soln): i in [1..4]];
  coeffs := [x/d: x in coeffs] where d is RationalGCD(coeffs);
  return &+[coeffs[i]*R4.i: i in [1..4]];
end function; 

function IsCompanionQI(qidata)
  QI1,QI2,qq1,qq2 := Explode(qidata);
  P7 := ProjectiveSpace(Rationals(),7);
  psi1 := map<Curve(QI1)->P7|qq1>;
  psi2 := map<Curve(QI2)->P7|qq2>;
  I1 := Ideal(Image(psi1));
  I2 := Ideal(Image(psi2));
  return I1 eq I2;
end function;  

function BarScalar(QI1,QI2,qq1,qq2,maps)
error "This routine only used in testing";
  rr,ss,tt,uu := Explode(maps);
  LHS := [Evaluate(q,rr): q in qq1];
  RHS := [Evaluate(q,ss): q in qq2];
  e1 := MyRatio(QI1,LHS[1],RHS[1]);
  LHS := [Evaluate(q,tt): q in qq1];
  RHS := [Evaluate(q,uu): q in qq2];
  e2 := MyRatio(QI2,LHS[1],RHS[1]);
  flag,nu := IsSquare(e1/e2);
  assert flag;
  return nu;
end function;

function MyLevel(a,b,p)
  v1 := Valuation(a,p);
  v2 := Valuation(b,p);
  return Minimum([Floor(v1/2),Floor(v2/4)]);
end function; 

function EllData(E,T)
  assert 2*T eq E!0;
  aa := aInvariants(E);
  assert forall{a : a in aa | IsIntegral(a)};
  a1,_,a3 := Explode(aInvariants(E));
  tr := [1/2,0,-a1/2,-a3/2];
  E1 := EllChangeCurve(tr,E);
  T1 := EllChangePoint(tr,T);
  assert T1[2] eq 0;
  tr := [1,T1[1],0,0];
  E2 := EllChangeCurve(tr,E1);
  _,a,_,b,_ := Explode(aInvariants(E2));
  assert aInvariants(E2) eq [0,a,0,b,0];
  repeat 
    a := ZZ! a;
    b := ZZ! b;
    S1 := PrimeDivisors(b);
    S2 := PrimeDivisors(a^2-4*b);
    S := {2} join Set(S1) join Set(S2);
    S := Sort(SetToSequence(S));
    u := &*[p^MyLevel(a,b,p): p in S];
    if u ne 1 then 
      a := (1/u)^2*a;
      b := (1/u)^4*b;
    end if;
  until u eq 1;
  return <[a,b],[-1] cat S>;
end function;

function CoverData1(elldata,xi1,dual) 
  RR2<u,v,w> := elldata[5,2]; 
  R3<X,Y,Z> := PolynomialRing(Rationals(),3);
  a,b := Explode(elldata[1]);
  if not dual then a,b := Explode([-2*a,a^2-4*b]); end if;
  Q := xi1*X^2 + a*X*Y + (b/xi1)*Y^2 - Z^2;
  soln := SolveQuadraticForm(Q);
  ff := SimonParametrisation(Q,soln:R:=elldata[5,1]);
  f,g,h := Explode(ff);
  assert Delta(f) eq 4*b/xi1;
  assert Delta(g) eq 4*xi1;
  assert Delta(h) eq a^2 - 4*b;
  assert xi1*f^2 + a*f*g + (b/xi1)*g^2 eq h^2;
  eqn := w^2 - Evaluate(f*g,[u,v]);
  return <GenusOneModel(eqn),ff>;
end function;

function AlignDoubling(QInew,QIold,BQold,tt,map,R2)
  R4 := PolynomialRing(QInew);
  BQnew := MyDouble(QInew,R2);
// psi := map<Curve(QIold)->Curve(BQold)|map>;
  vv := [Evaluate(map[i],tt): i in [1..2]];
  TT := SL4Covariants(QInew);
  ww := [TT[2],-TT[3]];
  qq := Equations(QInew) cat vv;
  mons := MD(R4,2);
  mat1 := Matrix(#qq,#mons,[MC(q,mon): mon in mons,q in qq]);
  mat2 := Matrix(#ww,#mons,[MC(q,mon): mon in mons,q in ww]);
  soln := Solution(mat1,mat2);
  M := Matrix(2,2,[soln[j,i+2]:i,j in [1..2]]);
  _,trans := IsTransformation(2,<1,M>);
  BQtemp := trans*BQnew;
  mat := Matrix(2,5,[Eltseq(BQ): BQ in [BQtemp,BQold]]);
  km := KernelMatrix(mat);
  flag,lambda := IsSquare(-km[1,1]/km[1,2]);
  assert flag;
  _,tr := IsTransformation(2,<lambda,M>);
  assert tr*BQnew eq BQold;
  return tr;
end function;

function CoverData2Subroutine(f,xi2)
  R2<x,z> := Parent(f);
  R3<X,Y,Z> := PolynomialRing(Rationals(),3);
  Q := Evaluate(f,[X,Y]) - xi2*Z^2;				       
  soln := SolveQuadraticForm(Q);
  pp := SimonParametrisation(Q,soln:R := R2);
  assert Det(z*SymMat(pp[1]) - x*SymMat(pp[2])) eq -xi2*f; 
  return pp;
end function;

function CoverData2(alpha)
  xi2 := alpha`xi2;
  f,g,h := Explode(alpha`data1[2]);
  RR2<u,v,w> := PolynomialRing(alpha`data1[1]);
  pp := CoverData2Subroutine(f,xi2);
  assert Evaluate(f,[pp[1],pp[2]]) eq xi2*pp[3]^2;
  vprint cbrank,3 : "p1 =",pp[1];
  vprint cbrank,3 : "p2 =",pp[2];
  vprint cbrank,3 : "p3 =",pp[3];
  qq := CoverData2Subroutine(g,xi2);
  vprint cbrank,3 : "q1 =",qq[1];
  vprint cbrank,3 : "q2 =",qq[2];
  vprint cbrank,3 : "q3 =",qq[3];
  assert Evaluate(g,[qq[1],qq[2]]) eq xi2*qq[3]^2;
  quartic := xi2*Evaluate(f,[qq[1],qq[2]]);
  C2 := GenusOneModel(w^2 - Evaluate(quartic,[u,v]));
  return <C2,pp,qq>;
end function;

function QuadricIntersectionD1(R,a,b,xi1)
  R<x1,x2,x3,x4> := R;
  q1 := x1*x3 - x2^2;
  q2 := x4^2 - xi1*x1^2 - a*x1*x3 - (b/xi1)*x3^2;
  return GenusOneModel([q1,q2]);
end function;

function QuadricIntersectionD1star(R,f,g)
  R<x1,x2,x3,x4> := R;
  q1 := x1*x4 - x2*x3;
  q2 := Evaluate(f,[x1,x2]) - Evaluate(g,[x3,x4]);
  return GenusOneModel([q1,q2]);
end function;

function QuadricIntersectionD2(R,ff,xi2)
  R<x1,x2,x3,x4> := R;
  ff := [Evaluate(f,[x1,x2]): f in ff];
  q1 := ff[1] - xi2*x3^2;
  q2 := ff[2] - xi2*x4^2;
  qq1 := [ff[1],xi2*x3*x4,ff[2],ff[3],x1*x4,x2*x4,x1*x3,x2*x3];
  return GenusOneModel([q1,q2]),qq1;
end function;

function QuadricIntersectionD3(R,pp,qq,xi3)
  R<x1,x2,x3,x4> := R;
  aa := TangentCoefficients(pp,[0,1]);
  bb := TangentCoefficients(qq,[0,1]);
  pp := [Evaluate(p,[x1,x2]): p in pp];
  qq := [Evaluate(q,[x3,x4]): q in qq];
  eqns := [pp[1] - xi3*qq[1],pp[2] - xi3*qq[2]];
  rr := [pp[1],pp[2],pp[3],xi3*qq[3]];
  tgt1 := aa[1]*x1 + aa[2]*x2 + aa[3]*x3;
  tgt2 := bb[1]*x1 + bb[2]*x2 + bb[3]*x4;
  f3 := tgt1*tgt2;
  return GenusOneModel(eqns),rr,xi3*x1*x3,f3;
end function;

function SolutionFromParams(pp,qq)
  u := [Evaluate(p,[1,0]): p in pp];  
  v := [Evaluate(q,[1,0]): q in qq];  
  if u[3] eq 0 and v[3] eq 0 then 
    soln := [u[1],u[2],v[1],v[2]];
  else
    soln := [u[1]*v[3],u[2]*v[3],u[3]*v[1],u[3]*v[2]];
  end if;
  d := RationalGCD(soln);
  return [x/d : x in soln];
end function;

function RecoverLinearForm(f,Q,D2star)
  R4 := Parent(f);
  quads := Equations(D2star) cat [f];
  mons := MD(R4,2);
  adjmat := Adjoint(SymMat(Q));
  adjquad := &+[adjmat[i,j]*R4.i*R4.j: i,j in [1..4]];
  mat := Matrix(3,#mons,[MC(f,mon): mon in mons,f in quads]);
  km := KernelMatrix(Transpose(mat));
  assert Nrows(km) eq 7;
  mons := [(IsSquare(mon) select 1 else 2)*mon: mon in mons];
  quads := [&+[km[i,j]*mons[j]: j in [1..10]]: i in [1..7]];
  X := Scheme(Proj(R4),quads cat [adjquad]);
  soln := Eltseq(Points(X)[1]);
  lambda1 := &+[soln[i]*R4.i: i in [1..4]];
  d := RationalGCD(Coefficients(lambda1));
  return (1/d)*lambda1;
end function;

function QIData1(a,b,xi1,covdata1,R4)
  R4<x1,x2,x3,x4> := R4; 
  ff := covdata1[2];
  f,g,h := Explode(ff);
  assert IsIntegral(b/xi1);
  D1 := QuadricIntersectionD1(R4,a,b,xi1);
  D1star := QuadricIntersectionD1star(R4,f,g);
  aa := [Evaluate(poly,[x1,x2]): poly in ff];
  bb := [MyPolarise(poly,[x1,x2],[x3,x4]): poly in ff];
  cc := [Evaluate(poly,[x3,x4]): poly in ff];
  qq1 := [x3^2,x1*x3,x2*x4,x1^2,x1*x4,x3*x4,x1*x2,x2*x3];
  qq2 := [aa[2],aa[1],bb[3],cc[1],cc[3],aa[3],bb[1],bb[2]];
  return <D1,D1star,qq1,qq2>;
end function;

function MyStep(qidata,xi,Q,bqf,soln)
  vprint cbrank,3 : "Entering \"MyStep\"";
  D,Dstar,qq1,qq2 := Explode(qidata);
  R4 := PolynomialRing(D);
  if soln eq [] then 
    soln := SolveQuadraticForm(Q);
  end if; 
  lambda := TangentForm(Q,soln);
  quads := [lambda^2] cat [lambda*R4.i: i in [1..4]];
  assert forall{x : x in Eltseq(D) | IsIntegral(x)};
  assert forall{x : x in Eltseq(Dstar) | IsIntegral(x)};
  quads := ConvertQuadrics(D,Dstar,qq1,qq2,quads);
  quads := [MinRedQuadric(D,q): q in quads];
  f := xi*quads[1];
  forms := [quads[i]: i in [2..5]];
  DD,rr,oddq := NewQuadricIntersection(D,bqf,f);
  qq := rr cat OddQuadrics(DD,rr,oddq,forms);
  vprint cbrank,3 : "Leaving \"MyStep\"";
  return DD,qq;
end function;

function CoverData3(elldata,alpha,dual:R4 := elldata[5,3])
  xi1 := alpha`xi1;
  a,b := Explode(elldata[1]);
  if dual then a,b := Explode([-2*a,a^2-4*b]); end if;
  C1,ff := Explode(alpha`data1);
  R2<x,z> := Universe(ff);
  qidata1 := QIData1(a,b,xi1,alpha`data1,R4);
// assert IsCompanionQI(qidata1);
  D1,D1star,qq1,qq2 := Explode(qidata1);
  assert forall{x : x in Eltseq(D1) | IsIntegral(x)};
  R4<x1,x2,x3,x4> := R4; 
  bqf := ExactQuotient(Equation(MyDouble(D1,R2)),x*z);
  QQ := Equations(D1star);
  _,pp,qq := Explode(alpha`data2);
  soln := SolutionFromParams(pp,qq);
  assert Evaluate(QQ[2],soln) eq 0;
  D2,qq1 := QuadricIntersectionD2(R4,ff,alpha`xi2);
  D2star,qq2 := MyStep(qidata1,alpha`xi2,QQ[2],bqf,soln);
  qidata2 := <D2,D2star,qq1,qq2>;
// assert IsCompanionQI(qidata2);
  quartic := x^4 - 2*a*x^2*z^2 + (a^2 - 4*b)*z^4;
  g1m := GenusOneModel(quartic); 
  tt := [qq2[i]: i in [1..4]];
  forms := [x4,x2,xi1*x1^2 - (b/xi1)*x3^2];
  ad := AlignDoubling(D2star,D1,g1m,tt,forms,R2);
  mat := ad`Matrix;
  QQ := Equations(D2star);
  QQ := [&+[mat[i,j]*QQ[j]: j in [1..2]]: i in [1..2]];
  bqf := ExactQuotient(Equation(MyDouble(D2,R2)),x*z);
  D3,rr,oddq,f3 := QuadricIntersectionD3(R4,pp,qq,alpha`xi3);
  f3a := ConvertQuadrics(D2star,D2,qq2,qq1,[f3])[1];
// print "MyDegree(D2,f3) =",MyDegree(D2,f3);
  lambda := RecoverLinearForm(f3a,QQ[1],D2star);
  quads := [lambda^2] cat [lambda*R4.i: i in [1..4]];
  quads := ConvertQuadrics(D2,D2star,qq1,qq2,quads);
  quads := [MinRedQuadric(D2,q): q in quads];
  forms1 := [quads[i]: i in [2..5]];
  ss := OddQuadrics(D3,rr,oddq,forms1);
  aa := alpha`xi3*MyRatio(D2,f3,quads[1]);
  D3star,qq2 := MyStep(qidata2,aa,QQ[2],bqf,[]);
  qq1 := rr cat ss;
  qidata3 := <D3,D3star,qq1,qq2>;
// assert IsCompanionQI(qidata3);
  return qidata3;
end function;

function CoverData4(elldata,alpha,dual) 
  xi1 := alpha`xi1;
  a,b := Explode(elldata[1]);
  if dual then a,b := Explode([-2*a,a^2-4*b]); end if;
  ff := alpha`data1[2];
  D3,D3star,qq1,qq2 := Explode(alpha`data3);
  R2<x,z> := Universe(ff);
  R4<x1,x2,x3,x4> := PolynomialRing(D3);
  f,g,h := Explode(ff);
  D2 := QuadricIntersectionD2(R4,ff,alpha`xi2);
  g1m := GenusOneModel(xi1*x^4 + a*x^2*z^2 + (b/xi1)*z^4);
  tt := [qq2[i]: i in [1..4]];
  forms := [x3,x4,(1/alpha`xi2)*Evaluate(h,[x1,x2])];
  mat := AlignDoubling(D3star,D2,g1m,tt,forms,R2)`Matrix;
  QQ := Equations(D3star);
  QQ := [&+[mat[i,j]*QQ[j]: j in [1..2]]: i in [1..2]];
  gg := [Evaluate(poly,[-z,x]): poly in [g,f]];
  D4,qq1 := MyStep(alpha`data3,alpha`xi4,QQ[1],gg[1],[]);
  D4star,qq2 := MyStep(alpha`data3,alpha`xi4,QQ[2],gg[2],[]);
  qidata4 := <D4,D4star,qq1,qq2>;
// assert IsCompanionQI(qidata4);
  return qidata4;
end function;

function PushOutForm2(covdata1,k)
  assert k in [1,2];
  C1,ff := Explode(covdata1);
  RR2<u,v,w> := PolynomialRing(C1);
  return Evaluate(ff[k],[u,v]);
// N.B. don't clear denominators just yet.
end function;

function PushOutForm3(xi2,covdata2,k)
  assert k in [1,2];
  C2,pp,qq := Explode(covdata2);
  R<u,v,w> := PolynomialRing(C2);
  pt := k eq 1 select [1,0] else [0,1];
  aa := TangentCoefficients(pp,pt);
  return Evaluate(aa[1]*qq[1] + aa[2]*qq[2],[u,v]) + (1/xi2)*aa[3]*w; 
// N.B. don't clear denominators just yet.
end function;
  
function PushOutForm(covdata,k)
  assert k in [1..4];
  QI,QIstar,qq1,qq2 := Explode(covdata);
  R4 := PolynomialRing(QI);
  xx := (R4.k)^2;
  f := ConvertQuadrics(QI,QIstar,qq1,qq2,[xx])[1];
  return MinRedQuadric(QI,f);
// N.B. don't clear denominators just yet.
end function;

///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////

// Computing images of the local connecting maps for descent 
// by 2-isogeny (over Q).

function MyLocalSqrt(x,p,prec)
  assert IsIntegral(x);
  /*
  vprint cbrank, 3 : "x =",x;
  vprint cbrank, 3 : "p =",p;
  vprint cbrank, 3 : "prec =",prec;
  */
  v := Integers()!(Valuation(x,p)/2);
  x0 := Integers()!(x/p^(2*v));
  assert p eq 2;
  assert x0 mod 8 eq 1;
  u := 1;
  for r in [2..(prec-1-v)] do
    if Valuation(x0 - u^2,2) eq r+1 then u +:= 2^r; end if;
  end for;    
  return u*p^v;
end function;

LMS := LocalModSquaresZ;

function LocalImageAtTwo(a,b)
// This routine is called with a and b integers 
// with either v(a) < 2 or v(b) < 4. (v = valuation at 2)
// Further the local connecting map delta : E(Q_2) -> Q_2^/Q_2^*
// where E : y^2 = x*(x^2 + a*x + b) is known to have image 
// of order 2. This routine finds the non-zero element of this image.
  if IsOdd(a) then return [GF2|0,0,1]; end if;
  lambda := LMS(b,2);
  if lambda ne [0,0,0] then return lambda; end if;
  b1 := a^2 - 4*b;
  lambda := LMS(b1,2);
  if lambda eq [0,0,0] then
    v := Valuation(b,2) + 4;
    sqrtb1 := MyLocalSqrt(b1,2,v + 3);
    lambda := LMS(-2*a + 2*sqrtb1,2);
    if lambda ne [0,0,0] then return lambda; end if; 
// In this case we put a1 + 2*sqrtb1 = (2*t)^2 and b = t^2*u^2
// Then b1 = a^2 - 4*b = (sqrtb1 - 2*t^2)^2 - 4*t^2*u^2, hence
// sqrtb1 = t^2 - u^2 and a = -(t^2 + u^2). If a and b are even 
// it follows that t and u are even, hence v(a) >= 2 and v(b) >= 4, 
// a contradiction to "minimality".
    assert Valuation(b,2) eq 0;
// Since b is odd we have im(delta) subset <-1,5>.
// Since +sqrtb1, -sqrtb1 in im(delta') we have -1 in im(delta').
// By duality im(delta) subset <2,5>. Hence im(delta) = <5>
    return [GF2|0,0,1];
  end if;
  v := Maximum(Valuation(b1,2),(1/2)*Valuation(b,2));
  sqrtb := MyLocalSqrt(b,2,v + 3);
  lambda1 := LMS(a + 2*sqrtb,2);
  lambda2 := LMS(a - 2*sqrtb,2);
  assert lambda eq [GF2|lambda1[i] + lambda2[i]: i in [1..3]];
  mat := Matrix(GF2,2,3,[lambda1,lambda2]);
  if Rank(mat) eq 2 then 
    return Eltseq(KM(HNRS(2)*Transpose(mat)));
  end if;
  if lambda1 ne [0,0,0] then 
    assert lambda2 eq [0,0,0];
    sqrtb *:= -1;
  end if;
  lambda0 := LMS(sqrtb,2);
  if lambda0 ne [0,0,0] then return lambda0; end if;
  assert Valuation(b,2) eq 0;
  c := MyLocalSqrt(a*sqrtb + 2*b,2,v + 3);  
  lambda1 := LMS(a + 2*sqrtb + 2*c,2);
  lambda2 := LMS(a + 2*sqrtb - 2*c,2);
  assert lambda eq [GF2|lambda1[i] + lambda2[i]: i in [1..3]];
  mat := Matrix(GF2,2,3,[lambda1,lambda2]);
  if Rank(mat) eq 2 then 
    return Eltseq(KM(HNRS(2)*Transpose(mat)));
  end if;
  if lambda1 ne [0,0,0] then 
    assert lambda2 eq [0,0,0];
    c *:= -1;
  end if;
  d := MyLocalSqrt(sqrtb*(a + 2*sqrtb + 2*c),2,4);
  lambda := LMS(sqrtb + c + d,2);
  assert lambda ne [0,0,0];
  return lambda; 
end function;

function LocalImageAtOddPrime(a,b,p)
  assert p gt 2;
  a1 := -2*a;
  b1 := a^2 - 4*b;
  lambda := LMS(b,p);
  if lambda ne [0,0] then return true,lambda; end if;
  lambda := LMS(b1,p);
  if lambda ne [0,0] then  return false,lambda; end if;
  if 2*Valuation(a,p) lt Valuation(b,p) then
    lambda := LMS(a,p);
    if lambda ne [0,0] then return false,lambda; end if;
  end if;
  if 2*Valuation(a1,p) lt Valuation(b1,p) then
    lambda := LMS(a1,p);
    if lambda ne [0,0] then return true,lambda; end if;
  end if;
  m := Integers()!(Valuation(b,p)/2);
  u := b/p^(2*m);
  v := Integers()!(Sqrt(GF(p)!u));
  if 2*Valuation(a,p) ge Valuation(b,p) then
    lambda := LMS(a + 2*p^m*v,p);
    if lambda ne [0,0] then return false,lambda; end if;
  end if;
  lambda := LMS(p^m*v,p);
  if lambda ne [0,0] then return true,lambda; end if;
  m := Integers()!(Valuation(b1,p)/2);
  u := b1/p^(2*m);
  v := Integers()!(Sqrt(GF(p)!u));
  if 2*Valuation(a1,p) ge Valuation(b1,p) then
    lambda := LMS(a1 + 2*p^m*v,p);
    if lambda ne [0,0] then return true,lambda; end if;
  end if;
  lambda := LMS(p^m*v,p);
  assert lambda ne [0,0];
  return false,lambda;
// In the remaining case both b and b1 are 4th powers
// Since p is a bad prime we have p | b or p | b1
// If p | b and p | b1 then p^2 | a and p^4 | b, hence not minimal.
// Otherwise a = square, hence split multicative reduction,
// hence Tamagawa ratio = 1/2 or 2 (not 1 as it will be here)
end function;

function AdjustedTamagawaExponent(E)
  Emin := MinimalModel(E);
  flag,iso := IsIsomorphic(E,Emin);
  assert flag;
  v1 := Valuation(TamagawaNumber(Emin,2),2);
  v2 := Valuation(IsomorphismData(iso)[4],2);
  return v1 - v2;
end function;

function LocalImages(elldata)
  a,b := Explode(elldata[1]);
  S := elldata[2];
  E := EllipticCurve([0,a,0,b,0]);
  E1 := EllipticCurve([0,-2*a,0,a^2-4*b,0]);
  im := <>;
  for p in S do
    if p eq -1 then 
      if b lt 0 or (a^2 - 4*b gt 0 and a gt 0) then
        mat := IM1;
      else
        mat := NM1;
      end if;
    elif p eq 2 then 
      v := AdjustedTamagawaExponent(E);
      v1 := AdjustedTamagawaExponent(E1);
      case (2 + v - v1) :
        when 0 : 
          mat := NM3;
        when 1 :
  	  assert ReductionType(E,2) ne "Split multiplicative";
          lambda := LocalImageAtTwo(a,b);
          mat := Matrix(3,lambda);
        when 2 :
  	  assert ReductionType(E,2) ne "Split multiplicative";
          a1 := -2*a;
          b1 := a^2 - 4*b;
          if a1 mod 4 eq 0 and b1 mod 16 eq 0 then
	    a1 := a1 div 4;
	    b1 := b1 div 16;
          end if;
          lambda := LocalImageAtTwo(a1,b1);
          mat := Matrix(3,lambda);
          mat := KM(HNRS(2)*Transpose(mat));
        when 3 :
          mat := IM3;
      end case;
    else
      c := TamagawaNumber(E,p)/TamagawaNumber(E1,p);
      if c eq 1/2 then 
        mat := NM2;
      elif c eq 2 then 
        mat := IM2;
      else
        assert c eq 1;
        flag,vv := LocalImageAtOddPrime(a,b,p);
        if flag then 
          mat := Matrix(2,vv);
        else
          mat := KM(HNRS(p)*Matrix(1,vv));
        end if; 
      end if;
    end if;
    Append(~im,mat);
  end for;
  im1 := <KM(HNRS(S[i])*Transpose(im[i])): i in [1..#S]>;
  return im,im1;
end function;

function TwoIsogenySelmerGroup(elldata,dualimages)
  S := elldata[2];

  nc := [Nrows(x) : x in dualimages];
  M := RMatrixSpace(GF2, #S, &+nc) ! 0;
  c := 1;
  for j := 1 to #S do
    if nc[j] gt 0 then
      image := LocalModSquaresMatrix(S,S[j]);
      condition := HNRS(S[j]) * Transpose(dualimages[j]);
      Mj := image * condition;
      InsertBlock(~M, Mj, 1, c);
      c := c + nc[j];
    end if;
  end for;

  return KernelMatrix(M), M;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// local solubility of binary quartics for p = 2

function IsF2Soluble(f,g)
// Determines whether there is a smooth GF2-point on
// the affine curve y^2 + f(x) y = g(x).
  for x,y in [0,1] do
    fx := Evaluate(f,x);
    gx := Evaluate(g,x);
    if y^2 + fx*y eq gx then 
      if fx ne 0 then 
        return true,[x,y],true;
      elif Evaluate(Derivative(f*y - g),x) ne 0 then 
  	return true,[x,y],false;
      end if;
    end if;
  end for;
  return false,_,_,_;
end function;

function HenselLiftAt2(f,g,pt);
  x,y := Explode(pt);
  assert Evaluate(f,x) mod 2 eq 0;
  assert Evaluate(Derivative(f*y - g),x) mod 2 eq 1;
  k := 0;
  kmax := 30;
  repeat
    k +:= 1;
    if k eq kmax then 
      k := 1; 
      kmax *:= 2;  
      x := pt[1]; 
      y +:= 2; 
    end if; 
    b := Integers()!((y^2 + Evaluate(f,x)*y - Evaluate(g,x))/2^k);
    x +:= 2^k*(b mod 2);
    rr := Evaluate(f^2 + 4*g,x);
  until rr ne 0 and IsZero(Vector(LocalModSquares(rr,2)));
  return x;
end function;

function IrregularPointsAt2(f,g)
  Rp := PolynomialRing(GF2);
  if Rp!f ne 0 then 
    df := Derivative(f);
    dg := Derivative(g);
    rts := Roots(Rp!f);
    xx := [Integers()!rt[1] : rt in rts];
    pts := [[x,Evaluate(g,x) mod 2]: x in xx];
    pts := [pt : pt in pts| Evaluate(df*pt[2]+dg,pt[1]) mod 2 eq 0];
    pts := [pt : pt in pts| Evaluate(g - pt[2]*f - pt[2]^2,pt[1]) mod 4 eq 0];
  elif Rp!g ne 0 then 
    flag,m := IsSquare(Rp!g);
    if flag then 
      m := Parent(f)!m;
      f1 := f + 2*m;
      g1 := g - m*f - m^2;
      assert Rp!g1 eq 0;
      g0 := Rp!ExactQuotient(g1,2);
      assert g0 ne 0; // otherwise quartic not minimal
      pts := [[Integers()|rt[1],Evaluate(m,rt[1])] : rt in Roots(g0)];
    else
      error "Case not yet written";
    end if;
  else
    g0 := Rp!ExactQuotient(g,2);
    assert g0 ne 0; // otherwise quartic not minimal
    pts := [[Integers()|rt[1],0]: rt in Roots(g0)];
  end if;
  return pts;
end function;

function IsZ2Soluble(f,g)
  R<X> := Parent(g);
  Rp := PolynomialRing(GF2);
  flag,pt,xflag := IsF2Soluble(Rp!f,Rp!g);
  if flag then 
    x := xflag select pt[1] else HenselLiftAt2(f,g,pt);
    return true,x; 
  end if;
  pts := IrregularPointsAt2(f,g);
  for pt in pts do
    x0,y0 := Explode(pt);
    ff := f + 2*y0;
    gg := g - y0*f - y0^2;
    ff := ExactQuotient(Evaluate(ff,x0 + 2*X),2);
    gg := ExactQuotient(Evaluate(gg,x0 + 2*X),4);
    flag,x1 := IsZ2Soluble(ff,gg);
    if flag then 
      return true,x0 + 2*x1; 
    end if;
  end for;
  return false,_;
end function;

function IsQ2Soluble(quartic)
  assert Degree(quartic) eq 2;
  if #Eltseq(quartic) eq 5 then 
    quartic2,tr := Minimise(quartic:CrossTerms);
    flag,xx := IsQ2Soluble(quartic2);
    if flag then 
      cob := tr`Matrix;
      return true,Eltseq(Vector(xx)*cob);
    end if;
    return false,_;
  end if;
  assert #Eltseq(quartic) eq 8;
  P := PolynomialRing(Integers()); X := P.1;
  seq := ChangeUniverse(Eltseq(quartic),Integers());
  l,m,n,a,b,c,d,e := Explode(seq);
  f := l*X^2 + m*X + n;
  g := a*X^4 + b*X^3 + c*X^2 + d*X + e;
  flag,x := IsZ2Soluble(f,g);
  if flag then 
    return true,[Rationals()|x,1];
  end if;
  f := n*X^2 + m*X + l;
  g := e*X^4 + d*X^3 + c*X^2 + b*X + a;
  flag,x := IsZ2Soluble(f,g);
  if flag then 
    return true,[Rationals()|1,x];
  end if;
  return false,_;
end function;

// local solubility of binary quartics for p odd

function IsQuarticSquare(g)
  a,b,c,d,e := Explode([Coefficient(g,i): i in [4..0 by -1]]);
  return (8*b*e^2 - 4*c*d*e + d^3 eq 0) 
    and (16*a*e^2 + 2*b*d*e - 4*c^2*e + c*d^2 eq 0)
    and (8*a*d*e - 4*b*c*e + b*d^2 eq 0)
    and (a*d^2 - b^2*e eq 0)
    and (8*a*b*e - 4*a*c*d + b^2*d eq 0)
    and (16*a^2*e + 2*a*b*d - 4*a*c^2 + b^2*c eq 0)
    and (8*a^2*d - 4*a*b*c + b^3 eq 0);
end function;
           
function IsFpSoluble2(g)
// Determines whether there is a smooth GF(p)-point on
// the affine curve y^2 = g(x).
  p := Characteristic(BaseRing(g));
  assert p ne 2;
  if g eq 0 then return false,_,_; end if;
  if IsQuarticSquare(g) and 
    LegendreSymbol(Integers()!LeadingCoefficient(g),p) eq -1 then
    return false,_,_; 
  end if;
  for x in [0..p-1] do
    gx := Evaluate(g,x);
    if LegendreSymbol(Integers()!gx,p) eq 1 then
      return true,x,true;
    end if;
    if gx eq 0 and p lt 50 and Evaluate(Derivative(g),x) ne 0 then 
      return true,x,false;
    end if;
  end for;
  error "Error in IsFpSoluble2 : please report";
  return false,_,_;
end function;

function HenselLiftAtp(g,x,p);
  assert p ne 2;
  dg := Derivative(g);
  mu := GF(p)!Evaluate(dg,x);
  assert mu ne 0;
  y := p;
  for k in [1,2] do
    lambda := GF(p)!((y^2-Evaluate(g,x))/p^k);
    b := Integers()!(lambda/mu);
    x +:= p^k*b;
  end for;
  assert (Evaluate(g,x) mod p^3) eq p^2;
  return x;
end function;

function IrregularPoints(g,p)
  assert BaseRing(g) eq Integers();
  assert Degree(g) le 4;
  R<X> := Parent(g);
  Rp := PolynomialRing(GF(p));
  g0 := Rp!g;
  if g0 ne 0 then 
    rts := Roots(g0);
    rts := [Integers()!(rt[1]): rt in rts | rt[2] ge 2];
    xx := [x : x in rts | Valuation(Evaluate(g,x),p) ge 2];
  else
    g0 := Rp!ExactQuotient(g,p);
    assert g0 ne 0; // otherwise quartic not minimal
    rts := Roots(g0);
    xx := [Integers()!(rt[1]): rt in rts];
  end if;
  return xx;
end function;

function IsZpSoluble(g,p)
  assert p ne 2;
  assert BaseRing(g) eq Integers();
  assert Degree(g) le 4;
  R<X> := Parent(g);
  Rp := PolynomialRing(GF(p));
  flag,x,xflag := IsFpSoluble2(Rp!g);
  if flag then 
    if not xflag then x := HenselLiftAtp(g,x,p); end if;
    return true,x; 
  end if;
  xx := IrregularPoints(g,p);
  for x0 in xx do
    h := ExactQuotient(Evaluate(g,x0 + p*X),p^2);
    flag,x1 := IsZpSoluble(h,p);
    if flag then return true,x0 + p*x1; end if;
  end for;
  return false,_;
end function;

function IsQpSoluble2(quartic,p)
  if p eq 2 then 
    return IsQ2Soluble(quartic); 
  end if;
  assert Degree(quartic) eq 2;
  assert #Eltseq(quartic) eq 5;
  P := PolynomialRing(Integers()); X := P.1;
  g := Evaluate(Equation(quartic),[X,1]);
  gg := Evaluate(Equation(quartic),[1,X]);
  if LegendreSymbol(Coefficient(g,4),p) eq 1 then 
    return true,[Rationals()|1,0]; 
  end if;
  flag,x := IsZpSoluble(g,p);
  if flag then 
    return true,[Rationals()|x,1];
  end if;
  a,b := Explode([Coefficient(g,i): i in [4,3]]);
  if Valuation(a,p) ge 2 and Valuation(b,p) ge 1 then 
    h := ExactQuotient(Evaluate(gg,p*X),p^2);
    flag,x := IsZpSoluble(h,p);
    if flag then 
      return true,[Rationals()|1,p*x];
    end if;
  end if;
  return false,_;
end function;

function IsRealSoluble2(quartic)
  assert Degree(quartic) eq 2;
  assert #Eltseq(quartic) eq 5;
  pts := [[1,0],[0,1],[1,1],[1,-1]];
  for pt in pts do
    if Evaluate(Equation(quartic),pt) gt 0 then 
      return true,pt;
    end if;
  end for;
  P := PolynomialRing(Integers()); X := P.1;
  g := Evaluate(Equation(quartic),[X,1]);
  R := RealField(50);
  rts := Roots(g,R);
  if #rts eq 0 then return false,_; end if;
  xx := [(rts[i][1]+rts[i+1][1])/2 : i in [1..#rts-1]];
  for x in xx do
    if Evaluate(g,x) gt 0 then
      for r in [1..100] do
	a := Round(x*2^r);
        if Evaluate(g,a/2^r) gt 0 then 
          return true,[a,2^r];
        end if;
      end for;
    end if;
  end for;
//  -x^3*z - 33204*x^2*z^2 - 433880888*x*z^3 - 1939708866105*z^4
//  2*x^3*z - 695*x^2*z^2 + 24737276*x*z^3 - 14854876493*z^4
  for k in [10,100,1000] do
    pts := [[10^k,1],[1,10^k],[-1,10^k],[10^k,-1]];
    for pt in pts do
      if Evaluate(Equation(quartic),pt) gt 0 then 
        return true,pt;
      end if;
    end for;
  end for;
  return false,_;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

function ElementList(S,mat)
  Z := Integers();
  n := Nrows(mat);
  return [&*[S[j]^(Z!mat[i,j]): j in [1..#S]]: i in [1..n]];
end function;

function IsAlternating(M)
  n := Nrows(M);
  assert n eq Ncols(M);
  return (M eq Transpose(M)) and forall{i : i in [1..n] | M[i,i] eq 0};
end function;

function CTP(badplaces,basis,localdata)
  mat := ZeroMatrix(GF2,#localdata,#basis);
  S := badplaces; // -1 means "real place"
  for i in [1..#localdata] do
    for j in [1..#basis] do
      for k in [1..#S] do
        p := S[k];
        vv := Vector(localdata[i][k])*HNRS(p);
        ww := LocalModSquares(basis[j],p);
        mat[i,j] +:= &+[vv[t]*ww[t]: t in [1..#ww]];
      end for;
    end for;
  end for;
  return mat;
end function;

function GetConstant(S,localdata,dualimages,mat);
  ans := [];
  for j in [1..#S] do
    vv := Vector(localdata[j]);
    vv := vv*HNRS(S[j])*Transpose(dualimages[j]);
    ans cat:= Eltseq(vv);
  end for;
  soln := Solution(mat,Vector(ans));
  return &*[S[i]^(Integers()!soln[i]): i in [1..#S]];
end function;

function MinRedQuarticAndForms(g1m,ff)
  RR2<u,v,w> := Universe(ff);
  quartic,tr := MinRed(g1m);
  assert #Tuple(tr) eq 2;
  la := tr`Scalar;
  p,q,r,s := Explode(Eltseq(tr`Matrix));
  ff := [Evaluate(f,[p*u + r*v,q*u + s*v,(1/la)*w]): f in ff];
  return quartic,ff;
end function;

function MinRedQIAndForm(QI,f)
  R4<x1,x2,x3,x4> := Parent(f);
  QI2,tr := MinRed(QI);
  return QI2,f^Transpose(tr[2]);
end function;

function MinRedQIAndForms(QI,ff)
  R4<x1,x2,x3,x4> := Universe(ff);
  QI2,tr := MinRed(QI);
  return QI2,[f^Transpose(tr`Matrix): f in ff];
end function;

function ShorterForm(g1m)
  seq := Eltseq(g1m);
  assert #seq eq 8;
  assert [seq[i]: i in [1..3]] eq [0,0,0];
  return GenusOneModel(Rationals(),2,[seq[i]: i in [4..8]]);
end function; 

function RealData2(ff)
  R2<x,z> := Universe(ff);
  f,g := Explode(ff);
  mons := [x^2,x*z,z^2];
  a,b,c := Explode([MC(f,mon): mon in mons]);
  d,e,f := Explode([MC(g,mon): mon in mons]);
  if b^2 - 4*a*c lt 0 and e^2 - 4*d*f lt 0 then 
    assert a*d gt 0;
  end if;
  if b^2 - 4*a*c lt 0 then 
    aa := a;
  else
    aa := (b^2 - 2*a*c)*d - a*b*e + 2*a^2*f;
  end if;
  return aa gt 0 select 0 else 1;
end function;

function LocalData2(S,fgh)
  f,g := Explode(fgh);
  quartic := GenusOneModel(f*g);
  localdata := [];
  for p in S do 
    if p eq -1 then 
      lms := [[GF2|RealData2([f,g])]];
    else   
      flag,xx := IsQpSoluble2(quartic,p);
      error if not flag,"Not soluble over Qp",Eltseq(quartic),p;
      yy := Evaluate(Equation(quartic),xx);
      assert yy ne 0;
      assert IsZero(Vector(LocalModSquares(yy,p)));
      zz := [Evaluate(f,xx),Evaluate(g,xx)];
      lms := [LocalModSquares(z,p) : z in zz];
      assert lms[1] eq lms[2];
    end if;
    localdata cat:= [lms[1]];
  end for;
  return localdata;
end function;

function LocalData3(S,quartic,f3list)
  f3 := f3list[1];
  assert #Eltseq(quartic) eq 5;
  R2<X,Z> := PolynomialRing(quartic); 
  RR<x,z,y> := Parent(f3); 
  r := Evaluate(f3,[X,Z,0]);
  alpha := MC(f3,y);
  assert f3 eq alpha*y + Evaluate(r,[x,z]);
  if alpha eq 0 then 
    s := ExactQuotient(Equation(quartic),r);
    return LocalData2(S,[r,s]);
  end if;
  localdata := [];
  for p in S do
    if p eq -1 then 
      flag,xx := IsRealSoluble2(quartic);
      assert flag;
      yy := Evaluate(Equation(quartic),xx);
      assert yy gt 0;
      rr := Evaluate(r,xx);
      lms := [GF2|rr ge 0 select 0 else 1];
    else
      flag,xx := IsQpSoluble2(quartic,p);
      assert flag;
      yy := Evaluate(Equation(quartic),xx);
      assert yy ne 0;
      assert IsZero(Vector(LocalModSquares(yy,p))); // eq 0;
      rr := Evaluate(r,xx);
      prec := 0;
      prec_needed := p eq 2 select 3 else 1;
      prec := prec + 10;
      repeat 
        prec +:= 3;
        Qp := pAdicField(p:Precision := prec);
        y := Sqrt(Qp!yy);
        z1 := alpha*y + rr; 
        if Precision(z1) lt prec_needed then 
          z1 := -alpha*y + rr; 
        end if;
      until Precision(z1) ge prec_needed;
      lms := LocalModSquares(z1,p); 
    end if;
    localdata cat:= [lms];
  end for;
  return localdata;
end function;

procedure PrintSummary(vv,ww:SwitchForPrinting:=false)
  if not IsVerbose("cbrank") then return; end if;
  if SwitchForPrinting then vv,ww := Explode([ww,vv]); end if;
  dd := ["  ": i in [1..6]];
  ee := ["  ": i in [1..6]];
  str := func<x|#s eq 1 select " " cat s else s where s is Sprint(x)>;
  for i in [1..#vv] do
    dd[7-i] := str(vv[i]);
  end for;
  for i in [1..#ww] do
    ee[7-i] := str(ww[i]);
  end for;
  print "  \/---------------------------------------------------\\";
  print "  |   SUMMARY TABLE      Step No :  6  5  4  3  2  1  |";
  print "  |---------------------------------------------------|";
  printf "  |  dim_2 ( E'(Q)/phi E(Q) )   <= %o %o %o %o %o %o  |\n",
    dd[1],dd[2],dd[3],dd[4],dd[5],dd[6];
  printf "  |  dim_2 ( E(Q)/phi'E'(Q) )   <= %o %o %o %o %o %o  |\n",
    ee[1],ee[2],ee[3],ee[4],ee[5],ee[6];
  str := func<x|#s eq 1 select s cat " " else s where s is Sprint(x)>;
  rk_bound := vv[#vv] + ww[#ww] - 2;
  printf "  |     Therefore rank E(Q) <= %o                     |\n",str(rk_bound);
  print "  \\---------------------------------------------------\/";
  error if rk_bound lt 0, "Clearly something wrong here";
end procedure;  

function LocalData4(S,fd,f4list)
  assert #f4list eq 4;
  C := Curve(fd);
// contribution from real place
  prec := 80;
  repeat
    repeat
      prec +:= 20;
      noerror := true;
      try
        flag,realpt := HasRealPoint(C : Precision:=prec, ReturnPoint:=true );
      catch e;
        assert "HasRealPointError1" in e`Object;
        noerror := false;
      end try;
    until noerror;
    assert flag;
//    cc := &+[Abs(x): x in realpt];
//    if cc ne 0 then realpt := [x/cc: x in realpt]; end if;
    Fpt := [Evaluate(f4,realpt): f4 in f4list];  
  until exists(xx){x : x in Fpt | Abs(x) gt 10^(-40) };
  localdata := [LocalModSquares(xx,-1)];
// contribution from finite places
  S0 := [p : p in S | p ge 0];
  for p in S0 do
    xx := ImageOfOneLocalPoint(C,f4list[1],p:prec := 50);
    Append(~localdata,LocalModSquares(xx,p));
  end for;
  return localdata;
end function;

function LocalData4Simult(S,fd,f4list) 
// variant of LocalData4 needed for 6th step (i.e. 8-descent)
  C := Curve(fd);
// contribution from real place
  prec := 80;
  repeat
    repeat
      prec +:= 20;
      noerror := true;
      try
        flag,realpt := HasRealPoint(C : Precision:=prec, ReturnPoint:=true );
      catch e;
        assert "HasRealPointError1" in e`Object;
        noerror := false;
      end try;
    until noerror;
    assert flag;
    Fpt := [Evaluate(f4,realpt): f4 in f4list];  
  until forall{x : x in Fpt | Abs(x) gt 10^(-40) };
  localdata := [[LocalModSquares(x,-1): x in Fpt]];
// contribution from finite places
  prec := 80;
  C4seq := PowerSequence(Integers());
  S0 := [p : p in S | p ge 0];
  for p in S0 do
    while true do
      flag,pt := IsLocallySolvable(fd,p:Precision:=prec,Random); 
      error if not flag,"Quadric intersection is not locally soluble";
      liftedpt := pt;
      pti := MakeIntegral(liftedpt);
      liftedprec := Min([Precision(pti[i]) : i in [1..#pti]]);
      Fpti := [Evaluate(f,C4seq!pti): f in f4list];
      vv := [Valuation(Integers()!Norm(f),p): f in Fpti];
      if (p eq 2) and (Maximum(vv) gt liftedprec-10) or 
             (p ne 2) and (Maximum(vv) ge liftedprec) then 
         error if prec ge 10^3, "Error in Local4DataSimult: " *
           "Lifted", p,"-adic point to precision", liftedprec, 
           "which was not enough."; 
         prec +:= 20;
         vprintf cbrank, 2: "Trying again with precision %o in " *
                                  "LocalData4Simult\n", prec;
      else 
        break; 
      end if;
    end while;
    Append(~localdata,[LocalModSquares(x,p): x in Fpti]);
  end for;
  return localdata;
end function;

function MyFactor(S,x)
  x := Rationals()!x;
  assert x ne 0;
  ans := [];
  for p in S do
    if p eq -1 then 
      m := x gt 0 select 0 else 1;
    else
      m := Valuation(x,p);
    end if;
    ans cat:= [GF2|m];
  end for;
  return ans;
end function;  

function LocalData(elldata,alpha,m)
  assert m in [1,2,3,4];
  case m :
  when 1 : 
    localdata := LocalData2(elldata[2],alpha`data1[2]);
    offset := 1; 
 when 2 :
    f3list := [PushOutForm3(alpha`xi2,alpha`data2,k): k in [1..2]];
    quartic := ShorterForm(alpha`data2[1]);  
    quartic,f3list := MinRedQuarticAndForms(quartic,f3list);
    d := RationalGCD(Coefficients(f3list[1]));
    f3list := [f3/d: f3 in f3list];
    offset := d;
    localdata := LocalData3(elldata[2],quartic,f3list);
  when 3 :
    f4list := [PushOutForm(alpha`data3,k): k in [1..4]];    
    QI := alpha`data3[1];
    QI,f4list := MinRedQIAndForms(QI,f4list);
    d := RationalGCD(Coefficients(f4list[1]));
    f4list := [f4/d: f4 in f4list];
    offset := d;
    localdata := LocalData4(elldata[2],QI,f4list);
  when 4 :
    f5list := [PushOutForm(alpha`data4,k): k in [1..4]];    
    QI := alpha`data4[1];
    QI,f5list := MinRedQIAndForms(QI,f5list);
    d := RationalGCD(Coefficients(f5list[1]));
    f5list := [f5/d : f5 in f5list];
    localdata := LocalData4(elldata[2],QI,f5list);
    offset := 0; // not needed
  end case;
  return localdata,offset;
end function;

///////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////

function SimpleLift(elldata,alpha,k,dual)
  S := elldata[2];
  assert k in [2,3,4];
  case k :
  when 2 : 
    if assigned alpha`data2 then return alpha; end if;
  when 3 : 
    if assigned alpha`data3 then return alpha; end if;
  when 4 : 
    if assigned alpha`data4 then return alpha; end if;
  end case;
  localdata,offset := LocalData(elldata,alpha,k-1);
  if dual then 
    basisT1 := ElementList(S,elldata[3,1]);
    matS1 := elldata[4,2];
    imdelta := elldata[4,3];
  else
    basisT1 := ElementList(S,elldata[4,1]);
    matS1 := elldata[3,2];
    imdelta := elldata[3,3];
  end if;
  assert CTP(elldata[2],basisT1,[localdata]) eq 0;
  xx := GetConstant(S,localdata,imdelta,matS1);
  xx := MySquareFree(xx*offset);
  case k : 
  when 2 : 
    alpha`xi2 := xx;
    alpha`data2 := CoverData2(alpha);
  when 3 : 
    alpha`xi3 := xx;
    alpha`data3 := CoverData3(elldata,alpha,not dual);
  when 4 : 
    alpha`xi4 := xx;
    alpha`data4 := CoverData4(elldata,alpha,dual);
  end case;
  return alpha;
end function;

function IteratedLift(elldata,alpha,m,SS,Theta,dual)
  if m eq 1 then return alpha; end if;
  assert m in [2,3,4];
  k := 1;
  tt := [m-1];
  while true do
    vprintf cbrank,3 : "m = %o  tt = %o\n",m,[tt[i] : i in [1..k]];
    alpha := SimpleLift(elldata,alpha,k+1,IsOdd(k) xor dual);
    k +:= 1;
    if k eq m then break; end if;
    tt := [tt[i]: i in [1..k-1]] cat [1];
    while tt[k-1] eq tt[k] do
      k -:= 1;
      tt[k] +:= 1;
    end while;
    l := tt[k];
    r := (IsEven(k+l) xor dual) select 1 else 2;
    s := (IsEven(k) xor dual) select 2 else 1;
    localdata := LocalData(elldata,alpha,k+l-1);
    basisUU := ElementList(elldata[2],SS[r,l+1]);
    basisU := ElementList(elldata[2],SS[r,l]);
    vprintf cbrank,3 : "r = %o  s = %o  l = %o \n",r,s,l;
    assert CTP(elldata[2],basisUU,[localdata]) eq 0;
    mat1 := CTP(elldata[2],basisU,[localdata]);
    if mat1 ne 0 then
      mat2 := Solution(Theta[s,l],mat1);
      xi := ElementList(elldata[2],mat2*SS[s,l])[1];
      vprint cbrank,3 : "Adjusting by xi =",xi;
      assert k in [2,3];
      case k :
      when 2 : 
        alpha`xi2 := MySquareFree(xi*alpha`xi2);
        alpha`data2 := CoverData2(alpha);
        delete alpha`data3;
        delete alpha`data4;
      when 3 : 
        alpha`xi3 := MySquareFree(xi*alpha`xi3);
        alpha`data3 := CoverData3(elldata,alpha,not dual);
        delete alpha`data4;
      end case;
    end if;
  end while;
  return alpha;
end function;

// New version of IteratedLift used to ReturnFourCoverings

function IteratedLiftQI(elldata,alpha,S,T,Theta,Theta1)
  alpha := SimpleLift(elldata,alpha,2,true); 
  localdata := LocalData(elldata,alpha,2);
  basisUU := ElementList(elldata[2],T[2]);
  basisU := ElementList(elldata[2],T[1]);
  assert CTP(elldata[2],basisUU,[localdata]) eq 0;
  mat1 := CTP(elldata[2],basisU,[localdata]);
  if mat1 ne 0 then
    mat2 := Solution(Theta1[1],mat1);
    xi := ElementList(elldata[2],mat2*T[1])[1];
    vprint cbrank,3 : "Adjusting by xi =",xi;
    alpha`xi2 := MySquareFree(xi*alpha`xi2);
    alpha`data2 := CoverData2(alpha);
  end if;
  alpha := SimpleLift(elldata,alpha,3,false); 
  localdata := LocalData(elldata,alpha,3);
  basisUU := ElementList(elldata[2],S[3]);
  basisU := ElementList(elldata[2],S[2]);
  assert CTP(elldata[2],basisUU,[localdata]) eq 0;
  mat1 := CTP(elldata[2],basisU,[localdata]);
  if mat1 ne 0 then
    mat2 := Solution(Theta1[2],mat1);
    xi := ElementList(elldata[2],mat2*T[2])[1];
    vprint cbrank,3 : "Adjusting by xi =",xi;
    alpha`xi2 := MySquareFree(xi*alpha`xi2);
    alpha`data2 := CoverData2(alpha);
  end if;
  delete alpha`data3;
  V := VectorSpace(GF2,Nrows(T[3]));
  mat := Matrix(#V,#elldata[2],[v*T[3] : v in V]);
  elts := ElementList(elldata[2],mat);
  vprintf cbrank,1 : "Computing %o quadric intersections\n",#elts;
  alpha0 := alpha;
  QIlist := [];
  vtime cbrank,1 :
  for ee in elts do
    vprint cbrank,2 : "eta =",ee;
    alpha := alpha0;
    alpha`xi2 := MySquareFree(ee*alpha`xi2);
    alpha`data2 := CoverData2(alpha);      
    alpha := SimpleLift(elldata,alpha,3,false); 
    localdata := LocalData(elldata,alpha,3);
    basisUU := ElementList(elldata[2],S[2]);
    basisU := ElementList(elldata[2],S[1]);
    assert CTP(elldata[2],basisUU,[localdata]) eq 0;
    mat1 := CTP(elldata[2],basisU,[localdata]);
    if mat1 ne 0 then
      mat2 := Solution(Theta[1],mat1);
      xi := ElementList(elldata[2],mat2*S[1])[1];
      vprint cbrank,3 : "Adjusting by xi =",xi;
      alpha`xi3 := MySquareFree(xi*alpha`xi3);
      alpha`data3 := CoverData3(elldata,alpha,true);
      delete alpha`data4;
    end if;
    alpha := SimpleLift(elldata,alpha,4,true); 
    Append(~QIlist,alpha`data4[1]);
  end for;
  return QIlist;
end function;

function PairingName(m,dual)
  dom := "S" cat IntegerToString(m);
  dom1 := dual select dom cat "'" else dom;
  dom2 := (IsEven(m) xor dual) select dom cat "'" else dom;
  pair := "Theta" cat IntegerToString(m);
  if dual then pair cat:= "'"; end if;
  return Sprintf("%o : %o x %o -> Z/2Z",pair,dom1,dom2);
end function;

function KernelName(m,dual:right:=false)
  pair := "Theta" cat IntegerToString(m);
  if dual then pair cat:= "'"; end if;
  ker := "S" cat IntegerToString(m+1);
  ker1 := dual select ker cat "'" else ker;
  ker2 := (IsEven(m) xor dual) select ker cat "'" else ker;
  if right then 
    return Sprintf("%o = ker%o(%o)",ker2,IsEven(m) select "_R" else "",pair);
  else
    return Sprintf("%o = ker%o(%o)",ker1,IsEven(m) select "_L" else "",pair);
  end if;
end function;

///////////////////////////////////////////////////////////////////

// Extension to 8-descent

function ComputeXi(QI,f)
  IC4 := Ideal(Equations(QI));
  R4 := Parent(f);
  mons := MD(R4,2);
  mq := Matrix(10,2,[MC(p,mon): p in Equations(QI),mon in mons]);
  assert exists(i){i : i in [10..1 by -1] | mq[i] ne 0};
  assert exists(j){j : j in [10..1 by -1] | mq[i,1]*mq[j,2] ne mq[i,2]*mq[j,1]};
  mm := [mons[r]: r in [1..10] | r notin {i,j}];
  B := PolynomialRing(Rationals(),8);
  BB := PolynomialRing(B,4);
  q := &+[B.i*Evaluate(mm[i],[BB.j : j in [1..4]]): i in [1..8]];
  qq := q^2;
  mons4 := MD(R4,4);
  polys := [MC(qq,Evaluate(mon,[BB.j: j in [1..4]])): mon in mons4];
  quartics := [mon*p : p in Equations(QI),mon in mons] cat [f];
  bigmat := Matrix(#quartics,#mons4,[MC(q,mon): mon in mons4,q in quartics]);
  km := KernelMatrix(Transpose(bigmat));
  eqns := [&+[km[i,j]*polys[j] : j in [1..#mons4]]: i in [1..Nrows(km)]];
  X := Scheme(Proj(B),eqns);
  assert Dimension(X) eq 0;
  assert Degree(X) eq 1;
  pts := Points(X);
  assert #pts eq 1;
  pt := Eltseq(pts[1]);
  d := &+[pt[i]*mm[i]: i in [1..8]];
  d := MinRedQuadric(QI,d);
  d /:= RationalGCD(Coefficients(d));
  LHS := NormalForm(f,IC4);
  RHS := NormalForm(d^2,IC4);
  xi := Rationals()!(LHS/RHS);
  return xi,d;
end function;

function GetXi1(E,T,g0)
  c4,c6 := Invariants(g0);
  I := c4/2^4;
  J := c6/2^5;
  P := PolynomialRing(Rationals()); XX := P.1;
  f := XX^3 - 3*I*XX + J;
  g4 := Hessian(g0);
  E1 := EllipticCurve(-27*Evaluate(f,-XX/3));
  flag,iso := IsIsomorphic(E,E1);
  assert flag;
  T1 := iso(T);
  phi0 := -Eltseq(T1)[1]/3;
  assert Evaluate(f,phi0) eq 0;
  LHS := (1/3)*(4*phi0*Equation(g0) - Equation(g4));
  myfact := Factorization(LHS);
  q3 := &*[d[1]^(Integers()!(d[2]/2)): d in myfact];
  q3 /:= RationalGCD(Coefficients(q3));
  xi1 := Rationals()!(LHS/q3^2);
  xi1,c := PowerFreePart(xi1,2);
  q3 *:= c;
  assert LHS eq xi1*q3^2;
  return xi1,q3;
end function;

function GetCovData1(elldata,g0,xi1,q3,RR2)
  R2 := PolynomialRing(g0);
  RR2<u,v,w> := RR2;
  R3<X,Y,Z> := PolynomialRing(Rationals(),3);
  h0 := Hessian(g0);
  jmat := Matrix(2,2,[Derivative(Equation(p),R2.i):i in [1,2],p in [g0,h0]]);
  g6 := (-1/12)*Determinant(jmat);
  c4,c6 := Explode(cInvariants(g0));
  g := Equation(g0);
  h := Equation(h0);
  assert 27*g6^2 eq -h^3 + 3*c4*g^2*h - 2*c6*g^3;
  a,b := Explode(elldata[1]);
  r := (b/xi1)*q3^2;
  s := 4*Equation(g0);
  assert cInvariants(g0) eq [16*a^2 - 48*b,-64*a^3 + 288*a*b];
  assert g6^2 eq r^3 + a*r^2*s + b*r*s^2;
  Q := xi1*X^2 + a*X*Y + (b/xi1)*Y^2 - Z^2;
  quartics := [R2|4*Equation(g0),q3^2,xi1*g6/(b*q3)];
  assert Evaluate(Q,quartics) eq 0;
  Q := xi1*X^2 + a*X*Y + (b/xi1)*Y^2 - Z^2;
  soln := [Evaluate(q,[1,0]): q in quartics];
  ff := SimonParametrisation(Q,soln:R:=R2);
  f,g,h := Explode(ff);
  assert xi1*f^2 + a*f*g + (b/xi1)*g^2 eq h^2;
  eqn := w^2 - Evaluate(f*g,[u,v]);
  return <GenusOneModel(eqn),ff>,quartics;
end function;

function GetCovData2(ff,q3,quartics,RR2);
  R2<x,z> := Universe(quartics);
  RR2<u,v,w> := RR2;
  mons := [x^2,x*z,z^2];
  mat := Matrix(Rationals(),3,3,[MC(f,mon): mon in mons,f in ff]);
  mat1 := mat^(-1);
  LL := [&+[mat1[i,j]*quartics[j]: j in [1..3]]: i in [1..3]];
  myfact := Factorization(LL[1]);
  q1 := &*[d[1]^(Integers()!(d[2]/2)): d in myfact];
  xi2 := Rationals()!(LL[1]/q1^2);
  q2 := R2!(LL[2]/(xi2*q1));
  assert LL eq [xi2*q1^2,xi2*q1*q2,xi2*q2^2];
  dd := RationalGCD(Coefficients(q1) cat Coefficients(q2));
  q1 /:= dd;
  q2 /:= dd;
  xi2 *:= dd^2;
  xi2 := 1/xi2;
  xi2,c := PowerFreePart(xi2,2);
  q1 /:= c;
  q2 /:= c; 
  assert forall{i : i in [1..3] | Evaluate(ff[i],[q1,q2]) eq xi2*quartics[i]};
  qq := [q1,q2,q3];
  pp := CoverData2Subroutine(ff[1],xi2);
  assert Evaluate(ff[1],[pp[1],pp[2]]) eq xi2*pp[3]^2;
  vprint cbrank,3 : "p1 =",pp[1];
  vprint cbrank,3 : "p2 =",pp[2];
  vprint cbrank,3 : "p3 =",pp[3];
  mydenom := 1/RationalGCD(&cat[Coefficients(q): q in qq]);
  qq := [mydenom*bqf: bqf in qq];
  vprint cbrank,3 : "q1 =",qq[1];
  vprint cbrank,3 : "q2 =",qq[2];
  vprint cbrank,3 : "q3 =",qq[3];
  assert Evaluate(ff[2],[qq[1],qq[2]]) eq xi2*qq[3]^2;
  quartic := xi2*Evaluate(ff[1],[qq[1],qq[2]]);
  C2 := GenusOneModel(w^2 - Evaluate(quartic,[u,v]));
  return <C2,pp,qq>,xi2,mydenom;
end function;

function PushOutForms(E,T,QI)
  R2<x,z> := PolynomialRing(Rationals(),2);
  RR2<u,v,w> := PolynomialRing(Rationals(),[1,1,2]);
  R4 := PolynomialRing(QI);
  IC4 := Ideal(Equations(QI));
  g0 := MyDouble(QI,R2);
  assert IsIsomorphic(Jacobian(g0),E);
  elldata := EllData(E,T);
  a,b := Explode(elldata[1]);
  flag,iso := IsIsomorphic(Jacobian(QI),EllipticCurve([0,a,0,b,0]));
  assert flag;
  uu := IsomorphismData(iso)[4];
  if uu eq 1 then 
    a := 4*a;
    b := 16*b;
    elldata := <[a,b],elldata[2]>;
    assert 2 in elldata[2];
    flag,iso := IsIsomorphic(Jacobian(QI),EllipticCurve([0,a,0,b,0]));
    assert flag;
    uu := IsomorphismData(iso)[4];
  end if;
  assert uu eq 2;
  assert cInvariants(g0) eq [16*a^2 - 48*b,-64*a^3 + 288*a*b];
  alpha := rec<CoveringData|>;
  xi1,q3 := GetXi1(E,T,g0);
  xi1 := b/xi1;
  vprint cbrank,3 : "";
  vprint cbrank,3 : "xi1 =",xi1;
  alpha`xi1 := xi1;
  alpha`data1,quartics := GetCovData1(elldata,g0,xi1,q3,RR2);
  ff := alpha`data1[2];
  alpha`data2,xi2,mydenom := GetCovData2(ff,q3,quartics,RR2);
  alpha`xi2 := xi2;
  vprint cbrank,3 : "xi2 =",xi2;
  C2,pp,qq := Explode(alpha`data2);
  quartic := -Evaluate(Equation(C2),[x,z,0]);
  assert quartic eq 4*mydenom^2*xi2^2*Equation(g0);
  A,T0,T1,B := Explode(SL4Covariants(QI));
  jmat := Matrix(R4,4,4,[Derivative(f,R4.i): f in [A,T0,T1,B],i in [1..4]]);
  J := (1/4)*Determinant(jmat);
  assert J^2 - Evaluate(Equation(g0),[T0,-T1]) in IC4;
  assert (2*mydenom*xi2*J)^2 - Evaluate(quartic,[T0,-T1]) in IC4;
  f3 := PushOutForm3(xi2,alpha`data2,1);
  LHS1 := Evaluate(f3,[T0,-T1,2*mydenom*xi2*J]);
  xi3,c := ComputeXi(QI,LHS1);
  xi3,r := PowerFreePart(xi3,2);
  c *:= r;
  f3 := PushOutForm3(xi2,alpha`data2,2);
  LHS2 := Evaluate(f3,[T0,-T1,2*mydenom*xi2*J]);
  xi3alt,d := ComputeXi(QI,LHS2);
  flag,r := IsSquare(xi3/xi3alt);
  assert flag;
  d /:= r;
  assert LHS1 - xi3*c^2 in IC4;
  assert LHS2 - xi3*d^2 in IC4;
  vprint cbrank,3 : "xi3 =",xi3;
  alpha`xi3 := xi3;
  polys := [Evaluate(qq[1],[T0,-T1]),Evaluate(qq[2],[T0,-T1]),2*mydenom*J];
  assert Evaluate(ff[1],[polys[1],polys[2]]) - xi2*polys[3]^2 in IC4;
  mons := [x^2,x*z,z^2];
  mat := Matrix(Rationals(),3,3,[MC(f,mon): mon in mons,f in pp]);
  mat1 := mat^(-1);
  LL := [&+[mat1[i,j]*polys[j]: j in [1..3]]: i in [1..3]];
  assert LL[1] - xi3*d^2 in IC4;
  assert LL[3] - xi3*c^2 in IC4;
  if LL[2] - xi3*c*d notin IC4 then d *:= -1; end if;
  assert LL[2] - xi3*c*d in IC4;
  c,d := Explode([d*xi3,c*xi3]);
  assert Evaluate(pp[1],[c,d]) - xi3*Evaluate(qq[1],[T0,-T1]) in IC4;
  assert Evaluate(pp[2],[c,d]) - xi3*Evaluate(qq[2],[T0,-T1]) in IC4;
  assert Evaluate(pp[3],[c,d]) - 2*mydenom*xi3*J in IC4;
  alpha`data3 := CoverData3(elldata,alpha,false:R4 := R4);
  f4 := PushOutForm(alpha`data3,1);
  LHS := Evaluate(f4,[c,d,T0,-T1]);
  xi4,f := ComputeXi(QI,LHS);
  xi4,r := PowerFreePart(xi4,2);
  f *:= r;
  assert LHS - xi4*f^2 in IC4;
  vprint cbrank,3 : "xi4 =",xi4;
  alpha`xi4 := xi4;
  alpha`data4 := CoverData4(elldata,alpha,false);
  flag,tr := IsEquivalent(alpha`data4[2],QI);
  assert flag;
  covdata4b := <alpha`data4[i]: i in [2,1,4,3]>;
  ff := [PushOutForm(covdata4b,k):k in [1..4]];
  gg := [f^Transpose(tr`Matrix): f in ff];
  vprintf cbrank,3 : "Pushout forms computed"; 
  vprintf cbrank,2 : ". "; 
  vprint cbrank,3 : "";
  d := RationalGCD(Coefficients(gg[1]));
  return [g/d: g in gg];
end function;

function TweakBinaryQuartic(E,BQ);
  E1 := Jacobian(BQ);
  flag,iso := IsIsomorphic(E,E1);
  assert flag;
  u := IsomorphismData(iso)[4];
  _,tr := IsTransformation(2,<1/u,IdentityMatrix(Rationals(),2)>);
  BQ := tr*BQ;
  assert cInvariants(BQ) eq cInvariants(E);
  return BQ;
end function;

function CasselsTatePairingOn2and4Selmer(E,BQlist,QIlist)
  BQlist := [TweakBinaryQuartic(E,BQ): BQ in BQlist];
  aa := [TwoSelmerElement(E,BQ): BQ in BQlist];
  pairing := ZeroMatrix(GF2,#QIlist,#BQlist);
  if #QIlist gt 0 then    
    S := {-1,2} join Set(BadPrimes(E));
    S := Sort(SetToSequence(S));
    TT := [x : x in E`TwoTorsionOrbits];
    for i in [1..#QIlist] do
      vprintf cbrank,2 : "(%o) : ",i; 
      QI := QIlist[i];
      assert cInvariants(QI) eq cInvariants(E);
      ff := [PushOutForms(E,T,QI)[1]: T in TT];
      ld := LocalData4Simult(S,QI,ff);
      row := &+[CTP(S,[a[j]: a in aa],[[l[j]: l in ld]]) : j in [1..3]];
      pairing[i] := Vector(row);
      vprint cbrank,2 : row;
    end for; 
  end if;
  return Transpose(pairing);
end function;

/////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////

intrinsic TwoPowerIsogenyDescentRankBound(E::CrvEll[FldRat],T::PtEll[FldRat]:Cutoff:=2,MaxSteps:=5,ReturnFourCoverings := false) -> RngIntElt,SeqEnum,SeqEnum
{Computes an upper bound for the rank of E(Q) where E/Q is an elliptic
curve with rational 2-torsion point T. The program finishes early if the 
current rank bound is less than Cutoff (by default 2), or if the number of 
steps exceeds MaxSteps (by default 5). Let phi : E -> E\' be the isogeny 
with kernel generated by T, and phihat : E\' -> E the dual isogeny. 
Let phi_m and phihat_m be the isogenies of degree 2^m obtained by composing 
phi and phihat m times. Then the rank bound after m steps is that obtained 
by computing the images of the Selmer groups attached to phi_m and phihat_m 
in the Selmer groups attached to phi and phihat. The dimensions of these 
images are also returned. In cases where E or E\' has full rational 
2-torsion, a 6th step, corresponding to 8-descent, may also be possible.}

  if ReturnFourCoverings then MaxSteps := 5; Cutoff := 0; end if;

  require MaxSteps in [1..6] : "MaxSteps should be in range [1..6]";
  require Curve(T) eq E and Order(T) eq 2 
        : "T should be a point on E of order 2";

  E,iso := MinimalModel(E);
  T := iso(T);
  elldata := EllData(E,T);
  vprint cbrank,1 : "a =",elldata[1,1];
  vprint cbrank,1 : "b =",elldata[1,2];
  vprint cbrank,1 : "S =",elldata[2];

  if ReturnFourCoverings then
    vprint cbrank,1 : "Switching to 2-isogenous curve";
    a,b := Explode(elldata[1]);
    E := EllipticCurve([0,-2*a,0,a^2-4*b,0]);
    T := E![0,0];
    E,iso := MinimalModel(E);
    T := iso(T);
    elldata := EllData(E,T);
    vprint cbrank,1 : "a =",elldata[1,1];
    vprint cbrank,1 : "b =",elldata[1,2];
    vprint cbrank,1 : "S =",elldata[2];
  end if;
 
  imdelta,imdelta1 :=  LocalImages(elldata);

  vprint cbrank,2 : "The vector space S1 = S^(phi)(E/Q) has basis ";
  S1,matS1 := TwoIsogenySelmerGroup(elldata,imdelta);
  vprint cbrank,2 : ElementList(elldata[2],S1);
  Append(~elldata,<S1,matS1,imdelta>);

  vprint cbrank,2 : "The vector space S1' = S^(phihat)(E'/Q) has basis ";
  T1,matT1 := TwoIsogenySelmerGroup(elldata,imdelta1);
  vprint cbrank,2 : ElementList(elldata[2],T1);
  Append(~elldata,<T1,matT1,imdelta1>);

  S := <S1>;
  SS := <T1>;
  rk_bound := Nrows(S1) + Nrows(T1) - 2;
  dimS := [Nrows(Sm) : Sm in S];
  dimT := [Nrows(Tm) : Tm in SS];
  PrintSummary(dimS,dimT:SwitchForPrinting:=ReturnFourCoverings);
  if rk_bound lt Cutoff or MaxSteps eq 1 then 
    return rk_bound,dimS,dimT;
  end if;

  R2<x,z> := PolynomialRing(Rationals(),2);
  RR2<u,v,w> := PolynomialRing(Rationals(),[1,1,2]);
  R4<x1,x2,x3,x4> := PolynomialRing(Rationals(),4);
  Append(~elldata,<R2,RR2,R4>);

  a,b := Explode(elldata[1]);
  E1 := MinimalModel(EllipticCurve([0,-2*a,0,a^2-4*b,0]));
  ntwotors := #Roots(DivisionPolynomial(E,2));
  ntwotors1 := #Roots(DivisionPolynomial(E1,2));

  Theta := <>;
  Theta1 := <>;

  alphalistS := [];
  alphalistT := [];

  eightflag := ntwotors1 eq 3 and MaxSteps eq 6;
  eightflag1 := ntwotors eq 3 and MaxSteps eq 6;

  for m in [1..5] do
    usetranspose := (m eq 4 and not eightflag1);
    for dual in [false,true] do
      if m eq 5 then 
        if (not dual) and not eightflag then continue; end if;
        if dual and not eightflag1 then continue; end if;
        pp := "Preparing to compute";
      else
        pp := "Computing";
      end if;
      if not (dual and usetranspose) then
        vprintf cbrank,2 : "*** %o the pairing %o ***\n",
          pp,PairingName(m,dual);
        alphalist := [];
        Sm := dual select SS[m] else S[m];
        oldlist := dual select alphalistT else alphalistS;
        for xi in ElementList(elldata[2],Sm) do
          if exists(a){a : a in oldlist | a`xi1 eq xi} then
            alpha := a;
          else
            alpha := rec<CoveringData|xi1 := xi>;
            alpha`data1 := CoverData1(elldata,xi,dual);
          end if;
          if m lt 5 then
            alpha := IteratedLift(elldata,alpha,m,<S,SS>,<Theta,Theta1>,dual);
          elif not assigned alpha`data4 then
            alpha := IteratedLift(elldata,alpha,4,<S,SS>,<Theta,Theta1>,dual);
          end if;
          Append(~alphalist,alpha);
        end for;
        if dual then 
          alphalistT := alphalist; 
        else 
          alphalistS := alphalist;
        end if;
        if m eq 5 then continue; end if;
        localdata := [LocalData(elldata,alpha,m): alpha in alphalist];
        U := (IsOdd(m) xor dual) select S[m] else SS[m];
        basis := ElementList(elldata[2],U);
        NewPairing := CTP(elldata[2],basis,localdata);
        if dual then 
          Append(~Theta1,NewPairing); 
        else
          Append(~Theta,NewPairing); 
        end if;
        vprintf cbrank,2 : "The pairing %o has matrix\n",PairingName(m,dual);
        vprint cbrank,2 : NewPairing;
        if IsOdd(m) then 
          assert IsAlternating(NewPairing); 
          rk_bound := Nrows(S[#S]) + Nrows(SS[#SS]) - Rank(NewPairing) - 2; 
        end if;
        if IsEven(m) and not dual then 
          rk_bound := Nrows(S[#S]) + Nrows(SS[#SS]) - 2*Rank(NewPairing) - 2;
        end if;
        error if rk_bound lt 0, "Clearly something wrong here";
        if IsEven(m) and dual then 
          assert NewPairing eq Transpose(Theta[m]);
          vprintf cbrank,2 : 
            "This is the transpose of Theta%o as expected.\n",m;
        end if;
        vprintf cbrank,2 : "The vector space %o has basis\n",
          KernelName(m,dual);
        if not dual then
          Append(~S,KernelMatrix(NewPairing)*S[m]);
          vprint cbrank,2 : ElementList(elldata[2],S[m+1]); 
        else
          Append(~SS,KernelMatrix(NewPairing)*SS[m]);
          vprint cbrank,2 : ElementList(elldata[2],SS[m+1]); 
        end if;
        if usetranspose then
          Append(~Theta1,Transpose(NewPairing)); 
          vprintf cbrank,2 : "The vector space %o has basis\n",
            KernelName(m,dual:right);
          Append(~SS,KernelMatrix(Transpose(NewPairing))*SS[m]); 
          vprint cbrank,2 : ElementList(elldata[2],SS[m+1]);
        end if;
        dimS := [Nrows(Sm): Sm in S]; 
        dimT := [Nrows(Tm): Tm in SS]; 
        PrintSummary(dimS,dimT:SwitchForPrinting:=ReturnFourCoverings);
      end if;
      if rk_bound lt Cutoff or (dual and MaxSteps eq m+1) then
        return rk_bound,dimS,dimT;
      end if;
      if ReturnFourCoverings and m eq 3 then break m; end if;
    end for;
  end for;

  if ReturnFourCoverings then 
    vprint cbrank,1 : "Compute list of 4-coverings";
    V := VectorSpace(GF2,Nrows(S[4]));
    mat := Matrix(#V,#elldata[2],[v*S[4] : v in V]);
    elts := ElementList(elldata[2],mat);
    vprintf cbrank,2 : "Looping over %o choices\n",#elts;
    QIlist := [];
    vtime cbrank,2 : for i in [1..#elts] do
      vprintf cbrank,2 : "ctr = %o/%o  xi = %o\n",i,#elts,elts[i];
      IndentPush();
      alpha := rec<CoveringData|xi1 := elts[i]>;
      alpha`data1 := CoverData1(elldata,elts[i],false);
      QIlist1 := IteratedLiftQI(elldata,alpha,S,SS,Theta,Theta1);
      IndentPop();
      QIlist cat:= QIlist1;
      vprint cbrank,2 : "#QIlist =",#QIlist;
    end for;
    return rk_bound,dimS,dimT,QIlist;
  end if;

  m := 5; // extension to 8-descent
 
  for dual in [false,true] do
    if (not dual and eightflag) or (dual and eightflag1) then
      vprintf cbrank,2 : 
        "*** Computing the pairing %o ***\n",PairingName(m,dual);
      alphalist := dual select alphalistT else alphalistS;
      QIlist := [alpha`data4[1]: alpha in alphalist];
      assert #QIlist eq (dual select Nrows(SS[m]) else Nrows(S[m]));
      localdata := [LocalData(elldata,alpha,4): alpha in alphalist];
      basis := ElementList(elldata[2],dual select S[4] else SS[4]);
      assert CTP(elldata[2],basis,localdata) eq 0;
      basis := ElementList(elldata[2],dual select S[3] else SS[3]);
      mat1 := CTP(elldata[2],basis,localdata);
      OldPairing := dual select Theta[3] else Theta1[3];
      mat2 := Solution(OldPairing,mat1);
      xilist := ElementList(elldata[2],mat2*(dual select S[3] else SS[3]));
      BQlist := [];
      for i in [1..#alphalist] do
        aa := alphalist[i];
        aa`xi2 := MySquareFree(xilist[i]*aa`xi2);
        BQ := CoverData2(aa)[1];
        Append(~BQlist,CompleteTheSquare(BQ));
      end for;
      EE := dual select E else E1;
      NewPairing := CasselsTatePairingOn2and4Selmer(EE,BQlist,QIlist);
      vprintf cbrank,2 : "The pairing %o has matrix\n",PairingName(m,dual);
      vprint cbrank,2 : NewPairing;
      assert IsAlternating(NewPairing); 
      rk_bound := Nrows(S[#S]) + Nrows(SS[#SS]) - Rank(NewPairing) - 2; 
      error if rk_bound lt 0, "Clearly something wrong here";
      vprintf cbrank,2 : "The vector space %o has basis\n",KernelName(m,dual);
      if not dual then 
        Append(~S,KernelMatrix(NewPairing)*S[m]);
        vprint cbrank,2 : ElementList(elldata[2],S[m+1]); 
      else
        Append(~SS,KernelMatrix(NewPairing)*SS[m]);
        vprint cbrank,2 : ElementList(elldata[2],SS[m+1]); 
      end if;
      dimS := [Nrows(Sm): Sm in S]; 
      dimT := [Nrows(Tm): Tm in SS]; 
      PrintSummary(dimS,dimT:SwitchForPrinting:=ReturnFourCoverings);
      if rk_bound lt Cutoff then
        return rk_bound,dimS,dimT;
      end if;
    end if;
  end for;

  return rk_bound,dimS,dimT;

end intrinsic;

intrinsic TwoPowerIsogenyDescentRankBound(E::CrvEll[FldRat]:Cutoff:=2,MaxSteps:=5,ReturnFourCoverings:=false) -> RngIntElt,SeqEnum,SeqEnum
{Returns TwoPowerIsogenyDescentRankBound(E,T) where T is the unique 2-torsion point on E}

  T, mT := TwoTorsionSubgroup(E);

  require #T gt 1 : "Curve has no 2-torsion point";
  require #T eq 2 : "Curve has more than one 2-torsion point, so a point must be specified (as the second argument)";

  return TwoPowerIsogenyDescentRankBound(E, T.1 @ mT :
                                         Cutoff:=Cutoff, MaxSteps:=MaxSteps,
                                         ReturnFourCoverings:=ReturnFourCoverings);
end intrinsic;

