freeze;

/************************************************************************\
*  Reduction of Genus One Models over Q (of degrees n = 2,3,4 and 5)     *
*  Author: T. Fisher                                                     *
*  Date: 22nd July 2008                                                  *
*  Version for n = 2 calls "QuarticReduce"                               *
*  Versions for n = 3,4 based on joint work with J. Cremona and M. Stoll *
\************************************************************************/

// Change Log

// T. Fisher, April 2010 :
// Added functions "GetRoots" and "MyConjugates" to stop 
// "ReductionCovariantFour" calling "Conjugates" for degree 4
// number fields. This was prompted by the example :- 
// g1m := GenusOneModel(Rationals(),4,[ 30, 20, 4, -9, -30, 21, 29, 
//   -198, 177, -290, -140466021, 83633827, 378827286, -37840822, 
//   -4029406, -145452736, 2867591, -200376996, -11873302, 117369319 ]);
// which took 15 seconds before the change, < 0.1 seconds after.

// T. Fisher, April 2010 : converted to use new TransG1 type

declare verbose Reduction,4;

// Find pathname by typing e.g. "Hessian:Maximal;" at the magma prompt

import "g1invariants.m" :
  MultiFact,AuxiliaryQuadrics,ExactPfaffianMatrix;
import "3descent-testeq.m" :
  RedTorsPts,ReductionInnerProduct;

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Id := IdentityMatrix;
Deriv := Derivative;
MySign := func<x|x ge 0 select 1 else -1>;
dyadic_rep := func<x|x eq 0 select 0 
  else a*2^b where a,b is MantissaExponent(x)>;
L2Norm := func<model|&+[x^2: x in Eltseq(model)]>;

function FirstSign(seq)
  xx := [x : x in seq | x ne 0];
  fnz := #xx eq 0 select 1 else xx[1];
  return MySign(fnz);
end function;

function IntegerMatrix(mat)
  n := Nrows(mat);
  mat1 := Matrix(n,n,[dyadic_rep(mat[i,j]):i,j in [1..n]]);
  denom := LCM([Integers()|Denominator(x) : x in Eltseq(mat1)]);
  return MatrixAlgebra(Integers(),n)!(denom*mat1);
end function;  

function LLLGramTransformation(M : Delta:=0.999)
 if true then _,T:=LLLGram(M : Delta:=Delta); return T; end if;  
 T:=DiagonalisingMatrix(M); Ti:=T^(-1); D:=T*M*Ti;
 A:=DiagonalMatrix([Abs(x) : x in Diagonal(D)]);  MAT:=IntegerMatrix(Ti*A*T);
 _,R:=LLLGram(MAT+Transpose(MAT) : Delta:=Delta); return R; end function;  

function MyEchelonForm(mat,tol)
// Row reduce an m by n matrix over the reals or complexes,
// always using largest available entry as the next pivot.
// Matrix returned is of form ( Id(m) | B )  
  m := Nrows(mat);
  n := Ncols(mat);
  for j in [1..m] do
    _,jj := Maximum([Abs(mat[k,j]): k in [j..m]]);
    jj +:= (j-1);
    temp := mat[j]; mat[j] := mat[jj]; mat[jj] := temp;
    if Abs(mat[j,j]) lt tol then return 0; end if;
    mat[j] *:= (1/mat[j,j]);
    for k in [1..m] do
      if k ne j then mat[k] -:= mat[k,j]*mat[j]; end if;
    end for;
  end for;
  return mat;
end function;

function SizeString(model)
  size := Round(L2Norm(model));
  logsize := Ilog(10,size);
  if logsize lt 10 then 
    return "L2Norm = " cat IntegerToString(size);
  else 
    return "Log10(L2Norm) = " cat IntegerToString(logsize);
  end if;
end function;

function CoefficientSize(model:name:="Model");
  cs := Ilog(10,Max([Round(Abs(c)): c in Eltseq(model)])); 
  if cs lt 10 then 
    vprintf Reduction, 2: "%o has coefficients\n%o\n",name,Eltseq(model);
  else
    vprintf Reduction, 2: "%o has coefficients of length %o\n",name,cs;
  end if;
  return cs;
end function;

//////////////////////////////////////////////////////////////
//                      Case n = 2                          //
//////////////////////////////////////////////////////////////

function ReduceTwo(model)
  assert Degree(model) eq 2;
  P := PolynomialRing(Integers()); X:=P.1;
  CrossTerms := (#Eltseq(model) eq 8);
  model1 := CrossTerms select CompleteTheSquare(model) else model;
  quartic := Evaluate(Equation(model1),[X,1]);
  _,M := QuarticReduce(quartic); // from CrvEll/FourDesc/quartred.m
  M := ChangeRing(M,Rationals());
  _,tr := IsTransformation(2,<1,Transpose(M)>);
  model := tr*model;
  if CrossTerms then 
    coeffs := Eltseq(model);
    r := [ -(Integers()!(coeffs[i]) div 2) : i in [1..3]];
    _,tr1 := IsTransformation(2,<1,r,Id(Rationals(),2)>);
    model := tr1*model;
    tr := tr1*tr;
  end if;
  return model,tr;
end function;

//////////////////////////////////////////////////////////////
//                      Case n = 4                          //
//////////////////////////////////////////////////////////////

SRCompare := func<b,a| Abs(a[2]) ne Abs(b[2]) 
    select Abs(b[2])-Abs(a[2]) else Abs(b[3])-Abs(a[3]) >;

function WomackTransformation(model)
// Returns a pair of "signed permutations" in GL(2,Z) and GL(4,Z)
// (just to make the final answer look pretty)
  Q := Rationals();
  assert Degree(model) eq 4;
  assert CoefficientRing(model) eq Q;
  R := PolynomialRing(model);
  q1,q2 := Explode(Equations(model));
  d0 := [<i,MC(q1,R.i^2),MC(q2,R.i^2)> : i in [1..4]]; 
  Sort(~d0, SRCompare);
  N1 := Matrix(Q,4,4,[<i,d0[i][1],1>: i in [1..4]]);
  _,tr := IsTransformation(4,<Id(Q,2),N1>);
  model := tr*model;
  qq := Equations(model);
  signs := [Q|FirstSign([MC(q,R.i^2): i in [1..4]]): q in qq];
  M := DiagonalMatrix(signs);
  _,tr := IsTransformation(4,<M,Id(Q,4)>);
  model := tr*model;
  q1,q2 := Explode(Equations(model));
  s1 := [Sign(MC(q1,R.1*R.j)): j in [1..4]];
  s2 := [MySign(MC(q2,R.1*R.j)): j in [1..4]];
  s := [Q|s1[i] ne 0 select s1[i] else s2[i]: i in [1..4]];
  N2 := DiagonalMatrix(s); 
  _,tr := IsTransformation(4,<M,N2*N1>);
  return tr;
end function;

function BQF_ReductionMatrix(f)
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

function GetRoots(F,prec) // only called from ReductionCovariantFour, deg(F)=4
  P := PolynomialRing(Rationals()); X:=P.1;
  R2<x,z> := PolynomialRing(Rationals(),2); 
  poly := DefiningPolynomial(F);
  poly /:= RationalGCD(Coefficients(poly));
  C := ComplexField(prec);
  if Degree(F) eq 4 then 
    quartic := R2!(z^4*Evaluate(poly,x/z));
    g1m := GenusOneModel(quartic);
    g1m,tr := Reduce(g1m);
    poly2 := Evaluate(Equation(g1m),[X,1]);
    I:=QuarticIInvariant(poly2); R:=QuarticRSeminvariant(poly2);
    rts:=FastRoots(ChangeRing(poly2,C) : IisZero:=I eq 0,RisZero:=R eq 0);
    a,b,c,d := Explode(Eltseq(tr`Matrix));
  else
    assert Degree(F) eq 2;
    bqf := R2!(z^2*Evaluate(poly,x/z));
    mat := BQF_ReductionMatrix(bqf);
    bqf2 := bqf^mat;
    poly2 := Evaluate(bqf2,[X,1]);
    rts := Roots(poly2,C);
    rts := [r[1] : r in rts];
    mat := Transpose(mat);
    a,b,c,d := Explode(Eltseq(mat));
  end if; 
  return [(a*rt+c)/(b*rt+d): rt in rts]; // FastRoots
end function;

function MyConjugates(x,rts);
  F := Parent(x); u := F.1;
  P := PolynomialRing(Rationals()); X:=P.1;
  poly := P!Eltseq(x); assert Evaluate(poly,u) eq x;
  return [Evaluate(poly,rt): rt in rts];
end function;

function ReductionCovariantFour(model,prec)
  Q := Rationals();
  R := RealField(prec);
  C := ComplexField(prec);
  P := PolynomialRing(Q); X:=P.1;
  a,bb,c,dd,e := Explode(SL4Invariants(model));
  covars := SL4Covariants(model);
  g := a*X^4 + 2*bb*X^3 + c*X^2 + 2*dd*X + e;
  ff := [f[1]: f in Factorization(g)| f[1] ne X];
  quadrics := <>;
  if a eq 0 then 
    qA,T1,T2,qB := Explode(covars);
    Append(~quadrics,T2 - 2*bb*qB);
  end if;    
  if e eq 0 then 
    qA,T1,T2,qB := Explode(covars);
    Append(~quadrics,T1 - 2*dd*qA);
  end if;    
  for f in ff do
    if Degree(f) gt 1 then
      F<theta> := NumberField(f);
// Since we use "Conjugates" below, we need to set the
// precision of F. This seems quite slow for large precisons, so it 
// might be worth re-writing to avoid the Kant machinery.
      SetKantPrecision(F,prec);
    else
      F := Q; 
      theta := Roots(f)[1][1];
    end if;   
    RR := PolynomialRing(F,4);
    covarsF := ChangeUniverse(covars,RR);
    qA,T1,T2,qB := Explode(covarsF);
    GG := theta^(-1)*e*qA + T1 + theta*T2 + theta^2*a*qB;
    Append(~quadrics,GG);
  end for;
  mats := <>;
  diagelts := [];
  for GG in quadrics do
    RR := Parent(GG);
    F := BaseRing(RR);
    G := Factorization(GG)[1][1];
    alpha := F!ExactQuotient(GG,G^2);
    assert alpha ne 0;
    assert GG eq alpha*G^2;
    if Degree(F) in [2,4] then 
      rts := GetRoots(F,5*prec);
      M1 := Matrix(C,4,Degree(F),[MyConjugates(MC(G,RR.i),rts): i in [1..4]]);
      aa := [C|Abs(x): x in MyConjugates(alpha,rts)];
      dg := [C|Abs(Evaluate(Derivative(g),rt)): rt in rts];
    else
      M1 := Matrix(C,4,Degree(F),[Conjugates(MC(G,RR.i)): i in [1..4]]);
      aa := [C|Abs(x): x in Conjugates(alpha)];
      dg := [C|Abs(x): x in Conjugates(Evaluate(Derivative(g),theta))];
    end if;
    Append(~mats,M1); 
    ll := [aa[i]/dg[i]^(1/2) : i in [1..Degree(F)]];
    diagelts cat:= ll;
  end for;
  M1 := HorizontalJoin(mats);
  M2 := Matrix(C,4,4,[Conjugate(M1[j,i]):i,j in [1..4]]);
  D := DiagonalMatrix(C,diagelts);
  M := M1*D*M2;
  Qmat := Matrix(R,4,4,[Re(M[i,j]): i,j in [1..4]]);
  dd := &+[Abs(x)^2: x in Eltseq(Qmat)];
  Qmat *:= dd^(-1/2);
  return Qmat + Transpose(Qmat); 
end function;

//////////////////////////////////////////////////////////////
//                      Case n = 5                          //
//////////////////////////////////////////////////////////////

function InvariantsAndHessian(model)
// Computes the invariants c4,c6 and Hessian H of a genus one model 
// of degree 5. (Calling the existing functions cInvariants and 
// Hessian separately leads to some duplication of effort.)
  assert Degree(model) eq 5;
  assert BaseRing(model) cmpeq Rationals();
  phi := Matrix(model);
  p := Equations(model);
  q := AuxiliaryQuadrics(p); // from g1invariants.m
  R := BaseRing(phi);
  RR := PolynomialRing(R); u := RR.1;
  SS<t> := quo<RR|u^4>; // this trick would speed up cInvariants
  U := Matrix(SS,5,5,[&+[MC(phi[j,k],R.i)*R.k: k in [1..5]]: i,j in [1..5]]);
  P := Matrix(R,5,5,
         [&+[MC(Deriv(p[k],j),R.i)*R.k: k in [1..5]]: i,j in [1..5]]);
  Q := Matrix(SS,5,5,[Deriv(q[i],j):i,j in [1..5]]);
  det1 := Determinant(P);
  det2 := Determinant(U+t*Q);
  T := [R|Coefficient(det2,i): i in [1,3]];
  cc := [&+[MultiFact(mon)*MC(det1,mon)*MC(d2,mon):mon in MD(R,5)]:d2 in T];
  c4 := cc[1]/40;
  c6 := -cc[2]/320;
  RR<y1,y2,y3,y4,y5> := PolynomialRing(R,5);
  M := Determinant(Matrix(RR,5,5,
         [&+[MC(Deriv(p[k],j),R.i)*RR.k : k in [1..5]]:i,j in [1..5]]));
  for ctr in [1..2] do
    M := &+[R.i*MC(q[i],R.j*R.k)*Deriv(Deriv(M,RR.j),RR.k)
	   : j,k in [1..5], i in [1..5] | j le k ];
  end for;
  q2m := [R|MC(M,RR.i): i in [1..5]];
  p22 := Eltseq(4*c4*Vector(p)-(3/16)*Vector(q2m));
  hessian := ExactPfaffianMatrix(p22,1,1); // from g1invariants.m
  coeffs := func<f|[MC(f,R.k): k in [1..5]]>;
  Umat := Matrix(10,5,[coeffs(phi[i,j]): i,j in [1..5] | i lt j]);
  Hmat := Matrix(10,5,[coeffs(hessian[i,j]): i,j in [1..5] | i lt j]);  
  Dmat := HorizontalJoin(Umat,Hmat);
  discr1 := Determinant(Dmat);
  discr2 := 12^2*(c4^3-c6^2);
  if discr1 eq -discr2 then hessian*:= -1; end if;
  return c4,c6,GenusOneModel(hessian);
end function;

function SyzygeticMatrix(model)
// This is a 3 by 5 matrix of quadratic forms. The first row contains
// the 4 by 4 Pfaffians of the model, and the last row contains the
// the 4 by 4 Pfaffians of the Hessian.
// The Hesse family has 12 singular fibres: the "syzygetic pentagons".
// These pentagons have 30 vertices in total. These make up the locus 
// where the syzygetic matrix has rank 1. (The total space of the Hesse 
// family is the locus where the matrix has rank 2.)
  assert Degree(model) eq 5;
  assert BaseRing(model) cmpeq Rationals();
  P := PolynomialRing(Rationals()); t := P.1;
  vprintf Reduction,2 : 
    "Computing the invariants, Hessian and syzygetic matrix\n";
  c4,c6,H := InvariantsAndHessian(model);
  vprintf Reduction,3 : "cInvariants = %o\n",[c4,c6]; 
  coeffsize := CoefficientSize(H:name:="Hessian");
  F := t*Vector(P,50,Eltseq(model))+Vector(P,50,Eltseq(H));
  FF := GenusOneModel(5,Eltseq(F));
  eqns := Equations(FF);
  R := PolynomialRing(model);
  RR := Universe(eqns);
  mons := MD(R,2);
  coeffs := [[MC(f,RR!mon): mon in mons]: f in eqns];
  p2 := [&+[Coefficient(c[j],2)*mons[j]: j in [1..#mons]]: c in coeffs];
  p12 := [&+[Coefficient(c[j],1)*mons[j]: j in [1..#mons]]: c in coeffs];
  p22 := [&+[Coefficient(c[j],0)*mons[j]: j in [1..#mons]]: c in coeffs];
  assert p2 eq Equations(model);
  assert p22 eq Equations(H);
  return Matrix(R,3,5,[p2,p12,p22]),c4,c6;
end function;

function ApplyToMat(tr,mat)
// Since the Hessian is a covariant, there is no need to keep 
// recomputing the syzygetic matrix.
  R := BaseRing(mat);
  S := ChangeRing(Adjoint(tr`EquationMatrix),R);
  T := Transpose(tr`Matrix);
  mat := Matrix(3,5,[mat[i,j]^T:j in [1..5],i in [1..3]]);
  return mat*S;
end function;

function SolveForPentagons(qq,C,tol)
  matR := 0;
  matC := 0;
  for quads in qq do 
    assert #quads eq 10;   // 10 homogeneous quadrics 
    RR := Universe(quads);
    assert Rank(RR) eq 5;  // in 5 variables 
    R := BaseRing(RR);     // over the reals
    mons := [RR.i*RR.j: i,j in [1..4]|i le j] cat [RR.i*RR.5: i in [1..5]];
    coeffmat := Matrix(10,15,[MC(q,mon): mon in mons,q in quads]);
    coeffmat := MyEchelonForm(coeffmat,tol);
    if coeffmat eq 0 then 
      vprintf Reduction,2 : "Pentagon not in general position\n";
      return 0,0; 
    end if;
    charmat := Matrix(4,5,[-coeffmat[i,j]: j in [11..15],i in [1..4]]);
    charmat := VerticalJoin(charmat,Vector(R,5,[1,0,0,0,0]));
    evals := Eigenvalues(charmat);
    s := func<n|n eq 1 select "ex" else "ices">;
    vprintf Reduction,2 : "Pentagon has %o real vert%o\n",#evals,s(#evals);
    realflag := true;
    if #evals ne 5 then
      charmat := ChangeRing(charmat,C);
      charpoly := CharacteristicPolynomial(charmat);
      evals := Roots(charpoly,C);
// Don't use Eigenvalues(charmat), since in "CovariantFromHyperplanes" 
// we assume the pairs of complex conjugate roots are adjacent.
      if #evals ne 5 then 
        vprintf Reduction,2 : "Unable to find all complex vertices\n";
        return 0,0; 
      end if;
      realflag := false;
    end if;
    F := realflag select R else C;
    evals := [F| x[1]: x in evals];
    mm := Minimum([Abs(evals[i]-evals[j]):i,j in [1..5]|i lt j]);
    if mm lt tol then 
      vprintf Reduction,2 : "Unable to distinguish vertices\n";
      return 0,0;
    end if;
    VdM := Matrix(F,5,5,[x^i : x in evals,i in [0..4]]);
    v := Vector(F,5,[0,0,0,0,1]);
    vv := [];
    for i in [1..5] do vv cat:= [v]; v := v*charmat; end for;
    augmat := HorizontalJoin(VdM,VerticalJoin(vv));
    augmat := MyEchelonForm(augmat,tol);
    if augmat eq 0 then return 0,0; end if;
    mat := Matrix(5,5,[augmat[i,j]: j in [6..10],i in [1..5]]);
    dd := [1/Sqrt(&+[Abs(x)^2: x in Eltseq(mat[i])]): i in [1..5]];
    mat := DiagonalMatrix(F,dd)*mat;
    if realflag then matR := mat; else matC := mat; end if;
  end for;
  return matR,matC;
end function;

function GramSchmidt(mat)
  d := Ncols(mat);
  for i := 1 to Nrows(mat) do
    s := [&+[mat[j,k]*mat[i,k]: k in [1..d]]: j in [1..i-1]];
    if i gt 1 then
      mat[i] -:= &+[s[j]*mat[j]: j in [1..i-1]];
    end if;
    n := Sqrt(&+[mat[i,j]^2 : j in [1..d]]);
    mat[i] *:= (1/n);
  end for;
  return mat;
end function;

function MyProjection(mat,vec)
  m := Nrows(mat);
  n := Ncols(mat);
  a := [&+[mat[j,k]*vec[k]: k in [1..n]]: j in [1..m]];
  vec -:= &+[a[j]*mat[j]: j in [1..m]];
  n := Sqrt(&+[vec[i]^2 : i in [1..n]]);
  return (1/n)*vec;
end function;

function RotationMatrix(theta)
  c := Cos(theta); 
  s := Sin(theta);
  return Matrix(2,2,[c,s,-s,c]);
end function;

function ClosestPointOnCircle(A,B)
// Given matrices A and B whose rows are orthonormal bases
// for subspaces V and W of Euclidean space R^d, finds 
// cos(phi)*B[1] + sin(phi)*B[2] such that distance to V
// is minimal.
  assert Ncols(A) eq Ncols(B);
  assert Nrows(B) eq 2;
  n := Nrows(A);
  M := B*Transpose(A); 
  x := &+[M[1,i]^2-M[2,i]^2: i in [1..n]];
  y := &+[2*M[1,i]*M[2,i]: i in [1..n]];
  phi := Arctan2(x,y)/2; // N.B. don't reverse the arguments!
  R := RotationMatrix(phi);
  S := R*M;  
  dd := [1-&+[S[i,j]^2: j in [1..n]]: i in [1..2]];
  dist,m := Minimum(dd);
  return R[m]*B,dist;
end function;

function CommonVector(A,B)
// Computes a basis for the intersection of the row spaces 
// of A and B, where the intersection is assumed 1-dimensional 
  assert Nrows(A) eq 5;
  assert Nrows(B) eq 3;
  A := GramSchmidt(A);
  B := GramSchmidt(B);
  M := A*Transpose(B);
  dd := [1-&+[M[i,j]^2: i in [1..5]]: j in [1..3]];
  _,m := Maximum(dd);
  AA := VerticalJoin(A,MyProjection(A,B[m]));
  BB := Matrix([Eltseq(B[i]): i in [1..3]| i ne m]);
  vec,d1 := ClosestPointOnCircle(AA,BB);
  BB := VerticalJoin(vec,B[m]);
  vec,d2 := ClosestPointOnCircle(A,BB); 
  return vec,Maximum(d1,d2);
end function;

function CovariantFromHyperplanes(realforms,complexforms,prec)
// Finds the covariant positive definite Hermitian form from the
// given linear forms associated to a elliptic normal quintic
  P := Universe(realforms);
  PP := Universe(complexforms);
  R := BaseRing(P); // real field
  Rprint := RealField(5);
  mons := MD(P,2);
  A := Matrix(R,5,15,[MC(realforms[i]^2,mon): mon in mons, i in [1..5]]);
//  vprintf Reduction,3 :  
//    "Basis for 5-dimensional vector space :\n%o\n",ChangeRing(A,Rprint);
  cc := complexforms;
  scores := [&+[Im(MC(c,PP.i))^2: i in [1..5]]: c in complexforms];
  _,m := Minimum(scores);
  if m notin {1,3,5} then
    vprintf Reduction,1 : "Failed to recognise real form\n";
    return 0;
  end if;
  case m :
    when 1 : polysC := [cc[1]^2,cc[2]*cc[3],cc[4]*cc[5]];
    when 3 : polysC := [cc[1]*cc[2],cc[3]^2,cc[4]*cc[5]];
    when 5 : polysC := [cc[1]*cc[2],cc[3]*cc[4],cc[5]^2];
  end case;
  coeffs := [[MC(f,PP!mon): mon in mons]: f in polysC];
  imsize := &+[Im(c[i])^2: i in [1..15],c in coeffs];
  vprintf Reduction,2 : "Rounding error = %o\n",Rprint!imsize;
  if imsize gt 10^(-3) then 
    vprint Reduction,1 : "Rounding error is too large";
    return 0;
  end if;
  B := Matrix(R,3,15,[Re(c[i]): i in [1..15], c in coeffs]);
//  vprintf Reduction,3 : 
//    "Basis for 3-dimensional vector space :\n%o\n",ChangeRing(B,Rprint);
  vec,dist := CommonVector(A,B);
  vprintf Reduction,2 : "Minimum distance = %o\n",Rprint!dist;
  if dist gt 10^(-3) then 
    vprint Reduction,1 : "Minimum distance is too large";
    return 0;
  end if;
  Q := &+[vec[i]*mons[i] : i in [1..#mons]];
  if MC(Q,P.1^2) lt 0 then Q := -Q; end if;
  Qmat := Matrix(R,5,5,[Deriv(Deriv(Q,i),j): i,j in [1..5]]);
  if not IsPositiveDefinite(Qmat) then 
    vprint Reduction,1 : "Covariant matrix is not positive definite";
    return 0;
  end if;
  dd := &+[Abs(x)^2: x in Eltseq(Qmat)];
  Qmat *:= dd^(-1/2);
  return Qmat + Transpose(Qmat); 
end function;

RandomMats := [
  [1,0,0,2,-2,0,-7,4,-8,6,3,0,1,6,-6,0,5,-6,9,-6,0,-2,0,-1,1],
  [-1,4,2,1,0,-1,2,1,1,0,-1,5,3,0,0,-2,9,5,2,0,1,-3,-1,-1,1],
  [3,0,-2,4,6,1,1,-2,4,1,-1,0,1,-2,-2,3,0,0,1,7,5,0,0,1,12],
  [1,1,-1,0,-1,0,1,3,-2,0,-1,-1,1,1,1,1,2,1,-2,-1,-1,-3,-8,8,2],
  [1,-1,-4,-7,-2,-2,2,3,6,0,3,-2,-5,-11,-1,1,-1,-3,-5,-1,1,-1,-2,-4,0],
  [0,-2,1,2,3,1,1,0,0,-1,0,0,0,-1,-1,0,-1,1,2,3,-2,-1,-1,-1,1]
];

function RealMultipliers(c4,c6,prec)
  R := RealField(prec);
  P := PolynomialRing(Rationals()); X:=P.1;
  if c6 ne 0 then 
    f1 := X^6 - 15*c4*X^4 + 40*c6*X^3 - 45*c4^2*X^2 + 24*c4*c6*X - 5*c6^2;
    f2 := (-2*X^5 + 30*c4*X^3 - 82*c6*X^2 + 90*c4^2*X - 33*c4*c6)/(3*c6);
    realrts := Roots(f1,R);
    vprintf Reduction,3 : 
      "RealRoots = %o\n",[RealField(15)|rt[1]: rt in realrts];
    ans := [[2*rt[1],Evaluate(f2,rt[1])]: rt in realrts];
    error if #ans ne 2,
       "Failed to compute real roots (prec = ",prec,
       ") - try increasing precision";
  else
    rt5 := Sign(c4)*SquareRoot(R!5);
    u := SquareRoot(3*rt5*c4);
    ans := [[sgn*u*(1+rt5),-3*rt5*c4]: sgn in [-1,1]];
  end if;
  return ans;
end function;

function ReductionCovariantFive(A,nos,prec)
  R := RealField(prec);
  C := ComplexField(prec);
  RR := PolynomialRing(R,5);
  CC := PolynomialRing(C,5);
  AR := ChangeRing(A,RR);
  qq := [ quads1 cat quads2
      where quads1 is [AR[2,j] - nn[1]*AR[1,j]: j in [1..5]] 
      where quads2 is [AR[3,j] - nn[2]*AR[1,j]: j in [1..5]]
		 : nn in nos ];
  ctr := 0;
  repeat
    if ctr eq 0 then 
      matR,matC := SolveForPentagons(qq,C,10^(-prec/2));
    elif ctr le #RandomMats then 
      T := Matrix(Integers(),5,5,RandomMats[ctr]);
      vprintf Reduction,2 : "We make a change of co-ordinates\n";
      TT := ChangeRing(T,R);
      qq1 := [[q^TT: q in q1]: q1 in qq];
      matR,matC := SolveForPentagons(qq1,C,10^(-prec/2));
      matR := matR*T^(-1);
      matC := matC*T^(-1);
    else 
      vprint Reduction,1 :
        "Problem was not resolved by a change of co-ordinates";
      return 0;
    end if;
    ctr +:= 1;
  until matR ne 0 and matC ne 0;
  forms1 := [&+[matR[i,j]*RR.j: j in [1..5]]: i in [1..5]];
  forms2 := [&+[matC[i,j]*CC.j: j in [1..5]]: i in [1..5]]; 
  Rprint := RealField(8);
  Cprint<i> := ComplexField(8);
  RRR<x1,x2,x3,x4,x5> := PolynomialRing(Rprint,5);
  CCC<x1,x2,x3,x4,x5> := PolynomialRing(Cprint,5);
  vprintf Reduction,3 : "Real pentagon defined by linear forms : \n%o\n",
    [&+[matR[i,j]*RRR.j: j in [1..5]]: i in [1..5]];
  vprintf Reduction,3 : "Imaginary pentagon defined by linear forms : \n%o\n",
    [&+[matC[i,j]*CCC.j: j in [1..5]]: i in [1..5]]; 
  return CovariantFromHyperplanes(forms1,forms2,prec);
end function;

//////////////////////////////////////////////////////////////
//                   Cases n = 2,3,4,5                      //
//////////////////////////////////////////////////////////////

function LLLReduceOnEquations(model)
  Q := Rationals();
  n := Degree(model);
  assert n in {4,5};
  eqns := Equations(model);
  R := Universe(eqns);
  mons := MD(R,2);
  coeffmat := Matrix(Q,#eqns,#mons,[MC(f,mon): mon in mons,f in eqns]);
  _,T := LLL(coeffmat : Delta:= 0.999);
  if n eq 5 then T := Transpose(T^(-1)); end if;
  _,tr := IsTransformation(n,<ChangeRing(T,Q),Id(Q,n)>);
  return tr*model,tr;
end function;

function LLLReduceOnAmbient(model)
  Q := Rationals();
  n := Degree(model);
  assert n in {4,5};
  d := n eq 4 select 2 else 5;
  if n eq 4 then 
    mat := ChangeRing(Matrices(model)[1],Integers());
    T := LLLGramTransformation(mat); // This is (usually) indefinite LLL
  else 
    R := PolynomialRing(model);
    phi := Matrix(model);
    coeffmat := Matrix(Q,5,10,
      [[MC(phi[j,k],R.i):j,k in [1..5]|j lt k]: i in [1..5]]);
    _,T := LLL(coeffmat : Delta:= 0.999);
  end if;
  _,tr := IsTransformation(n,<Id(Q,d),ChangeRing(T,Q)>);
  return tr*model,tr;
end function;

function AdHocReduce(model)
  Q := Rationals();
  n := Degree(model);
  assert n in {4,5};
  if n eq 4 then 
    _,tr := IsTransformation(n,<Id(Q,2),Id(Q,4)>);
  else 
    _,tr := IsTransformation(n,<Id(Q,5),Id(Q,5)>);
  end if;
  vprintf Reduction,2: "Performing ad hoc reduction \n";
  IndentPush();
  while true do
    model1,tr1 := LLLReduceOnEquations(model); 
    vprintf Reduction,2: 
      "LLL reduction on equations => %o\n",SizeString(model);
    if L2Norm(model1) lt L2Norm(model) then 
      model := model1; 
      tr := tr1*tr;
    end if;
    model1,tr1 := LLLReduceOnAmbient(model);
    vprintf Reduction,2: 
      "LLL reduction on ambient   => %o\n",SizeString(model);
    if L2Norm(model1) lt L2Norm(model) then 
      model := model1; 
      tr := tr1*tr;
    else 
      break; 
    end if; 
  end while;
  IndentPop();
  vprintf Reduction,1: "Ad hoc reduction     => %o\n",SizeString(model);
  return model,tr; 
end function;

function DefaultPrecision(n,coeffsize)
// TO DO : work out sensible default precisions
  case n :
    when 3 : return Max(10, coeffsize*3 div 2);  
       // from previous magma code
    when 4 : return 10 + 2*coeffsize; 
       // a wild guess 
    when 5 : return 50 + 12*coeffsize;
       // a guess based on a few examples
  end case;
end function;

intrinsic Reduce(model::ModelG1[FldRat] : prec:=0, Minkowski:=false) -> ModelG1, TransG1
{A reduced genus one model integrally equivalent to the given one.}

  Q := Rationals();
  K := CoefficientRing(model);
  n := Degree(model);

  require n in {2,3,4,5} : "Model must have degree 2,3,4 or 5.";
  require Discriminant(model) ne 0 : "Model is singular";
  require forall{ x : x in Eltseq(model) | IsIntegral(x) } 
    : "Coefficients of model must be integers";

  vprintf Reduction: "Reducing a genus one model of degree %o\n",n;

  if n eq 2 then 
    return ReduceTwo(model); // see above
  end if;
  idtrans1 := case<n| 3:1, 4:Id(Q,2), 5:Id(Q,5), default:"">;
  _,tr := IsTransformation(n,<idtrans1,Id(Q,n)>);
  vprintf Reduction,1: "Size of model given     %o\n",SizeString(model);
  if n in {4,5} then 
    model,tr1 := AdHocReduce(model);
    tr := tr1*tr;
  end if;
  coeffsize := CoefficientSize(model);
  if n eq 5 then syzmat,c4,c6 := SyzygeticMatrix(model); end if;
  if prec eq 0 then prec := DefaultPrecision(n,coeffsize); end if;
  vprintf Reduction,1 : "Working to real precision %o\n",prec;
  case n :
    when 3 : 
      torspts := RedTorsPts(Equation(model),prec);
    when 5 : 
      nos := RealMultipliers(c4,c6,prec);
  end case;
  history := {};
  done := false;
  earlyexit := false;
  while not done do
    vprintf Reduction,2 : 
      "Computing the reduction covariant (prec = %o)\n",prec;
    IndentPush();
    case n :
      when 3 : cov := ReductionInnerProduct(Equation(model),torspts,prec);
      when 4 : cov := ReductionCovariantFour(model,prec);
      when 5 : cov := ReductionCovariantFive(syzmat,nos,prec);
    end case;
    IndentPop();
    error if cov eq 0, 
      "Failed to compute reduction covariant ( prec =",prec,
      ") - try increasing precision";
    if n eq 3 then // scale to make nice for printing
      dd := &+[Abs(x)^2: x in Eltseq(cov)];
      cov *:= dd^(-1/2);
      cov := cov + Transpose(cov);
    end if;
    vprintf Reduction, 3:  
      "Reduction covariant:\n%o\n",ChangeRing(cov,RealField(Round(50/n)));
    if n eq 3 and IsDiagonal(cov) then 
       vprint Reduction, 2: "Diagonal matrix => early exit";
       earlyexit := true;
       break;
    end if;
    vprintf Reduction, 2: "Performing Heisenberg reduction\n";
    covZ := IntegerMatrix(cov); // Taken from earlier code for n = 4
    T := LLLGramTransformation(covZ : Delta:=0.999);
    vprintf Reduction, 3: "Transformation:\n%o\n", T;
    _,tr1 := IsTransformation(n,<idtrans1,ChangeRing(T,Q)>);
    model := tr1*model; 
    if n in {4,5} then 
      model,tr2 := LLLReduceOnEquations(model);
      tr1 := tr2*tr1;
    end if;
    vprintf Reduction,1: "Heisenberg reduction => %o\n",SizeString(model);
    mat := (tr1*tr)`Matrix;
    done := (mat in history);
    Include(~history,mat);
    if not done and n in {4,5} then 
      model,tr2 := AdHocReduce(model);
      tr1 := tr2*tr1;
    end if;
    if not done and n eq 5 then 
      vprint Reduction,2: "Updating the syzygetic matrix";
      syzmat := ApplyToMat(tr1,syzmat);
    end if;
// Perhaps could decrease precision for next iteration? 
    tr := tr1*tr;
  end while;
  if Minkowski and (not earlyexit) then 
    coeffsize := CoefficientSize(model);
    vprint Reduction,1: "Final stage - Minkowski (or LLL) reduction";
// Taken from earlier code for n = 3
    cov := tr1`Matrix*cov*Transpose(tr1`Matrix);
    c := 16;
    repeat
      c *:= 2;
      M := Matrix(n,n,[Round(c*e) : e in Eltseq(cov)]);
    until IsPositiveDefinite(M);
// Could we just use "IntegerMatrix" here?
    M := Matrix(n,n,[Round(1000*c*e) : e in Eltseq(cov)]);
/*
    vprint Reduction, 3: "Calling SuccessiveMinima"; 
    _,mins1 := SuccessiveMinima(LatticeWithGram(M));
    T := Matrix([Eltseq(v) : v in mins1]);
    vprintf Reduction, 3: "Transformation:\n%o\n", T;
*/
    _,T:=LLLGram(M : Delta:=0.99999); // use this instead
    vprintf Reduction, 3: "Transformation:\n%o\n", T;
    _,tr1 := IsTransformation(n, <idtrans1,ChangeRing(T,Q)>);
    model := tr1*model; 
    if n in {4,5} then 
      model,tr2 := LLLReduceOnEquations(model);
      tr1 := tr2*tr1;
    end if;
    tr := tr1*tr;
  end if;
  if n eq 4 then 
    tr1 := WomackTransformation(model);
// This is just a signed permutation to make the answer look pretty.
// Perhaps do something similar for n=3,5?
    model := tr1*model;
    tr := tr1*tr;
  end if;
  return model,tr;
end intrinsic;

