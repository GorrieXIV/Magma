freeze;

// 6and12descent.m
// T. Fisher
// Version : April 2007 
// Minor changes : March 2010

declare verbose SixDescent,1;
declare verbose TwelveDescent,1;

import "../CrvG1/g1invariants.m" : TransformationToMap;

Id := IdentityMatrix;
MC := MonomialCoefficient;
MD := MonomialsOfDegree;
MWD := MonomialsOfWeightedDegree;
Deriv := Derivative;

function MyRowReduce(mat)
  L := PureLattice(Lattice(mat));
  return LLL(Matrix(Rationals(),[Eltseq(x): x in Basis(L)]));
end function;

function MyRowReduceEqns(quads,d)  
  R := Universe(quads);
  mons := MonomialsOfDegree(R,d);
  mat := Matrix(#quads,#mons,[MC(q,mon):mon in mons,q in quads]);
  mat := MyRowReduce(mat);
  quads := [&+[mat[i,j]*mons[j]: j in [1..#mons]]:i in [1..Nrows(mat)]];
  return quads;
end function;

function MaximalMinors(mat)
  n := Nrows(mat);
  assert Ncols(mat) eq n+1;
  submats := [Matrix(n,n,[mat[i,j]
    : j in [1..n+1],i in [1..n] | j ne k]): k in [1..n+1]];
  minors := [(-1)^k*Determinant(submats[k]): k in [1..n+1]];
  return minors;
end function;

AbsEltseq := func<x|&cat[Eltseq(y): y in Eltseq(x)]>;

function RationalProjections(R,poly,flag)
  d := TotalDegree(poly);
  RR := Parent(poly);
  L := BaseRing(RR);
  mons := MonomialsOfDegree(R,d);
  if flag then 
    k := AbsoluteDegree(L);
    coeffs := [AbsEltseq(MC(poly,RR!mon)): mon in mons];
  else
    k := Degree(L);
    coeffs := [Eltseq(MC(poly,RR!mon)): mon in mons];
  end if;
  polys := [R|&+[coeffs[j][i]*mons[j]: j in [1..#mons]]: i in [1..k]];
  return polys;
end function;

function QuadricToMatrix(q)
  R := Parent(q);
  B := BaseRing(R);
  n := Rank(R);
  seq := [(i eq j select 2 else 1)*MC(q,R.i*R.j):i,j in [1..n]];
  return Matrix(B,n,n,seq);
end function;

function ContravariantMatrix(f1,f2)
  B := BaseRing(Parent(f1));
  P := PolynomialRing(B); t := P.1; 
  mat1 := RMatrixSpace(P,3,3)!QuadricToMatrix(f1);
  mat2 := RMatrixSpace(P,3,3)!QuadricToMatrix(f2);
  mat := Adjoint(mat1 + t*mat2);
  return Matrix(B,3,3,[Coefficient(mat[i,j],1): i,j in [1..3]]); 
end function;

function CovariantsThree(U)
  R := Parent(U);
  H := Hessian(U);
  M := &+[ContravariantMatrix(Deriv(U,R.i),Deriv(H,R.j))*R.i*R.j
    : i,j in [1..3]];
  vecU := Vector([Deriv(U,R.i): i in [1..3]]);
  vecH := Vector([Deriv(H,R.i): i in [1..3]]);
  TH := &+[(vecU*M)[i]*vecH[i]: i in [1..3]];
  mat := Matrix(3,3,[Deriv(f,R.i): i in [1..3],f in [U,H,TH]]);
  J := (1/3)*Determinant(mat);
  return H,TH,J,M;
end function;

function CovariantMatrixSix(phi)
  assert Degree(phi) eq 2;
  B := CoefficientRing(phi);
  g := Equation(phi);
  h := -3*Equation(Hessian(phi));
  F := Equation(phi);
  RR := Parent(F);
  hmat := Matrix(2,2,[Deriv(Deriv(F,RR.i),RR.j):i,j in [1..2]]);
  H := (1/3)*Determinant(hmat);
  assert h eq -3*H;
  R<x,z,y> := PolynomialRing(B,[1,1,2]);
  g := Evaluate(g,[x,z]);
  h := Evaluate(h,[x,z]);
  H := Evaluate(H,[x,z]);
  row1 := [-9*Deriv(H,z),-3*Deriv(g,z),-x*y];
  row2 := [ 9*Deriv(H,x), 3*Deriv(g,x),-z*y];
  MM := Matrix(R,2,3,[row1,row2]);
  return MM;
end function;

Grad := func<x|Vector([Deriv(x,i): i in [1..3]])>;
CrossProduct := func<x,y|
  Vector([x[2]*y[3]-x[3]*y[2],x[3]*y[1]-x[1]*y[3],x[1]*y[2]-x[2]*y[1]])>;

function CovariantMatrixTwelve(cubic)
  assert Degree(cubic) eq 3;
  U := Equation(cubic);
  R := Parent(U);
  c4,c6 := Invariants(U);
  H,TH,J,M := CovariantsThree(U);
  x := Vector(3,[R.i: i in [1..3]]);
  u := Grad(U); 
  h := Grad(H); 
  cc := [-3*h*M + 9*c4*H*x,u*M,(2/3)*CrossProduct(u,h),(-1/3)*H*x];
  A34 := Transpose(Matrix(4,3,[Eltseq(c): c in cc]));
  return A34;
end function;

// Equations for image of phi23 : C2 -> P(Mat(2,3)) 
function EqnsForImageOfPhi23(quartic)
  phi23 := Eltseq(CovariantMatrixSix(quartic));
  R2<x,z,y> := Universe(phi23);
  eqn := y^2 - Evaluate(Equation(quartic),[x,z]); 
  R6<[x]> := PolynomialRing(Rationals(),6);
  mons2 := MD(R6,2);
  mons6 := MWD(R2,6);
  I2 := ideal<R2|eqn>;
  ff := [NormalForm(Evaluate(mon,phi23),I2): mon in mons2];
  mat := Matrix(#ff,#mons6,[MC(f,mon): mon in mons6,f in ff]);
  cc := RationalGCD(Eltseq(mat));
  mat := ChangeRing(mat/cc,Integers());
  km := KernelMatrix(mat);
  km := MyRowReduce(km);
  assert Nrows(km) eq 9;
  quads := [&+[km[i,j]*mons2[j]: j in [1..#mons2]]: i in [1..9]];  
  return quads;
end function;

// Equations for image of phi34 : C3 -> P(Mat(3,4)) 
function EqnsForImageOfPhi34(cubic)
  R3 := PolynomialRing(cubic);
  R12<[x]> := PolynomialRing(Rationals(),12);
  phi34 := Eltseq(CovariantMatrixTwelve(cubic));
  mons2 := MD(R12,2);
  mons8 := MD(R3,8);
  I3 := ideal<R3|Equation(cubic)>;
  ff := [NormalForm(Evaluate(mon,phi34),I3): mon in mons2];
  mat := Matrix(#ff,#mons8,[MC(f,mon): mon in mons8,f in ff]);
  cc := RationalGCD(Eltseq(mat));
  mat := ChangeRing(mat/cc,Integers());
  km := KernelMatrix(mat);
  km := MyRowReduce(km);
  assert Nrows(km) eq 54;
  quads := [&+[km[i,j]*mons2[j]: j in [1..#mons2]]: i in [1..54]];  
  return quads;
end function;

// Find an invertible matrix with given last column
function LastColumnToMatrix(vec)
  vec := Eltseq(vec);
  k := Universe(vec);
  n := #vec;
  idmat := IdentityMatrix(k,n);
  assert exists(j){i : i in [n..1 by -1] | vec[i] ne 0};
  ii := [i : i in [1..n] | i ne j];
  mat := Matrix(k,n,n,[Eltseq(idmat[i]): i in ii] cat [vec]);
  return Transpose(mat);
end function;

function FlexMatrixTwo(U,pt)
  k := CoefficientRing(U);
  pt := ChangeUniverse(Eltseq(pt),k);
  assert Evaluate(Equation(U),pt) eq 0;
  g1 := LastColumnToMatrix(pt);
  _,tr := IsTransformation(2,<1/Determinant(g1),Transpose(g1)>);
  U1 := tr*U;
  _,_,c,b := Explode(Eltseq(U1));
  cob := Matrix(2,2,[0,1,1,0]);
  g2 := Matrix(2,2,[36*b,0,-12*c,1]); 
  return g1*g2;
end function;

function FlexMatrixThree(U,pt)
  k := CoefficientRing(U);
  pt := ChangeUniverse(Eltseq(pt),k);
  g1 := LastColumnToMatrix(pt);
  _,tr := IsTransformation(3,<1/Determinant(g1),Transpose(g1)>);
  U1 := tr*U;
  F := Equation(U1);
  R2<Z,X> := PolynomialRing(k,2);
  R3<z,x,y> := Parent(F);
  ff := [&+[MC(F,z^(m-j)*x^j*y^(3-m))*Z^(m-j)*X^j: j in [0..m]]: m in [1..3]];
  f1,f2,f3 := Explode(ff);
  beta := MC(f1,Z);
  alpha := -MC(f1,X);
  U2 := GenusOneModel((1/4)*f2^2 - f1*f3);
  g := FlexMatrixTwo(U2,[alpha,beta]);
  subst := [g[1,1]*Z+g[1,2]*X,g[2,1]*Z+g[2,2]*X];
  ff := Evaluate(f2,subst)/Determinant(g);
  g2 := DiagonalJoin(6*g,IdentityMatrix(k,1));
  g2[3,2] := -3*MC(ff,X*Z);
  g2[3,1] := -3*MC(ff,Z^2);
  return g1*g2; 
end function;

function FlexMatrixFour(phi,pt)
  k := CoefficientRing(phi);
  pt := ChangeUniverse(Eltseq(pt),k);
  g1 := LastColumnToMatrix(pt);
  I2 := IdentityMatrix(k,2);
  _,tr := IsTransformation(4,<I2,Transpose(g1)>);
  phi1 := tr*phi;
  QQ := Equations(phi1);
  R3<X1,X2,X3> := PolynomialRing(k,3);
  R4<x1,x2,x3,x4> := PolynomialRing(phi);
  ll := [&+[MC(Q,R4.i*x4)*R3.i: i in [1..3]]: Q in QQ];
  mons3 := MD(R3,2);
  mons4 := [Evaluate(mon,[x1,x2,x3]): mon in mons3];
  qq := [&+[MC(Q,mons4[i])*mons3[i]: i in [1..6]]: Q in QQ];
  mat := Matrix(k,2,3,[MC(l,R3.i): i in [1..3],l in ll]);
  pt3 := MaximalMinors(mat);
  pt3 := [-x : x in pt3];
// assert pt3[1] eq mat[1,2]*mat[2,3] - mat[1,3]*mat[2,2];
// assert pt3[2] eq mat[1,3]*mat[2,1] - mat[1,1]*mat[2,3];
// assert pt3[3] eq mat[1,1]*mat[2,2] - mat[1,2]*mat[2,1];
  cubic := -(ll[1]*qq[2] - ll[2]*qq[1])/Determinant(g1);
  g := FlexMatrixThree(GenusOneModel(cubic),pt3);
  ll := [l^g: l in ll];
  qq := [q^g: q in qq];
  mat := Matrix(k,2,2,[MC(l,R3.i): i in [1..2],l in ll]);
// assert Determinant(g)*Determinant(g1) eq -Determinant(mat);
  mat := mat^(-1);
  ll := [&+[mat[i,j]*ll[j]: j in [1..2]]: i in [1..2]];
// assert ll eq [X1,X2];
  qq := [&+[mat[i,j]*qq[j]: j in [1..2]]: i in [1..2]];
  abc := [-6*MC(qq[1],X1*R3.i): i in [1..3]];
// linform := -(abc[1]*X1 + abc[2]*X2 + abc[3]*X3);
// assert qq[1] eq (1/6)*(X1*linform - X2^2);
// c4,c6 := Explode(cInvariants(phi));
// assert qq[2] eq (1/6)*(X2*linform - X3^2 - 27*c4*X1*X2 - 54*c6*X1^2);
  g2 := DiagonalJoin(6*g,IdentityMatrix(k,1));
  g2[4] := Vector(k,4,abc cat [1]);
  return g1*g2; 
end function;

function FlexPointThree(phi)
  cubic := phi;
  R<x,y,z> := PolynomialRing(cubic);
  U := cubic;
  H := Hessian(U);
  P := PolynomialRing(Rationals()); X:=P.1;
  U1 := Equation(U);
  H1 := Equation(H);
  poly := Evaluate(Resultant(U1,H1,x),[0,X,1]);
  poly := Factorization(poly)[1][1];
  L := NumberField(poly);
  if L cmpeq Rationals() then 
    F3 := L; 
    iso := hom<L->F3|>; 
    aa := Roots(poly)[1][1]; 
  else
    F3,iso := OptimizedRepresentation(L);
    aa := L.1;
  end if;
  alpha := iso(aa);
  R<X,Z> := PolynomialRing(F3,2);
  U2 := Evaluate(U1,[X,alpha*Z,Z]);
  H2 := Evaluate(H1,[X,alpha*Z,Z]);
  gg := GCD(U2,H2);
  if TotalDegree(gg) eq 1 then
    rr := MC(gg,X);
    ss := MC(gg,Z);
  else
    P := PolynomialRing(F3);
    poly := Evaluate(gg,[P.1,1]);
    poly := Factorization(poly)[1][1];
    L := NumberField(poly);
    F3 := AbsoluteField(L);
    alpha := F3!(L!alpha);
    rr := 1;
    ss := -F3!(L.1);
  end if;
  return [-ss,alpha*rr,rr];
end function;

function FlexPointFour(E,phi) 
  Double := func<x|CompleteTheSquare(DoubleGenusOneModel(x))>;
  assert Degree(phi) eq 4;
  A,T1,T2,B := Explode(SL4Covariants(phi));
  phi2 := Double(phi);
  P := PolynomialRing(Rationals()); X:=P.1;
  pol1 := Evaluate(Equation(phi2),[X,1]);
  a := LeadingCoefficient(pol1);
  pol2 := a^3*Evaluate(pol1,X/a);
  pol2 := Factorization(pol2)[1][1];
  F := NumberField(pol2);
  F1<u>,iso := OptimisedRepresentation(F);
  uu := iso(F.1/a);
  RR<x1,x2,x3,x4> := PolynomialRing(F1,4);
  AA,TT1,TT2,BB := Explode([RR!f : f in [A,T1,T2,B]]);
  a,b,c,d,e := Explode(SL4Invariants(phi));
  GG := (e/uu)*AA + TT1 + uu*TT2 + a*uu^2*BB;
  ff := Factorization(GG);
  G := ff[1][1];
  I := ideal<RR|AA,BB,G,x4-1>;
  gb := GroebnerBasis(I);
  PP := PolynomialRing(F1); X:=PP.1;
  S<x,y,z> := PolynomialRing(F1,3);
  II := ideal<S|[Evaluate(f,[x,y,z,1]): f in gb]>;
  II := EliminationIdeal(II,2);
  pol1 := Evaluate(Basis(II)[1],[0,0,X]);
  pol2 := Factorization(pol1)[1][1];
  if Degree(pol2) eq 1 then
    F2 := F1;
    v := Roots(pol2)[1][1];
  else
    F2<v> := NumberField(pol2);
  end if;
  S<x,y> := PolynomialRing(F2,2);
  II := ideal<S|[Evaluate(f,[x,y,v,1]): f in gb]>;
  XX := Scheme(Spec(S),II);
  pts := Points(XX);
  if #pts gt 0 then
    pt4 := [pts[1][1],pts[1][2],v,1];
  else
    F2 := AbsoluteField(F2);
    II := EliminationIdeal(II,1);
    PP := PolynomialRing(F2); X:=PP.1;
    pol1 := Evaluate(Basis(II)[1],[0,X]);
    pol2 := Factorization(pol1)[1][1];
    F3<w> := NumberField(pol2);
    S := PolynomialRing(F3); x := S.1;
    poly := GCD([Evaluate(f,[x,w,v,1]): f in gb]);
    x := Roots(poly)[1][1];
    pt4 := [x,w,v,1];
  end if;
  assert Evaluate(AA,pt4) eq 0;
  assert Evaluate(BB,pt4) eq 0;
  assert Evaluate(G,pt4) eq 0;
  return pt4;
end function;

function FlexMatrix(phi) 
// Computes a flex matrix for the genus one model phi. 
// This matrix gives an isomorphism between the genus one curve 
// defined by phi and its Jacobian.
  d := Degree(phi); 
// Only implemented for d = 3, 4.
  c4,c6 := Explode(cInvariants(phi));
  E := EllipticCurve([-27*c4,-54*c6]);
  case d :
    when 3 :
      flexpt := FlexPointThree(phi);
      L := Universe(flexpt);
      phiL := ChangeRing(phi,L);
      tt := FlexMatrixThree(phiL,flexpt);
      flexmat := Transpose(tt);
    when 4 :
      flexpt := FlexPointFour(E,phi);
      L := Universe(flexpt);
      phiL := ChangeRing(phi,L);
      flexmat := FlexMatrixFour(phiL,flexpt);
      cob := DiagonalMatrix(L,[1,1,-1,1]);
      flexmat := flexmat*cob;
      flexmat := Transpose(flexmat);
  end case;
  return flexmat;
end function;

// Twists degree 6 curve in P(Mat(2,3)) by a 3 by 3 matrix
function NineQuadrics(R6,quads,flexmat)
  L := BaseRing(flexmat);
  R6L := PolynomialRing(L,6);
  mat6 := DiagonalJoin([flexmat : i in [1..2]]);
  subst := [&+[mat6[i,j]*R6L.j: j in [1..6]]: i in [1..6]];
  mons := MD(R6,2);
  qmat := ZeroMatrix(Rationals(),0,#mons);
  for ctr in [9..1 by -1] do
    eqn := Evaluate(quads[ctr],subst);
    qq := RationalProjections(R6,eqn,false);
    mymat := Matrix(#qq,#mons,[MC(q,mon): mon in mons,q in qq]);
    qmat := VerticalJoin(qmat,mymat);
    qmat := MyRowReduce(qmat);
    rk := Nrows(qmat);
    vprintf SixDescent : "ctr = %o  #quadrics = %o\n",ctr,rk;
    error if rk gt 9, "Too many quadrics";
    if rk eq 9 then break; end if;
  end for;
  qq := [&+[qmat[i,j]*mons[j]: j in [1..#mons]]: i in [1..9]];
  return qq;
end function;

// Twists degree 12 curve in P(Mat(3,4)) by a 4 by 4 matrix
function FiftyFourQuadrics(R12,quads,flexmat)
  L := BaseRing(flexmat);
  R12L := PolynomialRing(L,12);
  mat12 := DiagonalJoin([flexmat : i in [1..3]]);
  subst := [&+[mat12[i,j]*R12L.j: j in [1..12]]: i in [1..12]];
  mons := MD(R12,2);
  qmat := ZeroMatrix(Rationals(),0,#mons);
  mm := [Evaluate(mon,subst): mon in mons];
  flag := 0;
  for ctr in [54..1 by -1] do
    eqn := &+[MC(quads[ctr],mons[j])*mm[j]: j in [1..#mons]];
    ratproj := RationalProjections(R12,eqn,true);
    mymat := Matrix(#ratproj,#mons,[MC(q,mon): mon in mons,q in ratproj]);
    mymat := MyRowReduce(mymat);
    qmat := VerticalJoin(qmat,mymat);
    qmat := LLL(qmat: Fast := 1, Proof := false);
    rk := Maximum([i : i in [1..Nrows(qmat)]| qmat[i] ne 0]);
    qmat := Matrix(rk,#mons,[qmat[i,j]: j in [1..#mons],i in [1..rk]]);
    vprintf TwelveDescent : "ctr = %o  #quadrics = %o\n",ctr,rk;
    error if rk gt 54, "Too many quadrics";
    if rk eq 54 then flag +:= 1; end if;
    if flag ge 2 then break; end if;
  end for;
  qmat := MyRowReduce(qmat);
  qq := [&+[qmat[i,j]*mons[j]: j in [1..#mons]]: i in [1..54]];
  return qq;
end function;

function SixCoveringInternal(C2,C3) 
// Computes a 6-coverings from a 2-covering C2 and 3-covering C3. 
// The genus one models C2 and C3 must have the same invariants.
  flag,iso := IsIsomorphic(Jacobian(C2),Jacobian(C3));
  assert flag;
  vprintf SixDescent : "Entering \"SixCovering\"\n%o\n%o\n",C2,C3;
  vprint SixDescent : "Computing image of 2-covering in P(Mat(2,3)) ....";
  IndentPush();
  vtime SixDescent : quads := EqnsForImageOfPhi23(C2);
  IndentPop();
  vprint SixDescent : " .... done";
  vprint SixDescent : "Computing flex matrix for 3-covering ....";
  IndentPush();
  vtime  SixDescent : flexmat := FlexMatrix(C3);
  u := IsomorphismData(iso)[4];
  flexmat := DiagonalMatrix([1,u^2,u^3])*flexmat;
  IndentPop();
  vprint SixDescent : " .... done";
  R6<[x]> := Universe(quads);
  vprintf SixDescent : "Computing the 6-covering\n";
  IndentPush();
  vtime SixDescent : qq := NineQuadrics(R6,quads,flexmat);
  vprint SixDescent : "Checking the quadrics define a curve";
  C6 := Curve(Proj(R6),qq);
  IndentPop();
  vprint SixDescent : "Leaving \"SixCovering\"";
  return C6;
end function;

function TwelveCoveringsInternal(C3,C4) 
// Computes two 12-coverings from the 3-covering C3 and 4-covering C4. 
// We require that C3 and C4 are genus one models with the same invariants.
  flag,iso := IsIsomorphic(Jacobian(C3),Jacobian(C4));
  assert flag;
  vprintf TwelveDescent : "Entering \"TwelveCovering\"\n%o\n%o\n",C3,C4;
  vprint TwelveDescent : "Computing image of 3-covering in P(Mat(3,4)) ....";
  IndentPush();
  vtime TwelveDescent : quads := EqnsForImageOfPhi34(C3);
  IndentPop();
  vprint TwelveDescent : " .... done";
  vprint TwelveDescent : "Computing flex matrix for 4-covering ....";
  IndentPush();
  vtime TwelveDescent : flexmat := FlexMatrix(C4);
  u := IsomorphismData(iso)[4];
  flexmat := DiagonalMatrix([1,u^2,u^3,u^4])*flexmat;
  IndentPop();
  vprint TwelveDescent : " .... done";
  R12<[x]> := Universe(quads);
  CC12 := [];
  for i in [1..2] do
    vprintf TwelveDescent : 
      "Computing the %o 12-covering\n",["first","second"][i];
    IndentPush();
    vtime TwelveDescent : qq := FiftyFourQuadrics(R12,quads,flexmat);
    vprint TwelveDescent : "Checking the quadrics define a curve";
    C12 := Curve(Proj(R12),qq);
    CC12 cat:= [C12];
    mm := DiagonalMatrix(BaseRing(flexmat),[1,1,-1,1]);
    flexmat := mm*flexmat;
    IndentPop();
  end for;
  return CC12;
end function;

function SixCoveringMap(E,phi3,C6,mat)
  qq := Basis(Ideal(C6));
  assert #qq eq 9;
  assert forall{q : q in qq | TotalDegree(q) eq 2};
  maxc := func<f|Maximum([Abs(c): c in Coefficients(f)])>;
  vprint SixDescent : "Curve C6 in P^5 defined by 9 quadrics";
  vprintf SixDescent : 
    "First quadric is\n%o\nwith largest coefficient %o.\n",qq[1],maxc(qq[1]);
  vprintf SixDescent : 
    "Minimisation suggests change of coordinates \n%o\n",mat;
  qq := MyRowReduceEqns([q^mat: q in qq],2);
  vprintf SixDescent : 
    "First quadric is\n%o\nwith largest coefficient %o.\n",qq[1],maxc(qq[1]);
  R := Universe(qq); 
  C6min := Curve(Proj(R),qq);
  subst := [&+[mat[i,j]*R.j: j in [1..6]]: i in [1..6]];
  iso := map<C6min->C6|subst>;
  mat23 := Matrix(R,2,3,[R.i: i in [1..6]]);
  C3 := Curve(phi3);
  pi2 := map<C6->C3|MaximalMinors(mat23)>;
  return iso*pi2;
end function; 

function TwelveCoveringMap(E,phi4,C12,mat)
  qq := Basis(Ideal(C12));
  assert #qq eq 54;
  assert forall{q : q in qq | TotalDegree(q) eq 2};
  maxc := func<f|Maximum([Abs(c): c in Coefficients(f)])>;
  vprint TwelveDescent : "Curve C12 in P^11 defined by 54 quadrics";
  vprintf TwelveDescent : 
    "First quadric is\n%o\nwith largest coefficient %o.\n",qq[1],maxc(qq[1]);
  vprintf TwelveDescent : 
    "Minimisation suggests change of coordinates \n%o\n",mat;
  qq := MyRowReduceEqns([q^mat: q in qq],2);
  vprintf TwelveDescent : 
    "First quadric is\n%o\nwith largest coefficient %o.\n",qq[1],maxc(qq[1]);
  R := Universe(qq); 
  C12min := Curve(Proj(R),qq);
  subst := [&+[mat[i,j]*R.j: j in [1..12]]: i in [1..12]];
  iso := map<C12min->C12|subst>;
  mat34 := Matrix(R,3,4,[R.i: i in [1..12]]);
  C4 := Curve(phi4);
  pi3 := map<C12->C4|MaximalMinors(mat34)>;
  return iso*pi3;
end function; 

intrinsic SixDescent(model2::ModelG1,model3::ModelG1:C3 := Curve(model3)) 
 -> Crv,MapSch
{Computes a 6-coverings C6 from the given 2-covering C2 and 3-covering C3 of the elliptic curve E. The covering map C6 -> C3 is also returned.}
  PlaneCubic := C3;
  C2 := model2;
  C3 := model3;
  require Degree(C2) eq 2 and Degree(C3) eq 3 : "Models must have degrees 2 and 3";
  Z := Integers();
  Q := Rationals();
  if BaseRing(C2) cmpeq Z then C2 := ChangeRing(C2,Q); end if;
  if BaseRing(C3) cmpeq Z then C3 := ChangeRing(C3,Q); end if;
  require BaseRing(C2) cmpeq Q and BaseRing(C3) cmpeq Q : 
    "Models must be defined over the rationals";
  C2red := Reduce(Minimise(C2));
  C3min,tr3a := Minimise(C3);
  C3red,tr3b := Reduce(C3min);
  tr3 := tr3b*tr3a;
  E2 := Jacobian(C2red);
  E3 := Jacobian(C3red);
  flag,iso := IsIsomorphic(E2,E3);
  require flag : "Models must have the same Jacobian";
  E := MinimalModel(E2);
  _,tr := IsTransformation(2,<IsomorphismData(iso)[4],Id(Q,2)>);
  C2red := tr*C2red;
  assert cInvariants(C2red) eq cInvariants(C3red);
  C6 := SixCoveringInternal(C2red,C3red);
  qq := Basis(Ideal(C6));
  mat := MinimisationMatrix(qq,BadPrimes(E)); 
  pi := SixCoveringMap(E,C3red,C6,mat);
  C6min := Domain(pi);
  C6min`Nonsingular := true;
  iso := TransformationToMap(C3,C3red,tr3
           :Domain := Codomain(pi),Codomain := PlaneCubic); 
  return C6min,pi*iso;
end intrinsic;

intrinsic SixDescent(C2::CrvHyp,C3::Crv) -> Crv,MapSch
{"} //"
  model2 := GenusOneModel(C2);
  model3 := GenusOneModel(C3);
  return SixDescent(model2,model3:C3 := C3);
end intrinsic;

intrinsic TwelveDescent(model3::ModelG1,model4::ModelG1:C4:=Curve(model4)) 
 -> SeqEnum[Crv],SeqEnum[MapSch]
{Computes two 12-coverings C12 from the given 3-covering C3 and 4-covering C4 of the elliptic curve E. The covering maps C12 -> C4 are also returned.}
  QuadricIntersection := C4;
  C3 := model3;
  C4 := model4;
  require Degree(C3) eq 3 and Degree(C4) eq 4 : "Models must have degrees 3 and 4";
  Z := Integers();
  Q := Rationals();
  if BaseRing(C3) cmpeq Z then C3 := ChangeRing(C3,Q); end if;
  if BaseRing(C4) cmpeq Z then C4 := ChangeRing(C4,Q); end if;
  require BaseRing(C3) cmpeq Q and BaseRing(C4) cmpeq Q : 
    "Models must be defined over the rationals";
  C3red := Reduce(Minimise(C3));
  C4min,tr4a := Minimise(C4);
  C4red,tr4b := Reduce(C4min);
  tr4 := tr4b*tr4a;
  E3 := Jacobian(C3red);
  E4 := Jacobian(C4red);
  flag,iso := IsIsomorphic(E3,E4);
  require flag : "Models must have the same Jacobian";
  E := MinimalModel(E3);
  _,tr := IsTransformation(3,<IsomorphismData(iso)[4],Id(Q,3)>);
  C3red := tr*C3red;
  assert cInvariants(C3red) eq cInvariants(C4red);
  CC12 := TwelveCoveringsInternal(C3red,C4red);
  maps := [];
  for C12 in CC12 do
    qq := Basis(Ideal(C12));
    mat := MinimisationMatrix(qq,BadPrimes(E)); 
    pi := TwelveCoveringMap(E,C4red,C12,mat);
    C12min := Domain(pi);
    C12min`Nonsingular := true;
    iso := TransformationToMap(C4,C4red,tr4
           :Domain := Codomain(pi),Codomain := QuadricIntersection); 
    maps cat:= [pi*iso];
  end for;
  return [Domain(pi): pi in maps],maps;
end intrinsic;

intrinsic TwelveDescent(C3::Crv,C4::Crv) -> Crv,MapSch
{"} //"
  model3 := GenusOneModel(C3);
  model4 := GenusOneModel(C4);
  return TwelveDescent(model3,model4:C4 := C4);
end intrinsic;
