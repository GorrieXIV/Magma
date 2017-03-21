freeze;

// EIGHT COVERINGS  
// some routines for getting the 20 quadrics directly
// (and then minimising and reducing them)
// Version March 2010
// T. Fisher

import "8descent.m" : SingularQuadricsInThePencil,EtaleAlgebra,
                      _IntegralModel,ConicOfSingularQuadric;
//import "../CrvCon/points.m" : small_element;

Q := Rationals();
MC := MonomialCoefficient;
MD := MonomialsOfDegree;
NC := NumberOfComponents;
Id := IdentityMatrix;
Deriv := Derivative;
NiceRep := NiceRepresentativeModuloPowers;
qscore := func<qq|&+[&+[Abs(x)^2: x in Coefficients(q)]: q in qq]>;

intrinsic RationalGCD(S::Setq[RngElt]) -> RngElt
{The greatest common divisor of the elements of the set/sequence S.}
  Z := Integers();
  Q := Rationals();
  d := LCM([Denominator(Q!x):x in S| x ne 0] cat [1]);
  return Universe(S)!(GCD([Z!(x*d): x in S])/d);
end intrinsic;

intrinsic EltseqPad(x::FldNumElt) -> SeqEnum {Same as Eltseq} 
  return Eltseq(x);
end intrinsic;

function MyDegree(F)
  if ISA(Type(F),FldNum) then 
    return Degree(F); // case F a number field
  else
    return Degree(Modulus(F));  // case F an etale algebra
  end if;
end function;

function MyRowReduce(mat)
  L := PureLattice(Lattice(mat));
  return LLL(Matrix(Q,[Eltseq(x): x in Basis(L)]));
end function;

function ApplyMatrix(mat,quads)
  R := Universe(quads);
  q2 := [q^mat: q in quads];
  mons := MD(R,2);
  coeffs := Matrix(#quads,#mons,[MC(q,mon): mon in mons,q in q2]);
  coeffs := MyRowReduce(coeffs);
  n := Nrows(coeffs);
  return [&+[coeffs[i,j]*mons[j]: j in [1..#mons]]: i in [1..n]];
end function;   

// Given a fractional ideal I, finds a generator for I*J
// where J is chosen to be a product of small primes.
// Perhaps better just to use small_element ???

function IdealAlmostGenerator(I:UseSmallElt := false)
  UseSmallElt := false; // falls over when defining poly not monic
//  alpha0 := small_element(I);
  OF := Order(I); 
//  J0 := (ideal<OF|alpha0>)*I^(-1);
  clgp,map := ClassGroup(OF);  
  g0 := -(I @@ map);
  pr_list := [];
  if g0 eq clgp!0 then 
    J := ideal<OF|1>;
  else
    H := sub<clgp|>;
    p := 1;
    while g0 notin H do
      p := NextPrime(p);
      pp := Decomposition(OF,p);
      for pr in pp do
        g := pr[1] @@ map;
        if g notin H then 
          H := H + sub<clgp|g>;
          Append(~pr_list,pr[1]);
        end if;
      end for;
    end while;
    FF := FreeAbelianGroup(#pr_list);
    mm := hom<FF->clgp|[pr @@ map: pr in pr_list]>;
    soln := Eltseq(g0 @@ mm);
// to do? : closest vector
    J := &*[pr_list[i]^soln[i]: i in [1..#pr_list]];
  end if;
  flag,alpha := IsPrincipal(I*J);
  assert flag;
//  print "alpha0 =",alpha0;
//  print Factorization(J0);
//  print "alpha =",alpha;
//  print Factorization(J);
//  if UseSmallElt then return alpha0; else return alpha; end if;
   return alpha;
end function;

function NumberFieldXGCD(alpha,beta);
  F := Parent(alpha);
  OF := RingOfIntegers(F);
  FF := FieldOfFractions(OF);
  I := ideal<OF|alpha,beta>;
  flag,elt := IsPrincipal(I);
  if flag then 
    J := ideal<OF|1>;
  else
    elt := IdealAlmostGenerator(I:UseSmallElt);
    J := ideal<OF|elt>/I;
  end if;
  d := Degree(OF);
  bb := [a*t : t in Basis(J),a in [alpha,beta]];
  mm := Matrix(Rationals(),2*d,d,[Eltseq(FF!b): b in bb]);
  vv := Vector(Rationals(),Eltseq(FF!elt));
  c := RationalGCD(Eltseq(mm) cat Eltseq(vv));
  mm := ChangeRing((1/c)*mm,Integers());
  vv := ChangeRing((1/c)*vv,Integers());
  soln := Solution(mm,vv);
  r := &+[soln[i]*Basis(J)[i]: i in [1..d]];
  s := &+[soln[d+i]*Basis(J)[i]: i in [1..d]];
  assert r*alpha + s*beta eq elt;
  return F!elt,F!r,F!s;
end function;  

// Given a point P1 on the conic, finds a second point P2. 
// We try to make sure that the "additional bad primes" 
// (i.e. the primes pp where P1 and P2 have the same reduction pp) 
// are all small.

function SecondPointOnConic(conic,soln)
  eqn := Equation(conic);
  R<x,y,z> := Parent(eqn);
  F := BaseRing(R);
  OF := RingOfIntegers(F);
  FF := FieldOfFractions(OF);
  I := ideal<OF|soln>;
  dd := IdealAlmostGenerator(I);
  pt1 := [F|x/dd : x in soln];
  alpha,beta,gamma := Explode(pt1);
  ee,r,s := NumberFieldXGCD(alpha,beta);
  assert r*alpha + s*beta eq ee;
  ff,uu,vv := NumberFieldXGCD(ee,gamma);
  uu := uu/ff;
  vv := vv/ff;
  assert uu*ee + vv*gamma eq 1;
  M1 := Matrix(FF,3,3,
    [alpha,-s,-alpha*vv/ee,beta,r,-beta*vv/ee,gamma,0,uu]);
  subst1 := [&+[M1[i,j]*R.j: j in [1..3]]: i in [1..3]];
  assert Determinant(M1) eq 1;
  eqn2 := Evaluate(eqn,subst1);
  cc,alpha,beta := Explode([MC(eqn2,mon): mon in [x^2,x*y,x*z]]);
  assert cc eq 0;
  ee,uu,vv := NumberFieldXGCD(alpha,beta);
  mat := Matrix(FF,2,2,[uu,-beta/ee,vv,alpha/ee]);
  assert Determinant(mat) eq 1;
  M2 := DiagonalJoin(IdentityMatrix(FF,1),mat);
  subst2 := [&+[M2[i,j]*R.j: j in [1..3]]: i in [1..3]];
  eqn3 := Evaluate(eqn2,subst2);
  coeffs := [MC(eqn3,mon): mon in [x^2,x*y,x*z,y^2,y*z,z^2]];
  assert coeffs[1] eq 0;
  assert coeffs[3] eq 0;
  pts := [[1,0,0],[-coeffs[4],coeffs[2],0]];
  pts := [[Evaluate(s,pt): s in subst2]: pt in pts];
  pts := [[Evaluate(s,pt): s in subst1]: pt in pts];
  assert pts[1] eq pt1;
  pt2 := pts[2];
  assert Evaluate(eqn,pt2) eq 0;
  I := ideal<OF|pt2>;
  dd := IdealAlmostGenerator(I);
  pt2 := [F| x/dd : x in pt2];
  return pt1,pt2;
end function;

// Given points P1 and P2 on the conic, we consider the tangent
// line at P1, the tangent line at P2, and the chord through 
// P1 and P2. These pull back to linear forms L1,L2,M on P^3 
// such that Qsing has equation const*(L1*L2 - M^2).

function MyLinearForms(Qsing,conic,projn,pts:UseClassGroup:=true)
  R := Parent(Qsing);
  F := BaseRing(R);  
  OF := RingOfIntegers(F);
  C2 := Curve(conic);
  P1,P2 := Explode([C2!P : P in pts]);
  L1 := TangentLine(P1) @@ projn;
//  L2 := TangentLine(P2) @@ projn;
  TwoLines := Union(P1 @@ projn,P2 @@ projn);
  M := Span(Domain(projn),TwoLines);
  L1 := Equation(_IntegralModel(L1)); 
//  L2 := Equation(_IntegralModel(L2)); 
  M := Equation(_IntegralModel(M)); 
  if UseClassGroup then 
    I := ideal<OF|Coefficients(L1)>;
    dd := IdealAlmostGenerator(I);
    L1 := (1/dd)*L1;
    I := ideal<OF|Coefficients(M)>;
    dd := IdealAlmostGenerator(I);
    M := (1/dd)*M;
  end if;
  J := ideal<R|L1>;
  kk := F!(NormalForm(M^2,J)/NormalForm(Qsing,J));
  L2 := ExactQuotient(M^2 - kk*Qsing,L1);
  kappa := -1/kk;
  assert Qsing eq kappa*(L1*L2-M^2);
  return L1,L2,M,kappa;
end function;

// Given a quadric intersection phi4 over Q, and 4 four
// further quadrics defined over a degree 12 algebra FF,
// find in the space spanned by all 6 quadrics a third 
// quadric defined over Q.

function FindThirdQuadric(phi4,quads)
  R4FF := Universe(quads);
  FF<v> := BaseRing(R4FF);
  F<u> := BaseRing(FF);
  bb := [u^i*v^j: i in [0..3],j in [0..2]]; // a basis for FF over Q
  pencil := ChangeUniverse(Equations(phi4),R4FF);
  QQ := pencil cat quads;
  allq := [bb[i]*QQ[j]: i in [1..12],j in [1..6]];
  mons := MD(R4FF,2);
  toseq := func<x|&cat[EltseqPad(y): y in EltseqPad(x)]>;
  myseq := func<x|[y[i]: i in [2..12]] where y is toseq(x)>;
  mat := Matrix(72,110,[&cat[myseq(MC(q,mon)): mon in mons]: q in allq]);
  km := KernelMatrix(mat);
  assert Nrows(km) eq 3;
  a := [[&+[bb[j]*km[i,12*(k-1)+j]: j in [1..12]]: k in [1..6]]: i in [1..3]];
  qthree := [&+[a[i][j]*QQ[j]: j in [1..6]]: i in [1..3]];
  R4 := PolynomialRing(phi4);
  qthree := ChangeUniverse(qthree,R4);
  mons := MD(R4,2);
  mymat := Matrix(3,#mons,[MC(q,mon): mon in mons,q in qthree]);
  mymat := MyRowReduce(mymat);
  qnew := [&+[mymat[i,j]*mons[j]: j in [1..#mons]]: i in [1..3]];
  q1,q2 := Explode(Equations(phi4));
  assert exists(q3){q : q in qnew | q notin ideal<R4|q1,q2>};
  mat1 := Matrix(3,10,[MC(q,mon): mon in mons,q in [q1,q2,q3]]);
  mat2 := Matrix(3,10,[MC(q,mon): mon in mons,q in qthree]);
  soln := Solution(mat2,mat1);
  coeffs := [&+[soln[3,i]*a[i][j]: i in [1..3]]: j in [1..6]];
  assert R4FF!q3 eq &+[coeffs[i]*QQ[i]: i in [1..6]];
  coeffs := [coeffs[i] :  i in [3..6]];
  return q3,coeffs;
end function;

// Given a linear form L in n variables over a degree d algebra F
// computes the product of all d conjugates of L, and returns 
// the answer as an element of R (which should be a polynomial ring 
// in n variables).
 
function NormOfLinearForm(R,L)
  RF := Parent(L);
  F<u> := BaseRing(RF);
  n := Rank(RF);
  d := MyDegree(F);
  assert Rank(R) eq n;
  tomat := func<p|[EltseqPad(MC(p,RF.i)): i in [1..n]]>;
  toseq := func<mat|[&+[mat[i,j]*R.i: i in [1..n]]: j in [1..d]]>;
  Lmat := Matrix(R,d,d,[toseq(tomat(u^i*L)): i in [0..d-1]]);
  return Determinant(Lmat);
end function;

// Computes the first 8 quadrics. These define the union of 
// two eight coverings C8^+ and C8^- in P^7. Also returns
// a further 4 quadrics, defining the covering maps to C4.

function BasicQuadrics(R8,forms,vars,xi)
  R4F := Universe(forms);
  R8F := Universe(vars);
  z,zz := Explode(vars);
  tomat := func<f|[EltseqPad(MC(f,R4F.i)): i in [1..4]]>;
  mats := [tomat(f): f in forms]; 
  mat := Matrix(12,4,[[m[i,j]: i in [1..4]]: j in [1..4],m in mats]);
  mons := MD(R8,2);
  tomat := func<f|[EltseqPad(MC(f,R8F!mon)): mon in mons]>;
  mats := [tomat(q): q in [xi*z^2,xi*zz^2,xi*z*zz]];
  qq := [&+[m[i,j]*mons[i] : i in [1..#mons]]: j in [1..4],m in mats];
  _,B,_ := SmithForm(mat);
  km := KernelMatrix(mat);
  assert Nrows(km) eq 8;
  quads := [&+[km[i,j]*qq[j]: j in [1..12]]: i in [1..8]];
  xquads := [&+[B[i,j]*qq[j]: j in [1..12]]: i in [1..4]];
  return quads,xquads;
end function;

// Given a degree 4 extension of Q (either a number field or
// an etale algebra) computes its "splitting field" as an algebra.

function SetUpAlgebras(F,usenorm)
  eps1 := F.1;
  PP := PolynomialRing(F); X := PP.1;
  if ISA(Type(F),FldNum) then  // number field case
    q := DefiningPolynomial(F);
  else                         // etale algebra case
    q := Modulus(F);
  end if;
  poly := ExactQuotient(q,X-eps1);
  poly /:= LeadingCoefficient(poly);
  FF<eps2> := quo<PP|poly>; // FF<eps2> := NumberField(poly);
  iota1 := hom<F->F|eps1>;
  iota2 := hom<F->FF|eps2>;
  if usenorm then 
    return [iota1,iota2]; 
  end if;
  PPP := PolynomialRing(FF); X := PPP.1;
  poly2 := ExactQuotient(poly,X-eps2);
  FFF<eps3> := quo<PPP|poly2>;
  a,b := Explode([Coefficient(q,i): i in [4,3]]);
  eps4 := -(b/a) - eps1 - eps2 - eps3;
  iota3 := hom<F->FFF|eps3>;
  iota4 := hom<F->FFF|eps4>;
  return [iota1,iota2,iota3,iota4];
end function;

function ExtractCoefficients(R,ff)
  RR := Universe(ff);
  mons := MD(R,2);
  toseq := func<x|&cat[EltseqPad(y): y in EltseqPad(x)]>;
  mat := Matrix(36,24,[&cat[toseq(MC(f,RR!mon)):f in ff]: mon in mons]);
  mat := MyRowReduce(Transpose(mat));
//  assert Nrows(mat) eq 12;
  quads := [&+[mat[i,j]*mons[j]: j in [1..36]]: i in [1..Nrows(mat)]];
  return quads;
end function;

// The function BasicQuadrics above computed the first 8 quadrics.
// This function computes the remaining 12 quadrics for each of 
// the eight coverings C8^+ and C8^- in P^7.

function ExtraQuadrics(R8,phi4,forms,vars,xi)
  usenorm := false;
  F := BaseRing(Universe(forms)); 
  L,LL,M := Explode(forms);
  z,zz := Explode(vars);
  maps := SetUpAlgebras(F,usenorm);
  FF := Codomain(maps[2]);
  function mymap(R,poly,emb1,emb2)
    cffs := Coefficients(poly);
    mons := ChangeUniverse(Monomials(poly),R);
    poly1 := &+[emb1(cffs[i])*mons[i]: i in [1..#mons]];
    poly2 := &+[emb2(cffs[i])*mons[i]: i in [1..#mons]];
    return poly1,poly2;
  end function;
  R4FF := PolynomialRing(FF,4);
  R8FF := PolynomialRing(FF,8);
  L1,L2 := mymap(R4FF,L,maps[1],maps[2]); 
  LL1,LL2 := mymap(R4FF,LL,maps[1],maps[2]);
  M1,M2 := mymap(R4FF,M,maps[1],maps[2]);
  z1,z2 := mymap(R8FF,z,maps[1],maps[2]);
  zz1,zz2 := mymap(R8FF,zz,maps[1],maps[2]);
  if usenorm then
    Nz := NormOfLinearForm(R8FF,z);
    Nzz := NormOfLinearForm(R8FF,zz);
    z34 := ExactQuotient(Nz,z1*z2);
    zz34 := ExactQuotient(Nzz,zz1*zz2);   
    // TO DO: slow ExactQuotient here
  else    
    FFF := Codomain(maps[3]);
    R8FFF := PolynomialRing(FFF,8);
    z3,z4 := mymap(R8FFF,z,maps[3],maps[4]);
    zz3,zz4 := mymap(R8FFF,zz,maps[3],maps[4]);
    z34 := R8FF!(z3*z4);
    zz34 := R8FF!(zz3*zz4);
  end if;
  R4 := PolynomialRing(phi4);
  I4 := ideal<R4|Equations(phi4)>;
  xi12 := xi*maps[2](xi);   
  Nxi := Norm(xi);
  vprint EightDescent,4 : "Computing first new quadric";
  q3,coeffs := FindThirdQuadric(phi4,[L1*L2,L1*M2,L2*M1,M1*M2]);
  NL := NormOfLinearForm(R4,L);
  c1 := Rationals()!(NormalForm(NL,I4)/NormalForm(q3^2,I4));
  flag,b1 := IsSquare(Nxi/c1);
  assert flag;
  a,b,c,d := Explode(coeffs);
  f1 := b1*z34 - xi12*(a*z1*z2 + b*z1*zz2 + c*z2*zz1 + d*zz1*zz2);
  f2 := b1*z34 + xi12*(a*z1*z2 + b*z1*zz2 + c*z2*zz1 + d*zz1*zz2);
  vprint EightDescent,4 : "Computing second new quadric";
  qq3,coeffs := FindThirdQuadric(phi4,[LL1*LL2,LL1*M2,LL2*M1,M1*M2]);
  NM := NormOfLinearForm(R4,M);
  c3 := Rationals()!(NormalForm(NM,I4)/NormalForm(q3*qq3,I4));
  b2 := Nxi/(b1*c3);
  a,b,c,d := Explode(coeffs);
  g1 := b2*zz34 - xi12*(a*zz1*zz2 + b*zz1*z2 + c*zz2*z1 + d*z1*z2);
  g2 := b2*zz34 + xi12*(a*zz1*zz2 + b*zz1*z2 + c*zz2*z1 + d*z1*z2);
  vprint EightDescent,4 : "Extracting coefficients";
  qq1 := ExtractCoefficients(R8,[f1,g1]);
  qq2 := ExtractCoefficients(R8,[f2,g2]);
  return qq1,qq2;
end function;

// Computes two sequences of 20 quadrics, defining the eight 
// coverings C8^+ and C8^- in P^7. If flag is true then just
// returns the 8 quadrics common to both curves.

function TwentyQuadrics(phi4,lforms,xi,bb,flag)
  F := BaseRing(bb);
  R8F<v1,v2,v3,v4,w1,w2,w3,w4> := PolynomialRing(F,8);
  vars := [&+[bb[i,j]*R8F.j: j in [1..8]]: i in [1,2]];
  R8<X1,X2,X3,X4,X5,X6,X7,X8> := PolynomialRing(Rationals(),8);
  mons := MD(R8,2);
  vprint EightDescent,2 : "Computing first 8 quadrics";
  quads,xquads := BasicQuadrics(R8,lforms,vars,xi);
  mat8 := Matrix(8,#mons,[MC(q,mon): mon in mons,q in quads]);
  mat8 := MyRowReduce(mat8);
  if flag then 
    quads := [&+[mat8[i,j]*mons[j]: j in [1..#mons]]: i in [1..8]];
    return [quads],xquads;
  end if;
  vprint EightDescent,2 : "Computing next 12 quadrics";
  qq1,qq2 := ExtraQuadrics(R8,phi4,lforms,vars,xi);
  ans := [];
  for qq in [qq1,qq2] do
    mat12 := Matrix(#qq,#mons,[MC(q,mon): mon in mons, q in qq]);
    mat20 := MyRowReduce(VerticalJoin(mat8,mat12));
    quads := [&+[mat20[i,j]*mons[j]: j in [1..#mons]]: i in [1..Nrows(mat20)]];
    if #quads ne 20 then
      vprintf EightDescent,2 : "Only %o out of 20 quadrics computed\n",#quads;
      vprint EightDescent,2 : "Computing radical ....";
      I := ideal<R8|quads>;
      II := Radical(I);
      vprint EightDescent,2 : " .... done ";
      quads := MinimalBasis(II);
      assert #quads eq 20;
      mat20 := Matrix(#quads,#mons,[MC(q,mon): mon in mons, q in quads]);
      mat20 := MyRowReduce(mat20);
      quads := [&+[mat20[i,j]*mons[j]: j in [1..#mons]]: i in [1..20]];
    end if;
    ans cat:= [quads];
  end for;
  return ans,xquads; 
end function;

function ReductionTransformation(A,cob)
  P := ChangeRing(cob^(-1),BaseRing(A));
  A := P*A*Transpose(P);
  A := A + Transpose(A); 
  _,T := LLLGram(A);
  return ChangeRing(T^(-1),Rationals());
end function;


function ReductionCovariant(phi4,theta,forms,xi,basis) 

 // August 2012, SRD : added precision loop
 // (previously was always prec = 2000)
 // TO DO: better

 prec := 500;
 while true do
 vprint EightDescent, 2 : "ReductionCovariant: precision", prec;
 try

  tol := 10^(-prec/10);
  C := ComplexField(prec);
  R := RealField(prec);
  F := Parent(theta);
  for i in [1..NC(F)] do
    SetKantPrecision(F[i],prec);
  end for;
  a,b,c,d,e := Explode(SL4Invariants(phi4));
  P := PolynomialRing(Rationals()); X:=P.1;
  q := a*X^4 + 2*b*X^3 + c*X^2 + 2*d*X + e;
  assert forall{x: x in theta | Evaluate(q,x) eq 0};
  feps := <Evaluate(Deriv(q),t): t in theta>;
  Qsing := <>;
  kappa := <>;
  quartic := <>;
  for i in [1..NC(F)] do
    ff := [f[i]: f in forms];
    L1,L2,M := Explode(ff);
    RF := Universe(ff);
    q1,q2 := Explode(ChangeUniverse(Equations(phi4),RF));
    Append(~Qsing,theta[i]*q1 + q2); 
    Append(~kappa,F[i]!(Qsing[i]/(L1*L2-M^2)));
    for j in [1..4] do
      forms1 := ff cat [RF.j];
      mat1 := Matrix(4,4,[MC(f,RF.i):i in [1..4],f in forms1]);
      if Determinant(mat1) ne 0 then break; end if;
    end for;
    mat2 := Transpose(mat1^(-1));
    P0,P1,P2 := Explode([Eltseq(mat2[i]): i in [1..3]]);
    P<s,t> := PolynomialRing(F[i],2);
    lambda := [s^2*P0[i] + t^2*P1[i] + s*t*P2[i]: i in [1..4]];
    assert Evaluate(L1,lambda) eq s^2;
    assert Evaluate(L2,lambda) eq t^2;
    assert Evaluate(M,lambda) eq s*t;
    assert Evaluate(Qsing[i],lambda) eq 0;
    mat := Matrix(F[i],4,4,[Deriv(Deriv(Qsing[i],j),k): j,k in [1..4]]);
    singpt := Eltseq(KernelMatrix(mat));
    P := PolynomialRing(F[i]); X := P.1;
    PP := PolynomialRing(P); Y := PP.1;
    param := [Evaluate(lambda[j],[X,1]) + Y*singpt[j]: j in [1..4]];
    gg := Evaluate(Equations(phi4)[1],param);
    f,p,r := Explode([Coefficient(gg,i): i in [0..2]]);
    Append(~quartic,f - ExactQuotient(p^2,4*r));
  end for;   
  kconj := &cat[Conjugates(x:Precision:=prec): x in kappa];
  fconj := &cat[Conjugates(x:Precision:=prec): x in feps];
  xiconj := &cat[Conjugates(x:Precision:=prec): x in xi];
  aa := [Abs(kconj[i])^(1/2)/Abs(fconj[i])^(3/4)/Abs(xiconj[i])
                                                   : i in [1..4]];
  P := PolynomialRing(C); X := P.1;

  vprintf EightDescent,2: "Calculating embeddings ... ";
  vtime EightDescent,2:
  coeffs := [&cat[Conjugates(Coefficient(g,r):Precision:=prec)
                                    : g in quartic]: r in [0..4]];   
  gg := [&+[coeffs[r+1][j]*X^r: r in [0..4]]: j in [1..4]];
  vprint EightDescent,2: [PolynomialRing(ComplexField(8))!g : g in gg];

  // Need to tell FastRoots which invariants are zero
  Izero := [QuarticIInvariant(g) eq 0 : g in quartic];
  Rzero := [QuarticRSeminvariant(g) eq 0 : g in quartic];
  Izero := [Izero[i] : j in [1..Degree(F[i])], i in [1..NC(F)]];
  Rzero := [Rzero[i] : j in [1..Degree(F[i])], i in [1..NC(F)]];

  vprintf EightDescent,2: "Finding roots ... ";
  vtime EightDescent,2:
  rts := [FastRoots(gg[i] : IisZero:=Izero[i], RisZero:=Rzero[i]) 
         : i in [1..#gg]];
//rts := [[f[1]: f in Roots(poly)]: poly in gg];
  vprint EightDescent,2: [[ComplexField(8)!r: r in rr]: rr in rts];
  dd := [[Evaluate(Derivative(gg[i]),rt): rt in rts[i]]: i in [1..4]]; 
  c1 := [aa[i]*(&+[Abs(rts[i][k])^2/Abs(dd[i][k]): k in [1..4]])
                                                 : i in [1..4]];
  c2 := [aa[i]*(&+[    rts[i][k]   /Abs(dd[i][k]): k in [1..4]])
                                                 : i in [1..4]];
  c3 := [aa[i]*(&+[       1        /Abs(dd[i][k]): k in [1..4]])
                                                 : i in [1..4]];
  PP := Matrix(4,4,
    [&cat[Conjugates(b:Precision:=prec): b in bb] : bb in basis]);
  PP := Transpose(PP^(-1));
  PPconj := Matrix(4,4,[Conjugate(PP[i,j]):i,j in [1..4]]);
  AA := [PP*DiagonalMatrix(c)*Transpose(PPconj): c in [c1,c2,c3]];
  A := BlockMatrix(2,2,[AA[1],AA[2],Transpose(AA[2]),AA[3]]);
  diffr := Matrix(R,8,8,[Im(A[i,j]): i,j in [1..8]]);

  assert Maximum([Abs(x): x in Eltseq(diffr)]) lt tol;
  A := Matrix(R,8,8,[Re(A[i,j]): i,j in [1..8]]);
  diffr := A - Transpose(A);
  assert Maximum([Abs(x): x in Eltseq(diffr)]) lt tol;

  return A + Transpose(A);
 
 catch ERR   // assertion failure or division by zero
  prec *:= 2;
 end try;
 end while;

end function;

// Given xi in F^* representing an element of the Selmer set,
// computes equations for the corresponding eight coverings
// C8^+ and C8^- in P^7. The function returns 20 quadrics defining
// each curve, and 4 quadrics defining each covering map to C4.
// The eight coverings are reduced using the relevant reduction
// covariant, and an attempt is made to minimise at each of 
// the primes in badprimes. If flag is true then just returns 
// the 8 quadrics common to both curves.

function EightCoveringInternal(phi4,iso,lforms,xi,badprimes,flag)
  F := Domain(iso);        // etale algebra
  Fabs := Codomain(iso);   // product of number fields
  if NC(Fabs) eq 1 then 
    usefield := false;
    OF := RingOfIntegers(Fabs[1]);
    bb := [<Fabs[1]!x>  : x in Basis(OF)]; 
  else
    usefield := false;
    OF1 := RingOfIntegers(Fabs[1]);
    OF2 := RingOfIntegers(Fabs[2]);
    bb := [<Fabs[1]!x,Fabs[2]!0> : x in Basis(OF1)] 
      cat  [<Fabs[1]!0,Fabs[2]!x> : x in Basis(OF2)];
  end if;    
  vprint EightDescent,2: "Computing the reduction covariant";
  theta := iso(Domain(iso).1);
  vtime EightDescent,2:
  A := ReductionCovariant(phi4,theta,lforms,xi,bb);
  T0 := ReductionTransformation(A,Id(Q,8));
  if usefield then 
    F := Fabs[1];
    lforms := [l[1]: l in lforms];
    xi := xi[1];
    bb := [b[1]: b in bb];
  else 
    R4F<u1,u2,u3,u4> := PolynomialRing(F,4);
    function switch_to_etale_algebra(polys)
      RR := <Parent(f): f in polys>;
      coeffs := [<MC(polys[i],RR[i].j): i in [1..#polys]>: j in [1..4]];
      return &+[(coeffs[j] @@ iso)*R4F.j: j in [1..4]];
    end function;
    lforms := [switch_to_etale_algebra(f): f in lforms];
    xi := xi @@ iso;
    bb := [b @@ iso : b in bb]; 
  end if;
  bb := Matrix(F,2,8,bb cat [0: i in [1..8]] cat bb);
  bb := bb*ChangeRing(T0,F);
  allquads,xquads := TwentyQuadrics(phi4,lforms,xi,bb,flag);
  assert #allquads eq (flag select 1 else 2);
  R8<X1,X2,X3,X4,X5,X6,X7,X8> := Universe(allquads[1]); 
  qq := [];
  xqq := [];
  for quads in allquads do
    assert #quads eq (flag select 8 else 20);
    vprint EightDescent,2 : "Total quadric size =",qscore(quads);
    vprint EightDescent,2 : "Minimising";
    IndentPush();
// SetOutputFile("min-examples.m");
// printf "\n\nwhen 1 :\n";
// printf "R<X1,X2,X3,X4,X5,X6,X7,X8> := PolynomialRing(Q,8);\n\n";
// printf "quads := %o;\n\n",quads;
// printf "xquads := %o;\n\n",xquads;
// printf "badprimes := %o;\n\n",badprimes;
// printf "seq := %o;\n\n\n",Eltseq(phi4); 
// UnsetOutputFile();
    cob := MinimisationMatrix(quads,badprimes); // "higher-minimisation.m"
    IndentPop();
    cob *:= ReductionTransformation(A,T0*cob);
    newquads := ApplyMatrix(cob,quads);
    vprint EightDescent,2 : "Total quadric size =",qscore(newquads);
    qq cat:= [newquads];
    xqq cat:= [[q^cob : q in xquads]];
    vprintf EightDescent,2 : 
      "Sample quadrics\n%o\n",[newquads[i]: i in [1,#newquads]];
  end for;
  return qq,xqq;
end function;

intrinsic EightCoverings(C4,LL,Xi,Qsing,flag) -> SeqEnum, SeqEnum
{This is used by EightDescent to write the covering curves as genus one normal curves of degree 8 in P^7, and to minimise and reduce}
  phi4 := GenusOneModel(C4);
  Qsing := SingularQuadricsInThePencil(C4);
  Qsing_eqn := <Equations(x)[1]: x in Qsing>;
  LL := Parent(Qsing_eqn)!LL;
  F<eps>, iso, q := EtaleAlgebra(C4);
  Fabs := Codomain(iso);
  pp1 := {};
  pp2 := {};
  lforms := [<>: i in [1..3]];
  selreps := [<>: i in [1..#Xi]];
  for i in [1..NC(Fabs)] do
    conic,projn := ConicOfSingularQuadric(Qsing[i]);
    myline := Scheme(Ambient(Qsing[i]),[Qsing_eqn[i],LL[i]]);
    soln := Eltseq(Points(projn(myline))[1]);
    assert soln in conic;
    vprintf EightDescent,2 : "Computing second point on conic ... ";
    vtime EightDescent,2:
    pt1,pt2 := SecondPointOnConic(conic,soln);
    vprintf EightDescent,2 : "First point on conic\n%o\n",pt1;
//   vprint EightDescent,2 : "Height =",Log(HeightOnAmbient(conic!pt1));
    vprintf EightDescent,2 : "Second point on conic\n%o\n",pt2;
//   vprint EightDescent,2 : "Height =",Log(HeightOnAmbient(conic!pt2));
    OF := RingOfIntegers(Fabs[i]);
    FF := FieldOfFractions(OF);
    mat := Matrix(2,3,[pt1,pt2]);
    ff := Factorization(ideal<OF|Minors(mat,2)>);
    pp1 join:= {Minimum(f[1]): f in ff};
    vprintf EightDescent,2 : "Computing the linear forms ... ";
    vtime EightDescent,2 :
    L1,L2,M := MyLinearForms(Qsing_eqn[i],conic,projn,[pt1,pt2]);
    cc := Fabs[i]!(LL[i]/L1);
    ff1 := Factorization(ideal<OF|Coefficients(L1)>);
    ff2 := Factorization(ideal<OF|Coefficients(L2)>);
    gg := Factorization(ideal<OF|Coefficients(M)>);
    pp2 join:= {Minimum(f[1]): f in ff1 cat ff2 cat gg};
    vprint EightDescent,2 : "Finding nice representatives";
    myGCD := func<x|RationalGCD(Eltseq(FF!x))>;
    xx := [x[i]: x in SetToSequence(Xi)];
    xx := [NiceRep(x/cc,2): x in xx];
    if NC(Fabs) eq 1 then xx := [x/myGCD(x): x in xx]; end if;
    lforms := [Append(lforms[j],[L1,L2,M][j]): j in [1..3]];
    selreps := [Append(selreps[j],xx[j]): j in [1..#Xi]];
    vprint EightDescent,2 : "Selmer set =",selreps;
  end for;
  vprintf EightDescent,2 : "Bad primes from points on conic %o\n",pp1;
  vprintf EightDescent,2 : "Bad primes from linear forms %o\n",pp2;
  E := MinimalModel(Jacobian(C4));
  prime_list := &join[{2,3},pp1,pp2,Set(BadPrimes(E))];
  vprintf EightDescent,2 : "Bad primes %o\n",prime_list;
  R8<x1,x2,x3,x4,x5,x6,x7,x8> := PolynomialRing(Rationals(),8);
  maps := [];
  for xi in selreps do
    vprint EightDescent,2 : "xi =",xi;
    IndentPush();
    ff := &cat[Factorization(Integers()!Norm(x)): x in xi];
    bad_primes := prime_list join {p[1]: p in ff};
    bad_primes := Sort(SetToSequence(bad_primes));
    qq,xqq := 
      EightCoveringInternal(phi4,iso,lforms,xi,bad_primes,flag);

/******************
// Seeing if we get a nicer point on the conic in hindsight
    V := VectorSpace(Rationals(),8);
    vv := [V.i: i in [1..8]] 
      cat [V.i+k*V.j:i,j in [1..8],k in [1,2]|i lt j]; 
    elts := [[&+[v[j]*T1[i+4*k,j]*OF.i:i in [1..4],j in [1..8]]
      : k in [0,1]]:v in vv];
    forms := [s[2]*L1 - s[1]*M : s in elts];
    bestpt := pt1;
    bestht := Log(HeightOnAmbient(conic!pt1));
    for f in forms do
      eqns := Equations(Qsing[1]) cat [f];
      myline := Scheme(Ambient(Qsing[1]),eqns);
      solns := [Eltseq(P): P in Points(projn(myline))];
      for newpt in solns do
        newht := Log(HeightOnAmbient(conic!newpt));
        if newht lt bestht then   
          bestpt := newpt;
          bestht := newht;
        end if;
      end for;
    end for;
    print "In hindsight get point on conic";
    I := ideal<OF|bestpt>;
    dd := IdealAlmostGenerator(I);
    bestpt := [x/dd : x in bestpt];
    print bestpt;
    print "Height =",Log(HeightOnAmbient(conic!bestpt));
*****************/

   assert #qq[1] eq (flag select 8 else 20);
   for i in [1..#qq] do 
      C8 := Curve(Proj(R8),qq[i]);
      C8`Nonsingular := true;
      phi := map<C8 -> C4 | xqq[i] : Check := false >;  
      maps := maps cat [phi];
    end for;
    IndentPop();
  end for;
  return maps;
end intrinsic;

