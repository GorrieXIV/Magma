freeze;

//  Tesing equivalence of genus one models
//  Written by:  Tom Fisher
//  Version:     November 2006.

// This file contains intrinsics :-  
//
//   TwoTorsionOrbits(E)
//   TwoSelmerElement(E,quartic)
//   TwoTorsionMatrices(E,quartic)
//   RamificationPoints(f2)
//   RelativeSelmerElement(f2,f4)
//   IsEquivalent(model1,model2)  // now working for n = 2,3,4

// T. Fisher, April 2010 : converted to use new TransG1 type

declare attributes CrvEll: TwoTorsionOrbits;
declare attributes ModelG1: RamificationPoints;

import "g1invariants.m" : QuadricToMatrix;

Z := Integers();
Q := Rationals();
I2 := IdentityMatrix(Q,2);
I4 := IdentityMatrix(Q,4);
P := PolynomialRing(Q); X := P.1;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 2                           //
//                                                         //
/////////////////////////////////////////////////////////////

intrinsic TwoTorsionOrbits(E::CrvEll[FldRat] : OptimisedRep:=false) -> Tup
{Computes <T_1, ... , T_r> where the T_i are representatives for 
the Galois orbits on E[2] - O. }
  if assigned E`TwoTorsionOrbits then
    return E`TwoTorsionOrbits;
  end if;
  a1,_,a3 := Explode(aInvariants(E));
  b2 := Explode(bInvariants(E));
  c4,c6 := Explode(cInvariants(E));
  P := PolynomialRing(Q); X := P.1;
  F := X^3 - 27*c4*X - 54*c6;
  FF := [f[1] : f in Factorization(F)];
  function torspt(L,rt)
    x := (rt - 3*b2)/36;
    return E(L)![x,-(a1*x + a3)/2];
  end function;
  TT := <torspt(Q,Roots(f)[1][1]) : f in FF | Degree(f) eq 1>;
  if exists(f){f : f in FF | Degree(f) gt 1} then
    L<u> := NumberField(f);
    if OptimisedRep then 
      L := OptimisedRepresentation(L);
      u := L!u;
    end if;
    Append(~TT,torspt(L,u));
  end if;
  E`TwoTorsionOrbits := TT;
  return TT;
end intrinsic;

function irrationalinvariant(quartic,xT)
  a,b,c,d,e := Explode(ModelToSequence(quartic));
  phi := (-1/12)*xT;
  zz := (4*a*phi - 8*a*c + 3*b^2)/3;
  if zz eq 0 then 
    zz := ((phi + c)/3)^2 - 4*a*e;
  end if;
  return zz;
end function;

function torsmat2(quartic,xT)
  a,b,c,d,e := Explode(ModelToSequence(quartic));
  phi := (-1/12)*xT;
  alpha1 := 4*a*phi - 8*a*c + 3*b^2;
  alpha2 := b*phi - 6*a*d + b*c;
  alpha3 := -2/3*phi^2 + 2/3*c*phi - 3*b*d + 4/3*c^2;
  M := Matrix(2,2,[-alpha2,-alpha3,alpha1,alpha2]);
  if alpha1 eq 0 then 
    beta1 := alpha2;
    beta2 := 1/3*phi^2 + 2/3*c*phi - 12*a*e + 1/3*c^2;
    beta3 := d*phi - 6*b*e + c*d;
    M := Matrix(2,2,[-beta2,-beta3,beta1,beta2]);
  end if;
  return M;
end function;

intrinsic TwoSelmerElement(E::CrvEll[FldRat],quartic::ModelG1) -> Tup
{Given a binary quartic with the same invariants as E, returns the
corresponding element in (the algebra associated to) the 2-Selmer group of E.}
  require Degree(quartic) eq 2 
    : "Input must be a genus one model of degree 2.";
  require cInvariants(quartic) eq cInvariants(E) 
    : "Binary quartic and elliptic curve must have the same invariants.";
  require #Eltseq(quartic) eq 5 
    : "Not implemented yet for binary quartics with cross terms";  
  torspts := TwoTorsionOrbits(E);
  a1,a2,a3 := Explode(aInvariants(E));
  zz := func<T|irrationalinvariant(quartic,xT) 
    where xT is 36*T[1] + 3*(a1^2 + 4*a2)>;
  alpha := <zz(T) : T in torspts>;
  return alpha;
end intrinsic;

intrinsic TwoTorsionMatrices(E::CrvEll[FldRat],quartic::ModelG1) -> Tup
{Given a binary quartic with the same invariants as E, computes a matrix 
in GL_2(L) describing the action of E[2] on the quartic, 
where E[2] - \{0\} = Spec L.}
  require Degree(quartic) eq 2 
    : "Input must be a genus one model of degree 2.";
  require cInvariants(quartic) eq cInvariants(E) 
    : "Binary quartic and elliptic curve must have the same invariants.";
  require #Eltseq(quartic) eq 5 
    : "Not implemented yet for binary quartics with cross terms";  
  torspts := TwoTorsionOrbits(E);
  a1,a2,a3 := Explode(aInvariants(E));
  mat := func<T|torsmat2(quartic,xT) 
    where xT is 36*T[1] + 3*(a1^2 + 4*a2)>;
  return <mat(T) : T in torspts>;
end intrinsic;

function IsEqualModSquares(r1,r2);
  m := #r1;
  rts := <>;
  for i in [1..#r1] do
//    flag,t := IsSquare(r1[i]/r2[i]);
    flag,t := HasRoot(Polynomial([-r1[i]/r2[i],0,1]));
    if flag then 
      rts := Append(rts,t);
    else
      break;
    end if;
  end for;
  return flag,rts;
end function;

function LinearSolve(M1,M2,n)
  m := #M1;
  L := <BaseRing(M1[i]): i in [1..m]>;
  degs := [Degree(L[i]) : i in [1..m]];
  assert &+degs eq n^2-1;  
  mats1 := &cat[[Matrix(Q,n,n,[Eltseq(M1[t][i,j])[k] :i,j in [1..n]])
     : k in [1..degs[t]]] : t in [1..m]];
  mats2 := &cat[[Matrix(Q,n,n,[Eltseq(M2[t][i,j])[k] :i,j in [1..n]])
     : k in [1..degs[t]]] : t in [1..m]];  
  M := MatrixAlgebra(Q,n);
  m1 := ChangeUniverse(mats1,M); 
  m2 := ChangeUniverse(mats2,M);
  mat := Matrix(Q,n^2,n^2*(n^2-1),
    [ &cat[Eltseq(Eij*m1[k]-m2[k]*Eij) : k in [1..n^2-1]] : Eij in Basis(M)]); 
  km := KernelMatrix(mat);
  if Nrows(km) eq 1 then 
    soln := &+[km[1,i]*Basis(M)[i] : i in [1..n^2]];
    assert forall{i: i in [1..n^2-1] | soln*m1[i] eq m2[i]*soln};
  else 
    soln := M!0;
  end if;
  return soln;
end function;   

function IsEquivalentTwo(quartic1,quartic2,E)
  quartic1,g1 := RemoveCrossTerms(quartic1);
  quartic2,g2 := RemoveCrossTerms(quartic2);
  gg2 := InverseTransformation(g2);
  E2 := Jacobian(quartic2);
  flag,iso := IsIsomorphic(E,E2);
  if not flag then return false,_; end if;
  r,s,t,u := Explode(IsomorphismData(iso));
  originalquartic2 := quartic2;
  _,tr := IsTransformation(2,<1/u,I2>);
  quartic2 := tr*quartic2;
  assert cInvariants(quartic2) eq cInvariants(E);
  z1 := TwoSelmerElement(E,quartic1);
  z2 := TwoSelmerElement(E,quartic2);
  flag,sqrt := IsEqualModSquares(z1,z2);
  if not flag then return false,_; end if;
  M1 := TwoTorsionMatrices(E,quartic1);
  M2 := TwoTorsionMatrices(E,quartic2);
  M2 := <sqrt[i]*M2[i] : i in [1..#M2]>;
  detM1 := <Determinant(m) : m in M1>;
  detM2 := <Determinant(m) : m in M2>;
  assert detM1 eq detM2;
  L := CartesianProduct(<BaseRing(M): M in M1>);
  m := NumberOfComponents(L);
  for z in {-1,1} do   
    M2z := <z*M2[i] : i in [1..m]>;
    B := LinearSolve(M1,M2z,2);
    if B ne 0 then break; end if;
  end for;
  assert B ne 0;
  BB := B^(-1);
  dd := RationalGCD(Eltseq(BB));
  _,g := IsTransformation(2,<dd^2*u*Determinant(B),(1/dd)*Transpose(BB)>);
  assert g*quartic1 eq originalquartic2; 
  return true,gg2*g*g1;
end function;

/////////////////////////////////////////////////////////////
//                                                         //
//                         n = 4                           //
//                                                         //
/////////////////////////////////////////////////////////////

intrinsic RamificationPoints(f2::ModelG1) -> Tup
{Given a non-singular genus one model of degree 2 (over Q) without
cross terms, computes <R_1, ... , R_t> where the R_i are 
representatives for the Galois orbits of ramification points.}
  if assigned f2`RamificationPoints then
    return f2`RamificationPoints;
  end if;
  require Degree(f2) eq 2 : "Argument must be a genus one model of degree 2";
  require #Eltseq(f2) eq 5 : "Model should not have cross terms.";
  require Discriminant(f2) ne 0 : "Model is singular.";
  require CoefficientRing(f2) cmpeq Q 
     : "Argument must be defined over the rationals.";
  C := Curve(f2);
  poly :=  Evaluate(Equation(f2),[X,1]);
  ff := Factorization(poly);
  RR := <C(Q)![a[1],1,0] : a in Roots(poly)>;
  if Degree(poly) eq 3 then 
    Append(~RR,C(Q)![1,0,0]); 
  end if;
  for f in ff do
    if Degree(f[1]) gt 1 then 
      L<u> := NumberField(f[1]);
// Optimising would be a waste of time, since this isn't going
// to be called by FourDescent.
      Append(~RR,C(L)![u,1,0]);
    end if;
  end for;
  f2`RamificationPoints := RR;
  return RR;
end intrinsic;

function Double(phi)
  a,b,c,d,e := Explode(SL4Invariants(phi));
  return GenusOneModel(2,[a/4,b/2,c/4,d/2,e/4]);
end function;

intrinsic RelativeSelmerElement(f2::ModelG1,f4::ModelG1:m:=1) -> Tup 
{Given f4, a non-singular genus one model of degree 4 (over Q), that is a 2-covering of f2, computes the corresponding element in L^* / Q^* (L^*)^2 where L is the algebra corresponding to the ramification points of f2. There is an option to compute m elements of L^* representing the same coset.}

  require Degree(f2) eq 2 
    : "f2 must be a genus one model of degree 2.";
  require Degree(f4) eq 4 
    : "f4 must be a genus one model of degree 4.";
  require CoefficientRing(f2) cmpeq Q and CoefficientRing(f4) cmpeq Q
    : "Arguments must be defined over Q.";
  require Discriminant(f2) ne 0 : "The arguments must be non-singular.";
  require Eltseq(Double(f4)) eq Eltseq(f2)
    : "f2 must be the double of f4.";

  RR := RamificationPoints(f2);
  A,T1,T2,B := Explode(SL4Covariants(f4));
  a,b,c,d,e := Explode([4*x : x in Eltseq(f2)]);  

  V := VectorSpace(Q,4);
  ptlist := [V.i : i in [1..4]] cat [V.i + V.j: i,j in [1..4]| i lt j];
  ptlist := [Eltseq(pt) : pt in ptlist];
  elts := [<> : i in [1..m]];
  vecs := [<> : i in [1..4]];

  for R in RR do
    u,v := Explode(Eltseq(R));
    P<x1,x2,x3,x4> := PolynomialRing(Ring(Parent(R)),4);
    if u ne 0 and v ne 0 then 
      GG := (e*v^2/u)*(P!A) + v*(P!T1) + u*(P!T2) + a*(u^2/v)*(P!B);
    else
      GG := -d*v*(P!A) + v*(P!T1) + u*(P!T2) - b*u*(P!B);
    end if;
    M := QuadricToMatrix(GG);
    assert Rank(M) eq 1;
    zz := [];
    for pt in ptlist do
      z := Evaluate(GG,pt);
        if z ne 0 then  
          zz cat:= [z];
          if #zz eq 1 then 
            vec := [Evaluate(Derivative(GG,P.i),pt): i in [1..4]];
          end if;
        end if;
      if #zz eq m then break; end if;
    end for;
    elts := [Append(elts[i],zz[i]): i in [1..m]];
    vecs := [Append(vecs[i],vec[i]): i in [1..4]];
  end for;
  return elts,vecs;
end intrinsic;

function ChooseRandomPrimes(f,nprimes,S,coeffs)
  pp := [];
  while #pp lt nprimes do
    p := RandomPrime(20);
    if p notin S and forall{c : c in coeffs | Valuation(c,p) ge 0} then 
      rts := Roots(PolynomialRing(GF(p))!f);  
      if #rts gt 0 then 
        pp cat:= [<p,Z!(rt[1])> : rt in rts];
      end if;
    end if;
  end while;
  return pp;
end function;

function IsTupleSquare(xx);
  rts := <>;
  for x in xx do
    flag,t := HasRoot(Polynomial([-x,0,1]));
    if flag then 
      rts := Append(rts,t);
    else
      break;
    end if;
  end for;
  return flag,rts;
end function;

function IsRationalTimesSquare(seq,S)

// Each element of the sequence should represent the same element of
// L^*/(L^*)^2. This function determines whether that element is 
// in the image of Q(S,2).
// We assume for each prime of L outside S that some element
// in the sequence is a local unit.

  S := Sort(SetToSequence({-1} join S));
  LL := Universe(seq); 
  m := NumberOfComponents(LL);
  mat := ZeroMatrix(Z,#S,0);
  vec := []; 
 
  for j in [1..m] do
    F := DefiningPolynomial(LL[j]);
    polys := [&+[cc[i]*X^(i-1): i in [1..#cc]] 
              where cc is Eltseq(x[j]): x in seq];
    coeffs := &cat[Coefficients(poly): poly in [F] cat polys];
    pp := ChooseRandomPrimes(F,2*#S+5,S,coeffs);
    MyEvaluate := func<f,x,p|Z!Evaluate(PolynomialRing(GF(p))!f,GF(p)!x)>;
    mat1 := Matrix(Z,#S,#pp,[LegendreSymbol(a,p[1]): p in pp,a in S]);
    mat2 := Matrix(Z,#seq,#pp,
      [LegendreSymbol(MyEvaluate(f,p[2],p[1]),p[1]): p in pp,f in polys]);
    for j in [1..#pp] do
      symbols := {mat2[i,j] : i in [1..#seq] | mat2[i,j] ne 0};
      assert #symbols eq 1;
      vec cat:= SetToSequence(symbols);
    end for;
    mat := HorizontalJoin(mat,mat1);
  end for;

  toGF2 := func<x|x eq 1 select 0 else 1>;
  mat := Matrix(GF(2),Nrows(mat),Ncols(mat),[toGF2(x): x in Eltseq(mat)]);
  vec := Vector(GF(2),#vec,[toGF2(x): x in vec]);
  flag,soln,km := IsConsistent(mat,vec);
  if not flag then return false,_,_; end if;
  km := Matrix(Basis(km));
  solns := [Eltseq(soln + v*km) : v in VectorSpace(GF(2),Nrows(km))];    
  TT := [&*[S[i]^(Z!(e[i])) : i in [1..#S]] : e in solns];

  vprintf FourDescent,1 : "Looping through %o possibilities\n",#TT;

// N.B. Sometimes more than one solution, but this is always
// "explained" by 2-torsion. So we'll take the first we find.

  for t in TT do
    flag,u := IsTupleSquare(<t*x : x in seq[1]>);
    if flag then return true,t,u; end if;
  end for;
  return false,_,_;
end function;

function MyBadPrimes(x)
  f := MinimalPolynomial(x);
  d := LCM([Denominator(a): a in Coefficients(f)]);
  return LCM(d,Numerator(Coefficient(f,0)));
end function;

function BadPrimesForElements(seq)
  seq := [Z|MyBadPrimes(x): x in xx, xx in seq];
  return SequenceToSet(PrimeDivisors(GCD(seq)));
end function;

function IsEquivalentTwoTwo(f2,f4,g4)

// -> BoolElt,Tup
// {Given f4 = (A1,B1) and g4 = (A2,B2), non-singular 
// genus one models of degree 4 (over Q) with f2(x,z) = det(x*A1 + z*B1) 
// = det(x*A2 + z*B2), determines whether phi1 and phi2 are equivalent 
// in the sense that A2 = mu M A1 M^T and B2 = mu M B1 M^T for some
// mu in Q^* and M in GL(4,Q) with mu^4 (det M)^2 = 1.
// If true, the transformation g = <mu*I2,M> is also returned.}
//  require Degree(f2) eq 2 and Degree(f4) eq 4 and Degree(g4) eq 4  
//    : "The arguments must be genus one models of degrees 2, 4 and 4.";
//  require CoefficientRing(f2) cmpeq Q 
//   and CoefficientRing(f4) cmpeq Q and CoefficientRing(g4) cmpeq Q
//    : "The arguments must be defined over the rationals.";
//  require Discriminant(f2) ne 0 : "The arguments must be non-singular.";
//  require Eltseq(Double(f4)) eq Eltseq(f2) : "f2 must be the double of f4.";
//  require Eltseq(Double(g4)) eq Eltseq(f2) : "f2 must be the double of g4.";
 
  RR := RamificationPoints(f2);
  alphas,xx := RelativeSelmerElement(f2,f4:m := 3);
  betas,yy := RelativeSelmerElement(f2,g4:m := 3);
  seq := [<alphas[i][j]/betas[i][j]: j in [1..#RR]>: i in [1..3]];

  vprintf FourDescent,1: "Factoring the discriminant\n";
//  We need to decide whether an element in L^*/(L^*)^2 
//  is in the image of Q^*/(Q^*)^2. The factoring is required
//  to cut the search down to Q(S,2) for suitable S.
  d := Denominator(RationalGCD(Eltseq(f2)));
  vtime FourDescent,1: S := PrimeDivisors(Numerator(Discriminant(f2)));
  vtime FourDescent,1: S cat:= PrimeDivisors(d);
  S := SequenceToSet(S) join BadPrimesForElements(seq);
  flag,t,u := IsRationalTimesSquare(seq,S);

  if not flag then return false,_; end if;

  yy := [<u[i]*y[i] : i in [1..#RR]>: y in yy];
  MyEltseq := func<aa|&cat[Eltseq(a): a in aa]>;
  mat := Matrix(Q,4,4,[MyEltseq(x): x in xx]);
  solns := [Solution(mat,Vector(Q,4,MyEltseq(y))): y in yy];
  _,ans := IsTransformation(4,<t*I2,(1/t)*Matrix(Q,4,4,solns)>);

  assert (g4 eq ans*f4);
  return true,ans;

end function;

function IsEquivalentFour(f4,g4,E) 

// {Given f4 and g4, non-singular genus one models of degree 4 (over Q), 
// determines whether they are equivalent (over Q), and if so also returns a 
// transformation relating them.}
//   require Degree(f4) eq 4 and Degree(g4) eq 4
//    : "The arguments must be genus one models of degree 4.";
//  require CoefficientRing(f4) cmpeq Q and CoefficientRing(g4) cmpeq Q 
//    : "The arguments must be defined over Q.";
//  require Discriminant(f4) ne 0 and Discriminant(g4) ne 0 
//    : "The arguments must be non-singular.";
//  require cInvariants(E) eq cInvariants(f4) 
//    : "The first argument must have the same invariants as E.";

  f2 := Double(f4);
  g2 := Double(g4);
  flag,tr2 := IsEquivalentTwo(f2,g2,E);

  if not flag then return false,_; end if;

  M2 := TwoTorsionMatrices(E,f2);
  M2Q := [I2] cat [M : M in M2 | BaseRing(M) cmpeq Q];
  hh := [tr2*tr1 where _,tr1 is 
    IsTransformation(2,<1/Determinant(M),Transpose(M)>) : M in M2Q];
 
  for h2 in hh do
    h4 := <h2`Matrix,DiagonalMatrix([1,1,1,h2`Scalar])>;
    _,h4 := IsTransformation(4,h4);
    gg4 :=  h4^(-1)*g4; 
    flag,tr4 := IsEquivalentTwoTwo(f2,f4,gg4);
    if flag then 
      ans := h4*tr4; 
      d := RationalGCD(Eltseq(ans`Matrix));
      _,tr := IsTransformation(4,<d^2*ans`EquationMatrix,(1/d)*ans`Matrix>);
      return true,tr;
    end if;
  end for;

  return false,_;

end function;

/////////////////////////////////////////////////////////////
//                                                         //
//                      n = 2, 3, 4, 5                     //
//                                                         //
/////////////////////////////////////////////////////////////

intrinsic IsEquivalent(model1::ModelG1,model2::ModelG1: 
  E := Degree(model1) eq 5 select MinimalModel(Jacobian(model1)) else Jacobian(model1) ) -> BoolElt,Tup 
{Determines whether two non-singular genus one models over Q are equivalent,
and if so also returns the transformation relating them.}
  n := Degree(model1);
  require Degree(model2) eq n : "Models must have the same degree";
//  require n ne 5 : "Not implemented yet for models of degree 5";
  require CoefficientRing(model1) cmpeq Q 
    : "Models must be defined over the rationals";
  require CoefficientRing(model2) cmpeq Q 
    : "Models must be defined over the rationals";
  require n eq 5 or cInvariants(model1) eq cInvariants(E)
    : "First model must have the same invariants as E";
  if n eq 2 then
    return IsEquivalentTwo(model1,model2,E); 
                  // function defined in this file
  elif n eq 3 then 
    return IsEquivalent(Equation(model1),Equation(model2):E:=E);  
                  // intrinsic defined in "3descent-testeq.m" 
  elif n eq 4 then 
    return IsEquivalentFour(model1,model2,E); 
                  // function defined in this file
  else
    return IsEquivalentFive(model1,model2:E:=E);
                   // intrinsic defined in "5descent-testeq.m" 
  end if;
end intrinsic;












