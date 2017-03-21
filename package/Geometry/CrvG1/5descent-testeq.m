freeze;

/////////////////////////////////////////////////////
//                                                 //
//     TESTING EQUIVALENCE OF 5-COVERINGS          //
//             "5descent-testeq.m"                 //
//                                                 //
//                T. A. Fisher                     //
//                                                 //
//           Version: September 2014               //
//                                                 //
/////////////////////////////////////////////////////

// This file contains intrinsics :-  
//
// FiveTorsionPoints(E)
// FiveTorsionOrbits(E)
// FiveTorsionMatrices(E,model)
// FiveSelmerElement(E,model)
// FiveCoveringDependenceInformation(E,models)
// IsEquivalentFive(model1,model2)
// AddFiveCoverings(models,vectors)

import "../CrvEll/5coverings.m" : ReversePolynomial;
import "3descent-testeq.m" : LinearSolve;

declare attributes CrvEll: FiveTorsionPoints;

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Q := Rationals();
Id := IdentityMatrix;
clift := func<x|Integers()!(x+2)-2>;

function MaxOrder5(E)

    A := Coefficients(E);
    Fx<x5> := NumberField(DivisionPolynomial(E, 5));
    Fy<y5> := ext< Fx | Polynomial([ -(x5^3 + A[2]*x5^2 + A[4]*x5 + A[5]) , A[1]*x5 + A[3] , 1]) >;

    _ := Factorization(Discriminant(Integers(Fx)));
    _ := Factorization(Discriminant(Integers(Fy)));
    _ := Factorization(AbsoluteDiscriminant(Integers(Fy)));

    LZF0 := LLL(Integers(AbsoluteField(Fy)));
    assert Degree(LZF0) eq 24;
    assert LZF0.1^2 eq 1;
    D := Discriminant(LZF0);

    B := Basis(LZF0)[2..24];
    Bh := [AbsoluteLogarithmicHeight(b) : b in B];
    ParallelSort(~Bh, ~B);
    for b in B do
        g := b;
        f := MinimalPolynomial(g);
        if Degree(f) eq 24 then break; end if;
    end for;
    assert f eq MinimalPolynomial(g);

    F := NumberField(f);
    Embed(F, Fy, Fy!g);
    //time
    ZF := Order([F| F!b : b in Basis(LZF0)]);
    //time
    ZF := MaximalOrder(ZF);
    /*
    time
    ZF := MaximalOrder(F : Discriminant:=D);
    */

    vprintf FiveDescent, 1 : "Conductor(E) (%o digits) : %o\n",
           1+Ilog(10,Abs(N)), Factorization(N), N where N is Conductor(E);
    vprintf FiveDescent, 1 : "Discriminant (%o digits) : %o\n%o\n",
           1+Ilog(10,Abs(D)), Factorization(D), D;

    return ZF, Fy;

end function;

// Computes a tuple <T_1 ,..., T_r> of 5-torsion points on E,
// with one representative for each Galois orbit.

intrinsic FiveTorsionPoints(E::CrvEll[FldRat]) -> Tup // : OptimisedRep:=true ) 
{Same as FiveTorsionOrbits}
return FiveTorsionOrbits(E); // : OptimisedRep:=OptimisedRep);
end intrinsic;

intrinsic FiveTorsionOrbits(E::CrvEll[FldRat])-> Tup // : OptimisedRep:=true )
{Computes <T_1, ... , T_r> where the T_i are representatives for the Galois orbits on E[5] - \{O\}. }
  if assigned E`FiveTorsionPoints then
    return E`FiveTorsionPoints;
  end if;
  try 
    vprint FiveDescent,1 : "Computing maximal order for degree 24 number field";
    vtime FiveDescent,1 : OL,rel := MaxOrder5(E);
  catch e;
    error "FiveTorsionOrbits has only been implemented in the case there is one orbit.";
  end try;
  x5 := BaseRing(rel).1;
  y5 := rel.1;
  OL := LLL(OL);
  L := NumberField(OL);
  T := E(L)![x5,y5];
  assert Order(T) eq 5;
  TT := <T>;
  E`FiveTorsionPoints := TT;
  return TT;
end intrinsic;

function RandomPoints(C,m)
  pts := {};
  R := CoordinateRing(Ambient(C));
  k := BaseRing(R);
  assert IsFinite(k);
  n := Rank(R);
  repeat
    repeat 
      form := &+[Random(k)*R.i: i in [1..n]];
    until form ne 0;
    newpts := Points(C meet Scheme(Ambient(C),form));
    pts join:= {C!Eltseq(pt): pt in newpts};
  until #pts gt 5*m;
  repeat
    PP := {Random(pts): i in [1..m]};
  until #PP eq m;
  return SetToSequence(PP);
end function;

function QuickCoveringMap(E,model,pt)
// Used in both FiveTorsionMatrices and FiveCoveringDependenceInformation
  assert Degree(model) eq 5;
  error if cInvariants(model) ne cInvariants(E),
    "Model does not have same invariants as Jacobian";
  k := CoefficientRing(model);
  R := PolynomialRing(model);
  M := Matrix(model);
  M := Matrix(5,5,[Evaluate(M[i,j],pt): i,j in [1..5]]);
  _,_,A := SmithForm(KernelMatrix(M));
  _,_,B1 := SmithForm(Matrix(1,5,pt));
  flag,tr := IsTransformation(5,<A^(-1),B1^(-1)>);
  assert flag;
  model1 := tr*model;
  B2 := Id(k,5);
  B2[1] := Vector(5,[MC(Matrix(model1)[4,5],R.i): i in [1..5]]);
  flag,tr5 := IsTransformation(5,<A^(-1),Transpose(B2^(-1))*B1^(-1)>);
  assert flag;
  model1 := tr5*model;
  assert Matrix(model1)[4,5] eq R.1;
  ll := [Matrix(model1)[ii[1],ii[2]]: ii in [[2,3],[3,1],[1,2]]];
  hh := Matrix(2,3,[Matrix(model1)[i,j]: j in [1,2,3], i in [4,5]]);
  mm := Matrix(4,3,[MC(ll[j],R.i):j in [1..3],i in [2..5]]);
  pt4 := Eltseq(KernelMatrix(mm));
  R4<x1,x2,x3,x4> := PolynomialRing(k,4);
  qq := [Evaluate(&+[hh[i,j]*ll[j]: j in [1..3]],[0,x1,x2,x3,x4]): i in [1,2]];
  phi4 := GenusOneModel(qq);
  C4,E1,pi := nCovering(phi4);
  flag,iso := IsIsomorphic(E1,E);
  assert flag;
  u := 6*IsomorphismData(iso)[4]*ScalingFactor(5,tr5);
  u := (Integers()!(u + 2)) - 2;
  assert u in {-1,1};
  return u*iso(pi(C4!pt4));
end function;

function EllipticCurveData(model,pts)
  C := Curve(model);
  assert Degree(model) eq 5;
  k := BaseRing(model);
  P0 := C!Eltseq(pts[1]);
  pts := [C!Eltseq(pt): pt in pts];
  EE,map := EllipticCurve(C,P0);
  E,iso := WeierstrassModel(EE);
  cinv := cInvariants(model);
  c4,c6 := Explode(cinv);
  J := EllipticCurve([-27/6^4*c4,-54/6^6*c6]);
  assert cinv eq cInvariants(J);
  P := QuickCoveringMap(J,model,Eltseq(P0));
  flag,isoJ := IsIsomorphic(J,E);
  assert flag;
  P := isoJ(P);
  PP := [g(P): g in Automorphisms(E)];
  KE<x,y> := FunctionField(E);
  RR := PolynomialRing(k,5^2);
  mat := Matrix(RR,5,5,[RR.i : i in [1..5^2]]);
  for P in PP do
    xP,yP := Explode(Eltseq(P));
    ff := [1,x,y,x^2,(y+yP)/(x-xP)];
    psi := map<E -> Ambient(C)|ff>;
    C1 := Image(psi);
    pts1 := [psi(iso(map(pt))): pt in pts];
    relns := [];
    for i in [1..#pts] do
      b := Transpose(KernelMatrix(Matrix(k,5,1,Eltseq(pts1[i]))));
      r := Vector(RR,Eltseq(pts[i]))*mat*ChangeRing(b,RR);
      relns cat:= Eltseq(r);
    end for;
    bigmat := Matrix(#relns,5^2,[MC(r,RR.i): i in [1..5^2],r in relns]);
    rk := Rank(bigmat);
    if rk lt 5^2 then break; end if;
  end for;
  assert rk eq 24;
  km := KernelMatrix(Transpose(bigmat));
  cob := Matrix(k,5,5,Eltseq(km));
  return psi,Transpose(cob);
end function;

function GetTorsionMatrix(T,psi,pts)
  pts1 := [psi(P): P in pts];
  pts2 := [psi(P+T): P in pts];
  kk := Ring(Parent(T));
  RR := PolynomialRing(kk,5^2);  
  mat := Matrix(RR,5,5,[RR.i : i in [1..5^2]]);
  relns := [];
  for i in [1..#pts] do
    b := Transpose(KernelMatrix(Matrix(kk,5,1,Eltseq(pts2[i]))));
    r := Vector(RR,Eltseq(pts1[i]))*mat*ChangeRing(b,RR);
    relns cat:= Eltseq(r);
  end for;
  bigmat := Matrix(#relns,5^2,[MC(r,RR.i): i in [1..5^2],r in relns]);
  assert Rank(bigmat) eq 24;
  km := KernelMatrix(Transpose(bigmat));
  cob := Matrix(5,5,Eltseq(km));
  return Transpose(cob);
end function;

function TorsionMatrixOverFiniteField(model,T)
  k := BaseRing(model);
  C := Curve(model);
  pts := RandomPoints(C,10);
  psi,cob := EllipticCurveData(model,pts);
  E := Domain(psi);
  C1 := Image(psi);
  cobinv := cob^(-1);
  assert forall{f : f in Equations(C1) | f^cob in Ideal(C)};
  EE := Curve(T);
  kk := Ring(Parent(T));
  flag,iota := IsIsomorphic(EE,E);
  assert flag;
  T := iota(T);
  pts := [Random(E): i in [1..10]];
  MT := GetTorsionMatrix(T,psi,pts);
  return cob^(-1)*MT*cob;
end function;

intrinsic FiveTorsionMatrices(E::CrvEll[FldRat],model::ModelG1) -> Tup
{Given a genus one model of degree 5 with Jacobian E, computes the action of E[5] on the model.}
  require Degree(model) eq 5 : "Genus one model must have degree 5";
  require BaseRing(model) cmpeq Rationals() : "Model must be defined over the rationals";
  require IsIsomorphic(Jacobian(model),E) : "Elliptic curve E should be the Jacobian of the given model";
  if Maximum([Abs(x): x in Eltseq(model)]) gt 10 or 
     exists{x : x in Eltseq(model) | not IsIntegral(x)} then 
    print "WARNING: This implementation of FiveTorsionMatrices is only expected to work on models with very small integer coefficients (say less than 10)";
  end if;
  torspts := FiveTorsionPoints(E);
  require #torspts eq 1 : "FiveTorsionMatrices only implemented in the case Galois acts transitively on E[5] - {0}";
  T := torspts[1];
  L := Ring(Parent(T));
  OL := LLL(MaximalOrder(L));
  assert Order(T) eq 5;
  f := DefiningPolynomial(L);
  vprint FiveDescent,2 : "Selecting prime";
  dd := Discriminant(f);
  p := 10^15; // all rather arbitrary!
  repeat
    p := NextPrime(p);
    R := PolynomialRing(GF(p));
  until GF(p)!dd ne 0 and IsIrreducible(R!f);
  k := GF(p);
  vprint FiveDescent,2 : "Working with inert prime p =",p;
  vprint FiveDescent,2 : "Computing reduction of torsion point";
  pr := Decomposition(OL,p)[1,1];
  kk,resmap := ResidueClassField(pr);
  Ep := ChangeRing(E,k);
  Tp := Ep(kk)![resmap(x): x in Eltseq(T)];
  vprint FiveDescent,2 : "Computing mod p torsion matrix";
  modelp := ChangeRing(model,k);
  Cp := Curve(modelp);
  MTp := TorsionMatrixOverFiniteField(modelp,Tp);
  vprint FiveDescent,2 : "Checking mod p torsion matrix";
  Cpp := ChangeRing(Cp,kk);
  for Q in Equations(Cpp) do
    assert Q^MTp in Ideal(Cpp);
  end for;
  assert IsScalar(MTp^5);
  function GetElements(elts)
    elts := [OL!(e @@ resmap) : e in elts];
    bb := Basis(OL);
    bigmat := Matrix(Integers(),#bb,Degree(L)*#elts,
   		   [&cat[Eltseq(OL!(b*e)): e in elts]: b in bb]);
    II := p*Id(Integers(),Ncols(bigmat));
    bigmat := VerticalJoin(bigmat,II);
    bigmat := LLL(bigmat);
    AA := Matrix(#elts,24,Eltseq(bigmat[1]));
    vprint FiveDescent, 2 : AA[1];
    BB := [OL!Eltseq(AA[i]): i in [1..#elts]];
    return BB;
  end function;
  vprint FiveDescent, 1 : "Rational reconstruction";
  MT := ZeroMatrix(L,5,5);
  ee := GetElements([MTp[1,1],MTp[2,2]]);
  MT[1,1] := ee[1];
  MT[2,2] := ee[2];
  for i,j in [1..5] do
    vprintf FiveDescent,2 : "%o %o : ",i,j;
    if [i,j] notin {[1,1],[2,2]} then 
      ee := GetElements([MTp[1,1],MTp[i,j]]);
      MT[i,j] := (ee[2]/ee[1])*MT[1,1];
    else
      vprint FiveDescent,2 : "";
    end if;
  end for;
  vprint FiveDescent, 1 : "Checking MT";
  C := Curve(model);
  CL := ChangeRing(C,L);
  flag1 := forall{ Q : Q in Equations(CL) | Q^MT in Ideal(CL)};
  flag2 := IsScalar(MT^5);
  error if not (flag1 and flag2), 
    "Rational reconstruction in FiveTorsionMatrices was not successful";
  return <MT>;
end intrinsic;

intrinsic FiveSelmerElement(E::CrvEll[FldRat],model::ModelG1) -> Tup
{Given a genus one model of degree 5 with Jacobian E, returns an element in 
(the algebra associated to) the 5-Selmer group of E, corresponding to the model. }
  require Degree(model) eq 5 : "Genus one model must have degree 5";
  require BaseRing(model) cmpeq Rationals() : "Model must be defined over the rationals";
  M := FiveTorsionMatrices(E,model);
  return <Determinant(MT): MT in M>;
end intrinsic;

///////////////////

intrinsic FiveCoveringDependenceInformation(E::CrvEll[FldRat],models::SeqEnum
   : NumberOfPrimes := 2*#models) -> ModMatFldElt
{Given a sequence of genus one models of degree 5, all with Jacobian E, determines 
what relations they might satisfy in H^1(Q,E[5]), on the basis of reducing 
modulo a few primes. The subgroup of H^1(Q,E[5]) spanned by the given models
has dimension at least the number of rows of the matrix returned.}
  nprimes := NumberOfPrimes;
  mat := ZeroMatrix(GF(5),nprimes,#models);
  badprimes := BadPrimes(E);
  for ctr in [1..nprimes] do
    jj := 1;
    repeat
      p := RandomPrime(10);   
      m := 1;
      if p notin badprimes and p gt 100 then 
        Ep := EllipticCurve([GF(p)!x : x in aInvariants(E)]);
        m := #Ep;
      end if;
      jj +:= 1;
      error if jj gt 1000, "Error selecting primes in FiveCoveringDependenceInformation";
    until Valuation(m,5) eq 1 and #Automorphisms(Ep) eq 2;
    A,map := AbelianGroup(Ep); 
    nn := InvariantFactors(A);
    if #nn eq 1 then nn := [1,nn[1]]; gen := A.1; else gen := A.2; end if;
    vprintf FiveDescent,3 : "p = %o    E(F_p) = [ %o, %o ] \n",p,nn[1],nn[2];
    assert nn[1] mod 5 ne 0;
    ee := Integers()!(nn[2]/5);
    P := map(ee*gen);
    PP := [i*P: i in [1..5]];
    vv := [];
    for j in [1..#models] do  
      phi := ChangeRing(models[j],GF(p));
      pt := Eltseq(RandomPoints(Curve(phi),1)[1]);
      pt := QuickCoveringMap(Ep,phi,pt); 
      ans := GF(5)!Position(PP,ee*pt);
      Append(~vv,ans);
    end for;
    mat[ctr] := Vector(vv);
  end for;
  mat := EchelonForm(mat);
  r := Rank(mat);
  return Matrix(r,#models,[mat[i]: i in [1..r]]);
end intrinsic;

intrinsic IsEquivalentFive(model1::ModelG1,model2::ModelG1:E:=MinimalModel(Jacobian(model1))) -> BoolElt,TransG1 
{Determines whether genus one models of degree 5 defined over Q are equivalent and if so also returns 
the transformation relating them. }

  require Degree(model1) eq 5 : "model1 should have degree 5";
  require Degree(model2) eq 5 : "model2 should have degree 5";
  require BaseRing(model1) cmpeq Rationals() : "model1 should be defined over Q";
  require BaseRing(model2) cmpeq Rationals() : "model2 should be defined over Q";

  E1 := Jacobian(model1);
  E2 := Jacobian(model2);

  flag1,iso1 := IsIsomorphic(E,E1);
  require flag1 : "Elliptic curve given should be the Jacobian of model1";
  flag2,iso2 := IsIsomorphic(E,E2);
  if not IsIsomorphic(E,E2) then return false,_; end if;

  u1 := Abs(IsomorphismData(iso1)[4]);
  _,tr1 := IsTransformation(5,<Id(Q,5),DiagonalMatrix(Q,[6/u1,1,1,1,1])>);
  model1a := tr1*model1;
//  assert cInvariants(model1a) eq cInvariants(E);

  u2 := Abs(IsomorphismData(iso2)[4]);
  _,tr2 := IsTransformation(5,<Id(Q,5),DiagonalMatrix(Q,[6/u2,1,1,1,1])>);
  model2a := tr2*model2;
//  assert cInvariants(model2a) eq cInvariants(E);

  mat := FiveCoveringDependenceInformation(E,[model1a,model2a]: NumberOfPrimes := 5);
  
  if Nrows(mat) gt 1 then return false,_; end if;
  if Nrows(mat) eq 1 and mat[1,1] notin [mat[1,2],-mat[1,2]] then return false,_; end if;

  TT := FiveTorsionPoints(E);
  require #TT eq 1 : "IsEquivalentFive only implemented in the case Galois acts transitively on E[5] - {0}.";

  vprint FiveDescent,1 : "Computing 5-torsion matrix for first model";
  IndentPush();
  vtime FiveDescent,1 : M1 := FiveTorsionMatrices(E,model1)[1];
  IndentPop();
  vprint FiveDescent,1 : "Computing 5-torsion matrix for second model";
  IndentPush();
  vtime FiveDescent,1 : M2 := FiveTorsionMatrices(E,model2)[1];
  IndentPop();

  L := BaseRing(M1[1]);
  OL := LLL(MaximalOrder(L));
  LL := FieldOfFractions(OL);
  det1 := LL!Determinant(M1);
  det2 := LL!Determinant(M2);
  d1 := Denominator(RationalGCD(Eltseq(det1)));
  d2 := Denominator(RationalGCD(Eltseq(det2)));
  dd := Integers()!(Discriminant(E)*d1*d2);

  vprint FiveDescent,1 : "det(M1) =",Eltseq(det1);
  vprint FiveDescent,1 : "det(M2) =",Eltseq(det2);
  vprint FiveDescent,1 : "Equal mod fifth powers?";
  flag,elt := IsPower(det1/det2,5); 
  vprint FiveDescent,1 : flag;
  if not flag then 
    vprint FiveDescent,1 : "Inverting M2";
    M2 := Adjoint(M2); 
    det2 := LL!Determinant(M2);
    vprint FiveDescent,3 : "det(M2) =",Eltseq(det2);
    vprint FiveDescent,1 : "Equal mod fifth powers?";
    flag,elt := IsPower(det1/det2,5); 
    vprint FiveDescent,1 : flag;
  end if;

  if not flag then return false,_; end if;

  M2 *:= elt;
  assert Determinant(M1) eq Determinant(M2);
  B := LinearSolve(<M1>,<M2>); // imported from 3descent-testeq.m
  B := Transpose(Adjoint(B));
  B *:= 1/RationalGCD(Eltseq(B));
  flag,tr := IsTransformation(5,<Id(Rationals(),5),B>);
  eqns1 := Equations(tr*model1);
  eqns2 := Equations(model2);
  R := PolynomialRing(model1);
  mons := MD(R,2);
  mat1 := Matrix(5,15,[MC(f,mon): mon in mons,f in eqns1]);
  mat2 := Matrix(5,15,[MC(R!f,mon): mon in mons,f in eqns2]);
  A := Solution(mat2,mat1);
  A := Transpose(A);
  A *:= 1/RationalGCD(Eltseq(A));
  flag,tr := IsTransformation(5,<A,B>);
  model1new := tr*model1;
  mm := Matrix(2,50,[Eltseq(model1new),Eltseq(model2)]);
  assert Rank(mm) eq 1;
  km := KernelMatrix(mm);
  B *:= -km[1,1]/km[1,2];
  flag,tr := IsTransformation(5,<A,B>);
  assert tr*model1 eq model2;
  return true,tr;
end intrinsic;

intrinsic AddFiveCoverings(models::SeqEnum[ModelG1],vectorlist::SeqEnum[ModTupFldElt]) -> SeqEnum 
{Given a sequence of d genus one models all with the same Jacobian, and defined over Q, adds the 5-coverings as specified by vectorlist. This second argument should be a sequence of elements in VectorSpace(GF(5),d). In the case of non-trivial obstruction a zero model is returned.}

  require forall{m : m in models | BaseRing(m) cmpeq Rationals()}
    : "Models should be defined over the rationals";
  require forall{m : m in models | Degree(m) eq 5}
    : "Models should have degree 5";
  require #models gt 0 : "At least one model must be given";
  c4,c6 := Explode(cInvariants(models[1]));
  require c4^3 ne c6^2 : "Models must be non-singular";
  E := MinimalModel(EllipticCurve([-27*c4,-54*c6]));
  for i in [1..#models] do
    if i gt 1 then 
      c4,c6 := Explode(cInvariants(models[i]));
    end if;
    require c4^3 ne c6^2 : "Models must be non-singular";
    E1 := EllipticCurve([-27*c4,-54*c6]);
    require IsIsomorphic(E,E1) : "Models should all have the same Jacobian";
    if [c4,c6] ne cInvariants(E) then 
      models[i] := Minimise(models[i]);
    end if;
    models[i] := Reduce(models[i]);
  end for;
  TT := FiveTorsionPoints(E);
  require #TT eq 1 : 
    "AddFiveCoverings only implemented in case Galois acts transitively on E[5] - {0}";
  T := TT[1];
  L := Ring(Parent(T));
  R<x,y> := FunctionField(Rationals(),2);
  f24 := R!ReversePolynomial(T);
  TT := 2*T;
  sigma := hom<L->L|Evaluate(f24,[TT[1],TT[2]])>; 
  OL := LLL(RingOfIntegers(L));
  bb := [];
  cc := [];
  for model in models do
    vprint FiveDescent, 1 : "Computing MT (i.e. action of E[5])";
    IndentPush();
    MT := FiveTorsionMatrices(E,model)[1];
    IndentPop();
    b := Determinant(MT);
    sMT := Matrix(5,5,[sigma(MT[i,j]): i,j in [1..5]]);
    MT2 := MT^2;
    assert exists(j){j : j in [1..25] | Eltseq(sMT)[j] ne 0};
    c := Eltseq(MT2)[j]/Eltseq(sMT)[j];
    assert MT2 eq c*sMT;
    assert b^2 eq sigma(b)*c^5;
    Append(~bb,b);
    Append(~cc,c);
  end for;

//  if #models eq 2 then
//    vprint FiveDescent,1 : "Checking independence";
//    assert [[i,j] : i,j in [0..4] | IsPower(bb[1]^i*bb[2]^j,5) ] eq [[0,0]];
//  end if;

  myprint := func<x|#xx gt 10 select "[..(" cat Sprint(#xx) cat ")..]" 
                  else xx where xx is Sprint(x)>;

  norms := [Norm(b): b in bb];
  size := #Sprint(norms);
  vprint FiveDescent,1 : "alphas =",[myprint(x): x in bb];
  vprint FiveDescent,1 : "Norms =",[myprint(Norm(x)): x in bb];

  V := Universe(vectorlist);
  assert Dimension(V) eq #models;

  donelist := [];
  modellist := [];

  for v in vectorlist do
    vprint FiveDescent,1 : "Vector =",v;
    if exists(j){ Position(vectorlist,m*v) : m in [2,3] | m*v in donelist } then
      assert vectorlist[j] in [2*v,3*v];
      model := modellist[j];
      if not IsZero(Vector(Eltseq(model))) then
        vprint FiveDescent,1 : "Doubling";
        model := DoubleGenusOneModel(model);
      end if;
    elif exists(j){j : j in [1..#models] | v eq V.j} then 
      model := models[j];
    else
      mm := [clift(x) : x in Eltseq(v)];
      elt := &*[bb[i]^mm[i]: i in [1..#bb]];
      myrt := &*[cc[i]^mm[i]: i in [1..#bb]];
      vprintf FiveDescent,1 : 
        "Element = %o\nNorm = %o\n",myprint(elt),myprint(Norm(elt));
      vprint FiveDescent,1 : "Computing nice representative";
      vtime FiveDescent,1 : elt,c := NiceRepresentativeModuloPowers(elt,5);
      vprintf FiveDescent,1 : 
        "Element = %o\nNorm = %o\n",myprint(elt),myprint(Norm(elt));
      myrt *:= c^2/sigma(c);
      assert elt^2 eq sigma(elt)*myrt^5;
      vprint FiveDescent,1 : "Calling FiveDescentCoveringCurve";
      vtime FiveDescent,1 : model := 
        FiveDescentCoveringCurve(E,<elt>:factorhint := <c>,fifthroot := <myrt>);
      vprint FiveDescent,1 : "Finished with FiveDescentCoveringCurve";
    end if;

    if IsZero(Vector(Eltseq(model))) then 
      vprint FiveDescent,1 : "Covering has non-trivial obstruction";
    else
      vprint FiveDescent,1 : "Minimising and reducing";
      vtime FiveDescent,1 : model := Reduce(Minimise(model));
      R<x1,x2,x3,x4,x5> := PolynomialRing(model);
      vprint FiveDescent,1 : model;
      assert IsIsomorphic(Jacobian(model),E);
    end if;

    Append(~modellist,model);
    Append(~donelist,v);

  end for;

  return modellist;

end intrinsic;
