freeze;

// Local solubility of genus one models of degree 2,3,4 and 5
// Version: April 2010
// T. Fisher

// September 2014 : Degree 5 models added 

MC := MonomialCoefficient;
MD := MonomialsOfDegree;
Det := Determinant;
Diag := DiagonalMatrix;
Deriv := Derivative;
Id := IdentityMatrix;
IdTrans := IdentityTransformation;
Z := Integers();
Q := Rationals();

function MyIsSquare(a)
// We test whether a is square in GF(p) by computing the 
// Legendre symbol (a/p). This is quicker than using IsSquare 
// (which actually finds a square root).
  k := Parent(a);
  if a eq 0 then return true; end if;
  if IsPrimeField(k) then 
    p := Characteristic(k);
    flag := (LegendreSymbol(Integers()!a,p) eq 1);
  else
    flag := IsSquare(a); 
  end if;
  return flag;
end function;

function BinaryFormGCD(ff)
// We compute GCD's of binary forms by dehomogenising first.
// This is much faster than calling GCD directly.
  ff := [f : f in ff | f ne 0];
  assert forall{f : f in ff | IsHomogeneous(f)};
  R<x,y> := Universe(ff);
  P := PolynomialRing(BaseRing(R)); X := P.1;
  gg := [Evaluate(f,[X,1]) : f in ff];
  e := Minimum([TotalDegree(ff[i])-Degree(gg[i]): i in [1..#ff]]);
  g := GCD(gg);
  d := Degree(g) + e;
  return R!(y^d*Evaluate(g,x/y));
end function;

function BinaryFormRoots(F)
  R<x,y> := Parent(F);
  assert F ne 0;
  assert IsHomogeneous(F);
  P := PolynomialRing(BaseRing(R)); X := P.1;
  f := Evaluate(F,[X,1]);
  rts := [<[r[1],1],r[2]>: r in Roots(f)];
  e := TotalDegree(F) - Degree(f);
  if e gt 0 then 
    Append(~rts,<[1,0],e>);
  end if;
  return rts;
end function;

function LeadingMinors(M,r)
// The leading r by r minors of an n by n matrix 
  R := BaseRing(Parent(M));
  n := NumberOfRows(M);
  assert n eq NumberOfColumns(M);
  minors := [R|];
  ss := Sort([SetToSequence(s):s in Subsets({1..n},r)]);
  for s in ss do
    seq := [ x : x in s ];
    Mminor := Matrix(r,[M[seq[i],seq[j]]: i,j in [1..r]]);
    Append(~minors,Determinant(Mminor));
  end for;
  return minors;
end function;

function FanoScheme(model)
// Given a quadric intersection X, returns a scheme whose points 
// parametrise the lines on X.
  assert Degree(model) eq 4;
  k := CoefficientRing(model);
  assert Characteristic(k) ne 2;
  S<y1,y2,y3,y4,y5,y6> := PolynomialRing(k,6);
  A := Matrix(4,4,[0,y1,y2,y3,-y1,0,y4,y5,-y2,-y4,0,y6,-y3,-y5,-y6,0]);
  pfaffian := y1*y6 - y2*y5 + y3*y4;
  qq := &cat[Eltseq(A*M*A): M in Matrices(model)];
  return Scheme(Proj(S),qq cat [pfaffian]);
end function;

///////////////////////////////////////////////////////
//   Finding a smooth point on the reduction mod p   //
///////////////////////////////////////////////////////

// If there are smooth points, then these functions are
// guarenteed to find one, and should find one quickly even 
// for large p. 

function FindSmoothPointCrossTerms(model:rnd:=false)
// Finds a smooth k-point on a generalised binary quartic
  k := CoefficientRing(model); 
  assert Degree(model) eq 2;
  assert #Eltseq(model) eq 8;
  C := Curve(model);
  F := Equation(model);
  DF := [Derivative(F,i): i in [1..3]];
  RR := PolynomialRing(k); t := RR.1;
  r := rnd select Random(k) else k!0;
  for x0 in k do
    x := x0 + r;
    substs := [[x,1,t],[1,x,t]];
    for subst in substs do
      f := Evaluate(F,subst);
      rts := [k|r[1]: r in Roots(f)];
      for rt in rts do
	pt := [k|Evaluate(u,rt): u in subst];
        assert Evaluate(F,pt) eq 0;
        if exists{g : g in DF | Evaluate(g,pt) ne 0} then
	  return true,C!pt;
        end if;
      end for;
    end for;
  end for;
  return false,_;
end function;

function FindSmoothPointTwo(model:rnd:=false)
// Finds a smooth k-point on y^2 = binary quartic 
  k := CoefficientRing(model); 
  assert Degree(model) eq 2;
  assert #Eltseq(model) eq 5;
  assert Characteristic(k) ne 2;
  P1 := ProjectiveSpace(k,1);
  R := PolynomialRing(k); t := R.1;
  g := Evaluate(Equation(model),[t,1]);
  dg := Derivative(g);
  r := rnd select Random(k) else k!0;
  for x0 in k do
    x := x0 + r;
    yy := Evaluate(g,x);
    if MyIsSquare(yy) then
      if 2*yy ne 0 or Evaluate(dg,x) ne 0 then
        return true,P1![k|x,1];
      end if;
    end if;
  end for;
  a,b := Explode(Eltseq(model));
  if MyIsSquare(a) and (a ne 0 or b ne 0) then 
    return true,P1![k|1,0];
  end if;
  return false,_;
end function;

function FindSmoothPointThree(model:rnd:=false)
// Finds a smooth k-point on a genus one model of degree 3
// defined over a finite field k.
  k := CoefficientRing(model); 
  assert Degree(model) eq 3;
  RR := PolynomialRing(k); t := RR.1;
  F := Equation(model);
  DF := [Derivative(F,j): j in [1..3]];
  r := rnd select Random(k) else k!0;
  for ctr in [1,2] do
    for x0 in k do
      x := x0 + r;
      substs := [[1,x,t],[t,1,x],[x,t,1]];
      for subst in substs do
        f := Evaluate(F,subst);
        if f ne 0 then
          rts := [k|r[1]: r in Roots(f)];
        else 
  	  rts := (ctr eq 2) select [y : y in k] else [k|];
        end if;
        for rt in rts do
	  pt := [k|Evaluate(u,rt): u in subst];
          assert Evaluate(F,pt) eq 0;
          if exists{g : g in DF | Evaluate(g,pt) ne 0} then
	    return true,pt;
          end if;
        end for;
      end for;
    end for;
  end for;
  return false,_;
end function;

function FindSmoothPointFour(model:rnd:=false)
// Finds a smooth k-point on a genus one model of degree 4
// defined over a finite field k.
  k := CoefficientRing(model); 
  assert Degree(model) eq 4;
  RR<s,t> := PolynomialRing(k,2);
  qq := Equations(model);
  M := Matrix(2,4,[Derivative(q,j): j in [1..4],q in qq]);
  r := rnd select Random(k) else k!0;
  for ctr in [1,2] do
    for x0 in k do
      x := x0 + r;
      substs := [[1,x,s,t],[s,1,x,t],[s,t,1,x],[x,s,t,1]];
      for subst in substs do
        qq1 := [Evaluate(q,subst): q in qq];
        S := Scheme(Spec(RR),qq1);
        if ctr eq 2 or Dimension(S) eq 0 then
          solns := Points(S);
        else
 	  solns := [];
        end if;
        for s in solns do
	  pt := [k|Evaluate(u,Eltseq(s)): u in subst];
          assert [Evaluate(q,pt): q in qq] eq [0,0];
          MM := Matrix(2,4,[Evaluate(M[i,j],pt): j in [1..4],i in [1..2]]);
          if Rank(MM) eq 2 then 
	    return true,pt;
          end if;
        end for;
      end for;
    end for;
  end for;
  return false,_;
end function;

function FindSmoothPointFive(model:rnd:=false,giveupearly:=false)
// Finds a smooth k-point on a genus one model of degree 5
// defined over a finite field k.
  k := CoefficientRing(model); 
  assert Degree(model) eq 5;
  RR<s,t,u> := PolynomialRing(k,3);
  qq := Equations(model);
  M := Matrix(5,5,[Derivative(q,j): j in [1..5],q in qq]);
  r := rnd select Random(k) else k!0;
  ntries := 0;
  for ctr in [1,2] do
    for x0 in k do
      x := x0 + r;
      substs := [[1,x,s,t,u],[s,1,x,t,u],[s,t,1,x,u],[s,t,u,1,x],[x,s,t,u,1]];
      for subst in substs do
        qq1 := [Evaluate(q,subst): q in qq];
        S := Scheme(Spec(RR),qq1);
        if ctr eq 2 or Dimension(S) eq 0 then
          solns := Points(S);
          ntries +:= 1;
        else
 	  solns := [];
        end if;
        for s in solns do
	  pt := [k|Evaluate(u,Eltseq(s)): u in subst];
          assert [Evaluate(q,pt): q in qq] eq [0,0,0,0,0];
          MM := Matrix(5,5,[Evaluate(M[i,j],pt): j in [1..5],i in [1..5]]);
          if Rank(MM) eq 3 then 
	    return true,pt;
          end if;
        end for;
        ntries +:= 1;
        if giveupearly and ntries gt 10 then return false,_; end if;
      end for;
    end for;
  end for;
  return false,_;
end function;

////////////////////////////////////////////////////////////////////////
// Determining whether there is a smooth point on the reduction mod p //
////////////////////////////////////////////////////////////////////////

// For large p we do much better than an exhaustive search.

function HasSmoothPointTwo(model)
  k := CoefficientRing(model); 
  assert Degree(model) eq 2;
  p := Characteristic(k);
  if p eq 2 then
    _,tr := IsTransformation(2,<1,[0,0,0],Id(Q,2)>);
    model1 := tr*model; // now has cross terms
    flag := FindSmoothPointCrossTerms(model1);
    return flag;
  end if;
  model := CompleteTheSquare(model);
  if p lt 10 then 
    flag := FindSmoothPointTwo(model);
    return flag;
  end if;
  R := PolynomialRing(k); x := R.1;
  g := Evaluate(Equation(model),[x,1]);
  if g eq 0 then return false; end if;
  hh := Hessian(model);
  mat := Matrix(k,2,5,[Eltseq(model),Eltseq(hh)]);
  if Rank(mat) eq 1 then 
    return MyIsSquare(LeadingCoefficient(g));
  end if;
  return true;
end function;

function HasSmoothPointThree(model)
  k := CoefficientRing(model); 
  assert Degree(model) eq 3;
  if Characteristic(k) lt 10 then 
    flag := FindSmoothPointThree(model);
    return flag;
  end if;
  F := Equation(model);
  if F eq 0 then return false; end if;
  hh := Hessian(model);
  mat := Matrix(k,2,10,[Eltseq(model),Eltseq(hh)]);
  if Rank(mat) eq 1 then 
    ff := Factorization(F);
    return exists{f: f in ff| TotalDegree(f[1]) eq 1 and f[2] eq 1};
  end if;
  return true;
end function;

function HasSmoothPointFour(model)
  k := CoefficientRing(model); 
  assert Degree(model) eq 4;
  if Characteristic(k) lt 10 then 
    flag := FindSmoothPointFour(model);
    return flag;
  end if;
  R<x,y> := PolynomialRing(k,2);
  A,B := Explode(Matrices(model));
  rk1poly := BinaryFormGCD(Minors(x*A + y*B,2));
  if TotalDegree(rk1poly) ne 0 then return false; end if;
  rk2poly := BinaryFormGCD(Minors(x*A + y*B,3));
  assert rk2poly ne 0; // since quadrics are coprime
  if TotalDegree(rk2poly) eq 0 then return true; end if;
  ff := Factorization(rk2poly);
  m := &+[TotalDegree(f[1]): f in ff];
  if m eq 1 then 
    r,s := Explode([MC(ff[1][1],R.i): i in [1..2]]);
    M := s*A - r*B;
    assert Rank(M) eq 2;
    assert exists(x){x : x in LeadingMinors(M,2) | x ne 0};
    return MyIsSquare(-x);
  end if;
  assert m in {2,3};
  X := FanoScheme(model);
  assert Dimension(X) eq 0;
  assert Degree(X) in {4,5};
  return exists{x : x in Points(X) | not IsSingular(x)};
end function;

function HasSmoothPointFive(model)
  k := CoefficientRing(model); 
  assert Degree(model) eq 5;
// TO DO : make this more efficient for large p. In particular
// if the reduction mod p is a line (with multiplicity 5) or 
// a pair of lines (with multiplicities 2 and 3), or 5 Galois
// conjugate lines arranged in a pentagon, then we know there
// are no smooth GF(p)-points.
  flag,pt := FindSmoothPointFive(model:giveupearly);
  if not flag then 
    X := Curve(model);
    S := SingularSubscheme(X); 
    XX := {ReducedSubscheme(X0): X0 in IrreducibleComponents(X)};
    SS := {ReducedSubscheme(S0): S0 in IrreducibleComponents(S)};
    flag1 := (XX subset SS);
    if not flag1 then
      flag,pt := FindSmoothPointFive(model);
    end if;
  end if;
  if flag then 
    P := Curve(model)!pt; 
    assert Dimension(TangentSpace(P)) eq 1;
  end if;
  return flag;
end function;

///////////////////////////////////////////////////////////////
//   Finding the non-regular points on the reduction mod p   //
///////////////////////////////////////////////////////////////

// The non-regular points are singular points on the special fibre
// that might have Q_p points above them. 

forward NonRegularPointsTwo;
 
function NonRegularPointsCrossTerms(model,p)
  assert Degree(model) eq 2;
  assert CoefficientRing(model) cmpeq Q;
  assert #Eltseq(model) eq 8;  // must have cross terms 
  F := Equation(model);
  DF := [Derivative(F,i): i in [1..3]];
  k := GF(p);
  Rp := PolynomialRing(k,[1,1,2]);
  X := Scheme(Proj(Rp),Rp!F);
  if p gt 10 then 
    model1 := CompleteTheSquare(model);
    xx := NonRegularPointsTwo(model1,p);
  else
    xx := [[x,1]: x in k] cat [[1,0]];
  end if;
  RR := PolynomialRing(k); t := RR.1;
  xx := [[x,1]: x in k] cat [[1,0]];
  ans := [];
  for x in xx do
    f := Evaluate(F,[x[1],x[2],t]);
    yy := [k|r[1]: r in Roots(f)];
    for y in yy do
      pt := [k|x[1],x[2],y];
      assert Evaluate(F,pt) eq 0;
      if forall{g : g in DF | Evaluate(g,pt) eq 0} then 
        pt0 := ChangeUniverse(pt,Integers());
        pt1 := ChangeUniverse(pt0,Integers(p^2));
        if Evaluate(F,pt1) eq 0 then 
   	  Append(~ans,pt);
        end if;
      end if;
    end for;
  end for;
  return [X!pt : pt in ans];
end function;

function NonRegularPointsTwo(model,p)
  assert Degree(model) eq 2;
  assert CoefficientRing(model) cmpeq Q;
  if p eq 2 then
    _,tr := IsTransformation(2,<1,[0,0,0],Id(Q,2)>);
    model := tr*model; // now has cross terms
  end if;
  if #Eltseq(model) eq 8 then 
    return NonRegularPointsCrossTerms(model,p);
  end if;
  k := GF(p);
  F := Equation(model);
  Rp := PolynomialRing(k,2);
  g := Rp!F;
  if g ne 0 then 
    singpts := [r[1] : r in BinaryFormRoots(g)| r[2] ge 2];
    ans := [];
    for pt in singpts do
      pt0 := ChangeUniverse(pt,Integers());
      pt1 := ChangeUniverse(pt0,Integers(p^2));
      if Evaluate(F,pt1) eq 0 then 
        Append(~ans,pt);
      end if;
    end for;
  else
    g := Rp!((1/p)*F);
    assert g ne 0; // otherwise not minimal
    ans := [r[1] : r in BinaryFormRoots(g)]; 
  end if;
  P1 := ProjectiveSpace(k,1);
  return [P1!x : x in ans];
end function;

function NonRegularPointsThree(model,p)
  assert Degree(model) eq 3;
  assert CoefficientRing(model) cmpeq Q;
  k := GF(p);
  F := Equation(model);
  Rp := PolynomialRing(k,3);
  assert Rp!F ne 0; // otherwise not minimal
  X := Scheme(Proj(Rp),Rp!F);
  XX := SingularSubscheme(X);
  d := Dimension(XX);
  vprint LocSol,1 : "Singular locus has dimension",d;
  assert d in {0,1};
  if d eq 0 then 
    ans := [];
    singpts := [Eltseq(P): P in Points(XX)];
    for pt in singpts do
      pt0 := ChangeUniverse(pt,Integers());
      pt1 := ChangeUniverse(pt0,Integers(p^2));
      if Evaluate(F,pt1) eq 0 then 
        Append(~ans,pt);
      end if;
    end for;
  else
    ff := Factorization(Rp!F);
    assert exists(eqn){ f[1] : f in ff | f[2] ge 2};
    mat := Matrix(k,3,1,[MC(eqn,Rp.i): i in [1..3]]);
    km := ChangeRing(KernelMatrix(mat),Z);
    RR<s,t> := PolynomialRing(Q,2);
    subst := [&+[km[i,j]*RR.i: i in [1,2]]: j in [1..3]];
    g := (1/p)*Evaluate(F,subst);
    RRp<s,t> := PolynomialRing(k,2);
    rts := BinaryFormRoots(RRp!g);
    ans := [[k|Evaluate(s,r[1]): s in subst]: r in rts];
  end if;
  return [X!pt : pt in ans];
end function;

function IsNonRegularPointFour(model,p,pt)
  R := PolynomialRing(model);
  k := GF(p);
  qq := Equations(model);
  error if [k|Evaluate(q,pt): q in qq] ne [0,0],"Point is not on curve";
  M := Matrix(R,2,4,[Derivative(q,R.i): i in [1..4],q in qq]);
  jmat := Matrix(k,2,4,[Evaluate(M[i,j],pt):j in [1..4],i in [1,2]]);
  rr := Rank(jmat);
  if rr eq 0 then 
    pt0 := ChangeUniverse(pt,Integers());
    nn := [k|(1/p)*Evaluate(q,pt0): q in qq];
    assert nn ne [0,0]; // otherwise not minimal
    return true,nn;
  elif rr eq 1 then 
    mat := Transpose(jmat);
    assert exists(nn){Eltseq(mat[i]): i in [1..4]| not IsZero(mat[i])};
    km := ChangeUniverse(Eltseq(KernelMatrix(jmat)),Integers());
    q := &+[km[i]*qq[i]: i in [1..2]];
    pt0 := ChangeUniverse(pt,Integers());
    pt1 := ChangeUniverse(pt0,Integers(p^2));
    if Evaluate(q,pt1) eq 0 then 
      return true,nn;
    end if;
  end if;
  return false,_;
end function;

function NonRegularPointsFourDirect(model,p)
  assert Degree(model) eq 4;
  assert CoefficientRing(model) cmpeq Q;
  k := GF(p);
  modelp := ChangeRing(model,k);
  Rp := PolynomialRing(modelp);
  X := Scheme(Proj(Rp),Equations(modelp));
  XX := SingularSubscheme(X);
  pts := [Eltseq(pt): pt in Points(XX)];
  ans := [];
  for pt in pts do
    flag,nn := IsNonRegularPointFour(model,p,pt);
    if flag then 
      Append(~ans,<pt,nn>);
    end if;	 	  
  end for;
  P1 := ProjectiveSpace(k,1);
  return [<X!pt[1],P1!pt[2]> : pt in ans];
end function;

function NonRegularPointsFour(model,p);
  assert Degree(model) eq 4;
  assert CoefficientRing(model) cmpeq Q;
  if p lt 10 then 
    return NonRegularPointsFourDirect(model,p);
  end if;
// the following won't work when p = 2
  k := GF(p);
  R2<x,z> := PolynomialRing(Q,2);
  M := [ChangeRing(M,R2): M in Matrices(model)];
  F := Determinant(x*M[1] + z*M[2]);
  model2 := GenusOneModel(F);
  pts2 := NonRegularPointsTwo(model2,p);
  A,B := Explode(Matrices(model));
  ans := [];
  for pt2 in pts2 do
    M := (Z!pt2[1])*A + (Z!pt2[2])*B;
    nn := [pt2[2],-pt2[1]];
    M1 := ChangeRing(M,k);
    s := 4 - Rank(M1);
    assert s in {1,2,3}; 
    km := ChangeRing(KernelMatrix(M1),Z);
    _,_,T := SmithForm(km);
    T := T^(-1);
    Astar := T*M*Transpose(T);
    if pt2[1] eq 0 then
      Bstar := T*A*Transpose(T);
    else
      Bstar := T*B*Transpose(T);
    end if;
    A1 := ChangeRing((1/p)*Submatrix(Astar,1,1,s,s),k);
    B1 := ChangeRing(Submatrix(Bstar,1,1,s,s),k);
    if s eq 1 then 
      if A1 eq 0 and B1 eq 0 then 
        pt4 := [k|T[1,i]: i in [1..4]];
	Append(~ans,<pt4,nn>);
      end if;
    else
      RR := PolynomialRing(k,s);
      q1 := &+[A1[i,j]*RR.i*RR.j: i,j in [1..s]];
      q2 := &+[B1[i,j]*RR.i*RR.j: i,j in [1..s]];
      XX := Scheme(Proj(RR),[q1,q2]);
      assert Dimension(XX) le 0;
      pts4 := Points(XX); 
      pts4 := [[k|&+[T[j,i]*pt4[j]: j in [1..s]]: i in [1..4]]: pt4 in pts4];
      ans cat:= [<pt4,nn>: pt4 in pts4];
    end if;
  end for;
  X := Curve(ChangeRing(model,GF(p)));
  P1 := ProjectiveSpace(k,1);
  return [<X!pt[1],P1!pt[2]>: pt in ans];
end function;

function IsNonRegularPointFive(model,p,pt)
  R := PolynomialRing(model);
  k := GF(p);
  M := Matrix(model);
  M1 := Matrix(k,5,5,[Evaluate(M[i,j],pt): i,j in [1..5]]);
  assert Rank(M1) eq 2; // if rank is 0 then model not minimal
  M1 := ChangeRing(KernelMatrix(M1),Integers());
  _,_,A := SmithForm(M1); 
  A := A^(-1);
  A := Matrix(5,5,[A[j]: j in [5..1 by -1]]);
  M2 := Matrix(Integers(),5,1,pt);
  _,B := SmithForm(M2);
  B := Transpose(B^(-1));
  _,tr1 := IsTransformation(5,<A,B>);
  model := tr1*model;
  M := Matrix(model);
  M1 := Matrix(k,5,5,[Evaluate(M[i,j],[1,0,0,0,0]): i,j in [1..5]]);
  a := M1[1,2];
  assert a ne 0; // otherwise not minimal
  assert M1 eq Matrix(k,5,5,[<1,2,a>,<2,1,-a>]);
  forms := [M[4,5],M[5,3],M[3,4]];
  mat := Matrix(GF(p),3,5,[MC(f,R.j): j in [1..5],f in forms]);
  rk := Rank(mat);
  assert rk in [1,2]; // if rank is 0 then model not minimal
  M1 := ChangeRing(KernelMatrix(mat),Integers());
  _,_,A := SmithForm(M1);
  A := DiagonalJoin(IdentityMatrix(Integers(),2),Transpose(A));
  _,tr2 := IsTransformation(5,<A,Id(Q,5)>);
  model := tr2*model;
  M := Matrix(model);
  modelp := ChangeRing(model,GF(p));
  Mp := Matrix(modelp);
  if rk eq 1 then 
    assert Mp[3,4] ne 0;
    assert Mp[3,5] eq 0;
    assert Mp[4,5] eq 0;
    aa := k!(MC(M[3,5],R.1)/p);
    bb := k!(MC(M[4,5],R.1)/p);
    if aa ne 0 then
      A[4] -:= (bb/aa)*A[3];
    else
      temp := A[3];A[3] := A[4];A[4] := temp;
    end if;
    _,tr2 := IsTransformation(5,<A,Id(Q,5)>);
    return true,tr2*tr1;
  else
    assert Rank(mat) eq 2;
    assert Mp[3,4] ne 0;
    assert Mp[3,5] ne 0;
    assert Mp[4,5] eq 0;
    aa := k!(MC(M[4,5],R.1)/p);
    if aa eq 0 then 
      return true,tr2*tr1;
    else
      return false,_;
    end if;
  end if;
  return false,_;
end function;

function FindOnComponent(model,p,Gamma)
  assert Degree(model) eq 5;
  assert CoefficientRing(model) cmpeq Q;
// Gamma could either be 0-dimensional or a line.
// TO DO : Find the non-regular points on a line without
// having to loop over all p+1 points.
  k := GF(p);
  pts := [Eltseq(pt): pt in Points(Gamma)];
  ans := {};
  for pt in pts do
    flag := IsNonRegularPointFive(model,p,pt);
    if flag then 
      Include(~ans,pt);
    end if;	 	  
  end for;
  return ans;
end function;

function NonRegularPointsFive(model,p)
  assert Degree(model) eq 5;
  assert CoefficientRing(model) cmpeq Q;
  k := GF(p);
  modelp := ChangeRing(model,k);
  Rp := PolynomialRing(modelp);
  X := Scheme(Proj(Rp),Equations(modelp));
  assert Dimension(X) eq 1;
  XX := SingularSubscheme(X);
  if p lt 10 then 
    pts := [Eltseq(pt): pt in Points(XX)];
  else
    XXX := IrreducibleComponents(XX);
    pts := {};
    for X0 in XXX do
      Gamma := ReducedSubscheme(X0);
      dim := Dimension(Gamma);
      assert dim in [0,1];
//      if dim eq 1 then 
//        assert Degree(Gamma) eq 1; 
//      else
//        assert Degree(Gamma) in [1,2,5];
//      end if;
      pts join:= FindOnComponent(model,p,Gamma);
    end for;
  end if;
  pts := [Eltseq(pt): pt in pts];
  ans := [];
  for pt in pts do
    flag,tr := IsNonRegularPointFive(model,p,pt);
    if flag then 
      Append(~ans,<X!pt,tr>);
    end if;	 	  
  end for;
  return ans;
end function;

////////////////////////////////////////////////////
//   Testing Q_p solubility of genus one models   //
////////////////////////////////////////////////////

function IsQpSolubleCrossTerms(model,p:Affine:=false) 
// Determines whether a generalised binary quartic has a Qp-point.
// N.B. The model should already be minimal.
  assert Degree(model) eq 2;
  assert CoefficientRing(model) cmpeq Q;
  assert #Eltseq(model) eq 8;  // must have cross terms 
  modelp := ChangeRing(model,GF(p));
  flag := HasSmoothPointTwo(modelp);
  if flag then return true,IdTrans(2,Q); end if;
  irregpts := NonRegularPointsCrossTerms(model,p);
  if Affine then 
    irregpts := [pt : pt in irregpts | pt[2] ne 0];
  end if;
  for pt in irregpts do
    N := p*Id(Q,2);
    assert exists(j){j: j in [2..1 by -1] | pt[j] ne 0};
    vec := [Integers()|pt[i]/pt[j]: i in [1..2]];
    if j eq 1 then N[1] := N[2]; end if;
    N[2] := Vector(Q,2,vec);
    r := [Integers()|0,0,pt[3]];
    _,tr1 := IsTransformation(2,<1/p,r,N>);
    flag,tr := IsQpSolubleCrossTerms(tr1*model,p:Affine);
    if flag then return true,tr*tr1; end if;
  end for;
  return false,_;
end function;

function IsQpSolubleTwo(model,p:Affine:=false)
// Determines whether a binary quartic has a Qp-point.
// N.B. The model should already be minimal.
  assert Degree(model) eq 2;
  assert CoefficientRing(model) cmpeq Q;
  assert forall{x: x in Eltseq(model)| IsIntegral(x)};
  if p eq 2 then
    model := IdTrans(2,Q:CrossTerms)*model; // now has cross terms
  end if;
  if #Eltseq(model) eq 8 then 
    return IsQpSolubleCrossTerms(model,p);
  end if;
  modelp := ChangeRing(model,GF(p));
  flag := HasSmoothPointTwo(modelp);
  if flag then return true,IdTrans(2,Q); end if;
  irregpts := NonRegularPointsTwo(model,p);
  if Affine then 
    irregpts := [pt : pt in irregpts | pt[2] ne 0];
  end if;
  for pt in irregpts do
    N := p*Id(Q,2);
    assert exists(j){j: j in [2..1 by -1] | pt[j] ne 0};
    vec := [Integers()|pt[i]/pt[j]: i in [1..2]];
    if j eq 1 then N[1] := N[2]; end if;
    N[2] := Vector(Q,2,vec);
    _,tr1 := IsTransformation(2,<1/p,N>);
    flag,tr := IsQpSolubleTwo(tr1*model,p:Affine);
    if flag then return true,tr*tr1; end if;
  end for;
  return false,_;
end function;

function IsQpSolubleThree(model,p:Affine:=false)
// Determines whether ternary cubic has a Qp-point.
// N.B. The model should already be minimal.
  assert Degree(model) eq 3;
  assert CoefficientRing(model) cmpeq Q;
  assert forall{x: x in Eltseq(model)| IsIntegral(x)};
  modelp := ChangeRing(model,GF(p));
  flag := HasSmoothPointThree(modelp);
  if flag then 
    vprint LocSol,1 : "There are non-singular points on the reduction";
    return true,IdTrans(3,Q);
  end if;
  irregpts := NonRegularPointsThree(model,p);
  vprint LocSol,1 : "Non-regular points ",irregpts;
  if Affine then 
    irregpts := [pt : pt in irregpts | pt[3] ne 0];
  end if;
  for pt in irregpts do
    N := p*Id(Q,3);
    assert exists(j){j: j in [3..1 by -1] | pt[j] ne 0};
    vec := [Integers()|pt[i]/pt[j]: i in [1..3]];
    for i in [j..2] do N[i] := N[i+1]; end for;
    N[3] := Vector(Q,3,vec);
    _,tr1 := IsTransformation(3,<1/p^2,N>);
    flag,tr := IsQpSolubleThree(tr1*model,p:Affine);
    if flag then return true,tr*tr1; end if;
  end for;
  return false,_;
end function;

function IsQpSolubleFour(model,p:Affine:=false)
// Determines whether quadric intersection has a Qp-point.
// N.B. The model should already be minimal.
  assert Degree(model) eq 4;
  assert CoefficientRing(model) cmpeq Q;
  assert forall{x: x in Eltseq(model)| IsIntegral(x)};
  modelp := ChangeRing(model,GF(p));
  flag := HasSmoothPointFour(modelp);
  if flag then 
    return true,IdTrans(4,Q);
  end if;
  irregpts := NonRegularPointsFour(model,p);
  vprint LocSol,1 : "Non-regular points ",[pt[1]: pt in irregpts];
  if Affine then 
    irregpts := [pt : pt in irregpts | pt[1][4] ne 0];
  end if;
  D := DiagonalMatrix(Q,[1/p,1/p^2]);
  for pt in irregpts do
    _,_,T := SmithForm(Matrix(Z,1,2,Eltseq(pt[2])));
    N := p*Id(Q,4);
    assert exists(j){j: j in [4..1 by -1] | pt[1][j] ne 0};
    vec := [Integers()|pt[1][i]/pt[1][j]: i in [1..4]];
    for i in [j..3] do N[i] := N[i+1]; end for;
    N[4] := Vector(Q,4,vec);
    _,tr1 := IsTransformation(4,<D*Transpose(T),N>);
    flag,tr := IsQpSolubleFour(tr1*model,p:Affine);
    if flag then return true,tr*tr1; end if;
  end for;
  return false,_;
end function;

function IsQpSolubleFive(model,p:Affine:=false)
// Determines whether Pfaffian model has a Qp-point.
// N.B. The model should already be minimal.
  assert Degree(model) eq 5;
  assert CoefficientRing(model) cmpeq Q;
  assert forall{x: x in Eltseq(model)| IsIntegral(x)};
  modelp := ChangeRing(model,GF(p));
  flag := HasSmoothPointFive(modelp);
  if flag then 
    return true,IdTrans(5,Q);
  end if;
  irregpts := NonRegularPointsFive(model,p);
  vprint LocSol,1 : "Non-regular points ",[pt[1]: pt in irregpts];
  assert #irregpts le 3;
  if Affine then 
    irregpts := [pt : pt in irregpts | pt[1][1] ne 0];
  end if;
  M := DiagonalMatrix(Rationals(),[1,1,1,1/p,1/p]);
  N := DiagonalMatrix(Rationals(),[1,p,p,p,p]);
  _,tr2 := IsTransformation(5,<M,N>);
  R := PolynomialRing(model);
  for pt in irregpts do
    tr1 := tr2*pt[2];
    model1 := tr1*model;
    assert forall{ x : x in Eltseq(model1) | IsIntegral(x)};
    flag,tr := IsQpSolubleFive(model1,p:Affine);
    if flag then return true,tr*tr1; end if;
  end for;
  return false,_;
end function;

///////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////

// Note: IsLocallySoluble is identified with IsLocallySolvable (in bind)
 
intrinsic IsLocallySolvable(model::ModelG1,p::RngIntElt:
  Transformation:=false,Random:=false,Precision:=20) -> BoolElt, Any
{Determines whether there is a Q_p-point on the given genus one model defined over Q. The model should be non-singular. If true, then a Q_p-point is also returned. If Transformation is true then the second returned argument is instead a transformation tr such that tr*model has a smooth point mod p.}
  n := Degree(model);
  require n in {2,3,4,5} : "Genus one model must have degree 2,3,4 or 5";
  require BaseRing(model) cmpeq Q : "Genus one model must be defined over Q";
  require Discriminant(model) ne 0 : "Genus one model must be non-singular";
  require IsPrime(p) : "p must be a prime";
  vprintf LocSol,1 : 
    "Testing local solubility of a degree %o model at p = %o\n",n,p;
  if n eq 2 and p eq 2 then 
    model1,tr0,fp := Minimise(model:UsePrimes:=[p],CrossTerms); 
  else
    model1,tr0,fp := Minimise(model:UsePrimes:=[p]);
  end if;
  if p in fp then return false,_; end if;
  case n :
    when 2 : flag,tr1 := IsQpSolubleTwo(model1,p);
    when 3 : flag,tr1 := IsQpSolubleThree(model1,p);
    when 4 : flag,tr1 := IsQpSolubleFour(model1,p);
    when 5 : flag,tr1 := IsQpSolubleFive(model1,p);
  end case;
  if not flag then return false,_; end if;
  if Transformation then 
    return true,tr1*tr0; 
  end if;
  model0 := tr1*model1;
  if n eq 2 then model0 := IdTrans(2,Q:CrossTerms)*model0; end if;
  modelp := ChangeRing(model0,GF(p));
  case n :
    when 2 : flag,pt := FindSmoothPointCrossTerms(modelp:rnd:=Random);
    when 3 : flag,pt := FindSmoothPointThree(modelp:rnd:=Random);
    when 4 : flag,pt := FindSmoothPointFour(modelp:rnd:=Random);
    when 5 : flag,pt := FindSmoothPointFive(modelp:rnd:=Random);
  end case;
  error if not flag , "Error in RandomLocalPoint";
  tr := tr1*tr0;
  if n in {2,3} then 
    v1 := Valuation(tr`Scalar,p);
  else
    v1 := Valuation(Determinant(tr`EquationMatrix),p);
  end if;
  v2 := Valuation(Determinant(tr`Matrix),p);
  Precision := Max(Precision,20);
// to do: work out the right precision to use here
  prec := Precision + Abs(v1) + Abs(v2);
  Qp := pAdicField(p:Precision:=prec);
  pi := UniformizingElement(Qp);
  if n eq 2 then 
    C0 := HyperellipticCurve(model0);
    seq := [pt[i]: i in [1,3,2]];
    pt := C0(Qp)![Qp!x + O(pi): x in seq];	
  else
    C0 := Curve(model0);
    pt := C0(Qp)![Qp!x + O(pi): x in Eltseq(pt)];
  end if;
  pt := LiftPoint(pt,prec:Random:=Random);
  if n eq 2 then 
    x1,y,x2 := Explode(Eltseq(pt));
    rr := assigned tr`Shift select tr`Shift else [0,0,0];
    r0,r1,r2 := Explode(rr);
    y := (1/tr`Scalar)*y + (r0*x1^2 + r1*x1*x2 + r2*x2^2);
    pt := [x1,x2];
    pt := [&+[(tr`Matrix)[j,i]*pt[j]: j in [1..n]]: i in [1..n]];
    Append(~pt,y);
  else    
    pt := [&+[(tr`Matrix)[j,i]*pt[j]: j in [1..n]]: i in [1..n]];
  end if;
  CQp := PointSet(Curve(model),Qp);
  flag,pt := IsCoercible(CQp,pt);
  if flag then return true,pt; end if;
  error "Something is wrong with the Q_p point computed";
  return IsLocallySolvable(model,p:Precision:=2*Precision,Random:=Random);
end intrinsic;

intrinsic IsLocallySolvable(model::ModelG1) -> BoolElt
{Determines whether the given genus one model over Q has a Q_p point for all (finite) primes p. The model should be non-singular.}
  n := Degree(model);
  require n in {2,3,4,5} : "Genus one model must have degree 2,3,4 or 5";
  if BaseRing(model) cmpeq Z then 
    model := ChangeRing(model,Q);
  end if;
  require BaseRing(model) cmpeq Q : "Genus one model must be defined over Q";
  require Discriminant(model) ne 0 : "Genus one model must be non-singular";
  model := Minimise(model);
  Delta := Discriminant(model);
  pp := PrimeDivisors(Integers()!Delta);
  flag := true;
  for p in pp do
    flag := IsLocallySolvable(model,p:Transformation);
// N.B. Setting Transformation to true means we don't waste time actually 
// finding a point.
    if not flag then break; end if;
  end for;
  return flag;
end intrinsic;

