SetEchoInput(true);
//SetVerbose("Groebner", 1);

QUICK := true;

// Loading this file will check that some of the functions
// in g1invariants.m and hessepolynomials.m are correct.

// precisely the object that used to *be* the genus one model function
function OldData(model)
  n := model`Degree;
  if n in {2,3} then return model`Equation;
  elif n eq 4 then
    eqns := model`Equations;
    return Matrix(Universe(eqns),2,1,eqns);
  elif n eq 5 then return model`DefiningMatrix;
  end if;
end function;

function DiscreteInvariants(n,ab)
  a,b := Explode(ab);
  case n:
    when 2:
      D := a*(64*a^2-b^2);
      c4 := 192*a^2+b^2;
      c6 := 576*a^2*b-b^3;
    when 3:
      D := -a*(27*a^3+b^3);
      c4 := -216*a^3*b+b^4;
      c6 := 5832*a^6-540*a^3*b^3-b^6;
    when 4:
      D := a*b*(16*a^4-b^4);
      c4 := 256*a^8+224*a^4*b^4+b^8;
      c6 := -4096*a^12+8448*a^8*b^4+528*a^4*b^8-b^12;
    when 5:
      D := a^11*b-11*a^6*b^6-a*b^11;
      c4 := a^20+228*a^15*b^5+494*a^10*b^10-228*a^5*b^15+b^20;
      c6 := -a^30+522*a^25*b^5+10005*a^20*b^10+10005*a^10*b^20
         -522*a^5*b^25-b^30;
  end case;
  return D,c4,c6;
end function;

function DiscreteCovariants(n,r,ab)
  a,b := Explode(ab);
  assert GCD(r,n) eq 1;
  r := r mod n;
  case [n,r]:
    when [2,1]:
      f1 := [a,b];
      f2 := [2*a*b,192*a^2-b^2];
    when [3,1]:
      f1 := [a,b];
      f2 := [3*a*b^2,-108*a^3-b^3];
    when [3,2]:
      f1 := [-9*a^2*b,-54*a^3+b^3];
      f2 := [324*a^5-15*a^2*b^3,-270*a^3*b^2-b^5];
    when [4,1]:
      f1 := [a,b];
      f2 := [a*(-16*a^4+5*b^4),b*(80*a^4-b^4)];
    when [4,3]:
      f1 := [4*a^3*(16*a^4+7*b^4),b^3*(112*a^4+b^4)];
      f2 := [4*a^3*(-256*a^8+352*a^4*b^4+11*b^8),b^3*(2816*a^8+352*a^4*b^4-b^8)];
    when [5,1]:
      f1 := [a,b];
      f2 := [a*(-a^10+66*a^5*b^5+11*b^10),b*(11*a^10-66*a^5*b^5-b^10)];
    when[5,2]:
      f1 := [a^2*(a^5+7*b^5),b^2*(-7*a^5+b^5)];
      f2 := [-a^2*(a^15-119*a^10*b^5+187*a^5*b^10-17*b^15),
           -b^2*(17*a^15+187*a^10*b^5+119*a^5*b^10+b^15)];
    when[5,3]:
      f1 := [a^3*(a^10+39*a^5*b^5-26*b^10),b^3*(-26*a^10-39*a^5*b^5+b^10)];
      f2 := [-a^3*(a^20-207*a^15*b^5-391*a^10*b^10-1173*a^5*b^15+46*b^20),
           -b^3*(46*a^20+1173*a^15*b^5-391*a^10*b^10+207*a^5*b^15+b^20)];
    when[5,4]:
      f1 := [a^4*(a^15+171*a^10*b^5+247*a^5*b^10-57*b^15),
           b^4*(57*a^15+247*a^10*b^5-171*a^5*b^10+b^15)];
      f2 := [a^4*(-a^25+435*a^20*b^5+6670*a^15*b^10+3335*a^5*b^20-87*b^25),
           b^4*(87*a^25+3335*a^20*b^5+6670*a^10*b^15-435*a^5*b^20-b^25)];
  end case;
  return f1,f2;
end function;

K<a1,a2,a3,a4,a6> := FunctionField(Rationals(),5);
E := EllipticCurve([a1,a2,a3,a4,a6]);
c4E,c6E := Explode(cInvariants(E));
for n in [2..5] do
  phi := GenusOneModel(n,E);
  c4,c6 := Explode(cInvariants(phi));
c4,c6;
c4E,c6E;
  assert c4 eq c4E;
  assert c6 eq c6E;
end for;

R<a,b> := PolynomialRing(Rationals(),2);
Bracket := func<f,g|f[1]*g[2]-f[2]*g[1]>;
Deriv := Derivative;

for n in [2..5] do
  D,c4,c6 := DiscreteInvariants(n,[a,b]);
  r := 12 div (6-n);
  s := 4*n div (6-n);
  t := 6*n div (6-n);
  assert TotalDegree(D) eq r;
  assert TotalDegree(c4) eq s;
  assert TotalDegree(c6) eq t;
  mat := Matrix(2,2,[Deriv(Deriv(D,aa),bb):aa,bb in [a,b]]);
  assert c4 eq (-1/(r-1)^2)*Determinant(mat);
  mat := Matrix(2,2,[Derivative(f,aa):f in [D,c4],aa in [a,b]]);
  assert c6 eq (1/s)*Determinant(mat);
  assert c4^3-c6^2 eq 1728*D^n;
  U := Vector(2,[a,b]);
  dD := Vector(2,[-Derivative(D,b),Derivative(D,a)]);
  dc4 := Vector(2,[-Derivative(c4,b),Derivative(c4,a)]);
  dc6 := Vector(2,[-Derivative(c6,b),Derivative(c6,a)]);
  assert Bracket(dD,dc4) eq TotalDegree(c4)*c6;
  assert Bracket(dD,dc6) eq TotalDegree(c6)*c4^2;
  assert Bracket(dc4,dc6) eq 576*TotalDegree(c6)*n*D^(n-1);
  assert 3*D*dc4 eq n*(-c6*U+c4*dD);
  assert 2*D*dc6 eq n*(-c4^2*U+c6*dD);
  assert 1728*n*D^(n-1)*U eq 3*c6*dc4-2*c4*dc6;
  assert 1728*n*D^(n-1)*dD eq 3*c4^2*dc4-2*c6*dc6;
end for;

R<a,b> := PolynomialRing(Rationals(),2);

for n in [2..5] do
  D,c4,c6 := DiscreteInvariants(n,[a,b]);
  f1,f2 := DiscreteCovariants(n,1,[a,b]);
  assert f1 eq [a,b];
  assert f2 eq [-Derivative(D,b),Derivative(D,a)];
  f1,f2 := DiscreteCovariants(n,-1,[a,b]);
  kappa := case<n|2:1/192,3:1/18,4:1/4,5:1,default:0>;
  s := TotalDegree(c4);
  t := TotalDegree(c6);
  assert f1 eq [(1/s)*kappa*Derivative(c4,a),(1/s)*Derivative(c4,b)];
  assert f2 eq [(1/t)*kappa*Derivative(c6,a),(1/t)*Derivative(c6,b)];
end for;

function TwistedHesseModel(ab)
  phi := OldData(HesseModel(5,ab));
  R := BaseRing(phi);
  subst := [R.3,R.2,R.1,R.5,R.4];
  phi := Parent(phi)![Evaluate(phi[i,j],subst):i,j in [1..5]];
  return phi;
end function;

for n in [2..5] do
  a := Random([Rationals()!i: i in [-10..10] | i ne 0]);
  b := Random([Rationals()!i: i in [-10..10] | i ne 0]);
  phi := HesseModel(n,[a,b]);
  inv4,inv6 := Invariants(phi);
  D,c4,c6 := DiscreteInvariants(n,[a,b]);
  assert c4 eq inv4;
  assert c6 eq inv6;
  for r in [1..n-1] do 
    if GCD(r,n) eq 1 then 
      F1,F2 := HesseCovariants(phi,r);
      f1,f2 := DiscreteCovariants(n,r,[a,b]);
      if n eq 5 and r in [2,3] then
        FF1 := Parent(OldData(phi))!TwistedHesseModel(f1);
        FF2 := Parent(OldData(phi))!TwistedHesseModel(f2);
        assert OldData(F1) in {FF1,-FF1} and OldData(F2) in {FF2,-FF2};
      else
        assert OldData(F1) eq Parent(OldData(phi))!OldData(HesseModel(n,f1));
        assert OldData(F2) eq Parent(OldData(phi))!OldData(HesseModel(n,f2));
      end if;
    end if;
  end for;
end for;

R<a,b> := PolynomialRing(Rationals(),2);
S<la,mu> := PolynomialRing(R,2);

for n in [2..5] do
  D,c4,c6 := DiscreteInvariants(n,[a,b]); 
  rs := [1..n-1];
  if QUICK then rs := [Random(rs)]; end if;
  for r in rs do 
    if GCD(r,n) eq 1 then 
      DD,cc4,cc6,eps,alpha := HessePolynomials(n,r,[c4,c6] : Variables:=[la,mu]);
      assert (cc4^3-cc6^2) eq (c4^3-c6^2)^r*DD^n;
      f1,f2 := DiscreteCovariants(n,r,[a,b]);
      F1 := Vector(S,2,f1);
      F2 := Vector(S,2,f2);
      pencil := Eltseq(la*F1+mu*F2);
      assert alpha*Evaluate(D,pencil) eq D^r*DD;
      assert eps^2*Evaluate(c4,pencil) eq cc4;
      assert eps^3*Evaluate(c6,pencil) eq cc6;
    end if;
  end for;
end for;

K<c4,c6> := FunctionField(Rationals(),2);
R<t> := PolynomialRing(K);
S<la,mu> := PolynomialRing(K,2);
for n in [2..5] do
  DD,cc4,cc6 := HessePolynomials(n,1,[c4,c6] : Variables:=[la,mu]);
  U1 := Vector(R,[1,0]);
  H1 := -c6/(c4^3-c6^2)*Vector(R,[c6,-c4]);
  rsseq := Eltseq(U1+t*H1);
  J := c4^3/(c4^3-c6^2);
  alpha,beta := RubinSilverbergPolynomials(n,J : Parameter:=t);
  assert Evaluate(cc4,rsseq) eq c4*alpha;
  assert Evaluate(cc6,rsseq) eq c6*beta;
end for;

R<a,b> := PolynomialRing(Rationals(),2);
for n in [2..5] do
  phi := HesseModel(n,[a,b]);
  inv4,inv6 := Invariants(phi);
  D,c4,c6 := DiscreteInvariants(n,[a,b]);
  assert c4 eq inv4;
  assert c6 eq inv6;
  for r in QUICK select {1} else {1, n-1} do 
    F1,F2 := HesseCovariants(phi,r);
    f1,f2 := DiscreteCovariants(n,r,[a,b]);
    assert OldData(F1) eq Parent(OldData(phi))!OldData(HesseModel(n,f1));
    assert OldData(F2) eq Parent(OldData(phi))!OldData(HesseModel(n,f2));
  end for;
end for;
