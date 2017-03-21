freeze;

////////////////////////////////////////////////////////
//  Addition of genus one models as covering curves.  //
////////////////////////////////////////////////////////

//  Cases (2,2) and (3,3) moved here from "3descentcubics.m";
//  Case (2,4) added by T. Fisher, April 2010

declare verbose AddCovers, 1;

import "../CrvEll/FourDesc/d4.m" : EpsilonToCover;

Q := Rationals();
Id := IdentityMatrix;

// Case (2,2) : Adding binary quartics

function redo(a,b,c,d,e,phi)
 g:=Polynomial(Reverse([a,b,c,d,e])); g4:=QuarticG4Covariant(g); r:=1;
 while true do r:=1/r+Random([-10..10]);
  if r eq 0 then r:=Random([1..100]); end if;
  e:=(4*phi*Evaluate(g,r)+Evaluate(g4,r))/3;
  if Norm(e) ne 0 then return e; end if; end while; end function;

function n2add(m1,m2,c4J,c6J,s1,s2) P := PolynomialRing(Rationals()); X := P.1;
 F:=X^3-27*c4J*X-54*c6J; Q<s>:=quo<P|F>; phi:=-s/12;
 a,b,c,d,e:=Explode([m/s1^2 : m in ModelToSequence(m1)]);
 z1:=(4*a*phi-8*a*c+3*b^2)/3;
 if z1 eq 0 then z1:=((phi+c)/3)^2-4*a*e; end if;
 if Norm(z1) eq 0 then z1:=redo(a,b,c,d,e,phi); end if;
 a,b,c,d,e:=Explode([m/s2^2 : m in ModelToSequence(m2)]);
 z2:=(4*a*phi-8*a*c+3*b^2)/3;
 if z2 eq 0 then z2:=((phi+c)/3)^2-4*a*e; end if;
 if Norm(z2) eq 0 then z2:=redo(a,b,c,d,e,phi); end if;
 return GenusOneModel(TwoCover(z1*z2)); end function;

function check_invariants(A,B) P := PolynomialRing(Parent(A[1])); X := P.1;
 if A[3] eq 0 and (A[1] ne 0 or A[2] ne 0) then return false,_,_; end if;
 if B[3] eq 0 and (B[1] ne 0 or B[2] ne 0) then return false,_,_; end if;
 if A[3] ne 0 then r1:=[r[1] : r in Roots(X^4-A[1]/A[3])]; end if;
 if B[3] ne 0 then r2:=[r[1] : r in Roots(X^6-B[1]/B[3])]; else r2:=r1; end if;
 if A[3] eq 0 then r1:=r2; end if;
 S1:=Set(r1) meet Set(r2); if #S1 eq 0 then return false,_,_; end if;
 if A[3] ne 0 then r1:=[r[1] : r in Roots(X^4-A[2]/A[3])]; end if;
 if B[3] ne 0 then r2:=[r[1] : r in Roots(X^6-B[2]/B[3])]; else r2:=r1; end if;
 if A[3] eq 0 then r1:=r2; end if;
 S2:=Set(r1) meet Set(r2); if #S2 eq 0 then return false,_,_; end if;
 return true,Random(S1),Random(S2); end function;

// Case (3,3) : Adding ternary cubics

intrinsic AddCubics(model1::ModelG1,model2::ModelG1 :
		    E:=Jacobian(model1), ReturnBoth:=false) -> ModelG1
{The sum of two genus one models of degree 3 in the Weil-Chatelet group.}
  require model1`Degree eq 3 and model2`Degree eq 3 :
  "The given models must have degree 3";
  newcubic := AddCubics(model1`Equation, model2`Equation :
			E:=E, ReturnBoth:=ReturnBoth);
  return GenusOneModel(newcubic);
end intrinsic;

intrinsic AddCubics(cubic1::RngMPolElt,cubic2::RngMPolElt:
                    E:=Jacobian(cubic1), ReturnBoth:=false)  -> RngMPolElt
{The sum of the two ternary cubics as elements of H^1(Q,E[3]). 
 The ternary cubics must have the same invariants, 
 and if their sum is not representable as a cubic an error will result.}
  flag,model := IsGenusOneModel(cubic1);
  require flag and model`Degree eq 3 : "The arguments must be plane cubics";
  flag,model := IsGenusOneModel(cubic2);
  require flag and model`Degree eq 3 : "The arguments must be plane cubics";
  B1 := BaseRing(Parent(cubic1));
  require B1 cmpeq Rationals() : "cubic1 must be defined over Q.";
  B2 := BaseRing(Parent(cubic2));
  require B2 cmpeq Rationals() : "cubic2 must be defined over Q.";
  require cInvariants(model) eq cInvariants(E) :
    "The given cubics must have same invariants as E";
  alpha1 := ThreeSelmerElement(E,cubic1);
  alpha2 := ThreeSelmerElement(E,cubic2);
  alpha3 := <alpha1[i]*alpha2[i]: i in [1..#alpha1]>;
  alpha4 := <alpha1[i]*alpha2[i]^2: i in [1..#alpha1]>;
  cubic3 := Equation(ThreeDescentCubic(E,alpha3));
  if ReturnBoth then
     cubic4 := Equation(ThreeDescentCubic(E,alpha4));
     return cubic3, cubic4;
  else return cubic3; end if;
end intrinsic;

// Case (2,4) : Adding binary quartics and quadric intersections

function ModifyQuartic(E,q)
  q := RemoveCrossTerms(q);
  E1 := Jacobian(q);
  flag,iso := IsIsomorphic(E1,E);
  assert flag;
  u := IsomorphismData(iso)[4];
  _,tr := IsTransformation(2,<u,Id(Q,2)>);
  assert cInvariants(tr*q) eq cInvariants(E);
  return tr*q,u;
end function;

/*
K<a,b,c,d,e> := FunctionField(Rationals(),5);                     
P := PolynomialRing(K); X := P.1;
g := a*X^4 + b*X^3 + c*X^2 + d*X + e;
_,q := IsGenusOneModel(g);
c4,c6 := Explode(cInvariants(q));
I := c4/2^4;
J := c6/2^5;
f := X^3 - 3*I*X + J;
F<t> := quo<P|g>;
bb := 6*a*t^2 + 3*b*t + c;
elt := -Evaluate(f,-bb);
delta := Discriminant(q);
assert Norm(elt) eq (3^12/2^8)*delta^2;
// => element ee in next function is invertible
*/

function SquareRootOfAlpha(iso_L,iso_F,q);
  L := Domain(iso_L);
  F := Domain(iso_F);
  t := F.1;
  assert Evaluate(Equation(q),[t,1]) eq 0;
  LF<phi> := quo<PolynomialRing(F)|Modulus(L)>; 
  assert #Eltseq(q) eq 5;
  a,b,c,d,e := Explode(Eltseq(q));
  num := (4*a*t + b)*phi + (-8*a*c + 3*b^2)*t - 6*a*d + b*c;
  denom := phi + 6*a*t^2 + 3*b*t + c;
// taking num/denom sometimes gives error message:
// Runtime error in '/': Base ring must be Z/mZ or a field
  f := Modulus(L);
  I := (-1/3)*Coefficient(f,1);
  bb := 6*a*t^2 + 3*b*t + c;
  dd := phi^2 - bb*phi + bb^2 - 3*I;
  ee := -Evaluate(f,-bb);
  ans := num*dd*(1/ee);
  assert ans*denom eq num;
  return ans,phi;
end function;

function MySqrt(x)
  if Parent(x) cmpeq Q then 
    flag,t := IsPower(x,2);
    assert flag; 
    return t; 
  else 
    return Sqrt(x); 
  end if; 
end function;

function TwoSelmerElementLinear(E,quartic,iso)
  P := PolynomialRing(Rationals()); X:=P.1;
  g := Evaluate(Equation(quartic),[X,1]);
  g6 := QuarticG6Covariant(g);
  g6rev := P!(X^6*Evaluate(g6,-1/X));
  assert exists(j){j : j in [0..10] | Evaluate(g6rev,j) ne 0};
  _,tr := IsTransformation(2,<1,Matrix(Q,2,2,[1,-j,0,1])>);
  quartic := tr*quartic;
  g := Evaluate(Equation(quartic),[X,1]);
  r := QuarticRSeminvariant(g);
  assert r eq Evaluate(g6rev,j);
  assert r ne 0;
  return TwoSelmerElement(E,quartic),tr;
end function;

function TidyRepresentative(u,iso)
// find a nice representative in F^*/ Q^* (F^*)^2
  for ctr in [1..2] do
    xx := u @ iso;
    xx := <NiceRepresentativeModuloPowers(x,2) : x in xx>;
    u := xx @@ iso;
    u /:= RationalGCD(Eltseq(u));
  end for;
  return u;
end function;

function MyTwoTorsionPoint(E,phi)
  a1,_,a3 := Explode(aInvariants(E));
  b2 := bInvariants(E)[1];
  L := Parent(phi);
  xT := -(4*phi + b2)/12;
  yT := -(a1*xT + a3)/2;
  return E(L)![xT,yT];
end function;

function TwoFourAdd(E,QI,qq2,qq3)  
  vprintf AddCovers, 1 :"\nComputing binary quartics\n";
  q1,u := ModifyQuartic(E,DoubleGenusOneModel(QI));
  q2 := ModifyQuartic(E,qq2);
  q3 := ModifyQuartic(E,qq3);
  _,tr := IsTransformation(4,<Id(Q,2),DiagonalMatrix(Q,[u,1,1,1])>);
  QI := tr*QI;
  vprintf AddCovers, 1 :"\nSetting up L where [L:Q] = 3\n";
  c4,c6 := Explode(cInvariants(E));
  I := c4/2^4;
  J := c6/2^5;
  P := PolynomialRing(Q); X:=P.1;
  L<phi> := quo<P | X^3 - 3*I*X + J >;
  Labs, iso_L := AbsoluteAlgebra(L); 
  phiabs := phi @ iso_L;
  TT := <MyTwoTorsionPoint(E,x): x in phiabs>;
  E`TwoTorsionOrbits := TT;
  alpha,tr2 := TwoSelmerElementLinear(E,q1,iso_L);
  beta := TwoSelmerElementLinear(E,q2,iso_L);
  gamma := TwoSelmerElementLinear(E,q3,iso_L);
  q1 := tr2*q1;
  _,tr4 := IsTransformation(4,<tr2`Matrix,Id(Q,4)>);
  QI := tr4*QI;
  vprint AddCovers, 1 :"\nWe have the following elements of L";
  vprintf AddCovers, 1 :"alpha = %o = %o\n",alpha,alpha @@ iso_L;
  vprintf AddCovers, 1 :"beta = %o = %o\n",beta,beta @@ iso_L;
  vprintf AddCovers, 1 :"gamma = %o = %o\n",gamma,gamma @@ iso_L;
  vprintf AddCovers, 1 :"\nSetting up F where [F:Q] = 4\n";
  g := Evaluate(Equation(q1),[X,1]);
  error if Degree(g) ne 4, "Intermediate 2-covering is trivial";
  F<t> := quo<P|g>;
  Fabs, iso_F := AbsoluteAlgebra(F);
  vprintf AddCovers, 1 :
    "\nComputing square roots of alpha and beta*gamma in LF\n";
  rtalpha,PHI := SquareRootOfAlpha(iso_L,iso_F,q1);
  vprintf AddCovers, 1 :"Sqrt(alpha) = %o\n",rtalpha;
  toseq := func<xx|&cat[Eltseq(x): x in xx]>;
  elts := [<x^i: x in phiabs>: i in [0..2]];
  mymat := Matrix(Q,3,3,[toseq(xx): xx in elts]);
  function ToAlg(aa)
    soln := Solution(mymat,Vector(toseq(aa)));
    return &+[soln[i+1]*PHI^i: i in [0..2]];
  end function;  
  m := <MySqrt(beta[i]*gamma[i]/alpha[i]): i in [1..#TT]>;
  sqrtbetagamma := ToAlg(m)*rtalpha;
  vprintf AddCovers, 1 :"Sqrt(beta*gamma) = %o\n",sqrtbetagamma;
  betagamma := <beta[i]*gamma[i]: i in [1..#TT]>;
  assert ToAlg(alpha) eq rtalpha^2;
  assert ToAlg(betagamma) eq sqrtbetagamma^2;
  vprintf AddCovers, 1 :"\nComputing delta (using the formula in ANTS VIII)\n";
  ff := 1/Evaluate(Derivative(Modulus(L)),phi);
  ff := Evaluate(P!ff,PHI);
  delta := Trace(rtalpha*ff)*Trace(sqrtbetagamma*ff);
  vprint AddCovers, 1 : "delta =",delta;
  vprint AddCovers, 1 : "Impoving representative in F^*/(F^*)^2 Q^*";
  delta := TidyRepresentative(delta,iso_F);
  vprint AddCovers, 1 : "delta =",delta;
  assert IsSquare(Norm(delta));
  vprintf AddCovers, 1 : 
    "\nConverting quadric intersection to an element of F^*/(F^*)^2 Q^*\n";
  C := Curve(q1);
  tabs := t @ iso_F;
  rampts := <C(Fabs[i])![tabs[i],1,0] : i in [1..#tabs]>;
  q1`RamificationPoints := rampts;
  dd1 := RelativeSelmerElement(q1,QI)[1] @@ iso_F;
  vprint AddCovers, 1 : "dd1 =",dd1;
  vprint AddCovers, 1 : "Multiplying by delta";
  dd2 := delta*dd1;  
  assert IsSquare(Norm(dd1)/Coefficient(g,4));
  assert IsSquare(Norm(dd2)/Coefficient(g,4));
  vprint AddCovers, 1 : "dd2 =",dd2;
  vprint AddCovers, 1 : 
    "Converting element of F^*/(F^*)^2 Q^* to a quadric intersection";
  mats := EpsilonToCover(dd2);
  model := GenusOneModel([ChangeRing(M,Q): M in mats]);
  return Reduce(Minimise(model));
end function;

///////////////////////////////////////////////////////////

intrinsic AddCovers(model1::ModelG1,model2::ModelG1 :
	      E:=Jacobian(model1), ReturnBoth:=false) -> ModelG1 
{A genus one model of degree n representing the composition in H^1(Q,E[n]) of the two give models of degrees m and n where (m,n) = (2,2), (3,3) or (2,4). Note that if (m,n) = (3,3) then there is an ambiguity coming from the fact a ternary cubic only determines a 3-covering up to sign. If ReturnBoth is true then both possible answers are returned.}
  m := model1`Degree;
  n := model2`Degree;
  require [m,n] in {[2,2],[3,3],[2,4]} :
    "Models must have degrees m and n where (m,n) = (2,2), (3,3) or (2,4).";
  case [m,n] :
  when [2,2] : 
    if #Eltseq(model1) eq 8 then 
      model1 := CompleteTheSquare(model1);
    end if;
    if #Eltseq(model2) eq 8 then 
      model2 := CompleteTheSquare(model2);
    end if;
    c4,c6 := Explode(cInvariants(model1)); 
    c4m,c6m := Explode(cInvariants(model2));
    c4E,c6E := Explode(cInvariants(E));
    b,s1,s2 := check_invariants([c4,c4m,c4E],[c6,c6m,c6E]);
    require b: "cInvariants of models (and given E) must be compatible";
    ans := n2add(model1,model2,c4E,c6E,s1,s2); 
  when [3,3] :
    if ReturnBoth then 
      c1,c2 := AddCubics(model1`Equation, model2`Equation: E:=E, ReturnBoth);
      return GenusOneModel(c1),GenusOneModel(c2);
    end if;
    newcubic := AddCubics(model1`Equation, model2`Equation: E:=E);
    ans := GenusOneModel(newcubic);
  when [2,4] :
    E := MinimalModel(E);
    qq2 := model1;
    QI := model2;
    qq1 := CompleteTheSquare(DoubleGenusOneModel(QI));
    qq3 := qq1*qq2;
    ans := TwoFourAdd(E,QI,qq2,qq3);
  end case;
  return ans;
end intrinsic;

intrinsic '*'(model1::ModelG1,model2::ModelG1 :
	      E:=Jacobian(model1), ReturnBoth:=false) -> ModelG1 
{"} //"
  return AddCovers(model1,model2:E:=E,ReturnBoth:=ReturnBoth);
end intrinsic;

