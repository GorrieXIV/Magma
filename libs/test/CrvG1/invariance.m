
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


for n in [2..5] do
n;
  U := RandomModel(n:RequireNonsingular);
  g := RandomTransformation(n);
  lambda := ScalingFactor(n,g);
  UU := ApplyTransformation(g,U);
  c4,c6 := Explode(cInvariants(U));
  cc4,cc6 := Explode(cInvariants(UU));
  assert cc4 eq lambda^4*c4;
  assert cc6 eq lambda^6*c6;
end for;

for n in [2..5] do
  U := RandomModel(n:RequireNonsingular);
  g := RandomTransformation(n);
  lambda := ScalingFactor(n,g);
  UU := ApplyTransformation(g,U);
  H := Hessian(U);
  HH := Hessian(UU);
  assert OldData(HH) eq lambda^2*OldData(g*H);
  if assigned HH`Equation then
     assert HH`Equation eq lambda^2*ApplyTransformation(g,H)`Equation;
  elif HH`Degree eq 4 then 
     assert HH`Equations eq [ lambda^2*eqn : eqn in ApplyTransformation(g,H)`Equations ];
  end if;
end for;

function DualTransformation(n,g)
  g := Tuple(g);
  if n in [2..3] then 
    mat := MatrixRing(Rationals(),n)!g[2];
    gg := <1/g[1],Transpose(mat)^(-1)>;
  else
    m := n eq 4 select 2 else 5;
    matV := MatrixRing(Rationals(),m)!g[1];
    matW := MatrixRing(Rationals(),n)!g[2];
    gg := <Transpose(matV)^(-1),Transpose(matW)^(-1)>;
  end if;
  _,gg := IsTransformation(n,gg);
  return gg;
end function;

for n in [2..5] do
  U := RandomModel(n:RequireNonsingular);
  g := RandomTransformation(n);
  gg := DualTransformation(n,g);
  lambda := ScalingFactor(n,g);
  UU := ApplyTransformation(g,U);
  P,Q := Contravariants(U);
  PP,QQ := Contravariants(UU);
  assert OldData(PP) eq lambda^4*OldData(ApplyTransformation(gg,P));
  assert OldData(QQ) eq lambda^6*OldData(ApplyTransformation(gg,Q));
end for;

U := RandomModel(5:RequireNonsingular);
g := RandomTransformation(5);
matV := MatrixRing(Rationals(),5)!Tuple(g)[1];
matW := MatrixRing(Rationals(),5)!Tuple(g)[2];
_,gg := IsTransformation(5,<matW,Transpose(matV)^(-1)>);
UU := ApplyTransformation(g,U);
F,G := HesseCovariants(U,2);
FF,GG := HesseCovariants(UU,2);
dV := Determinant(matV);
dW := Determinant(matW);
assert dV^3*dW*OldData(ApplyTransformation(gg,F)) in [OldData(FF),-OldData(FF)];
assert dV^7*dW^3*OldData(ApplyTransformation(gg,G)) in [OldData(GG),-OldData(GG)];

U := RandomModel(5:RequireNonsingular);
g := RandomTransformation(5);
matV := MatrixRing(Rationals(),5)!Tuple(g)[1];
matW := MatrixRing(Rationals(),5)!Tuple(g)[2];
_,gg := IsTransformation(5,<Transpose(matW)^(-1),matV>);
UU := ApplyTransformation(g,U);
F,G := HesseCovariants(U,3);
FF,GG := HesseCovariants(UU,3);
dV := Determinant(matV);
dW := Determinant(matW);
assert dV^5*dW^3*OldData(ApplyTransformation(gg,F)) in [OldData(FF),-OldData(FF)];
assert dV^9*dW^5*OldData(ApplyTransformation(gg,G)) in [OldData(GG),-OldData(GG)];

