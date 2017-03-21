
SetSeed(1);

NUM := 5;

P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
F := FieldOfFractions(Z_F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3, b>;
for j := 1 to NUM do
  N := Random([1..50]);
  "Level", N;
  M := MaximalOrder(A);
  O := Order(M, N*Z_F);
  assert IsEichler(M, M); 
  assert IsEichler(O, M); 
end for;

// Try several "random" quaternion algebras over quadratic fields
for c := 1 to NUM do
  D := Random([d : d in [-100..100] | not IsSquare(d)]);
  K<w> := NumberField(x^2-D);
  Z_K := MaximalOrder(K);
  K<K1,w> := FieldOfFractions(Z_K);
  a := Random([i : i in [-50..50] | i ne 0]) + Random([-50..50])*w;
  b := Random([i : i in [-50..50] | i ne 0]) + Random([-50..50])*w;
  printf "D = %o, a = %o, b = %o\n", D, a, b;
  A := QuaternionAlgebra<K | a,b>;
  M := MaximalOrder(A);
  repeat
    N := Random([i : i in [-50..50] | i ne 0]) + Random([-50..50])*w;
  until Minimum(N*Z_K + Discriminant(M)) eq 1;
  printf "Level N = %o\n", N;
  O := Order(M, N*Z_K);
  assert IsEichler(M, M); 
  assert IsEichler(O, M); 
end for;

// Nonexamples due to Jeroen Sijsling 
A<i,j,k>:=QuaternionAlgebra<Rationals() | 2,-3>;
bg1:=(0/2) + (2/2)*i + (-2/2)*j + (0/2)*k;
bg2:=(0/2) + (2/2)*i + (2/2)*j + (0/2)*k;
bg3:=(0/2) + (2/2)*i + (0/2)*j + (2/2)*k;
bg4:=(2/2) + (0/2)*i + (0/2)*j + (0/2)*k;
O:=QuaternionOrder([bg1,bg2,bg3,bg4]);
M:=MaximalOrder(O);
assert not IsEichler(O, M);

A<i,j,k>:=QuaternionAlgebra<Rationals() | -2,5>;
bg1:=(2/2) + (0/2)*i + (0/2)*j + (0/2)*k;
bg2:=(1/2) + (0/2)*i + (-1/2)*j + (-2/2)*k;
bg3:=(0/2) + (0/2)*i + (2/2)*j + (-2/2)*k;
bg4:=(1/2) + (-3/2)*i + (1/2)*j + (-1/2)*k;
O:=QuaternionOrder([bg1,bg2,bg3,bg4]);
M:=MaximalOrder(O);
assert not IsEichler(O, M);

