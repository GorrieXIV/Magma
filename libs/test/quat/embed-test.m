
P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
F := FieldOfFractions(Z_F);
A := QuaternionAlgebra<F | -3,b>;
K := ext<F | x^2+1>;
mu, iota := Embed(K, A);
O := MaximalOrder(A);
p := ideal<Z_F | 2>;
M2F, phi := pMatrixRing(O, p); 

P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
c := Z_F!(120*b^2 + 48*b + 12);
K := ext<F | Polynomial([F | 3,0,1])>;
Kab := AbelianExtension(K);
NormEquation(Kab, c);
