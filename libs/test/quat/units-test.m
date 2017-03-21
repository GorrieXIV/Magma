
procedure check_unit_group(GG, umap)
  "Checking unit group multiplication table";
  for u in GG do assert IsUnit(u@umap); end for;
  for u1 in GG do for u2 in GG do
    assert IsScalar( (u1@umap) * (u2@umap) / (u1*u2)@umap );
  end for; end for;
end procedure;

P<x> := PolynomialRing(Rationals());

F := NumberField(x^2-NextPrime(Random(100)));
H<i,j,k> := QuaternionAlgebra<F|-1,-1>;
U, h := UnitGroup(MaximalOrder(H)); U;
check_unit_group(U, h);

F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
Foo := InfinitePlaces(F);
A := QuaternionAlgebra(ideal<Z_F | 2>, Foo);
IsDefinite(A);
O := MaximalOrder(A);
U, h := UnitGroup(O); U;
check_unit_group(U, h);

// Contains fourth roots of unity
K := NumberField(Polynomial([F | 1,0,1]));
bl, iota := Embed(K, A);
O := Order(iota(K.1));
U, h := UnitGroup(O); U;
check_unit_group(U, h);
