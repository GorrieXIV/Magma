NUM := 2;

P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
F := FieldOfFractions(Z_F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3, b>;
O := MaximalOrder(A);

// Should be the unit ideal, since A is unramified at finite places
Factorization(Discriminant(O));

// Try several "random" quaternion algebras over quadratic fields
for c := 1 to NUM do
  "Seed", GetSeed();
  D := Random([d : d in [-100..100] | not IsSquare(d)]);
  K<w> := NumberField(x^2-D);
  Z_K := MaximalOrder(K);
  K<K1,w> := FieldOfFractions(Z_K);
  a := Random([i : i in [-50..50] | i ne 0]) + Random([-50..50])*w;
  b := Random([i : i in [-50..50] | i ne 0]) + Random([-50..50])*w;
  printf "D = %o, a = %o, b = %o\n", D, a, b;
  A := QuaternionAlgebra<K | a,b>;
  O := MaximalOrder(A);
  AA := OptimizedRepresentation(A);
  ds := [<pp[1],pp[2],HilbertSymbol(A,pp[1])> : pp in Factorization(Discriminant(O))];
  print ds;
  assert forall{d: d in ds | d[3] eq -1};
end for;


// Old bug (fixed March 2010)
L<u> := NumberField(x^4 - 16/41*x^3 - 6/41*x^2 + 112/41*x - 11/41);

A<i,j,k> := QuaternionAlgebra< L | 1/2*(82*u^3 + 255*u^2 + 204*u + 13),
                                   (-10168*u^3 + 20040*u^2 - 26760*u + 7624) >;

O := Order([A| 1, 41*u, 1/2*(41*u^2 + 66*u + 1), 1/4*(41*u^3 + 25*u^2 + 19*u + 3),
               i, 41*u*i, 1/2*(41*u^2 + 66*u + 1)*i, 1/148*(41*u^3 + 1009*u^2 + 7015*u + 107)*i,
               j, 41*u*j, 1/2*(41*u^2 + 66*u + 1)*j, 1/12*(41*u^3 + 25*u^2 + 19*u + 11)*j,
               k, 41*u*k, 1/2*(41*u^2 + 66*u + 1)*k, 1/444*(41*u^3 + 1009*u^2 + 7015*u + 107)*k ]);
MaximalOrder(O);

