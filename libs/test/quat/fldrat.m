
// Test quaternion algebras over Q


// Basic stuff

a := Random([1..100]);
b := Random([1..100]);
a, b;

A := QuaternionAlgebra< Rationals() | -a, -b >;

O := Order(Integers(), Basis(A));
FactoredDiscriminant(O);

I := rideal< O | [A| 2, A.3] >;
Norm(I);


// Complicated routines (with attributes and stuff)

O := MaximalOrder(A);
FactoredDiscriminant(O);

rids := RightIdealClasses(O); 
#rids, "ideal classes";

ords := [];
for I in rids do 
  O := LeftOrder(I);
  if not exists{OO : OO in ords | IsConjugate(O, OO)} then
    Append(~ords, O);
  end if;
end for;
#ords, "order classes";

// recompute independently using the AlgAssVOrd code
_ords := ConjugacyClasses(O); 
assert #ords eq #_ords;

for O in ords do 
  assert 1 eq #[OO : OO in _ords | IsConjugate(O,OO)];
end for;

