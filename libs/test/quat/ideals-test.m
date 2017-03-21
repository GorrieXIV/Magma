SetSeed(3);


QUICK := true;

SetVerbose("Quaternion",1);

// quick test of ideal multiplication

F := NumberField(Polynomial([-1,1]) : DoLinearExtension);

ns := QUICK select [2,-3] else [-10 .. -1] cat [1 .. 10];
for n in ns do 
  printf "n = %o ", n;
  A := QuaternionAlgebra<F | -n, -210 >; 
  OA := MaximalOrder(A);
  I := RandomRightIdeal(OA);
  repeat a := A! [Random([1..10]) : i in [1..4]]; 
  until Norm(a) ne 0;

  aIl,aIr := rideal<LeftOrder(I)|a> * I;
  CheckIdeal(aIl);  
  CheckIdeal(aIr);  
  assert a*I eq aIr; 

  J := Conjugate(I);
  Jal,Jar := J * lideal<RightOrder(J)|a>;
  CheckIdeal(Jal);  
  CheckIdeal(Jar);  
  assert J*a eq Jal; 

  IJl,IJr := I*J;
  CheckIdeal(IJl);  
  CheckIdeal(IJr);  
  assert IJl eq ideal<LeftOrder(I) | Basis(Norm(I))>;
end for;
printf "\n";

P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
A<alpha,beta,alphabeta> := QuaternionAlgebra<F | -3, b>;
M := MatrixAlgebra(F,4) ! 1;
I := [ideal<Z_F | 1> : i in [1..4]];
O := Order(A, M, I);
O;

I := ideal<O | 2>;
I cmpeq (I + ideal<O | 2>);
I cmpeq (I + ideal<O | 3>);

Foo := InfinitePlaces(F);
A := QuaternionAlgebra(ideal<Z_F | 2*3*5>, Foo);
IsDefinite(A);
O := MaximalOrder(A);

I := rideal<O | Norm(O.2), O.2>;
J := rideal<O | Norm(O.3), O.3>;
IsIsomorphic(I, J);

// test ideal constructors
ds := [d : d in [2..30] | IsSquarefree(d)];
if QUICK then ds := [Random(ds)]; end if;
for d in ds do 
  "d =", d;
  K:=NumberField(Polynomial([-d,0,1]));
  A:=QuaternionAlgebra<K| -1,-1>;
  M:= MaximalOrder(A);
  for I in TwoSidedIdealClasses(M) do
    I1 := ideal<Order(I) | ZBasis(I)>;
    assert I eq I1;
    _ := ideal< Order(I) | PseudoMatrix(I) >;
  end for;
  for I in RightIdealClasses(M) do
    I1 := rideal<Order(I) | ZBasis(I)>;
    assert I eq I1;
    _ := rideal< Order(I) | PseudoMatrix(I) >;
  end for;
end for;

// Test for ideal classes: Definite quaternion algebras
// A = Hamiltonians over quadratic fields
 "\nd = 85";
  P<x> := PolynomialRing(Rationals());
  F<b> := NumberField(x^2-85);
  Z_F := MaximalOrder(F);
  A := QuaternionAlgebra<F | -1,-1>;
  O := MaximalOrder(A);
  time Rideals := RightIdealClasses(O);
  assert #Rideals eq 8;
  Irand := RandomRightIdeal(O); 
  isoms := [IsIsomorphic(Irand, J) : J in Rideals];
  // Irand should be isomorphic to exactly one representative!
  assert #[bool : bool in isoms | bool] eq 1;  

if not QUICK then
 "\nd = 401";
  P<x> := PolynomialRing(Rationals());
  F<b> := NumberField(x^2-401);
  Z_F := MaximalOrder(F);
  A := QuaternionAlgebra<F | -1,-1>;
  O := MaximalOrder(A);
  time Rideals := RightIdealClasses(O);
  assert #Rideals eq 140;
  Irand := RandomRightIdeal(O); 
  isoms := [IsIsomorphic(Irand, J) : J in Rideals];
  // Irand should be isomorphic to exactly one representative!
  assert #[bool : bool in isoms | bool] eq 1;  
end if;

// A = random algebra over real subfield of Q(zeta_9)
P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
Foo := InfinitePlaces(F);
ps := QUICK select [2,5] else [2,3,5,17,19];
Ps := &cat [[tup[1] : tup in Factorization(p*Z_F)] : p in ps];
for P in Ps do 
  printf "\nReal subfield of Q(zeta_9), prime discriminant \n%o\n", P;
  A := QuaternionAlgebra(P, Foo);
  O := MaximalOrder(A);
  time Rideals := RightIdealClasses(O);
  print "Total number of ideals:", #Rideals;
  Irand := RandomRightIdeal(O); 
  isoms := [IsIsomorphic(Irand, J) : J in Rideals];
  // Irand should be isomorphic to exactly one representative!
  assert #[bool : bool in isoms | bool] eq 1;  
end for;

// Test for ideal classes: Indefinite quaternion algebra
P<x> := PolynomialRing(Rationals());
Ds := [40,60,65,85];
if QUICK then Ds := [Random(Ds)]; end if;
Ds := [40];
for D in Ds do 
  F := NumberField(x^2-D);
  Z_F := MaximalOrder(F);
  Foo := RealPlaces(F);
  p := Random([p : p in [1..20] | IsPrime(p) and Gcd(p, D) eq 1]);
  oo := Random(Foo);
  print "D =", D, "p =", p, "oo =", oo;
  time pp := Decomposition(Z_F,p)[1][1];
  time A := QuaternionAlgebra(pp, [oo]);
  time O := MaximalOrder(A);
  time Rideals := RightIdealClasses(O);
  print "D = ", D, "p = ", p, "Total number of ideals:", #Rideals;
end for;

/* IsIsomorphic takes too long
Irand := RandomRightIdeal(O);
isoms := [IsIsomorphic(J, Irand) : J in Rideals];
assert #[bool : bool in isoms | bool] eq 1;
*/
