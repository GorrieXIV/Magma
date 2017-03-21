
SetVerbose("Quaternion", 3);

procedure test_the_map(O, phi, prec)
  Mat := Codomain(phi);
  basis_precs := [Precision(a) : a in Eltseq(phi(b)), b in ZBasis(O) | not IsWeaklyZero(a)];
  assert Min(basis_precs) ge prec - 10;
  is_zero := func<m| forall {IsWeaklyZero(x) or Valuation(x) gt prec - 10 : x in Eltseq(m)} >;
  assert is_zero( phi(M@@phi^2) - M ) where M is Mat![1,0,0,0];
  assert is_zero( phi(M@@phi^2) - M ) where M is Mat![0,0,0,1];
  assert is_zero( phi(M@@phi^2) ) where M is Mat![0,1,0,0];
  assert is_zero( phi(M@@phi^2) ) where M is Mat![0,0,1,0];
end procedure;

// A quaternion algebra "known" to be unramified at all finite places

pMAX := 1;
prec := 20; 
P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
A := QuaternionAlgebra<F | -3,b>;
OA := MaximalOrder(A);  CheckOrder(OA : Maximal);
for p in [p : p in [2..pMAX] | IsPrime(p)] do
  pps := [tup[1] : tup in Factorization(p*Z_F)];
  for pp in pps do
    "prime of norm", Norm(pp);
    time _,phi := pMatrixRing(OA, pp[1] : Precision:=prec);
    test_the_map(OA, phi, prec);
  end for;
end for;

// Random quaternion algebras over various extensions, at primes above 2 

NUM := 1;
counter := 0;
prec := 20;
while counter lt NUM do 
  "\ncounter =", counter;
  // redefine K etc inside the loop, otherwise it slows down hideously 
  c := Random({-1,1}) * Random([n : n in [2..50] | IsSquarefree(n)]);
  repeat 
    pol := x^Random({2,3,4}) + Random(1)*x - c; 
  until IsIrreducible(pol);
  K<s> := NumberField(pol);
  Z_K := MaximalOrder(K);
  S := [x+y*Z_K.2 : x,y in [-20..20] | x*y ne 0];
  a := Random(S);  b := Random(S); 
  "\nK =",K; "a =",a, "b =",b; "Seed =", GetSeed(); 
  A := QuaternionAlgebra<K | a,b>;
  printf "MaximalOrder ... "; time
  OA := MaximalOrder(A);  
  pps := [tup[1] : tup in Factorization(6*Z_K) | tup[1] notin RamifiedPlaces(A)];
  for pp in pps do 
    counter +:= 1;  
    "\nprime of norm", Norm(pp);
    time _,phi := pMatrixRing(OA, pp : Precision:=prec); 
    time test_the_map(OA, phi, prec);
  end for; 
end while; 

