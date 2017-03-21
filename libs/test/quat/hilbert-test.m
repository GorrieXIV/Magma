
QUICK := true;

// First test: Verify the correctness of all Hilbert symbols over the rationals
QQ := Rationals();

for a,b in [1..8] do
  bl := HilbertSymbol(QQ ! a, QQ ! b,2 : Al := "Evaluate") 
               eq NormResidueSymbol(a,b,2);
  print <a,b,bl>;
  if not bl then
    break a;
  end if;
end for;

// Second test: A quaternion algebra "known" to be unramified at all finite places
P<x> := PolynomialRing(Rationals());
F<b> := NumberField(x^3-3*x-1);
Z_F := MaximalOrder(F);
A := QuaternionAlgebra<F | -3,b>;
symbols := [];
ps := [p : p in [2..100] | IsPrime(p)];
if QUICK then ps := [Random(ps)]; end if;
for p in ps do 
  pps := Decomposition(Z_F,p);
  for pp in pps do
    Append(~symbols,HilbertSymbol(A,pp[1]));
  end for; 
end for;
symbols;

// Last test: Test "random" quaternion algebras over all quadratic extensions at even primes
cs := [2,-2,6,-6,-1,3,-3];
if QUICK then cs := [Random(cs)]; end if;
for c in cs do 
  K<s> := NumberField(x^2-c);
  Z_K := MaximalOrder(K);
  Z_Kmod8, f8 := quo<Z_K | 8>;
  PPK<xK> := PolynomialRing(K);
  S := [x+y*Z_K.2 : x,y in [0..7] | x*y ne 0];
  a := Random(S);
  b := Random(S);
  A := QuaternionAlgebra<K | a,b>;
  for pp in Decomposition(Z_K,2) do
    hsym := HilbertSymbol(A,pp[1]);
    if not IsIrreducible(xK^2-a) then
      print <c, a, b, hsym eq 1>;
      if hsym ne 1 then
        break c;
      end if;
    else
      lclsym := IsLocalNorm(AbelianExtension(ext<K | xK^2-a>),Z_K ! b,pp[1]);
      bl := (hsym eq 1) eq lclsym;
      print <c, a, b, bl>;
      if not bl then
        break c;
      end if;
    end if;
  end for;
end for;

// Old bug:
K := NumberField(x^8-500);
P := Ideal(Decomposition(K,2)[1][1]);
assert HilbertSymbol(K.1^2 + 40, K.1+1, P) eq 1;

