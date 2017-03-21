load galpols;

P:=PrimesUpTo(10^5);

for n:=2 to 6 do
for j:=1 to NumberOfTransitiveGroups(n) do
  G:=TransitiveGroup(n,j);
  f:=PolynomialWithGaloisGroup(n,j);
  Sprintf("%-2o %-4o %-10o %-40o",n,j,#G,GroupName(G));
  K:=NumberField(f);
  A:=ArtinRepresentations(K);

  // Check Minimize
  for a in A do
    if not IsFaithful(Character(a)) then
      assert a eq Minimize(a);
    end if;
  end for;

  // Check Frobenius elements
  for p in P do
    frob:=FrobeniusElement(K,p);
  end for;

  // Check arithmetic and L-series
  // (which includes local data at bad primes, char polys of Frobenius
  //  elements, conductors etc.)

  chi:=&+A;
  L:=LSeries(chi: Precision:=30);
  if LCfRequired(L) gt 100000 then continue; end if;
  err:=CheckFunctionalEquation(L);
  error if Abs(err) gt 10^-25,
    "TEST FAILED checkfunerr="*Sprint(RealField(5)!Abs(err)); 

end for;
end for;

">>> TESTING DONE <<<";
