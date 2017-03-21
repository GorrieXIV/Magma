Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
EC:=EllipticCurve;
HC:=HyperellipticCurve;
R<x>:=PR(Q);
DelCRs:=func<s|&cat([x: x in Eltseq(Sprint(s)) | x ne "\n"])>; 
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne "\n") and (x ne " ")])>; 


function PrintCurve(C)
  K:=BaseField(C);
  U<x>:=PR(K);
  s:=Sprint(C);
  p1:=Position(s," defined by ");
  p2:=Position(s," over ");
  if p1*p2 eq 0 then return s; end if;
  return DelSpaces(s[[p1+12..p2]]);
end function;


function TestLSeries(C: Precision:=0, LocalData:=[* *], ExcFactors:=[* *], BadPrimes:=[* *], EulerC:=true, FEQ:=true);
  "time",Cputime();
  PrintCurve(C);
  L:=LSeries(C: Precision:=Precision,LocalData:=LocalData,ExcFactors:=ExcFactors,BadPrimes:=BadPrimes);
  if EulerC then
    loc2:=EulerFactor(C,2);
    loc3:=EulerFactor(C,3);
  end if;
  locL2:=EulerFactor(L,2);
  locL3:=EulerFactor(L,3);
  cfs:=LCfRequired(L);
  "need",cfs,"coefficients";
  if cfs gt 15000 then return L; end if;
  ok:=Abs(CheckFunctionalEquation(L)) lt 1E-9;
  "functional equation",ok select "ok" else "failed";
  error if FEQ and not ok, "Failed!";
  return L;
end function;


">>> Guessing the local factor - descending from (1-x)^2 <<<";

C:=HC(x^5+x,x^3+1);
L:=TestLSeries(C: ExcFactors:=[<2,2,(1-x)^2>], Precision:=12, EulerC:=false, FEQ:=false);
L:=TestLSeries(C: BadPrimes:=[<2,2,(1+x)^2>], Precision:=12, EulerC:=false, FEQ:=false);
L:=TestLSeries(C: LocalData:=[<2,2,(1-x)*(1+x)>], Precision:=12, EulerC:=false, FEQ:=false);
Factorization(Conductor(L));
EulerFactor(L,2);
CheckFunctionalEquation(L);


">>> Hypergeometric motives <<<";

H:=HypergeometricData([3,4],[1,1,2,2]); t:=5^12;
C:=HyperellipticCurve(H,t); // Ogg does not apply
assert EulerFactor(H,t,5) eq EulerFactor(C,5);

H:=HypergeometricData([4,4],[1,1,3]);
C:=HyperellipticCurve(H,5^4);
//EulerFactor(C,2);
//EulerFactor(C,2);
//C:=HC(x^5+x,x^3+x^2+x);
L:=TestLSeries(C: LocalData:="Ogg", Precision:=12);
"Deg 0 Euler factor";
EulerFactor(L,5: Degree:=0);

for C in [HC(x^5+100003^10),HC(x^5+3,x),HC(x^5+1),HC(x^5,2),
   HC(2*x^5+x+1,1),HC(3*x^5+3*x-1,x)] do
  C;
  D:=Discriminant(C);
  "D =",Factorization(Z!D),"N =",Factorization(Conductor(C));
  for p in PrimeDivisors(Conductor(C)) do
    printf "%o ",p;
    printf "%o\n",EulerFactor(C,p);
  end for;
  L:=TestLSeries(C: Precision:=12);
end for;


">>> Genus 4 curve <<<";

C:=HC(x^7-x^6+x^4,x^5+x+1);
Genus(C);
L:=TestLSeries(C: Precision:=12);


">>> Descending local factors <<<";

// Regular model needs to extend the base field by a quadratic extension
// but it is clear that the local factor (1+x)^2 descends to 1+x^2.

C:=HC(x-1,x^3+1);
L:=TestLSeries(C);

C:=HC(x,x^3+x^2+x);
L:=TestLSeries(C);

C:=HC(-2*x^4-x,x^3+x^2+x);
L:=TestLSeries(C);

C:=HC(x-1,x^3+1);
L:=TestLSeries(C: LocalData:=[<2,2,1+x^2>]);

C:=HC(x,x^3+x^2+x);
L:=TestLSeries(C: LocalData:=[<2,2,1+x^2>]);


">>>  ExcFactors:=\"Ogg\" <<<";

C:=HC(x^4-1,x^3+x^2+x+1);
L:=TestLSeries(C: LocalData:="Ogg");


">>>  Various curves of genus 2  <<<";


L:=TestLSeries(HC(x^6+2): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+4): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+6): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+8): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+8*x^3+8): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+2*x^3+4): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+8*x^3+32): LocalData:="Ogg");
L:=TestLSeries(HC(x^6+4*x^3+32): LocalData:="Ogg");
//L:=TestLSeries(HC(x^6+32*x^3+32): LocalData:="Ogg");  // won't work? 


">>> Hyperelliptic curves over number fields <<<";


C:=HyperellipticCurve(-x,x^3+x^2+1);
K:=QuadraticField(-23);
CK:=BaseChange(C,K);
L:=LSeries(CK: Precision:=8);
err:=CheckFunctionalEquation(L);
assert Abs(err) lt 1E-6;
chi:=ArtinRepresentations(K)[2];
CT:=QuadraticTwist(C,-23);
for p in PrimesUpTo(50) do
  assert GaloisRepresentation(C,p)*GaloisRepresentation(chi,p) 
    eq GaloisRepresentation(CT,p);
end for;


">>> Testing DONE <<<";
