Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
EC:=EllipticCurve;
R<x>:=PR(Q);
PRC<X>:=PR(ComplexField());
Ar:=func<f|ArtinRepresentations(NumberField(f))>;


timelimit:=true;


procedure Test(E,A: Precision:=15) 
  if Type(E) eq MonStgElt then 
    E:=EllipticCurve(E);
  end if;
  "E=",CremonaReference(E);
  "A=",A;
  L:=LSeries(E,A: Precision:=Precision);
  need:=LCfRequired(L);
  "Need",need,"coefficients";
  if need gt 120000 then "Too many coefficients"; return; end if;
  err:=Abs(CheckFunctionalEquation(L));
  error if err gt 1E-9, "Functional equation failed";
  "Functional equation ok, err =",RealField(2)!err;
  for p in PrimeDivisors(Conductor(L)) do
    Sprintf("loc(%o) = %o",p,EulerFactor(L,p));
  end for;
end procedure;


SetVerbose("GalRep",2);
SetVerbose("ArtRep",1);

">>> Twists by bad 1- and 2- dimensional representations at p=2 <<<";

A1:=Ar(x^3-2)[3];
A2:=Ar(x^4+1)[4];
A3:=Ar(x^8+1)[4];
A4:=Ar(x^4-2)[5];

for cr in ["11a1","14a1","20a1","256a1"], A in [A1,A2,A3,A4] do
  Test(cr,A);
end for;

">>> Twists by bad 1- and 2- dimensional representations at p=3 <<<";

A1:=Ar(x^3-3)[3];
A2:=Ar(x^2+x+1)[2];
A3:=Ar(x^6-3)[6];
A4:=Minimize(Ar(x^9-3)[8]);

for cr in ["11a1","15a1","27a1","162a1"], A in [A1,A2,A3,A4] do
  if timelimit and (cr eq "27a1") then continue; end if;
  "Current time usage",Cputime();
  Test(cr,A);
end for;

">>> Frobenius and duality conventions <<<";

E:=EC("147b1");                               // C3 inertia
K:=Subfields(CyclotomicField(7),3)[1][1];
A:=ArtinRepresentations(K)[3];                // non-trivial non-self dual Euler
Test(E,A);                                    // factor at 7 for E*A
"Current time usage",Cputime();

">>> Testing DONE <<<";
