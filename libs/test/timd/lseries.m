firsttest:=1; 
lasttest:=100;

SetDefaultRealField(RealField(40));


procedure LTest(testno, LFUN: prec1:=30, prec2:=40, fail:=false, value:=false)
  Sprintf("TEST %o: %o",testno,LFUN);
  if testno lt firsttest then return; end if;
  if testno gt lasttest then return; end if;
  if fail then 
    try LFUN:=eval LFUN;
    catch e return;
    end try;
    error "Test",testno,"failed: expected to get an error"; 
  end if;
  starttime:=Cputime();

    if Type(LFUN) eq MonStgElt then
      LFUN:=eval LFUN;
    end if;
    I:=ComplexField(prec1).1;
    LSetPrecision(LFUN,prec1);
    ok:=func<r,p|Abs(r) le 0.15^p>;    // change cutoffs to 1.1 again
    e0:=CheckFunctionalEquation(LFUN);
    e1:=1 - Evaluate(LFUN,2.0) / Evaluate(LFUN,2.0: Cutoff:=1.1);e1;
    e2:=1 - Evaluate(LFUN,I) / Evaluate(LFUN,I: Cutoff:=1.1);e2;
    LSetPrecision(LFUN,prec2);
    LFUN`lastvalue:=Evaluate(LFUN,2.0);
    if (value cmpne false) and not ok(LFUN`lastvalue-value,prec2) then
      error "Value at s=2 does not agree with the expected answer";
    end if;
    e3:=1 - LFUN`lastvalue   / Evaluate(LFUN,2.0: Cutoff:=1.1);e3;
    e4:=1 - Evaluate(LFUN,I) / Evaluate(LFUN,I: Cutoff:=1.1);e4;

    passed:=ok(e0,prec1) and ok(e1,prec1) and ok(e2,prec1) and ok(e3,prec1) and ok(e4,prec2);
  error if not passed,
    "LSeries test "*Sprint(testno)*" failed";

  took:=Cputime()-starttime;
  "test",testno,"time",took;

end procedure;


AddAttribute(LSer,"lastvalue");

LTest(1,"RiemannZeta()");
LTest(2,"LSeries(EllipticCurve([0,0,1,-7,6]))");
LTest(3,"LSeries(NumberField(Polynomial([1,-2,-1,1])))");
LTest(4,"LSeries(NumberField(Polynomial([1,0,1])): ClassNumberFormula:=true)": prec1:=20); // Regulator crashes
LTest(5,"LSeries(DirichletGroup(37,CyclotomicField(36)).1)");

LTest(6,"LSeries(Newforms(\"11A\")[1])");
LTest(7,"LSeries(Newforms(\"1k12A\")[1])");
LTest(8,"LSeries(Newforms(\"37k4A\")[1])": fail:=true);
   // Have to specify complex embedding

if not IsEmpty({9,10,11} meet {firsttest..lasttest}) then
  f1,f2,f3:=Explode(Newforms("37k2"));
  LTest(9,"LSeries(f1[1])");
  LTest(10,"LSeries(f2[1])");
  LTest(11,"LSeries(f3[1])": fail:=true);
    // Pole of order 2 at s=1
end if;

if 14 in [firsttest..lasttest] then
  SetDefaultRealField(RealField(40));
  // Complex embeddings should not ignore this
  LTest(12,"LSeries(ComplexEmbeddings(Newforms(\"G1N13k2A\")[1])[1,1])");
  LTest(13,"LSeries(ComplexEmbeddings(Newforms(\"G1N17k2B\")[1])[1,1])");
  M:=ModularForms(Gamma0(47),2);
  f:=Newform(M,1);
  LTest(14,"LSeries(ComplexEmbeddings(f)[1][1])");
  SetDefaultRealField(RealField(28));
end if;

// Precision for quotients when the terms were originally defined with
// less terms
E:=EllipticCurve([0,0,0,0,1]);
K:=QuadraticField(3);
LTest(15,"LSeries(E,K)/LSeries(E)": prec1:=10, prec2:=50);

LTest(16,"LSeries(CyclotomicField(16))": prec1:=10, prec2:=15); // 8 Gamma factors [0,0,0,0,1,1,1,1]

SetDefaultRealField(RealField(28));
I:=ComplexField(28).1;
SetVerbose("LSeries",1);

// Regulator used to crash, now fixed
K:=NumberField(Polynomial([-2,0,1]));
LTest(17,"LSeries(K: Precision:=42, ClassNumberFormula:=true)": prec1:=10, prec2:=42);

// used to be complex number incompatibility, now fixed
G<Chi>:=DirichletGroup(37,CyclotomicField(36));
LTest(18,"LSeries(Chi)");

// same incompatibility, now fixed
if not IsEmpty({19,20,21} meet {firsttest..lasttest}) then
  LSqrt3:=LSeries(NumberField(Polynomial([3,0,1])));
  LZeta:=RiemannZeta();
  LQuo:=LSqrt3/LZeta;
  LChar3:=LSeries(DirichletGroup(3).1);
  LTest(19,"LQuo": prec2:=28); // like before, does not work with 40
  LTest(20,"LChar3");
  LTest(21,"LQuo*LZeta": prec2:=28);
end if;

LTest(22,"LSeries(NumberField(Polynomial([1,0,0,0,1])))");

// check multiplicativity for quadratic twists of elliptic curves
if not IsEmpty({23,24,25} meet {firsttest..lasttest}) then
  E:=EllipticCurve([0,0,0,1,2]);
  Etw:=QuadraticTwist(E,-1);
  EK:=BaseChange(E,QuadraticField(-1));
  LE:=LSeries(E);
  LEtw:=LSeries(Etw);
  LEK:=LSeries(EK);
  LTest(23,"LE");
  LTest(24,"LEtw");
  if assigned LE`lastvalue and assigned LEtw`lastvalue then
    LTest(25,"LEK": value:=LE`lastvalue * LEtw`lastvalue);
  end if;
end if;

LTest(26,"LSeries(Newforms(\"11A\")[1])");

if 27 in [firsttest..lasttest] then
  SetDefaultRealField(RealField(40));
  f:=Newforms("G1N17k2B")[1];f;
  LTest(27,"LSeries(ComplexEmbeddings(f)[1,1])");
  SetDefaultRealField(RealField(28));
end if;

// Evaluate didn't work, while adding RngSerLaurElt[NFldRe] to NFldComElt
// (fixed)
SetDefaultRealField(RealField(40));
f:=Newforms("G1N13k2A")[1];
LTest(28,"LSeries(ComplexEmbeddings(f)[1,1])");
SetDefaultRealField(RealField(28));

// works
M:=ModularForms(Gamma0(47),2);
f:=Newform(M,1);
LTest(29,"LSeries(ComplexEmbeddings(f)[1,1])": prec1:=10, prec2:=28);

// testing quotients
E:=EllipticCurve([1,1,0,1,1]);
K:=QuadraticField(6);
LTest(30,"LSeries(E,K)/LSeries(E)");

// should be very fast
E:=EllipticCurve([0,-1,1,0,0]);
f:=ModularForm(E);
LTest(31,"LSeries(f)*LSeries(f)");
LTest(32,"LSeries(f)*LSeries(f)*LSeries(f)*LSeries(f)");

// high precision
cf:=func<n:Precision:=0|RealField(Precision)!1>;
L:=LSeries(1,[0],1,cf: Poles:=[1], Residues:=[-1], Sign:=1);
LTest(33, "L": prec1:=20, prec2:=200);

//////////////////////////////////////////////////////////////////
// from advanced examples section (modulo small later changes)  //
//////////////////////////////////////////////////////////////////

// example - your own L-series of elliptic curves over Q
E:=EllipticCurve([1,2,3,4,5]);
N:=Conductor(E);
P<x>:=PolynomialRing(Integers());
cf:=func<p,d|1-TraceOfFrobenius(E,GF(p,1))*x
        +(N mod p ne 0 select p else 0)*x^2>;
L:=LSeries(2,[0,1],N,cf : Parent:=E, Sign:=RootNumber(E));
LTest(34, "L": prec1:=10, prec2:=20);

// example - your own L-series for the Dedekind zeta function
// (and compare with the standard one)
function DedekindZeta(K)
  M:=MaximalOrder(K);
  r1,r2:=Signature(K);
  gamma:=[0: k in [1..r1+r2]] cat [1: k in [1..r2]];
  disc:=Abs(Discriminant(M));
  P<x>:=PolynomialRing(Integers());
  cf:=func<p,d|&*[1-x^Degree(k[1]): k in Decomposition(M,p)]>;
  h:=#ClassGroup(M);
  reg:=Regulator(K);
  mu:=#TorsionSubgroup(UnitGroup(M));
  return LSeries(1, gamma, disc, cf: Parent:=K, Sign:=1, Poles:=[1],
    Residues:=[-2^(r1+r2)*Pi(RealField())^(r2/2)*reg*h/mu]);
end function;
Z:=DedekindZeta(CyclotomicField(5));
L1:=Z/RiemannZeta();
LTest(35,"L1": prec1:=10, prec2:=28);
L2:=LSeries(CyclotomicField(5))/RiemannZeta();
if assigned L1`lastvalue then
  LTest(36,"L2": prec1:=10, prec2:=28, value:=L1`lastvalue);
end if;

// example - genus 2 curve

P<x>:=PolynomialRing(Integers());
C:=HyperellipticCurve([x^5+x^4,x^3+x+1]); C;
J:=Jacobian(C);
loc:=func<p,d|p eq 13 select 1+5*x+13*x^2 else EulerFactor(J,GF(p,1))>;
LTest(37,"LSeries(2,[0,0,1,1],13^2,loc)": prec1:=10, prec2:=28);

// example - experimental maths a la Stark

if 38 in [firsttest..lasttest] then
  oldv:=GetVerbose("LSeries");
  SetVerbose("LSeries",0);
  L:=LSeries(2,[0,1],11,0: Sign:=1);
  for a_2:=-2 to 2 do
    LSetCoefficients(L,[1,a_2]);
    print a_2,CheckFunctionalEquation(L);
  end for;
  N:=LCfRequired(L);N;
  V:=[0: k in [1..N]];
  P<x>:=PolynomialRing(Integers());
  function Try(V,p,a_p)
    V[p]:=a_p;
    LSetCoefficients(L,func<p,d|1-V[p]*x+(p eq 11 select 0 else p)*x^2>);
    return Abs(CheckFunctionalEquation(L));
  end function;
  for p:=2 to 20 do
    if IsPrime(p) then
      hasse:=Floor(2*Sqrt(p));
      _,V[p]:=Min([Try(V,p,a_p): a_p in [-hasse..hasse]]);
      V[p]-:=hasse+1;
    end if;
  end for;
  LSetCoefficients(L,func<p,d|
    p gt 20 select 1 else 1-V[p]*x+(p eq 11 select 0 else p)*x^2>);
  LTest(38,"L": prec1:=10, prec2:=20);
  SetVerbose("LSeries",oldv);
  "Compare:";
  LGetCoefficients(L,20);
  qExpansion(Newforms("11A")[1],21);
end if;

// example - tensor product with parameters

E:=EllipticCurve([0,0,0,0,1]);
P<x>:=PolynomialRing(Integers());
K:=NumberField(x^3-2);
LE:=LSeries(E);
LK:=LSeries(K);
L:=TensorProduct(LE,LK,[])/LE;
//LTest(39, "L": prec1:=10, prec2:=20);    
  // used to be: may not give []  // might work soon
EK:=BaseChange(E,K);
p:=Decomposition(MaximalOrder(K),2)[1,1];
LocalInformation(E,2);
loc,model:=LocalInformation(EK,p);loc,model;
TraceOfFrobenius(Reduction(model,p));
L:=TensorProduct(LE,LK,[<2,4,1+2*x^2>])/LE;
LTest(40,"L": prec1:=10, prec2:=20);

// example - non-abelian twist of E

E:=EllipticCurve([0,0,0,0,1]);
P<x>:=PolynomialRing(Integers());
K:=NumberField(x^3-2);
LTest(41,"LSeries(E,K)/LSeries(E)": prec1:=10, prec2:=20);

// Artin representations

R<x>:=PolynomialRing(Rationals());

K:=NumberField(x^3-2);
LTest(42,"LSeries(K: Method:=\"Artin\")");
LTest(43,"LSeries(K: Method:=\"Default\")");
K:=NumberField(x^4-3);
LTest(44,"LSeries(K: Method:=\"Artin\")");
LTest(45,"LSeries(K: Method:=\"Default\")");

// twists of elliptic curves by artin reps

SetVerbose("LSeries",0);

F:=NumberField(x^4-3);
E:=EllipticCurve([0,-1,1,0,0]);
LTest(46,"LSeries(E,F: Method:=\"Artin\")": prec1:=6, prec2:=12);

LTest(47,"LSeries(CyclotomicField(7))");
LTest(48,"LSeries(E,CyclotomicField(7))");

// more Artin

if not IsEmpty({49..53} meet {firsttest..lasttest}) then
  K:=NumberField(x^3-2);
  A:=ArtinRepresentations(K);
  LTest(49,"LSeries(A[1])*LSeries(A[2])/LSeries(A[1])");
  LTest(50,"LSeries(A[2])");
  LTest(51,"LSeries(A[2]-A[3])": fail:=true);  // may not be virtual
  LTest(52,"LSeries(A[3]+A[2]-A[2])");
  LTest(53,"LSeries(A[2]+A[3])");
end if;

// tricky hyperelliptic curve (at 2 and at 3)

C:=HyperellipticCurve((x^2+1)*((x+9)^2+1)*((x-9)^2+1));  
L:=LSeries(C: LocalData:="Ogg");
weight,gamma,cond:=Explode(LSeriesData(L));
v:=LGetCoefficients(L,20000);
LTest(54,"LSeries(weight,gamma,cond,v)": prec1:=4, prec2:=5);

"All done";
