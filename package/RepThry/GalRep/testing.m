freeze;

import "../../RepThry/GalRep/galrep.m":    
                      GaloisRepresentationsPoly,GalRepCopy,IsGalQuotient,
                      E3TorsPoly,FixedFieldPoly,Commonify,embed2,PrintPolynomial,
                      IsNumZero,PrintEulerFactor,PrintComplex,ChangeCharacter,
                      poly,poly2,PrintField,RLog,IsZPoly,ThreeTorsExtType,
                      E4TorsPoly,EEulerExt,EulerFactorSubfield;
import "../../Ring/RngLoc/splitfield.m":
                      GaloisToPermutation,pAdicEltseq,
                      ComputeSplittingField,pAdicChangePrecision;
import "../../RepThry/GalRep/epsilon.m":    
                      RachelLocRecip;




Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
EC:=EllipticCurve;
PRC<X>:=PR(ComplexField());


function LSeriesGal(O: Precision:=18)
  weight,gamma,N,_,_,poles,residues:=Explode(LSeriesData(LSeries(O)));
  return LSeries(weight,gamma,N,func<p,d|PRC!EulerFactor(GaloisRepresentation(O,p))>: Precision:=Precision, Poles:=poles, Residues:=residues);
end function;


procedure TestG(O: Precision:=18)
  L1:=LSeries(O: Precision:=Precision);
  L2:=LSeriesGal(O: Precision:=Precision);
  err1:=Abs(CheckFunctionalEquation(L1));
  err2:=Abs(CheckFunctionalEquation(L2));
  Sprintf("%-6o %-8o %-8o %-22o %-22o",LCfRequired(L1),
    RealField(2)!err1,RealField(2)!err2,Evaluate(L1,2),Evaluate(L2,2));
  error if (err1 gt 0.001) or (err2 gt 0.001), "Functional equation failed";
end procedure;


function DelSymbols(s,delsymb) 
  if Type(s) ne MonStgElt then s:=Sprint(s); end if;
  if Type(delsymb) eq MonStgElt then delsymb:=Eltseq(delsymb); end if;  
  s:=[c: c in Eltseq(s) | not (c in delsymb)];
  return IsEmpty(s) select "" else &cat s;
end function;


function DelSpaces(s)    // delete spaces from a string s
  return DelSymbols(s," \n");
end function;


function MinimizedGenerators(G)
  if #G eq 1 then return [G|]; end if;
  _<[gens]>:=G;
  n:=[];
  G0:=sub<G|>;
  for i:=1 to #gens do
    if G0 eq G then break; end if;
    Append(~n,gens[i]);
    G0:=sub<G|G0,gens[i]>;
  end for;
  i:=1;
  repeat
    nnew:=Exclude(n,n[i]);
    if sub<G|nnew> eq G then n:=nnew; else i+:=1; end if;
  until i gt #n;
  return n;
end function;


function CyclotomicExtension(p,d: prec:=30)
  x:=PrimitiveRoot(p)^d mod p;
  z:=Exp(2*Pi(RealField(prec))*ComplexField(prec).1/p);
  r:=&+[z^Modexp(x,k,p): k in [1..(p-1) div d]];
  K:=NumberField(PowerRelation(r,d));
  fct:=Factorisation(Discriminant(IntegerRing(K)));
  if (#fct ne 1) or (fct[1,1] ne p) then
    error "CyclotomicExtension: failed";
  end if;
  return K;
end function;


function Last(v)
  try return v[#v]; catch e; end try;
  try w:=Eltseq(v); return w[#w]; catch e; end try;
  error "Last: unrecognized type";
end function;


procedure TestArtin(a,printdata)
  N:=Conductor(a);
  //if not IsPrime(N) then return; end if;

  prm:=PrimeDivisors(N);
  if not IsEmpty(prm) and (Max(prm) gt 10000) then return; end if;
  time0:=Cputime();
  eps:=[ComplexField()!RootNumber(HodgeStructure(a))] cat 
    [EpsilonFactor(GaloisRepresentation(a,p)): p in prm];
  elapsed:=Cputime()-time0;
  eps:=IsEmpty(eps) select 1 else &*eps;
  elapsed,eps ne 0 select "+" else "0",Degree(Character(a));
  if eps eq 0 then return; end if;
  if not IsNumZero(Abs(eps)^2/Conductor(a)-1) then
    error Sprintf("%o Unequal a=%o eps=%o N=%o",printdata,DelSpaces(Character(a)),
      PrintComplex(eps),Conductor(a));
  end if;
  L:=LSeries(a: Precision:=30);
  if LCfRequired(L) gt 10000 then return; end if;
  ok:=CheckFunctionalEquation(L);
  w1:=eps/Abs(eps);
  w2:=Sign(L); //!!
  if not IsNumZero(w1/w2-1) then
    error Sprintf("%o Unequal a=%o\neps=%o\nN=%o\nw1=%o\nw2=%o",
      printdata,a,eps,Conductor(a),w1,w2);
  end if;
end procedure;


procedure polyeq(f1,f2)
  R:=PolynomialRing(ComplexField());
  f:=R!f1 - R!f2;
  cfs:=Coefficients(f);
  if IsEmpty(cfs) then return; end if;
  err:=Max([Abs(c): c in cfs]);
  error if err gt 0.01, "Unequal polynomials";
end procedure;


procedure TestRepLoc()   // Needs attaching

  for data in [
    <11,2,1>,         // unramified principal series
    <11,11,1>,        // unramified Steinberg
    <45,3,1>,         // ramified Steinberg
    <147,7,2>,        // ramified principal series
    <20,2,1>,         // supercuspidal
    <49,7,1>          // supercuspidal
  ] do
  
    N,p,i:=Explode(data);
    Sprintf("N=%o p=%o i=%o",N,p,i);
  
    S:=CuspidalSubspace(ModularSymbols(N, 2, 1));
    N:=NewformDecomposition(S);
    l:=LocalComponent(N[i], p);   
    E:=EllipticCurve(N[i]);
    
    W:=WeilRepresentation(l); W;
    G:=GaloisRepresentation(E,p); G;
    assert ConductorExponent(W) eq ConductorExponent(G);
    "";
  end for;
  
end procedure;


procedure TestAll()

  ">>> SP and determinant <<<";

  K:=pAdicField(5,20);
  c1:=CyclotomicCharacter(K);
  A:=SP(K,2);
  c2:=Determinant(A);
  B:=Semisimplification(A);
  c3:=Determinant(B);
  assert c1 eq c2;
  assert c1 eq c3;
  
  ">>> Random tests: elliptic curves over extensions of K <<<";

  K:=pAdicField(2,200);
  R<x>:=PR(K);
  E1:=EllipticCurve("11a1");
  E1K:=BaseChange(E1,K);
  E2K:=QuadraticTwist(E1K,-2);
  A1:=GaloisRepresentation(E1K);
  A2:=GaloisRepresentation(E2K);
  pi:=PermutationCharacter(ext<K|x^2+2>,K);  
  chi:=Decomposition(pi)[2];
  assert A1*chi eq A2;
  assert A1 eq A2*chi;  
  
  K:=pAdicField(5,20);                     
  E:=EllipticCurve([K|0,5]);
  AE:=GaloisRepresentation(E);
  G:=Group(AE);
  for ch in CharacterTable(G) do
    A:=AE!!ch;
    A;
    assert Minimize(A) eq A;
  end for;

  ">>> FixedFieldPoly <<<";
  
  for H in [D`subgroup: D in Subgroups(G)] do
    f:=FixedFieldPoly(A,H);
    Q:=Group(GaloisRepresentations(f)[1]);
    GroupName(H),GroupName(Q),GroupName(quo<G|Core(G,H)>);
    assert IsIsomorphic(Q,quo<G|Core(G,H)>);
  end for;
  Q:=Rationals();

  ">>> Random tests II <<<";
      
  K:=pAdicField(5,20);
  R<X>:=PR(K);
  L:=GaloisRepresentations(X^3-5);
  s:=L[2]+L[3];
  assert s-L[2] eq L[3];
  assert s-L[3] eq L[2];
  
  R<x>:=PR(Q);
  K:=NumberField(x^2+3);
  P:=Ideal(Decomposition(K,2)[1,1]);
  KP,m:=Completion(K,P: Precision:=100);
  K;
  KP;

  E:=BaseChange(EC("256a1"),K);      
  EK:=EllipticCurve([m(a): a in aInvariants(E)]);
  "Computing GR(E,P)";
  A:=GaloisRepresentation(E,P);
  assert Valuation(Conductor(EK)) eq Valuation(Conductor(A));
  assert Valuation(Conductor(A)) eq 8;
  
  E:=BaseChange(EC("20a1"),K);
  EK:=EllipticCurve([m(a): a in aInvariants(E)]);
  "Computing GR(E,P)";
  A:=GaloisRepresentation(E,P);
  assert Valuation(Conductor(EK)) eq Valuation(Conductor(A));
  assert Valuation(Conductor(A)) eq 2;


  ">>> Commonify and arithmetic <<<";
  
  A1:=Last(GaloisRepresentations(X^2-2));
  A2:=Last(GaloisRepresentations(X^2+3));
  //B1,B2:=Commonify(A1,A2);
  s:=A1+A2;
  assert s-A1 eq A2;
  assert s-A2 eq A1;  
  
  ">>> Elliptic curves, various reduction types <<<";
   
  K:=pAdicField(5,50);
  E1:=EllipticCurve([K|1,3]);
  E2:=EllipticCurve([K|5,5]);
  E3:=EllipticCurve([K|7,3]);
  E4:=EllipticCurveWithjInvariant(K!1/5);
  E5:=EllipticCurve([K|0,5]);
  E6:=EllipticCurve([K|5,5]);
  
  K:=pAdicField(7,50);
  E1:=EllipticCurve([K|1,3]);
  E2:=EllipticCurve([K|7,7]);
  E3:=EllipticCurve([K|7,3]);
  E4:=EllipticCurveWithjInvariant(K!1/5);
  E5:=EllipticCurve([K|0,7]);
  E6:=EllipticCurve([K|7,7]);
  
  R<x>:=PR(K);
  L:=GaloisRepresentations(x^3-7);
  
  A1:=GaloisRepresentation(E1);
  A2:=GaloisRepresentation(E2);
  A3:=GaloisRepresentation(E3); A3;
  A4:=GaloisRepresentation(E4);
  A5:=GaloisRepresentation(E5);
  A6:=GaloisRepresentation(E6);
  
  A4b:=GaloisRepresentation(QuadraticTwist(E4,2));
  A4c:=GaloisRepresentation(QuadraticTwist(E4,5));
  A1b:=GaloisRepresentation(QuadraticTwist(E1,5));
  A1;
  A2;
  A3;
  A1*A3;
  CyclotomicCharacter(K)*A3;
  
  R<x>:=PR(Q);
  A:=ArtinRepresentations(NumberField(x^3-2));
  GaloisRepresentation(A[3],2);
  GaloisRepresentation(A[3],3);
  GaloisRepresentation(A[3],5);
  
  ">>> Dirichlet characters <<<";
  
  G<chi1,chi2>:=DirichletGroup(16);
  
  G1:=GaloisRepresentation(chi1,2);
  G2:=GaloisRepresentation(chi2,2);
  assert GaloisRepresentation(chi1*chi2,2) eq G1*G2;
  assert GaloisRepresentation(chi1^2*chi2,2) eq G1^2*G2;
  assert GaloisRepresentation(chi1*chi2^2,2) eq G1*G2^2;
  assert IsUnramified(GaloisRepresentation(chi1*chi2,3));
  assert IsUnramified(GaloisRepresentation(chi1*chi2,5));
  
  f:=PolynomialWithGaloisGroup(8,32);
  K:=NumberField(f);
  A:=ArtinRepresentations(K);
  a:=Last(A);
  
  GaloisRepresentation(a,3);
  GaloisRepresentation(a,53);
  GaloisRepresentation(a,61);
  
  ">>> Langlands <<<";
  
  for level in [11,20,30,36,100] do

    S := CuspidalSubspace(ModularSymbols(level, 2, 1));
    N := NewformDecomposition(S);
    for p in PrimesUpTo(20) do
      level,p;
      l:=LocalComponent(N[1], p); 
      W1:=WeilRepresentation(l);
      W2:=GaloisRepresentation(EllipticCurve(Sprint(level)*"a1"),p: Precision:=20);
      assert ConductorExponent(W1) eq ConductorExponent(W2);
      assert ConductorExponent(W1) eq Valuation(level,p);
    end for;

  end for;
    
  ">>> Modular forms <<<";
  
  f:=Newforms("11k2")[1];  
  f:=Newforms(CuspForms(11,2))[1,1];
  f:=Newforms(CuspForms(3,6))[1,1];
  G2:=GaloisRepresentation(f,2); G2;
  G3:=GaloisRepresentation(f,3); G3;
  G5:=GaloisRepresentation(f,5); G5;
  
  polyeq(EulerFactor(G2),EulerFactor(LSeries(f),2));
  polyeq(EulerFactor(G3),EulerFactor(LSeries(f),3));
  polyeq(EulerFactor(G5),EulerFactor(LSeries(f),5));
  G3*G3;

  ">>> Random tests III <<<";
    
  A:=ArtinRepresentations(NumberField(x^6-2));
  a:=Last(A);
  L:=LSeriesGal(a);
  LCfRequired(L);
  assert Abs(CheckFunctionalEquation(L)) lt 0.01;

  ">>> Random tests IV <<<";
  
  TestG(EllipticCurve("11a3"));
  TestG(EllipticCurve("20a1"));
  TestG(EllipticCurve("36a1"));
  TestG(EllipticCurve("256a1"));
  
  A:=ArtinRepresentations(NumberField(x^6-2));
  for a in A do 
    TestG(a); 
  end for;
  
  G<chi1,chi2>:=DirichletGroup(16,CyclotomicField(8));
  for a in Elements(G) do 
    TestG(a); 
  end for;
  
  ">>> Random tests V <<<";
  
  a:=ArtinRepresentations(NumberField(x^3-2))[3];
  for cr in ["20a1","36a1"] do
    E:=EllipticCurve(cr);
    L:=LSeries(E,a);
  
    for p in PrimesUpTo(20) do  
      G1:=GaloisRepresentation(E,p: Precision:=20);
      G2:=GaloisRepresentation(a,p: Precision:=20);
      eu1:=EulerFactor(L,p); 
      eu2:=EulerFactor(G1*G2); 
      polyeq(eu1,eu2);
    end for;  
  end for;
    
  E:=EllipticCurve("49a1");
  a:=ArtinRepresentations(NumberField(x^4-7))[5];
  L:=LSeries(E,a);
  eu1:=EulerFactor(L,7);
  
  G1:=GaloisRepresentation(E,7: Precision:=20);
  G2:=GaloisRepresentation(a,7: Precision:=20);
  G:=G1*G2;
  eu2:=EulerFactor(G);
  polyeq(eu1,eu2);
  
  ">>> Tame twists <<<";
  
  // Tame twists in the case of bad reduction
  
  D:=CremonaDatabase();
  time 
  for N in [11..50] cat [98,147,150] do
  for p in PrimeDivisors(N) do
  for u in [1..Min(p-1,10)] do
  if Valuation(N,p) ne 2 then continue; end if;
  for i:=1 to NumberOfIsogenyClasses(D,N) do
    E:=EllipticCurve(D,N,i,1);
    GE:=GaloisRepresentation(E,p);
    e:=#InertiaGroup(GE);
    a:=Last(ArtinRepresentations(NumberField(x^e-u*p)));
    if IsEven(e) and (N mod 8 eq 0) then continue; end if;
    //try L:=LSeries(E,a); ok:=true; catch e e`Object; ok:=false; end try;
    L:=LSeries(E,a); 
    //if not ok then continue; end if;
    p,u,CremonaReference(E),e;
    GA:=GaloisRepresentation(a,p);
    cfs:=[Abs(c): c in Coefficients(EulerFactor(L,p)-
      EulerFactor(GE*GA))];
    err:=IsEmpty(cfs) select 0 else Max(cfs);
    error if err gt 1E-20, "Failed! "*Sprint(err);
  end for;
  end for;
  end for;
  end for;


  ">>> Euler factors <<<";

  E:=EllipticCurve("20a1");
  A:=GaloisRepresentation(E,2);
  K0:=BaseField(A);
  
  F0:=ext<K0|PR(K0).1^3-2>;
  eu1:=EulerFactor(BaseChange(A,F0));
  eu2:=EulerFactor(GaloisRepresentation(BaseChange(E,F0)));
  polyeq(eu1,eu2);
  
  F0:=ext<K0|PR(K0).1^9+2>;
  eu1:=EulerFactor(BaseChange(A,F0));
  eu2:=EulerFactor(GaloisRepresentation(BaseChange(E,F0)));
  polyeq(eu1,eu2);
  
  F0:=ext<K0|2>;
  eu1:=EulerFactor(BaseChange(A,F0));
  eu2:=EulerFactor(GaloisRepresentation(BaseChange(E,F0)));
  polyeq(eu1,eu2);


  ">>> Semisimplification <<<";

  E:=EllipticCurve("20a1");
  
  A:=GaloisRepresentation(E,2);
  assert IsSemisimple(A);
  assert Semisimplification(A) eq A;
  
  A:=GaloisRepresentation(E,5);
  assert not IsSemisimple(A);
  assert #Decomposition(Semisimplification(A)) eq 2;
  assert Factorization(A) eq [* <5*x+1,2,1> *];

  ">>> Epsilon factors <<<";

  E:=EllipticCurve("11a1");
  G:=GaloisRepresentation(E,37);
  EpsilonFactor(G);
  
  E:=EllipticCurve("37a1");
  G:=GaloisRepresentation(E,37);
  K:=BaseField(G);
  
  K1:=ext<K|2>;
  K2:=ext<K|PR(K).1^2-37>;
  K3:=ext<K|PR(K).1^2-2*37>;
  K4:=ext<K|PR(K).1^4-37>;
  K5:=ext<K|PR(K).1^4-2*37>;
  
  LocalInformation(E,37);
  EpsilonFactor(G),RootNumber(E,37);
  
  for F in [K1,K2,K3,K4,K5] do
    assert RootNumber(BaseChange(E,F)) eq RootNumber(BaseChange(G,F));
  end for;

  E:=EllipticCurve("98a1");
  G:=GaloisRepresentation(E,7);
  K:=BaseField(G);
  
  GI:=InertiaInvariants(G);
  assert IsZero(GI);
  assert EulerFactor(GI) eq 1;
  assert EpsilonFactor(GI) eq 1;
  assert EpsilonFactor(G) eq -49;

  ">>> Epsilon factors II <<<";

  E:=EllipticCurve("98a1");
  p:=7;
  G:=GaloisRepresentation(E,p);
  assert RootNumber(G) eq RootNumber(E,p);
  
  E:=QuadraticTwist(EllipticCurve("98a1"),3);
  p:=7;
  G:=GaloisRepresentation(E,p);
  assert RootNumber(G) eq RootNumber(E,p);
  
  E:=QuadraticTwist(EllipticCurve("98a1"),7);
  p:=7;
  G:=GaloisRepresentation(E,p);
  assert RootNumber(G) eq RootNumber(E,p);
  
  E:=QuadraticTwist(EllipticCurve("98a1"),-7);
  p:=7;
  G:=GaloisRepresentation(E,p);
  assert RootNumber(G) eq RootNumber(E,p);
  
  ">>> Epsilon factors III <<<";
  
  E:=EC("147b1");
  p:=7;
  wE:=RootNumber(E,p);
  G:=GaloisRepresentation(E,p);
  wG:=RootNumber(G);
  "w(E) =",wE;
  "w(G) =",wG;
  assert wE eq wG;

  E:=EC("150a1");
  p:=5;
  wE:=RootNumber(E,p);
  G:=GaloisRepresentation(E,p);
  wG:=RootNumber(G);
  "w(E) =",wE;
  "w(G) =",wG;
  assert wE eq wG;
  
  ">>> Random tests VI <<<";

  E:=EC("150a1");
  p:=5;
  G:=GaloisRepresentation(E,p);
  K:=BaseField(G);
  EK:=BaseChange(E,K);
  R<x>:=PR(K);
  for f in [x^4-5,x^4-10,x^2-5,x^2-10,x^3-5,x^3-10] do
    f;
    F1:=ext<K|f>;
    EF1:=BaseChange(E,F1);
    loc,min:=LocalInformation(EF1);
    O1:=Integers(F1);
    k,m:=ResidueClassField(O1);
    B:=BaseChange(G,F1);
    assert B eq GaloisRepresentation(EF1);
    e:=EulerFactor(B);
    if Degree(e) ne 2 then continue; end if;
    Ered:=EllipticCurve([m(a): a in aInvariants(min)]);
    polyeq(EulerFactor(Ered),e);
  end for;

  E:=EC("147a1");
  p:=7;
  G:=GaloisRepresentation(E,p);
  K:=BaseField(G);
  EK:=BaseChange(E,K);
  R<x>:=PR(K);
  for f in [x^4-7,x^4-21,x^2-7,x^2-21,x^3-7,x^3-21] do
    f;
    F1:=ext<K|f>;
    EF1:=BaseChange(E,F1);
    loc,min:=LocalInformation(EF1);
    O1:=Integers(F1);
    k,m:=ResidueClassField(O1);
    B:=BaseChange(G,F1);
    assert B eq GaloisRepresentation(EF1);
    e:=EulerFactor(B);
    if Degree(e) ne 2 then continue; end if;
    Ered:=EllipticCurve([m(a): a in aInvariants(min)]);
    polyeq(EulerFactor(Ered),e);
  end for;

  n:=6;
  i:=10;
  p:=3;

  G:=TransitiveGroup(n,i);
  n,i,GroupName(G);
  f:=PolynomialWithGaloisGroup(n,i);
  K:=NumberField(f);
  a:=ArtinRepresentations(K)[3];
  G:=GaloisRepresentation(a,p);
  e:=EpsilonFactor(G);
  assert IsNumZero(e-Sqrt(3));
  
  ">>> Artin signs <<<";
    
  R<x>:=PR(Q);  
  f:=x^2+3;
  K:=NumberField(f);
  art:=ArtinRepresentations(K: Ramification:=true);
  a:=art[2];
  TestArtin(a,"");
  L:=LSeries(a: Precision:=18);
  ok:=CheckFunctionalEquation(L);
  assert IsNumZero(ok);
  
  for p in PrimesUpTo(40) do
    if p mod 4 ne 1 then continue; end if;
    f:=DefiningPolynomial(CyclotomicExtension(p,4));
    K:=NumberField(f);
    DelSpaces(f);
    art:=ArtinRepresentations(K: Ramification:=true);
    for j:=1 to #art do
      TestArtin(art[j],DelSpaces(<n,i,j>));
    end for;
  end for;
  
  //SetDefaultRealField(RealField(100));
  
  for n:=2 to 5 do   // 7
  for i:=1 to NumberOfTransitiveGroups(n) do
    G:=TransitiveGroup(n,i);
    n,i,GroupName(G);
    f:=PolynomialWithGaloisGroup(n,i);
    K:=NumberField(f);
    art:=ArtinRepresentations(K: Ramification:=true);
    for j:=1 to #art do
      TestArtin(art[j],DelSpaces(<n,i,j>));
    end for;
  end for;
  end for;


  ">>> Minimize <<<";

  K0:=pAdicField(2,20);
  K:=ext<K0|PR(K0).1^4-2>;
  PermutationCharacter(K,K0);
  
  K0:=pAdicField(2,20);
  K:=ext<K0|PR(K0).1^8-2>;
  PermutationCharacter(K,K0);
  
  for A in GaloisRepresentations(K,K0) do
    A;
    assert Minimize(A) eq A;
  end for;
  
  K0:=pAdicField(2,20);
  K1:=ext<K0|2>;
  K2:=ext<K1|PR(K1).1^2-2>;
  K:=ext<K2|2>;
  PermutationCharacter(K,K0);
  
  for A in GaloisRepresentations(K,K0) do
    A;
    assert Minimize(A) eq A;
  end for;

  ">>> Testing induction and equality <<<";
  
  for cr in ["11a1","14a1","15a1","20a1"] do
  for d in [1,-1,2,-2,3,-3,5,-5,6,-6] do
  for p in [2,3,5] do
    cr,d,p;
    K0:=pAdicField(p,40);
    R<x>:=PR(K0);
    _,_,e:=Factorisation(x^2-d: Extensions:=true);
    K:=e[1]`Extension;
    if Degree(K,K0) ne 2 then continue; end if;
    
    E:=EllipticCurve(cr);
    EK0:=BaseChange(E,K0);
    ET0:=QuadraticTwist(EK0,d);
    EK:=BaseChange(EK0,K);
  
    A:=GaloisRepresentation(EK);
    I:=Induction(A,K0);
    N:=GaloisRepresentation(EK0)+GaloisRepresentation(ET0);
  
    error if I ne N, 
      Sprintf("Ind failed: cr=%o d=%o p=%o",cr,d,p);
    
  end for;
  end for;
  end for;


  ">>> Zero, One, basic arithmetic <<<";
  
  K:=pAdicField(2,20);                      // Zero representations
  F:=ext<K|2>;                              // IsOne, IsZero
  L:=GaloisRepresentations(F,K);            // basic arithmetic
  U:=L[1]-L[1];
  V:=(U*L[1]+U*U) + Induction(BaseChange(U,Field(U)),BaseField(U));
  assert U eq V;
  assert U+V eq U-V;
  assert IsOne(L[1]);
  assert not IsOne(L[2]);
  assert U*L[1] eq U;
  assert U*L[2] eq U;
  assert not IsOne(U);
  assert IsZero(U);
  (&+L)^3 - (&+L)^1;
  (&+L)^3 - (&+L)^2;
  // (&+L)^3 - (&+L)^4;    
  Decomposition((&+L)^3);


  ">>> Ramified principal series test <<<";
  
  N := 147;     
  p := 7;
  i := 2;
  
  S:=CuspidalSubspace(ModularSymbols(N, 2, 1));
  N:=NewformDecomposition(S);
  l:=LocalComponent(N[i], p);   
  E:=EllipticCurve(N[i]);
  l;
  WeilRepresentation(l);
  
  chi1:=GaloisRepresentation
    (ArtinRepresentation(l`PrincipalSeriesParameters[1]),p);
  chi2:=GaloisRepresentation
    (ArtinRepresentation(l`PrincipalSeriesParameters[2]),p);
  
  A:=GaloisRepresentation
    (ArtinRepresentation(l`PrincipalSeriesParameters[1])
     +ArtinRepresentation(l`PrincipalSeriesParameters[2]),p);
  B:=GaloisRepresentation(E,p);
  
  K:=BaseField(A);
  R<x>:=PR(K);
  F:=ext<K|x^6-7>;
  BaseChange(A,F);
  EulerFactor(BaseChange(A,F));
  EulerFactor(BaseChange(B,F));
  loc,min:=LocalInformation(BaseChange(E,F));
  k,m:=ResidueClassField(Integers(F));
   
  EulerFactor(EllipticCurve([m(a): a in aInvariants(min)]));
  R<x>:=PR(Q);

  ">>> Sym^2 of an elliptic curve <<<";
  
  E:=EllipticCurve("14a1");
  A:=GaloisRepresentation(E,2);
  T:=A*A; 
  T;
  K:=BaseField(A);
  B:=T-CyclotomicCharacter(K)^(-1);
  assert B eq UnramifiedCharacter(K,4)*SP(K,3);

  ">>> Root numbers of twists <<<";

  K:=pAdicField(3,20);
  
  G1:=GaloisRepresentations(Polynomial([K|-3,0,1]))[2];
  G2:=GaloisRepresentations(Polynomial([K|-6,0,1]))[2];
  u:=Minimize(G1*G2); 
  
  assert UnramifiedRepresentation(K,1+x)*G1 eq G2;
  r1:=RootNumber(UnramifiedRepresentation(K,1+x)*G1);
  r2:=RootNumber(G2);
  assert IsNumZero(r1-r2);

  ">>> Root numbers of some semi-ramified characters <<<";
  
  D:=FullDirichletGroup(5*19);
  L:=[chi: chi in Elements(D) | (Order(chi) eq 6) and 
    (Conductor(chi) eq 5*19) and IsOdd(chi) and (Imaginary(chi(2)) ge 0)];
  assert #L eq 1;
  chi:=L[1];
  G5:=GaloisRepresentation(chi,5); G5;
  G19:=GaloisRepresentation(chi,19); G19;
  Ginfty:=HodgeStructure(ArtinRepresentation(chi)); Ginfty;
  localrootno:=
    [ComplexField()| RootNumber(G5),RootNumber(G19),RootNumber(Ginfty)];
  globalrootno:=&*localrootno;
  L:=LSeries(chi: Precision:=30);
  ok:=CheckFunctionalEquation(L);
  w1:=Sign(L);
  w2:=globalrootno;
  assert IsNumZero(w1-w2);

  ">>> Local root numbers vs Iwacomp <<<";
  
  // see iwacomp/iwfull/rhoeps.out
  A:=ArtinRepresentations(NumberField(x^3-17))[3];
  eps:=EpsilonFactor(A,3); eps;
  assert IsNumZero(eps-ComplexField().1*Sqrt(3));
  A:=ArtinRepresentations(NumberField(x^3-19))[3];
  eps:=EpsilonFactor(A,3); eps;
  assert IsNumZero(eps-ComplexField().1*Sqrt(3));
  A:=ArtinRepresentations(NumberField(x^3-26))[3];
  eps:= EpsilonFactor(A,3); eps;
  assert IsNumZero(eps-ComplexField().1*Sqrt(3));
  A:=ArtinRepresentations(NumberField(x^3-28))[3];
  eps:=EpsilonFactor(A,3); eps;
  assert IsNumZero(eps-ComplexField().1*Sqrt(3));

  ">>> Rachel's local reciprocity convention <<<";  

  for p in [7,11,13], d in [4..6] do
    Sprintf("p=%o d=%o",p,d);

    K:=pAdicField(p,20);
    F:=ext<K|d>;
    OF:=Integers(F);
    k,m:=ResidueClassField(OF);
    
    aut:=Automorphisms(F);
    pi:=K!p;                              // uniformizer
    frob:=aut[RachelLocRecip(pi,F,aut)];  // under Rachel's local reciprocity 
    assert m(frob(OF!k.1)) eq k.1^p;      // goes to x->x^q on the residue field,
                                          // opposite to Tate's
  end for;  

  
  ">>> Epsilon-factors under unramified twists <<<";
  
  K:=pAdicField(5,20);
  R<x>:=PR(K);
  K<pi>:=ext<K|x^2-5>;
  R<x>:=PR(K);
  F:=ext<ext<K|x^4-pi>|4>;
  list:=GaloisRepresentations(F,K);
  #list,"one-dim characters";
  I:=list[1]`I;

  assert exists(s){s: s in list | Order(Restriction(Character(s),I)) eq 4};
  assert exists(u){s: s in list | Order(Restriction(Character(s),I)) eq 1
                                  and Order(Character(s)) eq 4};
  Qi<i>:=CyclotomicField(4);
  u2:=UnramifiedCharacter(K,i);
  assert exists(u){s: s in list | s eq u2};
  assert forall{t: t in list | t*u eq t*u2};
  assert IsNumZero(EpsilonFactor(u)-EpsilonFactor(u2));
  assert forall{t: t in list | IsNumZero(EpsilonFactor(t*u)-EpsilonFactor(t*u2))};


  ">>> Det on elliptic curve = inverse cyclotomic character <<<";

  for cr in ["15a1","98a1","100a1","97344dr1"] do
  for p in [2,3,5,7,13] do
    E:=EllipticCurve(cr);
    A:=GaloisRepresentation(E,p);
    assert Determinant(A) eq CyclotomicCharacter(BaseField(A))^(-1);
  end for;
  end for;

  
  ">>> Inverses and division <<<";
  
  K:=ext<pAdicField(5,20)|2>;
  R<x>:=PR(K);
  
  assert 0/CyclotomicCharacter(K) eq ZeroRepresentation(K);
  assert 1/CyclotomicCharacter(K) eq CyclotomicCharacter(K)^(-1);
  assert CyclotomicCharacter(K)/CyclotomicCharacter(K) eq PrincipalCharacter(K);
  
  list:=GaloisRepresentations(x^8-2);
  U:=[A/CyclotomicCharacter(K)/B: A,B in list];
  &+U/Last(list);


  ">>> Compatibility conventions <<<";
  
  K:=CyclotomicField(7);
  A:=ArtinRepresentations(K)[6];
  chi:=DirichletCharacter(A);
  G1:=GaloisRepresentation(A,2);
  G2:=GaloisRepresentation(chi,2);
  
  f1:=PRC!EulerFactor(A,2);
  f2:=PRC!EulerFactor(chi,2);
  f3:=PRC!EulerFactor(G1);
  f4:=PRC!EulerFactor(G2);
  
  polyeq(f1,f2);
  polyeq(f1,f3);
  polyeq(f1,f4);


  ">>> Representations not computed to full precision <<<";

  R<x>:=PR(Q);
  K:=pAdicField(2,20);
  F:=ext<K|Polynomial([K|2,0,1])>;
  chi:=PermutationCharacter(F,K)-UnramifiedCharacter(K,1);
  
  A:=UnramifiedRepresentation(K,4,2,1+x+x^2+x^3+x^4+x^5);
  A,InertiaInvariants(A),EulerFactor(A),A*chi,InertiaInvariants(A*chi),EulerFactor(A*chi);
  A:=UnramifiedRepresentation(K,4,0,1+x+x^2+x^3+x^4+x^5);
  A,InertiaInvariants(A),EulerFactor(A),A*chi,InertiaInvariants(A*chi),EulerFactor(A*chi);
  A:=UnramifiedRepresentation(K,4,2,1-x);
  A,InertiaInvariants(A),EulerFactor(A),A*chi,InertiaInvariants(A*chi),EulerFactor(A*chi);
  A:=UnramifiedRepresentation(K,4,0,1-x);
  A,InertiaInvariants(A),EulerFactor(A),A*chi,InertiaInvariants(A*chi),EulerFactor(A*chi);

  ">>> TestRepLoc <<<";

  TestRepLoc();

  ">>> TESTING DONE <<<";

end procedure;



/////////////////////////////////////


//SetVerbose("GalRep",3); 
//SetVerbose("ArtRep",3); 


intrinsic TestGalRep() {}
 TestAll(); 
end intrinsic;
