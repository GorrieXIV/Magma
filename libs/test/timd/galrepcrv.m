Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
EC:=EllipticCurve;
PRC<X>:=PR(ComplexField());
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;


function PrintCurve(C)
  K:=BaseField(C);
  U<x>:=PR(K);
  s:=Sprint(C);
  p1:=Position(s," defined by ");
  p2:=Position(s," over ");
  if p1*p2 eq 0 then return s; end if;
  return DelSpaces(s[[p1+12..p2]]);
end function;


function E4TorsPoly(E)
  _,_,_,A4,A6:=Explode(aInvariants(WeierstrassModel(E)));
  F:=BaseRing(E);
  R<x>:=PR(F);
  return x^12+(10*A4+54*A6)*x^10+(-120*A4^2+40*A6)*x^9+(132*A4^3+15*A4^2-810*A4*A6+891*A6^2)*x^8+
         (96*A4^3+192*A4*A6-2592*A6^2)*x^7+(560*A4^4+432*A4^3*A6-52*A4^3+1260*A4^2*A6+3780*A4*A6^2+2916*A6^3+384*A6^2)*x^6+
         (-576*A4^5-336*A4^4+1344*A4^3*A6-3888*A4^2*A6^2-240*A4^2*A6+9072*A6^3)*x^5+
         (-528*A4^6+280*A4^5-2160*A4^4*A6+15*A4^4-7128*A4^3*A6^2-420*A4^3*A6+1890*A4^2*A6^2-14580*A4*A6^3-240*A4*A6^2-24057*A6^4)*x^4+
         (128*A4^6-160*A4^5+1792*A4^4*A6-2592*A4^3*A6^2-1440*A4^2*A6^2+12096*A4*A6^3-23328*A6^4-320*A6^3)*x^3+
         (-480*A4^7+864*A4^6*A6-208*A4^6+720*A4^5*A6+10*A4^5-6480*A4^4*A6^2-354*A4^4*A6+11664*A4^3*A6^3+132*A4^3*A6^2+4860*A4^2*A6^3+96*A4^2*A6^2-21870*A4*A6^4-2592*A4*A6^3+39366*A6^5+10368*A6^4)*x^2+
         (-384*A4^8-64*A4^7-384*A4^6*A6+8*A4^6-5184*A4^5*A6^2-320*A4^5*A6-432*A4^4*A6^2+8*A4^4*A6-5184*A4^3*A6^3-192*A4^3*A6^2-17496*A4^2*A6^4-2160*A4^2*A6^3+64*A4*A6^3-17496*A6^5-1728*A6^4)*x
         -64*A4^9-16*A4^8-288*A4^7*A6+4*A4^7-1296*A4^6*A6^2-16*A4^6*A6+A4^6-216*A4^5*A6^2+14*A4^5*A6-3888*A4^4*A6^3-37*A4^4*A6^2-8748*A4^3*A6^4-108*A4^3*A6^3+16*A4^3*A6^2-729*A4^2*A6^4+96*A4^2*A6^3-13122*A4*A6^5-432*A4*A6^4-19683*A6^6+64*A6^4;
end function;


function E3TorsPoly(E)
  _,_,_,A4,A6:=Explode(aInvariants(WeierstrassModel(E)));
  F:=BaseRing(E);
  R<x>:=PR(F);
  c4,c6:=Explode(cInvariants(E));
  c4zero:=IsZero(c4) or (Valuation(c4) ge 3/4*Precision(F));
  return c4zero select (x^6-8*c6)*(x^2+6*c6)
                else   x^8-6*c4*x^4-8*c6*x^2-3*c4^2;
end function;


function ThreeTorsExtType(E)
  K:=BaseField(E);
  K:=ChangePrecision(K,Precision(K)*4);
  E:=BaseChange(E,K);
  fct:=[Degree(d[1]): d in Factorization(E3TorsPoly(E))];
  c4,c6:=Explode(cInvariants(E));
  if Valuation(c4) ge Precision(K) then c4:=0; end if;
  if Valuation(c6) ge Precision(K) then c6:=0; end if;
  delta:=Discriminant(E);
  mu3:=IsEven(InertiaDegree(K,PrimeField(K)));
  del,rt:=IsPower(delta,3);
  mi:=Min(fct);
  ma:=Max(fct);
  vprintf GalRep,2: "ThreeTorsExtType: fct=%o mu3=%o del=%o\n",
    DelSpaces(fct),mu3,del;
  fct:=Set(fct);
  if mu3 and del then
    if mi lt 8 then return "C" cat Sprint(mi); else return "Q8"; end if;
  end if;
  if mu3 then
    if mi le 2 then return "C" cat Sprint(3*mi); else return "SL(2,3)"; end if;
  end if;
  if del then
    if mi le 2 then return "C2",1; end if;
    if mi eq 4 then return "D4",1; end if;
    if IsSquare(-3*(c4-12*rt)) and IsSquare(-3*(c4^2+12*c4*rt+(12*rt)^2))
      then return "C8",0;
      else return "SD16",2;
    end if;
  end if;
  if (fct eq {1,6}) or (fct eq {2,3}) then return "S3",1; end if;
  if mi eq 2 then return "D6"; else return "GL(2,3)"; end if;
end function;


procedure TestAll()

  ">>> Non-abelian inertia on an elliptic curve at p=2 <<<";

  E:=EllipticCurve("32a1");
  K:=pAdicField(2,40);
  R<x>:=PR(K);
  EK:=BaseChange(E,K);
  A:=GaloisRepresentation(EK: Minimize:=false);
  assert IdentifyGroup(Group(A))        eq <64,7>;   // Q8:C8
  assert IdentifyGroup(InertiaGroup(A)) eq <8,4>;    // Q8
  A:=Minimize(A);
  assert IdentifyGroup(Group(A))        eq <16,8>;   // SD16
  assert IdentifyGroup(InertiaGroup(A)) eq <8,4>;    // Q8
  assert ConductorExponent(A) eq 5;

  K1:=pAdicField(2,40);
  K2:=ext<K1|2>;
  
  EL:=["20a1","44a1","32a1","64a1","80b1","144a1","176b1","176c1","256a1",
       "256d2","272b1","97344dr1"];
  
  for cr in EL, K in [K1,K2] do
    EQ:=EllipticCurve(cr);
    j:=jInvariant(EQ);
    N:=Conductor(EQ);
    E:=BaseChange(EQ,K);
    if IsOdd(N) or (Valuation(j,2) lt 0) then continue; end if;
    T:=ThreeTorsExtType(E);
    if T in ["SL(2,3)","GL(2,3)"] then continue; end if;
    A:=GaloisRepresentation(E);
    G:=Group(A);
    I:=InertiaGroup(A);
    GN:=GroupName(G);
    IN:=GroupName(I);
    CremonaReference(EQ),T,GN,IN;
    if T eq GN then continue; end if;
    if IsCyclic(Group(T)) and IsCyclic(G) and (#Group(T) mod #G eq 0) then continue; end if;
    if T eq "SD16" and GN eq "Q8:C8" then continue; end if;
    error "Failed!";
  end for;

  ">>> Non-abelian inertia on an elliptic curve at p=3 <<<";

  E:=EllipticCurve("27a1");
  K:=pAdicField(3,80);
  R<x>:=PR(K);
  EK:=BaseChange(E,K);
  A:=GaloisRepresentation(EK);
  assert IdentifyGroup(InertiaGroup(A)) eq <12,1>;    // C3:C4

  E:=EllipticCurve("36a1");
  K:=pAdicField(3,80);
  R<x>:=PR(K);
  EK:=BaseChange(E,K);
  A:=GaloisRepresentation(EK);
  assert IdentifyGroup(InertiaGroup(A)) eq <4,1>;     // C4

  E:=EllipticCurve("45a1");
  K:=pAdicField(3,80);
  R<x>:=PR(K);
  EK:=BaseChange(E,K);
  A:=GaloisRepresentation(EK);
  assert IdentifyGroup(InertiaGroup(A)) eq <2,1>;     // C2
  
  ">>> EC: Almost worst reduction at 2 <<<";    // worst [0,0,0,1,2] is too slow
  
  E:=EllipticCurve([0,0,0,1,0]);
  GE:=GaloisRepresentation(E,2: Minimize:=true);
  
  ">>> Galois representations of hyperelliptic curves (good reduction) <<<";
  
  R<x>:=PR(Q);
  C:=HyperellipticCurve(x^5+x^2+1);
  GaloisRepresentation(C,3: Degree:=0);
  GaloisRepresentation(C,3: Degree:=1);
  GaloisRepresentation(C,3: Degree:=2);
  GaloisRepresentation(C,3: Degree:=3);
  GaloisRepresentation(C,3: Degree:=4);
  GaloisRepresentation(C,3: Degree:=5);
  GaloisRepresentation(C,3);
  
  ">>> Galois representations of hyperelliptic curves (bad reduction) <<<";
  
  // These 3 not implemented yet:
  C:=HyperellipticCurve(5*x*(x-5)*(x-1));             // I2 action
  C:=HyperellipticCurve((x^2+5)*((x-1)^2+5)*(x+1));   // Frob order 1 in Qp(r)
  C:=HyperellipticCurve(x*(x-5)*(x-1)*(x-6)*(x-2));   // Frob order 1 in Qp(r)
  
  for C in [HyperellipticCurve((x^2+5)*((x-1)^2+5)*(x^2+2)), 
      HyperellipticCurve(x*(x-5)*(x-1)*(x-2)*(x^2-2)),   
      HyperellipticCurve(x*(x-5)*(x-1)*(x^2-2)),   
      HyperellipticCurve(x*(x-5)*(x-1)*(x-2)*(x-3)),
      HyperellipticCurve((x^2+10)*((x-1)^2+10)*(x^2+2))] do
    A:=GaloisRepresentation(C,5);
    A;
    assert Determinant(A) eq CyclotomicCharacter(BaseField(A))^-2;
    assert EulerFactor(C,5) eq EulerFactor(A);
    assert Conductor(C,5) eq ConductorExponent(A);
  end for;
  
  C:=HyperellipticCurve(x^7+1,x); 
  GaloisRepresentation(C,10007: Degree:=1);    // not full degree
  
  C:=HyperellipticCurve(x^5+10007,x);          
  A:=GaloisRepresentation(C,10007: Degree:=1); A;    // full degree
  assert Determinant(A) eq CyclotomicCharacter(BaseField(A))^-2;
  assert EulerFactor(C,10007) eq EulerFactor(A);
  assert Conductor(C,10007) eq ConductorExponent(A);

  

end procedure;


procedure TestLandG()
  cfmax:=2;
  MaxDisc:=10^5;
  R<x>:=PR(Q);
  
  discs:=[];
  curves:=[];
  
  for height in [2..2] do
  "H",height;
  for b0,b1,b2,b3,b4,b5,b6 in [-cfmax..cfmax] do
    H:=&+[2*Abs(x)+(x lt 0 select 3 else (x gt 0 select 2 else 0)): x in [b0,b1,b2,b3,b4,b5,b6]];
    H:=Round(Sqrt(H));
    if H ne height then continue; end if;
    
    //"B",b0,b1,b2,b3,b4,b5,b6; 
    
    for a0,a1,a2,a3 in [0..1] do 
      f:=a3*x^3+a2*x^2+a1*x+a0;
      g:=b6*x^6+b5*x^5+b4*x^4+b3*x^3+b2*x^2+b1*x+b0;
      F:=4*g+f^2;
      if (Degree(F) lt 6) or (Discriminant(F) eq 0) then continue; end if;
      C:=MinimalWeierstrassModel(HyperellipticCurve(g,f));
      D:=Z!Discriminant(C);
      if Abs(D) gt MaxDisc then continue; end if;
      
      i:=Position(discs,D);
      if i eq 0 then 
        Append(~discs,D);
        Append(~curves,[C]);
      else
        if exists{C2: C2 in curves[i] | IsIsomorphic(C,C2)} then continue; end if;
        Append(~curves[i],C);
      end if;
  
      //Sprintf("%-8o %-25o",D,PrintCurve(C)); 
      
      // L-functions
      
      try 
        L:=LSeries(C: Precision:=10);
        Lok:=true;
      catch e
        Lok:=false;
      end try;
  
      if Lok then
        err:=CheckFunctionalEquation(L);
        assert Abs(err) lt 1E-7;
      end if;
  
      // Galois representations
    
      GR:=[];
      Gno:=[];
      Gyes:=[];
      for p in PrimeDivisors(D) do
        try
          Append(~GR,GaloisRepresentation(C,p)); Append(~Gyes,p);
        catch e
          Append(~Gno,p); 
        end try;
      end for;
      Gok:=IsEmpty(Gno);
    
      Sprintf("%-8o %-30o L:%-3o G:%-15o %o",D,PrintCurve(C),
        Lok select "yes" else "no",
        Gok select "yes" else DelSpaces(Gno),DelSpaces(Gyes));

      if Gok then 
        w:=Round(Real(Sign(L)));
        assert Abs(w) eq 1;
        assert w eq &*[RootNumber(A): A in GR];
      end if;

      for p in Gyes do
        if p gt 50 then continue; end if;
        K:=QuadraticField(p);
        CK:=BaseChange(C,K);
        P:=Ideal(Decomposition(K,p)[1,1]);
        GK:=GaloisRepresentation(CK,P);
        ChangePrecision(~GK,2*Precision(GK));
        KP:=BaseField(GK);
        QP:=PrimeField(KP);
        G:=GaloisRepresentation(BaseChange(C,QP));
        assert BaseChange(G,KP) eq GK;
      end for;
      
    end for;
  end for;
  end for;
end procedure;


TestAll();
TestLandG();

">>> ALL DONE <<<";
