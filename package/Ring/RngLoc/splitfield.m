freeze;


/*

  IMPLEMENTS
  
  function ComputeSplittingField(f,p: prec:=20, std:=true, Gal:=false, squarefree:=false)
  
  Given a squarefree polynomial f over Z, Q (->K=Q_p) or over a p-adic ring/field K
  compute the splitting field F of f over K. Returns
     O       ring of integers of F,
     Zp      prime ring of O
     r       roots of f in F
  if Std=true, converts O/Zp to a standard form, totally ramified over unramified.
  if Gal=true (forces Std), returns in addition
     G       Galois group Gal(F/K) as a permutation group on r
     I       Inertia subgroup of G
     ramgps  Ramification subgroups of G, a as sequence <G_i, i>, i increasing
             The first one is always I
     frob    Frobenius element, as an element of G 
     act     map G->Aut F
  if squarefree=true, assumes (does not check) that f is squarefree
  [SquareFreeFactorization is, ahem, not always robust]
  
  wrappers:
  
  intrinsic GaloisGroup(f::RngUPolElt[FldPad]) -> GrpPerm, SeqEnum, UserProgram
  intrinsic GaloisGroup(f::RngUPolElt[RngPad]) -> GrpPerm, SeqEnum, UserProgram
  intrinsic SplittingField(f::RngUPolElt[FldPad]: Std:=true) -> FldPad, SeqEnum
  intrinsic SplittingField(f::RngUPolElt[RngPad]: Std:=true) -> FldPad, SeqEnum
  
  v1 Tim Dokchitser Nov 2014
*/


// TODO: automatically change precision when *, +, minimize etc fails ?

// mmylib functions

Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | (x ne " ") and (x ne "\n")])>;
SortSet:=func<X|Sort(SetToSequence(Set(X)))>; 


function VectorContent(v)
  den:=LCM([Denominator(x): x in v]);
  v:=[Z!(den*x): x in v];
  gcd:=GCD(v);
  v:=[x div gcd: x in v];
  return gcd/den,v;
end function;


function PrintField(F)
  if AbsoluteDegree(F) eq 1 then
    return Sprintf("Q%o[%o]",Characteristic(ResidueClassField(Integers(F))),Precision(F)); 
  end if;
  B:=BaseField(F);
  if RamificationDegree(F,B) eq 1 then 
    return Sprintf("ext<%o|%o>",PrintField(B),Degree(F,B));
  end if;
  R<x>:=PR(Integers(B));
  return Sprintf("ext<%o|%o>",PrintField(B),DelSpaces(R!DefiningPolynomial(F)));
end function;


function MySquarefreePart(f)
  
  // Easy cases: degree 1, not padics, p-adic of precision 0 (yuck)
  
  if Degree(f) le 1 then return f; end if;
  F:=BaseRing(f);
  if Type(F) eq RngPad then
    F:=FieldOfFractions(F);
    f:=PR(F)!f;
  end if;
  if Type(F) ne FldPad then
    return SquarefreePart(f);
  end if;

  prec:=Precision(F);
  error if prec eq 0, "Cannot do much with p-adic of precision 0";

  R<x>:=PR(F);
  O:=Integers(F);
  k,m:=ResidueClassField(O);
  p:=Characteristic(k);

  // Cheap trick to make Derivative monic (for monic f) when p|degree

  fd:=f;
  if Degree(f) mod p eq 0 then
    v:=[Valuation(Evaluate(f,n)): n in [1..2*Degree(f)]];
    m,i:=Min(v);
    fd:=f*(x-i);
  end if;

  g:=GCD(f,Derivative(fd));
  
  plc:=Precision(LeadingCoefficient(g));
  d:=Degree(g);
  ok:=(d eq 0) and (plc gt prec/4) or (d gt 0) and (plc gt prec/2);
  error if not ok,
    "Not enough precision to determine whether the polynomial is square-free for\n"*
    "f="*DelSpaces(f)*" d="*DelSpaces(d)*" prec="*DelSpaces(prec)*" plc="*DelSpaces(plc);
  return (d eq 0) select f else (f div g);
end function;


function FactorizationNewtonPolygon(h)
  // Based on A. Jorza's notes 
  // "Newton Polygons and Factoring polynomials over Local Fields"

  R<x>:=Parent(h);
  O:=BaseRing(h);
  R0:=R;
  
  mv:=func<f|f eq 0 select Infinity() else Min([Valuation(c): c in Coefficients(f)])>;
  trunc:=func<f,d|Parent(f)![Coefficient(f,i): i in [0..d]]>;

  val:=[v: v in ValuationsOfRoots(h) | v[1] ne Infinity()];
  if (Degree(h) le 1) or (#val eq 1) then return [h]; end if;
  m,i:=Max([v[1]: v in val]);
  d:=Z!val[i][2];  

  lead:=Coefficient(h,d);
  f0:=R![Coefficient(h,i) div lead: i in [0..d]];
  g0:=R!lead;
  
  mv0:=-1;
  mv1:=-1;
  repeat
    t:=h-f0*g0;
    q:=t div f0;
    r:=t-q*f0;
    mv2:=mv(r);
    if mv2 le mv0 then break; end if;
    mv0:=mv1;
    mv1:=mv2;
    f0:=trunc(f0+r div lead,d);        
    g0:=trunc(g0+q*lead,Degree(h)-d+1);
  until false;
  return FactorizationNewtonPolygon(R0!f0) cat FactorizationNewtonPolygon(R0!(h div f0));  
end function;

mv:=func<f|Min([Valuation(c): c in Coefficients(f)])>;


function pAdicEltseq(x: base:=Q)
  if (Type(x) in [RngPadElt,RngIntElt]) and (AbsoluteDegree(Parent(x)) eq AbsoluteDegree(base)) 
    then return base!x;
  elif (Type(x) in [FldPadElt,FldRatElt]) and (AbsoluteDegree(Parent(x)) eq AbsoluteDegree(base)) 
    then return base!x;
  elif Type(x) in [FldPad,RngPad] then
    L:=[* *];
    while AbsoluteDegree(x) ne AbsoluteDegree(base) do
      Append(~L,pAdicEltseq(DefiningPolynomial(x)));
      x:=BaseRing(x);
    end while;
    return L;
  else 
    return [pAdicEltseq(c: base:=base): c in Coefficients(x)];
  end if;
end function;


function pAdicFromEltseq(R,x)
  if Type(x) in [RngIntElt,FldRatElt] then 
    return R!x; 
  elif Type(x) eq List then
    for i:=#x to 1 by -1 do
      R:=ext<R|pAdicFromEltseq(PR(R),x[i])>;
    end for;
    return R;
  else B:=BaseRing(R);
       return R![pAdicFromEltseq(B,c): c in Eltseq(x)];
  end if;
end function;


function pAdicChangePrecision(R,prec: base:=Q)
  if prec eq Precision(R) then
    return R,map<R->R|x:->x,x:->x>;
  end if;
  bprec:=prec div AbsoluteRamificationDegree(R);
  p:=Characteristic(ResidueClassField(Integers(R)));
  if base cmpeq Q 
    then B:=Type(R) eq FldPad select pAdicField(p,bprec) else pAdicRing(p,bprec);
    else B:=base;
  end if;
  S:=pAdicFromEltseq(B,pAdicEltseq(R: base:=base));
  return S,map<R->S|x:->pAdicFromEltseq(S,pAdicEltseq(x: base:=base)),
                    x:->pAdicFromEltseq(R,pAdicEltseq(x: base:=base))>;
end function;


function AbsoluteTotallyRamifiedExtension(R: base:=PrimeRing(R))
//! does not construct embeddings

  f := InertiaDegree(R,base);
  e := RamificationDegree(R,base);
  B := f eq 1 select base else UnramifiedExtension(base, f);
  if e eq 1 then return B; end if;

  resext := PR(Z)!MinimalPolynomial(PrimitiveElement(k),PrimeField(k)) 
    where k is ResidueClassField(Integers(B));
  rB := Roots(resext,B)[1,1];
  rR := Roots(resext,R)[1,1];
  piR := UniformizingElement(R);

  cf :=func<x|Flat(pAdicEltseq(x: base:=base))>;
  l  := Matrix([cf(piR^i*rR^j) : j in [0..f-1], i in [0..e-1] ] cat [cf(piR^e)]);
  n  := NullspaceMatrix(l);

  assert Nrows(n) eq 1;
  assert IsUnit(n[1][e*f+1]);

  n := n/n[1][e*f+1];
  M := Matrix(e,f,Prune(Eltseq(n)));
  f := [Evaluate(Polynomial(Eltseq(M[i])),rB): i in [1..e]] cat [B|1];
  S := TotallyRamifiedExtension(B, Polynomial(f));

  return S;
end function;


function pAdicFactorization(h)
  if Degree(h) le 1 then return [h]; end if;
  R:=BaseRing(h);
  Rprec:=Precision(R);
  val:=[v: v in ValuationsOfRoots(h) | v[1] ne Infinity()];

  // Break by Newton polygon
  if #val gt 1 then
    S,m:=pAdicChangePrecision(R,2*Rprec);
    hS:=PR(S)![m(c): c in Coefficients(h)];
    fct:=FactorizationNewtonPolygon(hS);
    fct:=[PR(R)![c@@m: c in Coefficients(f)]: f in fct];
    return &cat[pAdicFactorization(f): f in fct];
  end if;
  
  // Magma factorization
  S,m:=pAdicChangePrecision(R,4*Rprec);
  hS:=PR(S)![m(c): c in Coefficients(h)];
  fct:=Factorisation(hS);
  fct:=[PR(R)![c@@m: c in Coefficients(f[1])]: f in fct];
  return fct;

end function;

  
function pAdicAdjoinRoot(h: Mode:=Min)
  R:=BaseRing(h);
  if Degree(h) le 1 then return R; end if;
  Rprec:=Precision(R);
  
  for precfactor in [1,3,8] do
  try
    S,m:=pAdicChangePrecision(R,precfactor*Rprec);
    hS:=PR(S)![m(c): c in Coefficients(h)];
    fct,r,e:=Factorisation(hS: Extensions:=true);
    e:=[d`Extension: d in e];
    degs:=[AbsoluteDegree(F): F in e];
    if Mode eq Min 
      then m,i:=Min(degs); 
      else m,i:=Max(degs); 
    end if;
    if degs[i] eq AbsoluteDegree(R) then return R; end if;
    F:=e[i];
    F0:=pAdicChangePrecision(F,Rprec*RamificationDegree(F,S): base:=R);
    return F0;
  catch e
    err:=e`Object; 
  end try;
  end for;
  error "Failed to adjoin a root:",err;
  
end function;


/*
function HenselLiftFct(f)
  R:=BaseRing(f);
  O:=Integers(R);
  K:=FieldOfFractions(O);
  k,m:=ResidueClassField(O);
  R<x>:=PR(O);
  f:=R!f;
  fct:=Factorisation(PR(k)![m(c): c in Coefficients(f)]);
  if #fct le 1 then return [f]; end if;
  vprint ArtRep,2: "HenselLiftFct",DelSpaces([<Degree(d[1]),d[2]>: d in fct]);
  ok:=exists(i){i: i in [1..#fct] | not IsEmpty(Roots(fct[i][1]))};
  if not ok then 
    return HenselLift(f,[d[1]^d[2]: d in fct]); 
  end if;
  r:=Roots(fct[i][1]);
  r:=O!r[1][1];
  f:=Evaluate(f,x+r);
  vprint ArtRep,2: "HenselLiftFct: val",DelSpaces(ValuationsOfRoots(f));

  Oprec:=Precision(O);
  S,m:=pAdicChangePrecision(O,2*Oprec);
  fS:=PR(S)![m(c): c in Coefficients(f)];
  F:=FactorizationNewtonPolygon(fS);
  F:=[Evaluate(PR(R)![c@@m: c in Coefficients(f)],x-r): f in F];
  return &cat[HenselLiftFct(f): f in F];

end function;
*/


procedure SplitStep(~F: tame:=false)
   
  if Type(F) eq RngUPolElt then
    F:=[<F,BaseRing(F)!1,BaseRing(F)!0>];
  end if;
  
  if forall{d: d in F | Degree(d[1]) le 1} then 
    vprint ArtRep,3: "ss Done";
    return; 
  end if;

  O:=Integers(BaseRing(F[1][1]));
  pi:=UniformizingElement(O);
  R<x>:=PR(O);
  F:=[<R!d[1],O!d[2],O!d[3]>: d in F];
  K:=FieldOfFractions(O);
  k,m:=ResidueClassField(O);
  p:=Characteristic(k);
  lin:=func<d|(Degree(d[1]) eq 1) and (d[2] eq 1)>;
 
  kext:=1;    // unramified
  text:=1;    // tame

  i:=1;
  repeat

    f,s1,s2:=Explode(F[i]);
    if Degree(f) le 1 then i+:=1; continue; end if;
    fbar:=PR(k)!f;
    fct:=Factorisation(fbar);
  
    // f factors mod p into coprime factors -> Hensel lift factorisation
  
    if #fct ne 1 then
      onlyroots:=forall{d: d in fct | lin(d)};
      vprint ArtRep,3: "ss "*
        Sprintf("k[%o]: %o -> factors %o",i,DelSpaces(fct),onlyroots select "(roots)" else "");
      for d in fct do
        if not lin(d) then continue; end if;
        rbar:=-Coefficient(d[1],0)/Coefficient(d[1],1);
        vprint ArtRep,3: "ss root",rbar;
        r:=HenselLift(f,O!rbar);
        Append(~F,<x-r,s1,s2>);
        if onlyroots then continue; end if;
        F[i][1] div:= x-r;
      end for;
      if onlyroots then F:=Remove(F,i); continue; end if;
      fct:=[d: d in fct | not lin(d)];
      if #fct gt 1 then
        fct:=HenselLift(F[i][1],[d[1]^d[2]: d in fct]);
        F:=Remove(F,i) cat [<d,s1,s2>: d in fct];
      end if;
      continue;
    end if;

    g:=fct[1][1];
  
    // f mod p = g^d, g non-linear -> extend k
    
    if Degree(g) ne 1 then 
      vprint ArtRep,3: "ss "*Sprintf("k[%o]: %o -> extending k",i,DelSpaces(g));
      kext:=LCM(kext,Degree(g));
      i+:=1;
      continue;
    end if;   
  
    // f mod p = g^d, g linear x-r -> translate
    r:=-ConstantCoefficient(g)/LeadingCoefficient(g);
    if r ne 0 then
      vprint ArtRep,3: "ss "*Sprintf("k[%o]: %o -> translating",i,DelSpaces(g));
      f:=Evaluate(f,x+O!r);
      F[i][1]:=f;
      F[i][3]+:=F[i][2]*O!r;
    end if;     

    // Rescale roots by pi^m if possible
  
    val:=[v: v in ValuationsOfRoots(f)];
    v:=Min([v[1]: v in val]);
    if (v ge 1) and (v lt Precision(K) div 2) then 
      m:=Floor(v);
      vprint ArtRep,3: "ss "*
        Sprintf("v[%o]: %o -> rescaling by pi^%o",i,DelSpaces(val),m);
      d:=Degree(f);
      F[i][1]:=R![Coefficient(f,i) div pi^(m*(d-i)): i in [0..d]];
      F[i][2]*:=pi^m;
      F[i][3]*:=1;
      continue;
    end if;

    // tame ext
    if tame then
      d:=Denominator(VectorContent([v[1] eq Infinity() select 1 else v[1]: v in val]));
      t:=d div p^Valuation(d,p);
      if t ne 1 then
        vprint ArtRep,3: "ss "*Sprintf("v: %o -> tame ext %o",DelSpaces(val),t);
        text:=LCM(text,t);
      end if;
    end if;

    i+:=1;        
  until i gt #F;

  if kext ne 1 then            // Unramified extension
    vprint ArtRep,3: "ss "*  
      "UNR ext",kext;
    K:=ext<K|kext>;
    O:=Integers(K);
    R<x>:=PR(O);
    F:=[<R!d[1],O!d[2],O!d[3]>: d in F];
  end if;    

  if text ne 1 then            // Tame extension
    vprint ArtRep,3: "ss TAME ext",text;
    K:=ext<K|x^text-UniformizingElement(O)>;
    O:=Integers(K);
    R<x>:=PR(O);
    F:=[<R!d[1],O!d[2],O!d[3]>: d in F];
  end if;    
  if text*kext gt 1 then return; end if;

  // Wild extension

  degs:=[Degree(d[1]): d in F | Degree(d[1]) gt 1];
  if IsEmpty(degs) then 
    vprint ArtRep,3: "ss Done";
    return; 
  end if;
  d:=Min(degs);
  assert exists(i){i: i in [1..#F] | Degree(F[i][1]) eq d};
  vprint ArtRep,3: "ss "*Sprintf("d=%o wild ext",d);

  K:=pAdicAdjoinRoot(F[i][1]: Mode:=Max);
  ONew:=Integers(K);

  vprint ArtRep,3: Sprintf("extending d=%o e=%o f=%o",
    Degree(ONew,O),RamificationDegree(ONew,O),InertiaDegree(ONew,O));

  error if Degree(ONew,O) eq 1, "SplitStep: Insufficient precision";
  
  O:=ONew;
  R<x>:=PR(O);
  F:=[<R!d[1],O!d[2],O!d[3]>: d in F];
  vprint ArtRep,3: "ss RES",DelSpaces({* Degree(d[1]): d in F *});
end procedure;


procedure pAdicSplit(~F,~r: tame:=false)
  repeat
    if Type(F) eq RngUPolElt 
      then O:=BaseRing(F);
      else O:=BaseRing(F[1][1]);
    end if;
    d:=AbsoluteDegree(O);
    e:=AbsoluteRamificationDegree(O);
    vprintf ArtRep,2: "pAdicSplit prec=%o (d=%o e=%o f=%o) %o\n",
      Precision(O),d,e,d div e,
      Type(F) eq RngUPolElt select Degree(F) else DelSpaces({* Degree(d[1]): d in F *});
    SplitStep(~F: tame:=tame);
  until forall{d: d in F | Degree(d[1]) le 1};
  r:=[d[2]*(-ConstantCoefficient(d[1])/LeadingCoefficient(d[1]))+d[3]: d in F];
end procedure;


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


function aut1(api)
  OK<pi>:=Integers(Parent(api));
  basis:=[pi^i: i in [0..Degree(OK)-1]];
  abasis:=[api^i: i in [0..Degree(OK)-1]];
  M:=Matrix([Eltseq(x): x in abasis]);
  Minv:=M^(-1);
  function a(x: inv:=false)
    xO:=Valuation(x) ge 0 select OK!x else OK!(1/x); 
    e:=Eltseq(xO);
    v:=Vector(e)*(inv select Minv else M);
    r:=OK!Eltseq(v);
    return Valuation(x) ge 0 select r else 1/r; 
  end function;
  return a;
end function;


function aut2(api,au)
  OK<pi>:=Integers(Parent(api));
  OU<u>:=BaseRing(OK);
  dU:=Degree(OU);
  dK:=Degree(OK);
  basis:=[pi^i*u^j: j in [0..dU-1], i in [0..dK-1]];
  abasis:=[api^i*au^j: j in [0..dU-1], i in [0..dK-1]];
  M:=Matrix([&cat[Eltseq(c): c in Eltseq(x)]: x in abasis]);
  Minv:=M^(-1);
  function a(x: inv:=false)
    xO:=Valuation(x) ge 0 select OK!x else OK!(1/x); 
    e:=&cat[Eltseq(c): c in Eltseq(xO)];
    v:=Vector(e)*(inv select Minv else M);
    r:=OK![OU!c: c in Partition(Eltseq(v),dU)];
    return Valuation(x) ge 0 select r else 1/r; 
  end function;
  return a;
end function;


// Convert a Galois automorphism of a p-adic field (map field->field)
// to a permutation in S_n

function GaloisToPermutation(F,r)
  perm:=[];
  for x in r do
    Fx:=F(x);
    list:=[Valuation(Fx-R): R in r];
    v,m:=Max(list);
    assert (v gt 0) and (#[x: x in list | x eq v] eq 1);     // F must permute the roots, just checking
    Append(~perm,m);
  end for;
  return Sym(#r)!perm;
end function;



function ComputeSplittingField(f,p: prec:=20, tame:=false, std:=true, Gal:=false, squarefree:=false)

  B:=BaseRing(f);
  assert Type(B) in [FldRat,RngInt,FldPad,RngPad];

  if Type(B) in [RngInt,RngPad] then
    B:=FieldOfFractions(B);
    f:=PR(B)!f;
  end if;

  if not squarefree then
    f:=MySquarefreePart(f);
  end if;

  // Make f monic

  lead:=LeadingCoefficient(f);
  if lead ne 1 then f:=f/lead; end if;

  // Rescale if necessary
  
  if Type(B) in [RngInt,FldRat] 
    then vroots:=[v[1]: v in ValuationsOfRoots(f,p) | v[1] ne Infinity()];
         pi:=p;
         scaleval:=Floor(Min(vroots));
    else vroots:=[v[1]: v in ValuationsOfRoots(f)   | v[1] ne Infinity()];
         pi:=UniformizingElement(B);
         prec:=Precision(B);
         scaleval:=Min(0,Floor(Min(vroots)));
  end if;

  scale:=pi^scaleval;
  if scaleval ne 0 then
    vprint ArtRep,2: "Rescaling by pi^"*Sprint(scaleval);
    f:=Evaluate(f,x*scale)/scale^Degree(f) where x is PR(B).1;
  end if;

  if Type(B) in [RngInt,FldRat] 
    then Qp:=pAdicField(p,prec);
         Zp:=Integers(Qp);
         g:=PR(Zp)!f;
    else Qp,m:=pAdicChangePrecision(B,prec);
         Zp:=Integers(Qp);
         g:=PR(Zp)![m(c): c in Coefficients(f)];
  end if;
  pAdicSplit(~g,~r: tame:=tame);      // Compute splitting field
  O:=BaseRing(g[1][1]);
  vprint ArtRep,3: "f(r) vals "*DelSpaces({Valuation(Evaluate(f,x)): x in r});

  if not std then 
    return O,PrimeRing(O),[x*scale: x in r],f; 
  end if;

  vprint ArtRep,2: "AbsoluteTotallyRamifiedExtension";
  O:=AbsoluteTotallyRamifiedExtension(O: base:=Zp);     
    // Convert O to standard form
  vprint ArtRep,2: "Roots";
  //r:=[r[1]:r in Roots(f,O)];
  g:=PR(O)!f;
  pAdicSplit(~g,~r: tame:=tame);      // Roots of f in the new O
  error if #r ne Degree(f),
        "Failed to compute splitting field: not enough precision (?)";
  vprint ArtRep,3: "f(r) vals "*DelSpaces({Valuation(Evaluate(f,x)): x in r});
  
  if not Gal then return O,Zp,[x*scale: x in r],f; end if;
  
  vprint ArtRep,2: "Computing the automorphism group";    // Aut

  K:=FieldOfFractions(O);
  pi:=UniformizingElement(O);
  e:=RamificationDegree(O,Zp);
  Ppol:=e gt 1 select DefiningPolynomial(O) else PR(O).1-pi;
  g:=PR(O)!Ppol;
  P:=[d[1]: d in Roots(g)];              // Split minpoly of a uniformizer
  error if #P ne Degree(Ppol),
      "Failed to compute splitting field: not enough precision (?)";
  rdiff:=[Valuation(r[i]-r[j]): i,j in [1..#r] | i lt j];
  pow:=IsEmpty(rdiff) select 0 else Min(Max(rdiff)+1,Degree(K));
  
  pidiff:=[Valuation(u-pi): u in P];    // v(P[i]-P[j]) determine 
                                         // ramification filtration
  error if not exists(piind){j: j in [1..#P] | pidiff[j] gt 0.7*Precision(K)},
    "Failed to compute splitting field: not enough precision (?)";
  Iindices:=SortSet(Remove(pidiff,piind));
  Isizes:=[#[x: x in pidiff | x ge i]: i in Iindices];
  vprint ArtRep,2: "Inertia indices",DelSpaces(Iindices);
  vprint ArtRep,2: "Inertia sizes",DelSpaces(Isizes);

  U:=e eq 1 select K else BaseRing(K);   // maximal unramified ext inside K
  OU:=Integers(U);
  kU,mU:=ResidueClassField(OU);
  kB,mB:=ResidueClassField(Zp);

  I:=sub<Sym(#r)|>;                  // build up from ramification subgroups
  Ifil:=[];
  actlist:=[* *];
  for i:=#Iindices to 1 by -1 do  
    for j:=1 to #P do
      if pidiff[j] eq Iindices[i] then
        sigma:=aut1(P[j]);
        perm:=GaloisToPermutation(sigma,r);
        Append(~actlist,<P[j],U.1,sigma,perm>);
        I:=sub<Sym(#r)|I,perm>;
        if #I ge Isizes[i] then break; end if;
      end if;
    end for;
    assert #I eq Isizes[i];
    Append(~Ifil,<I,Iindices[i]>);
  end for;
  assert #I eq #P;
  if IsEmpty(Ifil) then Ifil:=[<I,1>]; end if;
  
  vprint ArtRep,2: "x->x^q on the residue field";           

  if Degree(OU,Zp) eq 1 then                                // Frobenius on U
    Uq:=OU.1; 
    frobcf:=func<x|x>;
  else
    u:=[r[1]: r in Roots(DefiningPolynomial(OU),OU)];
    assert exists(Uq){x: x in u | mU(x) eq z} where z is mU(OU.1)^#kB;  // x->x^q on kU
    frobcf:=aut1(Uq);
  end if;

  vprint ArtRep,2: "Frobenius";
  
  Pconj:=P[1];
  if InertiaDegree(O,Zp) eq 1 then
    frobsigma:=func<x|x>; 
  elif O eq OU then
    frobsigma:=aut1(Uq);
  else
    if not forall{c: c in Coefficients(Ppol) | IsCoercible(Zp,c)} then
      fconj:=PR(O)!PR(OU)![frobcf(c): c in Coefficients(Ppol)];
      Pconj:=Roots(fconj,O: Max:=1)[1,1];
    end if;
    frobsigma:=aut2(Pconj,Uq);
  end if;
  frob:=GaloisToPermutation(frobsigma,r);
  Append(~actlist,<Pconj,Uq,frobsigma,frob>);

  G<[gens]>:=sub<Sym(#r)|I,frob>;                       // full Galois group
  vprint ArtRep,2: "Automorphism group done ->",GroupName(G);

  // Automorphism action of G on elements of K
 
  actlist:=[* d: j in [1..#gens] |                        
    exists(d){d: d in actlist | d[4] eq gens[j]} *];
  assert #actlist eq #gens;
      
  function actgen(j)                               // action of jth generator
    if Order(G.j) eq 1 then return func<x|K!x>; end if;
    pi,cfact,sigma,g:=Explode(actlist[Abs(j)]);
    if j gt 0 then 
      return hom<K->K|x:->sigma(x)>;
    else
      return hom<K->K|x:->sigma(x: inv:=true)>;
    end if;      
  end function;
  
  h:=hom<FreeGroup(#gens)->G|gens>;             // action on a general element
  act:=func<g|Order(g) eq 1 select func<x|K!x> else &*[actgen(j): j in Eltseq((G!g)@@h)]>;

  ramgps:=Reverse(Ifil);
  G<[gens]>:=sub<Sym(#r)|MinimizedGenerators(G)>;
  if GetVerbose("ArtRep")+GetVerbose("GalRep") ne 0 then
    Sprintf("F/%o: G=%o I=%o G_i=%o",
     PrintField(Qp),GroupName(G),GroupName(I),DelSpaces([Sprintf("%o|%o",GroupName(H[1]),H[2]): H in ramgps]));
  end if;
  return O,Zp,[x*scale: x in r],G,I,ramgps,frob,act,f;
  
end function;


///////////////////////// INTRINSIC WRAPPERS ///////////////////////////////


intrinsic GaloisGroup(f::RngUPolElt[FldPad]: squarefree:=false) -> GrpPerm, SeqEnum, UserProgram
{Galois group G of a squarefree polynomial f over a p-adic field. Returns G as a permutation group on the roots of f in its splitting field F, the roots themselves, and a map G->Aut(F/K).}
  O,B,r,G,I,ramgps,frob,act:=ComputeSplittingField(f,0: Gal:=true, squarefree:=squarefree);
  return G,r,act;
end intrinsic;


intrinsic GaloisGroup(f::RngUPolElt[RngPad]: squarefree:=false) -> GrpPerm, SeqEnum, UserProgram
{Galois group G of a squarefree polynomial f over a p-adic ring. Returns G as a permutation group on the roots of f in its splitting field F, the roots themselves, and a map G->Aut(F/K).}
  O,B,r,G,I,ramgps,frob,act:=ComputeSplittingField(f,0: Gal:=true, squarefree:=squarefree);
  return G,r,act;
end intrinsic;


intrinsic SplittingField(f::RngUPolElt[FldPad]: Std:=true) -> FldPad, SeqEnum
{Splitting field of a squarefree polynomial f over a p-adic field and the roots of f in it.}
  O,B,r:=ComputeSplittingField(f,0: Gal:=false, std:=Std);
  return FieldOfFractions(O),r;
end intrinsic;


intrinsic SplittingField(f::RngUPolElt[RngPad]: Std:=true) -> FldPad, SeqEnum
{Splitting field of a squarefree polynomial f over a p-adic ring and the roots of f in it.}
  O,B,r:=ComputeSplittingField(f,0: Gal:=false, std:=Std);
  return O,r;
end intrinsic;
