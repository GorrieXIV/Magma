/*************************************************************************
Change log:

Sep 2006 (TD),
Aug 2010 (TD,VD)

  Commented out previous script by Mark Watkins for root numbers at
  odd places, implemented general root numbers of elliptic curves over
  local and global fields (2006); improved algorithms (2010)

  (local/FldPad)
  intrinsic LocalRootNumber(E::CrvEll[FldPad]) -> RngIntElt
  intrinsic RootNumber(E::CrvEll[FldPad]) -> RngIntElt
  (local/FldNum)
  intrinsic RootNumber(E::CrvEll[FldNum], P::RngOrdIdl) -> RngIntElt
  intrinsic LocalRootNumber(E::CrvEll[FldNum], P::RngOrdIdl) -> RngIntElt
  (global/FldNum)
  intrinsic RootNumber(E::CrvEll[FldNum]) -> RngIntElt

  Based on:

  - Original function (Cremona following Halberstadt I suppose)
    if the base field happens to be Q_p
  - Uses minor modifications of Rohrlich/Kobayashi for places v|infty, odd p
  - Uses joint algorithms (Tim Dokchitser, Vladimir Dokchitser,
    `Root numbers and parity of ranks of elliptic curves', Crelle 2010(?)

  Also implements Conductor, LocalInformation for E over the p-adics
****************************************************************/

freeze;

declare verbose Rootno,3;
// 0 - silent
// 1 - print reduction types and root number case at every place
// 2 - additional info


import "minmodel.m": rst_transform,TateAlgorithm;


Z:=Integers();
PR:=PolynomialRing;


intrinsic Conductor(E::CrvEll[FldPad]) -> FldPadElt
{The conductor of E.}
  K:=BaseField(E);
  vcond:=LocalInformation(E)[3];
  return UniformizingElement(K)^vcond;
end intrinsic;


intrinsic LocalInformation(E::CrvEll[FldPad]) -> Tup, CrvEll
{Tate's algorithm for an elliptic curve over a p-adic field:
 computes local reduction data at the prime ideal P,
 and a local minimal model.
 Output is
    <P, vpd, fp, c_p, K, split>, Emin
 where
    P = uniformizer of the maximal ideal of the base field,
    vpd = valuation of local minimal discriminant
    fp = valuation of conductor
    cp = Tamagawa number
    K = Kodaira Symbol
    split = false if non-split mult. red., true otherwise
    Emin = integral minimal model at P} //'
    
  K:=BaseField(E);
  _,red:=ResidueClassField(IntegerRing(K));
  val:=Valuation;
  pi:=UniformizingElement(K);
  return TateAlgorithm(E,pi,red,val,pi);
end intrinsic;

// Residue symbol 1 if square and -1 otherwise
ResidueSymbol:=func<a|IsSquare(a) select 1 else -1>;

// quadratic norm symbol (a,b) in a local field K of odd residue char
function QuadraticNormSymbol(K,a,b)
  u:=UniformizingElement(K);
  a/:=u^(2*(Valuation(a) div 2));
  if IsSquare(a) then return 1; end if;
  if Valuation(a) eq 0 then return (-1)^Valuation(b); end if;
  b/:=u^(2*(Valuation(b) div 2));
  if IsSquare(b) then return 1; end if;
  if Valuation(b) eq 0 then return (-1)^Valuation(a); end if;
  return QuadraticNormSymbol(K,a,-b/a);
end function;


function IsNorm(L,K,xi)
  vprint Rootno,2: "IsNorm: computing the unit group";
  U,m:=UnitGroup(IntegerRing(K));
  vprint Rootno,2: "IsNorm: unit group done";
  return NormEquation(IntegerRing(L),m,IntegerRing(K)!xi) select 1 else -1;
end function;


// Residue field of a local field
ResidueField:=func<K|ResidueClassField(IntegerRing(K))>;


/*
// returns L=K(pi^(1/d)), unique tame degree d ext, K local
TameExtension:=func<K,d|ext<K|PR(K).1^d-UniformizingElement(K)>>;

// exp(x) = Exp(2*Pi*I*x)
exp:=func<x|Exp(2*Pi(RealField())*ComplexField().1*x)>;

// norm of the relative discriminant of L/K to Qp; ??div. by. i. deg??
function RelDisc(K,L)
  d:=Discriminant(IntegerRing(L),IntegerRing(K));
  if d eq 0 then error "Not enough precision in RelDisc"; end if;
  return Valuation(d);
end function;

// n(Psi) where Psi is the standard additive character of K, Trace to Qp
NPsi:=func<K|RelDisc(PrimeField(K),K)>;
// reldisc sometimes returns 0
function NPsi(K)  // n(Psi) where Psi is the standard additive character of K
  KR:=IntegerRing(K);
  piKf:=UniformizingElement(K);
  kR,redk:=ResidueClassField(KR);
  uk:=KR!(kR.1);
  Qp:=PrimeField(K);
  npsi:=[Min([Valuation(Trace(K!(uk^j*piKf^-k),Qp)): j in [0..Degree(kR)-1]]):
    k in [0..Valuation(KR!(Degree(K,Qp)*4))-1]];
  npsi:=Min([j: j in [1..#npsi] | npsi[j] lt 0])-2;
  return npsi;
end function;

// quartic polynomial that defines F(E[3]_x)/F
Deg4Pol:=func<F,c4,c6|x^4-6*(F!c4)*x^2-8*(F!c6)*x-3*(F!c4)^2
  where x is PR(F).1>;

// polynomial (from cubic extensions paper) that defines F(E[3])/F
Deg8Pol:=func<F,c4,c6|
  Valuation(Expand(F!c4)) ge Precision(F)
    select (x^6-8*Expand(F!c6))*(x^2+6*Expand(F!c6))
    else   x^8-6*Expand(F!c4)*x^4-8*Expand(F!c6)*x^2-3*Expand(F!c4)^2
  where x is PR(F).1>;
Deg8PolNE:=func<F,c4,c6|
  c4 eq 0 select (x^6-8*(F!c6))*(x^2+6*(F!c6))
          else   x^8-6*(F!c4)*x^4-8*(F!c6)*x^2-3*(F!c4)^2
  where x is PR(F).1>;

// Which square root is adjoined to get a quadratic ext L from K
WhichRootAdjoined:=func<K,L|Discriminant(MinimalPolynomial(L.1,K))>;

// Determines whether sub is a substring of str; for try/catch error analysis
IsSubstring:=func<sub,str|Position(str,sub) ne 0>;

// delete spaces from a string s; for printing/debugging purposes
DelSpaces:=func<s|&cat([x: x in Eltseq(Sprint(s)) | x ne " "])>;

// print standard epsilon factors: +1,-1,I,-I; for debugging purposes
function preps(x)
  IsComplex:=func<x|IsCoercible(ComplexField(),x)>;
  if Abs(x-1) le 0.000001 then return 1;
  elif Abs(x+1) le 0.000001 then return -1;
  elif IsComplex(x) and Abs(x-ComplexField().1) le 0.000001 then return "I";
  elif IsComplex(x) and Abs(x+ComplexField().1) le 0.000001 then return "-I";
  elif IsReal(x) and Abs(x-BestApproximation(x,1000)) le 0.000001 then return BestApproximation(x,1000);
  else return x;
  end if;
end function;

// Given abelian L/K of degree 2^...=d=ef, find totally ramified extension
// of K of degree e which is contained in L^un - can be SLOW

function RamifiedDescent(K,L: rnd:=false)
  vprint Rootno,2: Sprintf("Ramified descent: [K:Q2]=%o [L:K]=%o e=%o ab:%o",
    Degree(K,PrimeField(K)),Degree(L,K),RamificationDegree(L,K),IsAbelian(L,K));
  KR:=IntegerRing(K);
  LR:=IntegerRing(L);
  vprint Rootno,3: "RD: Computing the unit group of K";
  UK,m:=UnitGroup(K);
  if rnd then repeat piK:=Random(KR); until Valuation(piK) eq 1;
         else piK:=UniformizingElement(K); end if;
  vprint Rootno,3: "RD: Computing the unit group of L";
  Ugens:=[ Norm(g,KR)@@m : g in UnitGroupGenerators(LR)];
  Rgens:=sub<UK|Append(Ugens,piK@@m)>;
  vprint Rootno,3: "RD: Computing the class field";
  return ClassField(m,Rgens);
end function;

function RamifiedDescent2(K,K1,K2,L: rnd:=false)
  vprint Rootno,2: Sprintf("Ramified descent: [K:Q2]=%o [L:K]=%o e=%o ab:%o",
    Degree(K,PrimeField(K)),Degree(L,K),RamificationDegree(L,K),IsAbelian(L,K));
  L:=ext<K1|MinimalPolynomial(UniformizingElement(L),K1)>;
  KR:=IntegerRing(K);
  LR:=IntegerRing(L);
  vprint Rootno,3: "RD: Computing the unit group of K";
  UK,m:=UnitGroup(K);
  if rnd then repeat piK:=Random(KR); until Valuation(piK) eq 1;
         else piK:=UniformizingElement(K); end if;
  vprint Rootno,3: "RD: Computing the unit group of L";
  Ugens:=[ Norm(g,KR)@@m : g in UnitGroupGenerators(LR)];
  Rgens:=sub<UK|Append(Ugens,piK@@m)>;
  vprint Rootno,3: "RD: Computing the class field";
  return ClassField(m,Rgens);
end function;

// Transform the coefficients of an elliptic curve according to r,s,t
// copy of Cremona's, but working with coefficients rather than curves
procedure RSTTransform(~a1,~a2,~a3,~a4,~a6,r,s,t)
  a6:=a6+r*(a4+r*(a2+r))-t*(a3+r*a1+t);
  a4:=a4-s*(a3+2*t)+r*(2*a2+3*r)-a1*(t+r*s);
  a3:=a3+r*a1+2*t;
  a2:=a2-s*(a1+s)+3*r;
  a1:=a1+2*s;
end procedure;

// Given an integral model of E over a 2-adic field K and assuming
// (does not check!) that E has good reduction over K, find a good model
// Adaptation of Tate's algorithm, but possibly slightly faster
// because it does not use elliptic curves on the way
function LocalGoodModel(EQ)
  Q:=BaseField(EQ);
  KR:=IntegerRing(Q);
  kR,red:=ResidueClassField(KR);
  KRP<ky>:=PR(kR);
  p:=UniformizingElement(Q);
  vdelta:=Valuation(Discriminant(EQ));
  a1,a2,a3,a4,a6:=Explode(aInvariants(EQ));
  while vdelta ne 0 do
    if Valuation(a1) eq 0 then
      x0:=-a3/a1; x0r:=red(x0);
    else
      _,x0r:=IsSquare(red(KR!-a4)); x0:=Q!x0r;
    end if;
    y0r:=Roots(ky^2+(kR!a1*x0r+kR!a3)*ky-x0r^3-kR!a2*x0r^2-kR!a4*x0r-kR!a6)[1,1];
    y0:=KR!y0r;
    RSTTransform(~a1,~a2,~a3,~a4,~a6,x0,0,y0);

    alpha:=KR!(Roots(ky^2+kR!a1*ky-kR!a2)[1,1]);
    beta:=KR!(Roots(ky^2+kR!(a3/p)*ky-kR!(a6/p^2))[1,1]);
    RSTTransform(~a1,~a2,~a3,~a4,~a6,0,alpha,beta*p);

    rt:=KR!(Roots(ky^3+kR!(a2/p)*ky^2+kR!(a4/p)*ky+kR!(a6/p^3))[1,1]);
    RSTTransform(~a1,~a2,~a3,~a4,~a6,p*rt,0,0);

    rt:=KR!(Roots(ky^2+kR!(a3/p^2)*ky-kR!(a6/p^4))[1,1]);
    RSTTransform(~a1,~a2,~a3,~a4,~a6,0,0,p^2*rt);

    a1/:=p; a2/:=p^2; a3/:=p^3; a4/:=p^4; a6/:=p^6;

    vdelta-:=12;
  end while;
  return EllipticCurve([a1,a2,a3,a4,a6]);
end function;

function AdjoinRoot(K,polcoeffs)  // -> L,root
  pol:=PR(K)![K!x: x in polcoeffs];
  f,_,e:=Factorisation(pol: Extensions:=true, IsSquarefree:=true);
  mindeg,ind:=Min([Degree(p[1]): p in f]);
  if mindeg eq 1
    then return K,-Coefficient(f[ind][1],0)/Coefficient(f[ind][1],1);
    else return E,Roots(pol,E)[1,1] where E is e[ind]`Extension;
  end if;
end function;

// Adjoin Kraus's roots of A and B to K1 that contains delta^(1/3)
// returns K2=K1(sqrt(A),sqrt(B)), sqrt(A), sqrt(B)
function AdjoinRootsAB(K1,c4,c6,rootdelta: twist:=1)
  A:=(c4-12*rootdelta);
  B:=c4^2+12*c4*rootdelta+(12*rootdelta)^2;
  if Valuation(A) ge Valuation(B) then
    K2,rootB:=AdjoinRoot(K1,[-twist*B,0,1]); rootA:=c6*twist/rootB;
  else
    K2,rootA:=AdjoinRoot(K1,[-twist*A,0,1]); rootB:=c6*twist/rootA;
  end if;
  return K2,rootA,rootB;
end function;

function ThreeTorsionExtType(E,fct)
// debugging purposes really, although might be useful for somebody
  K:=BaseField(E);
  c4,c6:=Explode(cInvariants(E));
  if Valuation(c4) ge Precision(K) then c4:=0; end if;
  if Valuation(c6) ge Precision(K) then c6:=0; end if;
  delta:=Discriminant(E);
  mu3:=IsEven(InertiaDegree(K,PrimeField(K)));
  del,rt:=IsPower(delta,3);
  mi:=Min(fct);
  ma:=Max(fct);
  if mu3 and del then
    if mi lt 8 then return "Cy" cat Sprint(mi); else return "Qu8"; end if;
  end if;
  if mu3 then
    if mi le 2 then return "Cy" cat Sprint(3*mi); else return "Sl24"; end if;
  end if;
  if del then
    if mi eq 2 then return "Cy2",1; end if;
    if mi eq 4 then return "Di8",1; end if;
    if IsSquare(-3*(c4-12*rt)) and IsSquare(-3*(c4^2+12*c4*rt+(12*rt)^2))
      then return "Cy8",0;
      else return "Sy16",2;
    end if;
  end if;
  if (fct eq {1,6}) or (fct eq {2,3}) then return "Di6",1; end if;
  if mi eq 2 then return "Bo12"; else return "Gl48"; end if;
end function;

// K(E[3])/K in steps, following Kraus
function ExtensionTower(K,c4,c6,delta)
  K1,rootdelta:=AdjoinRoot(K,[-delta,0,0,1]);
  K2,rootA,rootB:=AdjoinRootsAB(K1,c4,c6,rootdelta);
  C:=2*(c4+6*rootdelta+rootB);
  K3,rootC:=AdjoinRoot(K2,[-C,0,1]);
  K4,YT:=AdjoinRoot(K3,[-(XT^3-(c4/48)*XT-c6/864),0,1])
    where XT is (rootA+rootC)/12;
  return K1,K2,K3,K4,rootdelta;
end function;

function TwistedExtensionTower(K,c4,c6,delta)
  K1,rootdelta:=AdjoinRoot(K,[-delta,0,0,1]);
  K2,rootA,rootB:=AdjoinRootsAB(K1,c4,c6,rootdelta: twist:=-3);
  K2p:=ext<K2|2>;
  _,w:=IsSquare(K2p!-3);
  C:=2*(c4+6*rootdelta+rootB/w);
  K3,rootC:=AdjoinRoot(K2p,[-C,0,1]);
  K4,YT:=AdjoinRoot(K3,[-(XT^3-(c4/48)*XT-c6/864),0,1])
    where XT is (rootA/w+rootC)/12;
  return K1,K2,K2p,K3,K4,rootdelta;
end function;

function NChi(FList)  // FList=[K,{K_i},L] defines an abelian extension L/K
                      // of degree 2^m; -> conductor of prim. char. of L/K
  if #FList eq 1 then return 0; end if;
  K:=FList[1];
  L1:=FList[2];
  L:=FList[#FList];
  F:=[FList[j]: j in [2..#FList]]; // defines L/L1
  if Degree(L1,K) eq 1 then return NChi(F); end if; // degree?
  if #FList eq 2
    then return RelDisc(K,L);
    else return Integers()!((RelDisc(K,L1)+InertiaDegree(L,L1)*NChi(F))/RamificationDegree(L1,K));
  end if;
end function;

function EpsFactor(FldList:
         trsign:=1,normonly:=0,log:=false,chipower:=1,
         piKf:=0,brute:=false)
  Q:=Rationals();
  K:=FldList[1];
  L:=FldList[#FldList];
  Qp:=PrimeField(K);
  Zp:=IntegerRing(Qp);
  KPol<x>:=PR(K);

  deg:=Degree(L,K);                                     // [L:K]
  edeg:=RamificationDegree(L,K);
  fdeg:=deg div edeg;

  if deg eq 1 then
    error "EpsFactor: Trivial extension";
  end if;

  nchi:=NChi(FldList);

  vprint Rootno,2: Sprintf("EpsFactor: Cyclic local extension of degree %o with e=%o f=%o",
    deg,edeg,fdeg);

  KR:=IntegerRing(K);                   // Rings of integers of K
  LR:=IntegerRing(L);                   // L (top field)
  if InertiaDegree(FldList[2],K) gt 1
    then KunR:=IntegerRing(FldList[2]);  // KunR (max unr ext)
    else KunR:=KR;
  end if;
  if piKf eq 0 then
    piKf:=UniformizingElement(K);         // Uniformizer of K, canonically
  end if;                                 // given or random
  piK:=KR!piKf;
  piLf:=UniformizingElement(L);
  piL:=LR!piLf;
  kR,redk:=ResidueClassField(KR);        // Residue fields
  lR,redl:=ResidueClassField(LR);
  kunR,redkun:=ResidueClassField(KunR);
  leadk:=func<x,d|redk(x/piKf^d)>;      // reduction maps on pi^d/pi^(d+1)
  leadl:=func<x,d|redl(x/piLf^d)>;
  uk:=KR!(kR.1);                        // lift of residue field generators
  ul:=KunR!(kunR.1);
  rootsunity:=Roots(x^(#kR-1)-1);
  rootsunity:=[x[1]: x in rootsunity];  // roots of unity in K
  rootsred:=[redk(x): x in rootsunity];  // and their respective reductions

  npsi:=NPsi(K);

  piQ:=<UniformizingElement(M): M in FldList>;
  r:=Valuation(edeg,2)+1;    // uniformizers of intermediate flds Q_1,..,Q_r

  unitcondexp:=nchi-1;
  G<g>:=AbelianGroup(CyclicGroup(deg));

  vprint Rootno,2: Sprintf("n(psi)=%o, n(chi)=%o",npsi,nchi);

  if IsOdd(deg) then error "EpsFactor: Tame case should never be called!"; end if;

  function Chi(e,list,chi)
    e/:=rootsunity[Position(rootsred,redk(e))];
    chival:=G!0;
    repeat
      v:=Valuation(e-1);
      if (v gt unitcondexp) or (v ge Precision(K)) then break; end if;
      l:=Append([x: x in list[v]],e);
      N:=Nullspace(Matrix([Eltseq(leadk(x-1,v)): x in l]));
      w:=Eltseq(Basis(N)[1]);
      e/:=&*[l[j]^(Z!(w[j]/w[#w])): j in [1..#w-1]];
      chival+:=&+[chi[v][j]*(Z!(w[j]/w[#w])): j in [1..#w-1]];
    until false;
    return chipower*chival;
  end function;

  procedure ReduceElt(e,~list,~chi,~chival,~r)
    repeat
      v:=Valuation(e-1);
      if (v gt unitcondexp) or (v ge Precision(K)) then r:=0; return; end if;
      l:=Append([x: x in list[v]],e);
      N:=Nullspace(Matrix([Eltseq(leadk(x-1,v)): x in l]));
      if Dimension(N) gt 0 then
        w:=Eltseq(Basis(N)[1]);
        e*:=&*[l[j]^(Z!(w[j]/w[#w])): j in [1..#w-1]];
      else
        if chival ne G!0 then
          chival:=((Z!((deg+Eltseq(Chi(e^2,list,chi))[1])/2)))*g;
          vprint Rootno,3:Sprintf("Appending %o -> %o; square=%o",
              e,chival,Chi(e^2,list,chi));
        end if;
        Append(~list[v],e); Append(~chi[v],chival); r:=e; return;
      end if;
    until false;
  end procedure;

  procedure GenerateUnits(unitfun,~list,~chi,chival,numfound,~r)
    for i:=1 to 4*unitcondexp^2 do
    for j:=0 to Degree(lR)-1 do
      c:=chival;
      ReduceElt(unitfun(i,j),~list,~chi,~c,~r);
      if r ne 0 then numfound-:=1; end if;
      if numfound eq 0 then return; end if;
    end for;
    end for;
  end procedure;

  vprint Rootno,3: "Generating unit subgroup";

  list:=[[]: i in [1..unitcondexp]];
  chi:=list;
  QGen:=[KR!0: i in [1..r]];
  unrofs:=fdeg eq 1 select 0 else 1;
  for k:=r to 1 by -1 do
    num:=(k eq r) select unitcondexp*Degree(lR)-r+1 else 1;
    GenerateUnits(func<i,j|Norm(1+ul^j*piQ[k+unrofs]^i,K)>,~list,~chi,
      fdeg*(2^(k-1))*g,num,~QGen[k]);
    vprint Rootno,3 : [#l: l in list];
  end for;

  QGen[r]:=0;
  gens:=Reverse(Prune(QGen));
  vprint Rootno,3: Sprintf("Missing generators: %o",gens);
  vprint Rootno,3: Sprintf("of the form 1+uk*pi^: %o",[Valuation(x-1): x in gens]);

  if normonly ne 0 then
    return Eltseq(Chi(normonly,list,chi))[1] eq 0 select 1 else -1;
  end if;

  shft2:=(K!piK)^(-npsi-nchi);
  frac:=func<x|x-Floor(x)>;
  Tr:=func<x|Expand(Trace(trsign*x*shft2,Qp))>;
  TrFrac:=func<x|frac(Q!Tr(x))>;

  if brute then
    d:=unitcondexp;
    V:=VectorSpace(kR,d+1);
    sum:=0;
    vprint Rootno,2: "Going through" cat Sprint(#V) cat "elements";
    count:=0;
    for v in V do
      count+:=1;
      l:=Eltseq(v);
      if l[1] ne 0 then
        x:=&+[KR!l[i+1]*piK^i: i in [0..d]];
        c:=Chi(x,list,chi);
        t:=TrFrac(x);
        Sprintf("%o %o %o",x,c,Q!t);
        sum+:=exp(t)*exp(Eltseq(c)[1]/deg);
      end if;
    end for;

    vprint Rootno,2: "Epsilon     = " cat Sprint(ComplexField(18)!sum);
    vprint Rootno,3: "|Epsilon|^2 = " cat Sprint(Abs(sum^2));
    vprint Rootno,3: "Arg/Pi      = " cat Sprint(Arg(sum)/Pi(RealField()));

    eps:=sum;
    return eps/Abs(eps);
  end if;

  xi:=0;    /////// deligne's xi
  d:=nchi div 2;
  gf:=kR;
  for o:=0 to d-1 do
    e:=unitcondexp-o;
    b:=[uk^j*piK^o: j in [0..Degree(kR)-1]];
    t0:=[Tr(xi*(uk-1)) : uk in list[e]];
    t:=Matrix(GF(2),[[GF(2)!(2*Tr(b[j]*(uk-1))) : uk in list[e]]: j in [1..Degree(kR)]]);
    c:=[Eltseq(x)[1]: x in chi[e]];
    v:=[GF(2)!(2*(c[j]/deg-t0[j])): j in [1..Degree(kR)]];
    w:=Eltseq(Transpose(t)^(-1)*Transpose(Matrix(GF(2),[v])));
    xi+:=&+[uk^j*(Z!w[j+1])*piK^o: j in [0..Degree(kR)-1]];
    vprint Rootno,3: "Deligne's xi =" cat Sprint(xi);
  end for;

  vprint Rootno,2: "Deligne's xi = " cat Sprint(xi);

  if GetVerbose("Rootno") ge 3 then
    checklist:=[];
    frac:=func<x|Q!x-Floor(Q!x)>;
    for e:=unitcondexp-d+1 to unitcondexp do
    for j:=0 to Degree(kR)-1 do
      w:=uk^j*piK^e;
      chk:=(Z!Eltseq(Chi(1+w,list,chi))[1])/deg;
      Append(~checklist,<chk,TrFrac(xi*w)>);
    end for;
    end for;
    print checklist;
  end if;

  if IsEven(nchi) then
    xi_chi:=exp(Eltseq(Chi(-xi,list,chi))[1]/deg);
    xi_tr:=exp(TrFrac(-xi));
    xi_prod:=xi_chi*xi_tr;
  else
    m:=nchi div 2;
    xi_prod:=&+[(
      exp(Eltseq(Chi(u,list,chi))[1]/deg)*exp(TrFrac(u))
    ) where u is -xi*(1+piK^m*(KR!x)) : x in kR];
  end if;

  xi_arg:=Arg(xi_prod)/Pi(RealField());

  vprint Rootno,2: "Arg/Pi via xi = " cat Sprint(preps(xi_arg));

  // compatibility of local reciprocity: units vs piK
  pi2fdeg:=Chi(piK^fdeg/Norm(piLf,K),list,chi);
  frob:=Z!(Eltseq(pi2fdeg)[1]/fdeg)*g;
  frobzeta:=exp(Eltseq(frob)[1]/deg);
  chic:=frobzeta^(-npsi-nchi);

  eps:=xi_prod*chic;
  vprint Rootno,2: "Epsilon factor = " cat Sprint(preps(eps/Abs(eps)));
  return eps/Abs(eps),frobzeta,nchi,npsi,xi,Abs(eps),xi_prod;
end function;


function RootNumberAdditiveAt2(E,loc,k)
  _,vdelta,vcond,cp,kod,split:=Explode(loc);
  K:=BaseField(E);
  I:=ComplexField().1;
  c4,c6:=Explode(cInvariants(E));
  if Valuation(c4) ge Precision(K) then c4:=0; end if;
  if Valuation(c6) ge Precision(K) then c6:=0; end if;
  delta:=Discriminant(E);

  prec:=100;
  vprint Rootno,2: "Factoring the 3-torsion polynomial:";
  vprint Rootno,3: Deg8PolNE(K,c4,c6);
  
  repeat         // keep increasing precision until factorisation is happy
    try 
      Kbig:=ChangePrecision(K,prec);
      fpol:=Factorisation(Deg8Pol(Kbig,c4,c6): IsSquarefree:=true);
      fct:=[Degree(x[1]): x in fpol];
      vprint Rootno,2: Sprintf("precision=%o worked; degrees = %o",prec,fct);
      ok:=true;
    catch e
      if not IsSubstring("recision",e`Object) then
        error "Failed to factorize the 3-torsion polynomial";
      end if;
      vprint Rootno,2: e`Object;
      vprint Rootno,2: Sprintf("precision=%o failed",prec);
      ok:=false;
      prec:=2*prec;
    end try;
  until ok;

  fct:=Set(fct);
  if not (fct in {{2},{4},{8},{1,3},{2,6},{2,4},{2,3},{1,6}}) then
    fpol;
    error "Something is wrong with the factorization of the 3-torsion polynomial";
  end if;
  mi:=Min(fct);
  ma:=Max(fct);
  mu3:=IsEven(InertiaDegree(K,PrimeField(K)));
  del,rt:=IsPower(delta,3);

  //vprint Rootno,1: "  Gal(K(E[3])/K)=" cat ThreeTorsionExtType(E,fct);

  if ((mu3 and del) and (mi lt 8)) or ((mu3 and not del) and (mi le 2))
     or ((not mu3 and del) and (mi eq 8) and IsSquare(-3*(c4-12*rt))
     and IsSquare(-3*(c4^2+12*c4*rt+(12*rt)^2)))
  then // G is cyclic
    if mi eq 3 then
      vprint Rootno,1: "  Gal(K(E[3])/K)=C3 --> 1"; return 1;
    end if;
    _,_,e:=Factorisation(Deg8Pol(Kbig,c4,c6): Extensions:=true, IsSquarefree:=true);
    KY:=e[1]`Extension;
    rno:=IsNorm(KY,Kbig,-1);
    vprint Rootno,1: Sprintf("  Gal(K(E[3])/K)=C%o, (-1,K(E[3])/K) --> %o",
      Degree(KY,Kbig),rno);
    return rno;
  end if;

  run:=WhichRootAdjoined(K,ext<K|2>);
  if ((mu3 and del) and
        IsSquare(run*(c4-12*rt)) and IsSquare(run*(c4^2+12*c4*rt+(12*rt)^2))
      ) // sqrt(A),sqrt(B) generated quadratic unramified -> unr Q
      or ((not mu3) and (mi le 4)) // C2xC2, D6, D8 or Bo
  then // Induced from an unramified character
    // D8 or Q (unr)
    if (fct eq {4}) or (fct eq {8}) then
      K:=ext<Kbig|2>;
      _,xi:=IsSquare(K!-3);
      _,_,e:=Factorisation(Deg8Pol(K,Kbig!c4,Kbig!c6): Extensions:=true, IsSquarefree:=true);
      KY:=e[1]`Extension;
      rno:=IsNorm(KY,K,xi);
      vprint Rootno,1: Sprintf("  Gal(K(E[3])/K)=%o, (xi,K(E[3])/K) --> %o",
        fct eq {4} select "Di8" else "Qu8(unr)",rno);
      return rno;
    end if;
    // D6
    if (fct eq {2,3}) or (fct eq {1,6}) then
      vprint Rootno,1: "  Gal(K(E[3])/K)=D6 --> -1";
      return -1,"Di6"; // tamely ramified character has conductor 1
    end if;
    // C2xC2 or Borel
    _,X3:=AdjoinRoot(Kbig,Eltseq(Deg4Pol(Kbig,c4,c6)));
    KY:=AdjoinRoot(Kbig,c4 eq 0 select [6*c6,0,1] else [-X3,0,1]);
    K:=BaseField(KY);
    if RamificationDegree(KY,K) eq 1
      then error "Dihedral case: KY/K is unramified"; end if;
    // (3,y), y = y-coordinate of a K-rational 3-torsion point
    rno:=(-1)^(vcond div 2)*IsNorm(KY,K,3);
    vprint Rootno,1: Sprintf("  Gal(K(E[3])/K)=%o --> %o",
       del select "C2*C2" else "Bo12",rno);
    return rno;
    //return EpsFactor([K,KY]: normonly:=3),data;
  end if;

  if mu3 then // Qu, Sl
    K1,rootdelta:=AdjoinRoot(K,[-delta,0,0,1]);
    K2,rootA,rootB:=AdjoinRootsAB(K1,c4,c6,rootdelta: twist:=-3);
    K1,K2,K3,K4:=ExtensionTower(K,c4,c6,delta);
    rno:=Round(EpsFactor([K1,K2]) * EpsFactor([K2,K3,K4])
      * (-I)^(InertiaDegree(K,PrimeField(K))*(vcond+2*NPsi(K))));
    vprint Rootno,1: Sprintf("  Gal(K(E[3])/K)=%o --> %o",
       del select "Qu8(ram)" else "Sl24",rno);
    return rno;
  end if;

  Korg:=K;
  for i:=1 to 3 do
  try
    prec:=20*i;
    vprint Rootno,3: "Building GL2(F_3) extension tower in Sy/Gl case, prec="
      cat Sprint(prec);
    K:=i eq 3 select Korg else ChangePrecision(Korg,prec);
    c4:=K!c4;
    c6:=K!c6;
    delta:=K!delta;
    K1,K2,K2p,K3,K4:=TwistedExtensionTower(K,c4,c6,delta); // K1=K
    //Q:=RamifiedDescent(K2,K4: rnd:=true);
    Q:=RamifiedDescent2(K2,K2p,K3,K4: rnd:=true);
    EG:=LocalGoodModel(EllipticCurve([Q|a: a in aInvariants(E)]));
    ek:=EllipticCurve([ResidueField(Q)|x : x in aInvariants(EG)]);
    pinorm:=Norm(UniformizingElement(Q),K2);
    frob:=IsEven(vcond) select 1 else Integers()!
      TraceOfFrobenius(ek)/(-2)^((1+InertiaDegree(K,PrimeField(K)))/2);
    vprint Rootno,3: "TrFrob:" cat Sprint(TraceOfFrobenius(ek));
    if Abs(frob) ne 1 then
      error "Wrong trace of frobenius in Sy/GL case";  
    end if;
    rno:=Round(frob*EpsFactor([K1,K2])
	    * EpsFactor([K2,K2p,K3,K4]: piKf:=pinorm)
	    * (-I)^(InertiaDegree(K,PrimeField(K)) * (vcond + 2*NPsi(K))));
    vprint Rootno,1: "  Gal(K(E[3])/K)=Sy16/Gl48 --> " cat Sprint(rno);
    return rno;
  catch e
    if i eq 3 then
      error "Root number failed in the Sy16/Gl48 case at v|2";
    end if;
  end try;
  end for;
end function;
*/


function H(f,K: l:=2)
  f:=PR(K)!Eltseq(f);
  E:=EllipticCurve(f);

  loc:=LocalInformation(E);
  vtam:=Valuation(loc[4],l);      // contribution from the Tamagawa number
  if l ne 2 then return (-1)^vtam; end if;
  u:=Z!((Valuation(Discriminant(E))-loc[2])/12);
  res:=AbsoluteInertiaDegree(K);
//    Sprintf("tam=%o v(disc/mindisc)/12=%o residuedegree=%o",loc[4],u,res);
  return (-1)^(vtam+u*res);
end function;


function Hp(f,r,K: l:=2)
  prec:=Precision(K);
  R<x>:=PR(K);
  f:=Evaluate(R!Eltseq(f),x+r);
  zero,a4t,a2t,one:=Explode(Eltseq(f));
  vprint Rootno, 2: Sprintf("1=%o 0=%o f=%o prec=%o",one,zero,f,prec);
  assert Valuation(zero) ge prec div 2;    //! div 2: some sort of
  assert Valuation(one-1) ge prec div 2;   //  precision check
  fp:=x^3-2*a2t*x^2+(a2t^2-4*a4t)*x;
  return H(fp,K: l:=l);
end function;


function pAdicExtension(f)
  _,_,e:=Factorisation(f: Extensions:=true);
  F:=e[1]`Extension;
  r:=Roots(f,F)[1][1];
  return F,r;
end function;


function RootNumberPotGoodAt2(E,loc,k)
  K:=BaseField(E);
  minprec := Valuation(Discriminant(E))+16+6*Valuation(K!4); //!
  error if minprec gt Precision(K),
    Sprintf("Need at least precision %o to compute the local 2-adic root number",minprec);
  R<x>:=PR(K);
  a1,a2,a3,a4,a6:=Explode(aInvariants(E));
  f:=x^3+a2*x^2+a4*x+a6 + (a1*x+a3)^2/4;     // Put into short form y^2=f
  disc:=Discriminant(f);
  rts:=[r[1]: r in Roots(f)];

  rno:=(-1)^AbsoluteDegree(K);                // (-1)^[K_P:Q_2] contributes
  if #rts eq 3 then                                             // d = 1
    vprint Rootno,2: "[K(E[2]):K] = 1";
    return rno * H(f,K) * Hp(f,rts[1],K) * Hp(f,rts[2],K) * Hp(f,rts[3],K);
  elif #rts eq 1 then                                           // d = 2
    vprint Rootno,2: "[K(E[2]):K] = 2";
    f:=Evaluate(f,x+rts[1]);
    zero,a4t,a2t,_:=Explode(Eltseq(f));
    F,r:=pAdicExtension(x^2+a2t*x+a4t);
    return rno * H(f,K) * Hp(f,0,K) * Hp(f,0,F) * Hp(f,r,F);
  elif IsSquare(disc) then                                      // d = 3
    vprint Rootno,2: "[K(E[2]):K] = 3";
    F,r:=pAdicExtension(f);
    return rno * H(f,F) * Hp(f,r,F);
  else                                                          // d = 6
    vprint Rootno,2: "[K(E[2]):K] = 6";
    M:=pAdicExtension(x^2-disc);
    L,r:=pAdicExtension(f);
    F:=pAdicExtension(PR(L).1^2-disc);
    return rno * H(f,L) * Hp(f,r,L) * H(f,F) * Hp(f,F!r,F)
               * H(f,M: l:=3) * H(f,F: l:=3);
  end if;
end function;


function RootNumberPotGoodAt3(E,loc,k)
  _,vdelta,vcond,cp,kod,split:=Explode(loc);
  K:=BaseField(E);
  kod:=Sprint(kod);
  if kod eq "I0*" then             // I0* -> Kobayashi i)
    rno:=ResidueSymbol(k!-1)^(vdelta div 2);
  elif kod in ["III","III*"] then    // III,III* -> Kobayashi ii)
    rno:=ResidueSymbol(k!-2);
  elif kod in ["II","IV","II*","IV*"] then  // Kobayashi iii)
    _,E:=LocalInformation(E);
    delta:=Discriminant(E);
    _,_,b6,_:=Explode(bInvariants(E));
    if Valuation(b6) mod 3 eq 0 then
      error("RootNumberPotGoodAt3: 3|v(b6) for the minimal model");
    end if;
    rno:=ResidueSymbol(delta)*QuadraticNormSymbol(K,delta,b6)*
         ResidueSymbol(k!Valuation(b6))^vdelta*
         ResidueSymbol(k!-1)^(vdelta*(vdelta-1) div 2);
  elif kod eq "I0" then rno := 1;
  else
    error("Unexpected reduction type at v|3");
  end if;
  vprint Rootno,1: Sprintf("  Kobayashi's residue symbol --> %o",rno);
  return rno;
end function;


// from Rohrlich `Galois theory, elliptic curves and root numbers', Thm. 2

function RootNumberPotMultAt2(E,P)
  F:=BaseField(E);
  c4,c6:=Explode(cInvariants(E));

  if Type(F) ne FldPad then
    prec:=2*Valuation(2*c6,P)+1;
    K,FtoK:=Completion(F,P: Precision:=prec);
    ChangePrecision(~K,prec);
    c6:=K!FtoK(c6);
  else
    K:=F;
  end if;

  M:=pAdicExtension(PR(K).1^2+c6);
  vprint Rootno,2: "Potentially multiplicative at 2, computing (-c6,-1)";
  return IsNorm(M,K,-1);
end function;


// main root number function over a local/global field

function LocalRootNumberGen(E: P:="undefined", Halberstadt:=true)

  // Base field, res. field, delta (not nec. minimal), pot good/pot mult red
  F:=BaseField(E);
  if Type(F) eq FldRat then return RootNumber(E,P); end if;
  if Type(F) eq FldPad then
    k:=ResidueField(F);
    if Halberstadt and Degree(F,PrimeField(F)) eq 1 then
      // F=Qp => use Halberstadt/Q
      E:=EllipticCurve([Rationals()!PrimeField(F)!x: x in aInvariants(E)]);
      p:=Characteristic(k);
      rno:=RootNumber(E,p);
      vprint Rootno,1: Sprintf("  F=Q%o, using Halberstadt/Q --> %o",p,rno);
      return rno;
    end if;
    potmult:=Valuation(jInvariant(E)) lt 0;
    vsomedelta:=Valuation(Discriminant(E)) mod 12;
  else
    k:=ResidueClassField(P);
    potmult:=Valuation(jInvariant(E),P) lt 0;
    vsomedelta:=Valuation(Discriminant(E),P) mod 12;
  end if;
  p:=Characteristic(k);

  // additive reduction with p>3 -> cyclic inertia -> neat formula
  if (p gt 3) and (not potmult) then
    rno:=(-1)^((#k mod 24)*vsomedelta div 12);
    vprint Rootno,1:Sprintf("v|%o>3 and pot. good red. v(delta)=%o #k=%o --> %o",
      p,vsomedelta,#k,rno);
    return rno;
  end if;

  // In all other cases, need minimal model
  if Type(F) eq FldPad
    then loc,model:=LocalInformation(E);
    else loc,model:=LocalInformation(E,P);
  end if;
  _,vdelta,vcond,cp,kod,split:=Explode(loc);
  vprint Rootno,1: Sprintf("v|%o %o v(N)=%o v(delta)=%o",p,kod,vcond,vdelta);

  if vcond eq 0 then return 1; end if;

  if potmult then
  if vcond gt 1 then          // additive, potentially multiplicative
    rno:=(p eq 2) select RootNumberPotMultAt2(E,P) else ResidueSymbol(k!-1);
    vprint Rootno,1: Sprintf("Potentially mult. (-1,K) --> %o",rno);
    return rno;
  elif split then             // split multiplicative
    vprint Rootno,1: Sprintf("  %o split --> -1",Sprint(kod)); return -1;
  else                        // nonsplit
    vprint Rootno,1: Sprintf("  %o non-split --> 1",Sprint(kod)); return 1;
  end if;
  end if;

  if Type(F) ne FldPad then
    if p eq 2
      then prec:=vdelta+16+6*Valuation(F!4,P); //!
      else prec:=vdelta+2;
    end if;
    K,FtoK:=Completion(F,P: Precision:=prec);
    ChangePrecision(~K,prec);
    E:=EllipticCurve([K!FtoK(x): x in aInvariants(model)]);
  end if;

  return (p eq 2) select RootNumberPotGoodAt2(E,loc,k)
                  else   RootNumberPotGoodAt3(E,loc,k);
end function;


// Definitions for the intrinsics:

intrinsic RootNumber(E::CrvEll[FldPad]: halberstadt:=true) -> RngIntElt
{Local root number (+1/-1) of an elliptic curve over a p-adic field}
  return LocalRootNumberGen(E: Halberstadt:=halberstadt);
end intrinsic;

intrinsic LocalRootNumber(E::CrvEll[FldPad]: halberstadt:=true) -> RngIntElt
{Local root number (+1/-1) of an elliptic curve over a p-adic field}
  return LocalRootNumberGen(E: Halberstadt:=halberstadt);
end intrinsic;

intrinsic RootNumber(E::CrvEll[FldNum], P::RngOrdIdl) -> RngIntElt
{Local root number (+1/-1) of E at a prime ideal P}
  return LocalRootNumberGen(E: P:=P);
end intrinsic;

intrinsic LocalRootNumber(E::CrvEll[FldNum], P::RngOrdIdl) -> RngIntElt
{Local root number (+1/-1) of E at a prime ideal P}
  return LocalRootNumberGen(E: P:=P);
end intrinsic;

intrinsic LocalRootNumber(E::CrvEll[FldRat], p::RngIntElt) -> RngIntElt
{Local root number (+1/-1) of E at a prime ideal P}
 return RootNumber(E,p); end intrinsic; // MW, utility func for FldRat

intrinsic RootNumber(E::CrvEll[FldNum]) -> RngIntElt
{Global root number (+1/-1) of an elliptic curve E defined over
 a number field K. This is the product of local root numbers over all
 places (-1 from each infinite place), and is the conjectural sign in the
 functional equation relating L(E/K,s) to L(E/K,2-s)}
  K:=BaseField(E);
  if Type(BaseField(K)) ne FldRat then
    K:=AbsoluteField(K);
    E:=EllipticCurve([K!a: a in aInvariants(E)]);
  end if;
  r1,r2:=Signature(K);
  vprint Rootno,1: "&*(v|infty) --> (-1)^" cat Sprint(r1+r2);
  rno:=(-1)^(r1+r2)* // from infinite places
    &*[Integers()|LocalRootNumber(E,x[1]): x in LocalInformation(E)|x[3] ne 0];
  vprint Rootno,1: "Global root number --> " cat Sprint(rno);
  return rno;
end intrinsic;

intrinsic LocalRootNumbers(E::CrvEll[FldNum]) -> SeqEnum
{The bad primes and local root numbers of E.
 The primes at infinity (each real place gives -1) are not included.}
 K:=AbsoluteField(BaseField(E)); E:=EllipticCurve([K!a: a in aInvariants(E)]);
 return [<x[1],LocalRootNumber(E,x[1])> : x in LocalInformation(E)|x[3] ne 0];
end intrinsic;

intrinsic LocalRootNumbers(E::CrvEll[FldRat]) -> SeqEnum
{The bad primes and local root numbers of E.
 The prime at infinity (which gives -1) is not included.}
 return [<p,RootNumber(E)> : p in BadPrimes(E)]; end intrinsic;


/*** Previous script by Mark Watkins
intrinsic RootNumber(E::CrvEll[FldNum],P::RngOrdIdl) -> RngIntElt
{The local root number of the elliptic curve E
(defined over a number field) at the prime ideal P.
(Not implemented for P dividing 2.)}
 p := Factorisation(Norm(P))[1][1];
 require IsOdd(p) : "P must be odd";
 F:=BaseRing(E); l,M:=LocalInformation(E,P); C,toC:=Completion(F,P); K:=l[5];
 a1,_,a3:=Explode(aInvariants(M)); M:=rst_transform(M,[0,-a1/2,-a3/2,1]);
 vd:=Valuation(Discriminant(M),P); vj:=Valuation(jInvariant(M),P);
 if vj lt 0 then c6:=cInvariants(M)[2]; v6:=Valuation(c6,P);
  if v6 eq 0 then if IsSquare(toC(-c6)) then return -1; else return 1; end if;
  elif IsSquare(toC(-1)) then return +1; else return -1; end if; end if;
 K:=KodairaSymbol(M,P); KS:=KodairaSymbol;
 if K eq KS("I0") or K eq KS("I0*") then
  if IsSquare(toC(-1)) then return 1;
  elif vd mod 4 eq 0 then return 1; else return -1; end if; end if;
 if K eq KS("III") or K eq KS("III*") then
  if IsSquare(toC(-2)) then return 1; else return -1; end if; end if;
 for u := 1 to 10000 do
  a6 := aInvariants(M)[5];
  if a6 ne 0 and Valuation(a6,P) mod 3 ne 0 then break; end if;
  M:=rst_transform(M,[1,0,0]); end for;
 vd:=Valuation(Discriminant(M),P); vj:=Valuation(jInvariant(M),P);
 if K eq KS("II") or K eq KS("II*") or K eq KS("IV") or K eq KS("IV*") then
  if IsSquare(toC(Discriminant(M))) then delta:=1; else delta:=-1; end if;
  delta:=delta*HilbertSymbol(Discriminant(M),aInvariants(M)[5],P);
  vc:=Valuation(aInvariants(M)[5],P);
  if vd mod 2 eq 1 and not IsSquare(toC(vc)) then delta:=-delta; end if;
  if not IsSquare(toC(-1)) and (vd mod 4 eq 2 or vd mod 4 eq 3) then
   delta:=-delta; end if; return delta; end if;
  require false : "Something is wrong with the code in the case of Kodaira symbol", K;
end intrinsic;
***/
