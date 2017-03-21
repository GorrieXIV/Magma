freeze;

/*******************************************************************
L-Series of hyperelliptic curves

implements

  intrinsic LSeries(C::CrvHyp: Precision:=0, LocalData:=[* *])
  intrinsic Conductor(C,P) / ConductorExponent(C)
  intrinsic HodgeStructure(C)
  intrinsic EulerFactor(C,P)
  
  over Q, p-adic fields and number fields

version 1: T+V Dokchitser, Aug 2010
  assumes the curve has a global regular Weierstrass model
version 2: TD+VD, Sep 2010
  L-series for arbitrary hyperelliptic curves, using RegularModel machinery
  troublesome cases remaining: v_p(delta)>=12 for some p
version 2: TD, Nov 2014
  Use semistable models away from 2, added general p-adics and number fields
  only troublesome case remaining: v_2(delta)>=12

*******************************************************************/


declare attributes CrvHyp: Conductor, RootNumber, LocalData;

declare verbose CrvHyp,3;


// Semistable model data

component:=recformat<
  D,     // A group of disks that determines the component {{1,2},{5,6}}
  sign,  // 0 if the group determines one component, 
         // +1/-1 otherwise to distinguish between them
  r,     // root index of the root that is sent to 0
  R,     // root index of the root that is sent to 1
  nu,    // minimal coefficient valuation of f( (R-r)X+r )
  sq,    // square part of f((R-r)X+r)/pi^nu mod pi
  Ck,    // curve y^2 = f((R-r)X+r)/pi^nu/sq^2  mod pi  over the residue field
  IS,    // inertia stabilizer of the component
  A      // Hom(IS->Aut(Ck)), inertia action on the component
>;

point:=recformat<
  i,     // index of the component on which P lies and as not at infinity 
  x,     // x-coordinate (in the residue field or an extension thereof)  
  y      // y-coordinate (also)
>;

localcurvedata:=recformat<
  C,             // C  = parent curve
  K,             // K  = base field
  P,             // P  = prime at which we are working
  conductor,     // conductor exponent
  mindisc,       // valuation of minimal discriminant (/Q only)
  tamecond,      //   = tame conductor exponent  
  wildcond,      //   + wild conductor exponent 
  localfactor,   // local factor in Q[T]
  degree,        //   computed up to this degree
  rootnumber,    // local root number
  ///// p=2 ////////
  R,             // regular model at p=2
  //// p<>2 ///////
  p,             // p  = residue characteristic 
  Qp,            // Qp = local base field (actually some extension of Q_p)
  f,             // f  = polynomial for y^2=f(x)
  n,             // n  = Degree(f)
  OK,            // OK = ring of integers of K
  F,             // K  = splitting field of f
  pi,            // pi = uniformizer of K
  OF,            // O  = O_K ring of integers
  k,q,           // k  = k_K residue field, order q, 
  red,           //      red = reduction map O->k
  r,             // r  = [r_1,...,r_n] roots of f in K
  G,             // G  = Gal(K/Q), decomposition group inside Sym(n)
  I,             // I  = inertia subgroup of G
  Gact,          // map G->Aut(K/Q) 
  ramgps,        // higher ramification subgroups of I [...,<G_i,i>,...]
  Frob,          // Frobenius element of G
  Co,            // Co = [Co_1,...,Co_m] components of the semistable model
                 //      of type `component'
  Pt,            // Pt = points of intersections of components 
                 //     [...,[<c1,x1,y1>,<c2,x2,y2>],...]
                 //     point x1,y1 on Co[c1] = point x2,y2 on Co[c2]
  A,A0,          // Galois representation H^1_et(C) of type GalRep
                 // and A0 some perm char of G
  Gr,GtoGr            
>;


import "../Crv/RegModel/interface.m" : 
  number_of_points_on_special_fibre, splitting_degrees;
import "../../Ring/RngLoc/splitfield.m":
  GaloisToPermutation,DelSpaces,MinimizedGenerators;


////////////////// mmylib stuff


Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
_Degree:=Degree;

function DelSymbols(s,delsymb) 
  if Type(s) ne MonStgElt then s:=Sprint(s); end if;
  if Type(delsymb) eq MonStgElt then delsymb:=Eltseq(delsymb); end if;  
  s:=[c: c in Eltseq(s) | not (c in delsymb)];
  return IsEmpty(s) select "" else &cat s;
end function;

function Last(v)
  try return v[#v]; catch e; end try;
  try w:=Eltseq(v); return w[#w]; catch e; end try;
  error "Last: unrecognized type";
end function;

function PrintField(F)
 if AbsoluteDegree(F) eq 1 then
  return Sprintf("Q%o[%o]",Characteristic(ResidueClassField(Integers(F))),Precision(F)); 
 end if;
 B:=BaseField(F);
 if RamificationDegree(F,B) eq 1 then 
   return Sprintf("ext<%o|%o>",PrintField(B),Degree(F,B));
 end if;
 R<x>:=PR(Integers(B),1); // Mark's hack, even though F is p-adic
 return Sprintf("ext<%o|%o>",PrintField(B),
		DelSpaces(Evaluate(DefiningPolynomial(F),x)));
end function;

CharacterCharPoly:=func<c,g|
  CharacteristicPolynomialFromTraces([c(g^i): i in [1..c[1]]])>;

function SubMin(G,gens)
 H:=sub<G|gens>; H:=sub<G|MinimizedGenerators(H)>; return H;
end function;

function BaseChangeCurve(C,m)
  f,g:=HyperellipticPolynomials(C);
  f:=Polynomial([Parent(m(0))| m(c): c in Coefficients(f)]);
  g:=Polynomial([Parent(m(0))| m(c): c in Coefficients(g)]);
  return HyperellipticCurve(f,g);
end function;

function PrintCurve(C)
  K:=BaseField(C);
  //  U<x>:=PR(K);
  s:=Sprint(C);
  p1:=Position(s," defined by ");
  p2:=Position(s," over ");
  if p1*p2 eq 0 then return s; end if;
  return DelSpaces(s[[p1+12..p2]]);
end function;

function PrintIdeal(P)
  if Type(P) eq RngOrdIdl then 
    return Sprintf("P|%o",Characteristic(ResidueClassField(P))); 
  else 
    return P; 
  end if;
end function;
  
procedure SortBy(~L,f: sign:=1)
  if Type(L) eq SetEnum then
    L:=SetToSequence(L);
  end if;
  Sort(~L,func<a,b|fa lt fb select -sign else (fa eq fb select 0 else sign)
                   where fa is f(a) where fb is f(b)>);
end procedure;                


function SquarefreePartWithLead(f)
  fct:=Factorisation(f);
  Sq:=&*[Parent(f)| F[1]^(F[2] div 2): F in fct];
  return f div Sq^2, Sq;
end function;

///////////////////////////////////////////////////////////////////


function PrintPadic(r)
  K:=Parent(r);
  O:=IntegerRing(K);
  K:=FieldOfFractions(O);
  r:=K!r;
  k<z>,m:=ResidueClassField(O);
  pi:=UniformizingElement(K);
  v:=Valuation(r);
  if v gt 0.8*Precision(K) then return "0"; end if;
  u:=m(r/pi^v);
  if (u ne z) and not IsCoercible(Z,u) and (#k lt 100) and 
    exists(i){i: i in [1..#k-1] | z^i eq u} then u:="z^"*Sprint(i); end if;
  s:=Sprintf("%o*pi^%o",u,v);
  return s;
end function;


function pointact(data,P,sigma,piquo,frobexp)
  Co:=data`Co;
  r:=data`r;
  red:=data`red;
  C1:=Co[P`i];
  C2list:=[C: C in Co | C`D eq Dsigma] where Dsigma is (C1`D)^sigma;
  C2:=C2list[1];  
  assert C1`nu eq C2`nu;
  kX:=Parent(P`x);
  kY:=Parent(P`y);  
  p:=Characteristic(kX);
  Xsigma:=(P`x)^(p^frobexp);
  Ysigma:=(P`y)^(p^frobexp);
  r1:=r[C1`r]; R1:=r[C1`R];
  r2:=r[C2`r]; R2:=r[C2`R];
  r1sigma:=r[(C1`r)^sigma];
  R1sigma:=r[(C1`R)^sigma];
  Xnew:=red((R1sigma-r1sigma)/(R2-r2)) * Xsigma + red((r1sigma-r2)/(R2-r2));

  U<t>:=PR(kX);
  tnew:=red((R1sigma-r1sigma)/(R2-r2)) * t + red((r1sigma-r2)/(R2-r2));
  num:=U![c^(p^frobexp): c in Eltseq(C1`sq)];
  den:=Evaluate(C2`sq,tnew);
  tcorr:=Evaluate(num/den,P`x);

  Ynew:=piquo^(C1`nu div 2) * tcorr * Ysigma;    //!
  if (C2`sign ne 0) and (C2`sign ne Ynew) then
    C2:=C2list[2]; 
    assert C2`sign eq Ynew;
  end if;
  Pnew:=rec<point|i:=Position(Co,C2), x:=Xnew, y:=Ynew>;
  vprint CrvHyp,3: frobexp,DelSpaces([C1`r,C1`R]),"->",DelSpaces([C2`r,C2`R]),
    [* P`i,P`x,P`y *], [* Pnew`i,Pnew`x,Pnew`y *];
  return Pnew;
end function;


function pointpermutation(Pts,F)
  perm:=[];
  for i:=1 to #Pts do
    Pnew:=F(Pts[i]);
    assert exists(j){j: j in [1..#Pts] | 
      (Pts[j]`i eq Pnew`i) and (Pts[j]`x eq Pnew`x) and (Pts[j]`y eq Pnew`y)};
    Append(~perm,j);  
  end for;
  return Sym(#Pts)!perm;
end function;


function roottopoint(data,i)
  Co:=data`Co;
  r:=data`r;
  assert exists(C){C: C in Co | {i} in C`D};
  ur:=r[C`r];
  uR:=r[C`R];
  alpha:=r[i];
  x:=data`red((alpha-ur)/(uR-ur));
  f:=HyperellipticPolynomials(C`Ck);
  y:=Evaluate(f,x);
  assert y eq 0;
  return rec<point|i:=Position(Co,C), x:=x, y:=y>;
end function;


function eig(M)
  eigorders:=[];
  for F in Factorisation(CharacteristicPolynomial(M)) do
    f,m:=Explode(F);
    Fq<r>:=ext<GF(2)|f>;
    eigorders cat:= [Order(r): i in [1..m*Degree(f)]];
  end for;
  return eigorders;
end function;


function CharacterFromStabilizers(G,S);  
  CG:=CharacterRing(G);
  fixedpts:=[#[U: U in S | g[3] in U]: g in ConjugacyClasses(G)];
  char:=CG!fixedpts;
  assert IsCharacter(char);
  return char;
end function;


procedure SemilinearCompose(q1,a1,b1,q2,a2,b2,~q,~a,~b)
  q:=q1*q2;
  a:=a2*a1^q2;
  b:=a2*b1^q2+b2;
end procedure;


function FixedPointCount(C,a,b,c,q,degree)
  vprint CrvHyp,2: "Fixed point count",PrintCurve(C),"under",
    Sprintf("X->%o*X^%o+%o, Y->%o*Y^%o, deg=%o",a,q,b,c,q,degree);

  g:=Genus(C);
  if (degree eq 0) or (g eq 0) then return PR(Q)!1,true; end if;
  k:=BaseField(C);
  
  vprint CrvHyp,2: "k:",DelSpaces(MinimalPolynomial(k.1)),"order",Order(k.1);
  f,f2:=HyperellipticPolynomials(C);
  assert f2 eq 0;

  if (a eq 1) and (b eq 0) and (c eq 1) then
    k0:=sub<k|Eltseq(f)>;
    k1:=#k0 eq q select k0 else ext<k0|Round(Log(#k0,q))>;
    f1:=Polynomial([k1!k0!c: c in Eltseq(f)]);
    C:=HyperellipticCurve(f1);
    if degree ge g then
      vprint CrvHyp,2: "Descending the curve and computing Euler factor over F_"*Sprint(q);
      loc:=PR(Q)!EulerFactor(Jacobian(C));
      full:=true;
    else 
      vprint CrvHyp,2: "Descending the curve and counting points over F_"*Sprint(q);
      T:=PowerSeriesRing(Q,degree+1).1;
      ser:=Exp(&+[#BaseChange(C,ext<k|n>)/n*T^n: n in [1..degree]]);
      loc:=PR(Q)!Eltseq(ser * (1-T) * (1-q*T));
      full:=false;
    end if;  
    vprint CrvHyp,2: "loc =",loc;
    return loc,full;
  end if;

  vprint CrvHyp,2: "Semi-linear fixed point count over F_"*Sprint(q);
 
  a:=k!a; b:=k!b; c:=k!c;

  // store a,b,c for ith powers of Frobenius, i=1..g

  aa:=[a: i in [1..g]];          
  bb:=[b: i in [1..g]];
  cc:=[c: i in [1..g]];
  for i:=2 to g do
    SemilinearCompose(q^(i-1),aa[i-1],bb[i-1],q,a,b,~qprod,~aa[i],~bb[i]);
    SemilinearCompose(q^(i-1),cc[i-1],0,q,c,0,~qprod,~cc[i],~dummy);
  end for;

  // y=0 -> GCD ( f, ax^q+b-x)
  
  R:=PR(k); x:=R.1;
  U,m:=quo<R|f>;
  zero_count:=func<i|Degree(GCD(f,(aa[i]*m(x)^(q^i)+bb[i]-m(x))@@m))>;

  // y=infty -> c a_(2g+2) ^ ((q-1)/2) = a^(g+1)   => 2 pts, =0 => 1 pt
  //   from pts at infinity plus minus (1,sqrt(a_(2g+2)),0) under (x,y,z)->(ax^q+bz^q,cy^q,z^q)
  //! -> TeX
 
  u:=Coefficient(f,2*g+2);
  inf_count:=func<i|u eq 0 select 1 else (u^((q^i-1) div 2) eq aa[i]^(g+1)/cc[i] select 2 else 0)>;
  
  // y<>0,infty -> c f^((q-1)/2)=1, ax^q+b=x, y^2=g(x)
  
  function nonz_count(i)
    h:=aa[i]*x^(q^i)+bb[i]-x;
    U,m:=quo<R|h>;
    return 2*Degree(GCD(h,(cc[i]*m(f)^((q^i-1) div 2)-1)@@m));
  end function;

  function count(i)
    zer:=zero_count(i);
    inf:=inf_count(i);
    non:=nonz_count(i);
    vprint CrvHyp,2:Sprintf("count(%o): zero=%o inf=%o nonz=%o",i,zer,inf,non);
    return zer+inf+non;
  end function;
  
  RSQ:=PowerSeriesRing(Q,g+1); T:=RSQ.1;
  RQ:=PR(Q); _<x>:=PR(Q,1); // Mark's Hack
  F:=Exp(-&+[(q^i+1-count(i))/i*T^i: i in [1..Min(g,degree)]]);   
  if degree lt g 
    then loc:=RQ![Coefficient(F,i): i in [0..degree]]; full:=false;
    else loc:=RQ!([Coefficient(F,i): i in [0..g]] cat 
              [q^(i-g)*Coefficient(F,2*g-i): i in [g+1..2*g]]); full:=true;
  end if;
  vprint CrvHyp,2: "loc =",Evaluate(loc,x);
  return loc,full;  
end function;


function GeometricQuotient(C,I,D,act,GtoGr,rootonCk)
  k:=BaseField(C);
  fred:=HyperellipticPolynomials(C);
  
  S:=Sylow(I,2);         
  assert IsCyclic(S);
  elt2:=exists(sigma){sigma: sigma in S | [a,c] in {[k|-1,1],[k|-1,-1],[k|1,-1]}  
    where a,b,c is act(sigma)};
  //">>",DelSpaces([[a,b,c] where a,b,c is act(sigma): sigma in S]);

  if elt2 then
    a,b,c:=act(sigma);
    vprint CrvHyp,2: "Elt of order 2 acting:",a,b,c;
    if (a eq 1) and (b eq 0) and (c eq -1) then 
      return HyperellipticCurve(PR(k).1),true;  // Hyperelliptic involution -> P^1
    end if;     
    Yaction:=c ne 1;         // I acts non-trivially on the Y-coordinate?
    if Yaction then 
      SigmaPrime:={};
      vprint CrvHyp,2: DelSpaces([[a,b,c] where a,b,c is act(g): g in I]);
      for g in I do
        ag,bg,cg:=act(g);                    
        if ag eq 1 then continue; end if;    // Identity (ignore) or x->x+b (no fixed pts)
        Include(~SigmaPrime,bg/(1-ag));      // Solve ax+b = x
      end for;          
      lambda:=&*[k|a^n: a in SigmaPrime] where n is Z!(#I/2/#SigmaPrime);
      lambda:=lambda^2;   //! Check
      vprint CrvHyp,2: "lambda =",lambda;
    end if;      
  else
    Yaction:=false;
  end if;
  c:=LeadingCoefficient(fred) * (Yaction select (PR(k).1-lambda) else 1);

  OddDisks:=[d: d in D | IsOdd(#d)];
  m:=#OddDisks;
  actOD:=hom<I->Sym(m)|sigma:->Sym(m)![Position(OddDisks,OddDisks[i]^GtoGr(sigma)): i in [1..m]]>;
  quotientroots:=[];
  for o in Orbits(actOD(I)) do
    rootorbit:=[rootonCk(Representative(OddDisks[i])): i in o];
    assert forall{r: r in rootorbit | Evaluate(fred,r) eq 0};
    Append(~quotientroots,&*rootorbit);
  end for;
  quotientf:=c* &*[PR(k).1-a: a in quotientroots]; 
  Qc:=HyperellipticCurve(quotientf);
  return Qc,Yaction;
end function;


function LocalDataWithSemistableModel
(C: degree:=Infinity(), AllSubgroupInfo:=false)  
  // Local data at odd primes using semistable reduction
  // with local factor computed up to degree given by "degree" 

  curve:=C; // C: y^2 = f(x) hyperelliptic curve over K
  K:=BaseField(C);
  assert Type(K) eq FldPad; 
    FC,GC:=HyperellipticPolynomials(C);
  f:=FC+GC^2/4;
  n:=Degree(f);
  g:=Genus(C);
  degree:=Min(degree,2*g);
  vprintf CrvHyp,1: "Local data C/%o g=%o n=%o degree=%o\n",
    PrintField(K),g,n,degree;
  // F = splitting field of f

  if assigned C`LocalData then 
    D:=C`LocalData[1];
    K            :=D`K; 
    A            :=D`A0; 
    G<[Ggens]>   :=D`G;
    r            :=D`r;
    Gr<[Grgens]> :=D`Gr;
    GtoGr        :=D`GtoGr;
  else 
    vprint CrvHyp,1: "Computing semistable model";
    F0:=SplittingField(f: Std:=false);  // F = Splitting field of f /K
    f2:=DefiningPolynomial(ext<K|2*InertiaDegree(F0,K)>);
    R:=PR(K); X:=R.1;
    rdeg:=RamificationDegree(F0,K);
    tdeg:=rdeg div p^Valuation(rdeg,p) 
      where p is Characteristic(ResidueClassField(Integers(K)));
    f3:=X^(2*tdeg)-UniformizingElement(K);
    vprint CrvHyp,2: "Biquadratic extension";
    A:=GaloisRepresentations(f2*f3*f)[1];                   // Biquadratic ext
    G<[Ggens]>:=Group(A);                                   // G
    r:=[r[1]: r in Roots(f,A`F)];
    assert #r eq n;
    Grgens:=[GaloisToPermutation(A`act(g),r): g in Ggens];
    Gr<[Grgens]>:=sub<Sym(n)|Grgens>;                       // Gr
    GtoGr:=hom<G->Gr|Grgens>;
    assert #Kernel(GtoGr) ge 4;  // 1 -> ker -> G -> Gr -> 1
   end if;

  OK:=Integers(K);
  kK:=ResidueClassField(OK);
  F:=Field(A);
  OF:=Integers(F);
  pi:=UniformizingElement(F);
  k<z>,red:=ResidueClassField(OF);
  q:=#k;
  p:=Characteristic(k);

  I<[Igens]>:=A`I;
  ramgps:=A`ramgps;
  Frob:=A`Frob;
  Frobr:=GtoGr(Frob);
  Gact:=A`act;

  error if IsEven(p), "p must be odd in LocalDataWithSemistableModel";

  tamecharacter:=map<G->k|x:->red(Gact(x)(pi)/pi)>;
  
  vprintf CrvHyp,1: "G=%o I=%o order(Frob)=%o G(rts)=%o ramgps=%o\n",
    GroupName(G),GroupName(I),Order(Frob),GroupName(Gr),
    DelSymbols([<GroupName(D[1]),D[2]>: D in ramgps]," \"");       

  // Action of prime-to-2 inertia (I_odd) on the Tate module
  
  Iodd:=NormalSubgroups(I: OrderEqual:=#I div 2^Valuation(#I,2))[1]`subgroup;
  V:=VectorSpace(GF(2),2*g);
  P:=[V|0] cat Basis(V) cat [V|[-1: j in [1..2*g]]];    // images of P_i-P_1
  act:=func<sigma|
	    Matrix([P[j^GtoGr(sigma)]-P[1^GtoGr(sigma)] : j in [2..2*g+1]])>;

    //! also for n=2*g+2?
  TwoTors:=GModule(G,[Parent(act(G.0)) | act(sigma): sigma in Ggens]);
  CCIodd:=[c[3]: c in ConjugacyClasses(Iodd)];
  charIodd:=CharacterRing(Iodd)!
    [&+[MoebiusMu(e)/EulerPhi(e): e in eig(act(c))]: c in CCIodd];
  
  // Wild exponent of the conductor
  
  lastindex:=1;
  wildcond:=0;                               
  g0:=#I;
  for Gn in ramgps do
    if Gn[2] eq 1 then continue; end if;  
    coinvdim:=2*g-InnerProduct(Restriction(charIodd,Gn[1]),
              PrincipalCharacter(Gn[1]));
    if coinvdim eq 0 then break; end if;
    wildcond +:= coinvdim * (Gn[2]-lastindex) * #(Gn[1]) / g0;
    lastindex:=Gn[2];
  end for;
  wildcond:=Z!wildcond;
  
  // No invariants of I_odd => local factor = 1 
  
  trivs:=InnerProduct(charIodd,PrincipalCharacter(Iodd));
  if trivs eq 0 then 
    tamecond:=2*g;
    conductor:=tamecond+wildcond;
    localfactor:=PR(Q)!1;
  end if;
  
  // Bosch's Kreise

  vprint CrvHyp,2: "v(r_i-r_j) matrix:";
  vprint CrvHyp,2: Matrix([[Valuation(r[i]-r[j]): i in [1..n]]: j in [1..n]]);
  
  valrange:={Valuation(ri-rj): ri,rj in r | ri ne rj};
  Kr:={{i}: i in [1..n]};
  for i in [1..n], vmax in valrange do
    D:={j: j in [1..n] | Valuation(r[i]-r[j]) ge vmax};
    Include(~Kr,D);  
  end for;
  Kr:=SetToSequence(Kr);
  
  // Going up 
  
  KrU:=[];
  for D in Kr do
    if #D eq n 
      then U:={Z|};
      else Ups:=[U: U in Kr | (D subset U) and (D ne U)];
           min,j:=Min([#U: U in Ups]);
           U:=Ups[j];
    end if;
    Append(~KrU,U);
  end for;
  
  // Benachbarter Kreise -> components (or component pairs),
  // top one first
  
  CompD:=[{Kr[j]: j in [1..#Kr] | KrU[j] eq U}: U in Set(KrU) | U ne {}];
  SortBy(~CompD,func<D|-&+[#d: d in D]>); 
  
  PK<XK>:=PR(F);
  Pk<Xk>:=PR(k);
  fK:=PK!f;
  CK:=HyperellipticCurve(fK);
  P1:=Curve(ProjectiveSpace(k,1));

  CompDAct:=hom<G->Sym(#CompD)|                         // G acting on disks
    [[Position(CompD,CompD[i]^GtoGr(g)): i in [1..#CompD]]: g in Ggens]>; 
  CompDorbits:=Orbits(CompDAct(G));   
  CompDorbitReps:=[Z| Rep(x): x in CompDorbits];
  
  Components:=[* *];

  Pts:=[]; 
  
  for Dindex:=1 to #CompD do
    D:=CompD[Dindex];
    DE:=SetToSequence(D);
    i1:=Min({Min(U): U in D});                           // r
    i2:=Min({Min(U): U in D | not (i1 in U)});           // R
    l1:=r[i1];
    l2:=r[i2];
    fsubx:=Evaluate(fK,(l2-l1)*XK+l1);                   // x' = (x-r)/(R-r)
    nu:=Min([Valuation(c): c in Eltseq(fsubx)]);         // x = r+(R-r)x'
    assert IsEven(nu);
  
    // components 
  
    fsubx/:=pi^nu;
    CKD:=HyperellipticCurve(fsubx);
    rhsk,sqpart:=SquarefreePartWithLead(Pk!fsubx);
    hasup:=exists(up){i: i in [1..#CompD] | S in CompD[i]} 
      where S is &join D;
    numcomp:=Degree(rhsk) eq 0 select 2 else 1;   

    IStab:=SubMin(I,[sigma: sigma in I | D^GtoGr(sigma) eq D]);

    co:=rec<component|
      D:=D,       // A group of disks determining the component;  {{1,2},{5,6}}
      r:=i1,      // root index of the root that is sent to 0;      1 
      R:=i2,      // root index of the root that is sent to 1;            5
      nu:=nu,     // minimal coefficient valuation of f( (R-r)X+r )
      sq:=sqpart, // square part of f((R-r)X+r)/pi^nu mod pi
      IS:=IStab   // inertia stabilizer of the component
    >;

    if numcomp eq 2 then                 // Two components
      sqrtc:=Sqrt(k!rhsk);
      co`sign:=sqrtc;
      co`Ck:=P1;
      Append(~Components,co); 
      co`sign:=-sqrtc;
      Append(~Components,co); 
      Inf:=[#Components-1,#Components];
      vprint CrvHyp,1: Sprintf("%-2o %o over F_%o, genus %o\n   nu=%o D=%o IStab=%o",
        Dindex,"P1+P1",#k,Genus(co`Ck),nu,DelSpaces(D),DelSpaces(Generators(IStab)));
      //vprint CrvHyp,1: Sprintf("[%o] (%o,%o)  %-20o %-20o %o",nu,
      //  #Components-1,#Components,DelSpaces(D),"P1+P1",DelSpaces(Generators(IStab)));
    else                                      // One component 
      co`sign:=0;
      co`Ck:=HyperellipticCurve(rhsk);        
      Append(~Components,co); 
      if IsEven(Degree(rhsk)) then
        Inf:=[#Components,#Components];     // pts at infty
      else 
        Inf:=[#Components];
      end if;
      vprint CrvHyp,1: Sprintf("%-2o %o over F_%o, genus %o\n   nu=%o D=%o IStab=%o",
        Dindex,PrintCurve(co`Ck),#k,Genus(co`Ck),nu,DelSpaces(D),DelSpaces(Generators(IStab)));
    end if;

    if hasup then
      UCo:=[C: C in Components | C`D eq CompD[up]];      // upper components
      ur:=r[UCo[1]`r];
      uR:=r[UCo[1]`R];
      alpha:=r[i1];
      xa:=red((alpha-ur)/(uR-ur));
      if #UCo eq 1 then      
        uf:=HyperellipticPolynomials(UCo[1]`Ck);
        ya:=Sqrt(Evaluate(uf,xa));
      else    
        ya:=UCo[1]`sign;
      end if;
      P:=rec<point|i:=Position(Components,UCo[1]), x:=xa, y:=ya>;
      Append(~Pts,P); 
      if ya ne 0 then
        P`i:=Position(Components,Last(UCo));
        P`y:=-ya;
        Append(~Pts,P); 
      end if;     
    end if;
  end for;

  // Store what we've got so far in data

  data:=rec<localcurvedata|
    C:=C,           // C  = parent curve
    K:=K,           // K  = p-adic base field 
    P:=p,           // P  = prime at which we are working
    p:=p,           // p  = residue characteristic 
    f:=f,           // f  = polynomial for y^2=f(x)
    n:=n,           // n  = Degree(f)
    F:=F,           // F  = biquadratic extension of the splitting field of f
    OF:=OF,         // OF = ring of integers of F
    k:=k,q:=q,      // k  = k_F residue field, order q, 
    pi:=pi,         // pi = uniformizer of F
    red:=red,       //      red = reduction map OF->k
    r:=r,           // r  = [r_1,...,r_n] roots of f in F
    G:=G,           // G  = Gal(F/Q), so 1 -> C2^2 -> G -> Gr -> 1
    Gr:=Gr,         // Gr = Gal(f/Q), subgroup of Sym(n)
    GtoGr:=GtoGr,   //      surjective homomorphism G->Gr, kernel C2^2
    I:=I,           // I  = inertia subgroup of G
    ramgps:=ramgps, // higher ramification subgroups of I [...,<G_i,i>,...]
    Frob:=Frob,     // Frobenius element of G
    Co:=Components, // List of components
    Pt:=Pts,        // List of intersection points
    Gact:=Gact,     // map G->Aut(F/Q) 
    A0:=A           // some GalRep of Gal(F/Q)
  >; 

  // add roots to points
  
  Pts:=[roottopoint(data,i): i in [1..n]] cat Pts;
  vprint CrvHyp, 2: "PtsR:",DelSpaces([ Sprint(<Pts[j]`i,Pts[j]`x,Pts[j]`y>): 
    j in [1..n] ] );
  vprint CrvHyp, 2: "PtsI:",DelSpaces([ Sprint(<Pts[j]`i,Pts[j]`x,Pts[j]`y>): 
    j in [n+1..#Pts] ] );
  
  // Galois action on points [roots + intersection points]

  G0:=sub<G|Igens,Frob>;        // same group, different generators
  assert G0 eq G;

  gens:=[];
  for g in Igens do
    Fg:=func<P|pointact(data,P,GtoGr(g),tamecharacter(g),0)>;
    sigma:=pointpermutation(Pts,Fg);
    Append(~gens,sigma);
    vprint CrvHyp,2: "I>",Order(g),DelSpaces(sigma);
  end for;
  IPts:=sub<Sym(#Pts)|gens>;
  Fg:=func<P|pointact(data,P,Frobr,tamecharacter(Frob),Degree(kK,PrimeField(kK)))>;   
  FrobGPts:=pointpermutation(Pts,Fg);
  Append(~gens,FrobGPts);
  GPts:=sub<Sym(#Pts)|gens>;

  G0toGPts:=hom<G0->GPts|gens>;
  GtoGPts:=hom<G->GPts|g:->G0toGPts(G0!g)>;
  vprint CrvHyp,2: "F GPts>",DelSpaces(FrobGPts);
  vprint CrvHyp,2: "G GPts>",GroupName(GPts);
  ptschar:=PermutationCharacter(GPts);
  if #Pts gt n then
    intptsact:=GSet(GPts,{n+1..#Pts});
    intptsfix:=[#[x: x in intptsact | x^g[3] eq x]: g in ConjugacyClasses(GPts)];
    intptschar:=CharacterRing(GPts)!intptsfix;  
    assert IsCharacter(intptschar);
  else
    intptschar:=CharacterRing(GPts)!0;  
    vprint CrvHyp,2: "PermChar(points): ",DelSpaces(intptschar);
  end if;
 
  // Permutation character on components
  
  CStabs:=[];
  for i:=1 to #Components do
    C:=Components[i];
    D:=C`D;
    Ps:={j: j in [1..#Pts] | Pts[j]`i eq i};
    CStab:=[g: g in GPts | (D^g eq D) and (Ps^g eq Ps)];
    Append(~CStabs,CStab);
  end for;
  compchar:=CharacterFromStabilizers(GPts,CStabs);  
  vprint CrvHyp,2: "PermChar(components): ",DelSpaces(compchar);
  assert IsCharacter(compchar);

  // Permutation character on loops; e.g. Dicks-Dunwoody section 9.2
  
  loopchar:=intptschar - compchar + PrincipalCharacter(GPts);
  vprint CrvHyp,2: "PermChar(loops): ",DelSpaces(loopchar);    
  assert (loopchar eq 0) or IsCharacter(loopchar);

  Ch:=CharacterTable(GPts);
  dec:=Decomposition(Ch,loopchar);
  ininv:=&+[CharacterRing(GPts) | dec[i]*Ch[i]: i in [1..#Ch] | 
    Restriction(Ch[i],IPts) eq Degree(Ch[i])*PrincipalCharacter(IPts)  ];
  frobcharloops:=ininv eq 0 select PR(Q)!1 else PR(Q)!CharacterCharPoly(ininv,FrobGPts);
  cyc:=Degree(frobcharloops);
  
  reduced:=AllSubgroupInfo select 2 else 4;
  posgenquo:=[C: C in Components | (Position(CompD,C`D) in CompDorbitReps) 
    and (C`nu mod reduced eq 0) and Genus(C`Ck) gt 0]; 
  vprint CrvHyp,2: "Positive genus reduced components: ",
    [Genus(C`Ck): C in posgenquo];

  x:=PR(Q).1;
  //  localfactor:=frobcharloops;        // local factor - toric part
  // now multiplied at end

  localfactor:=PR(Q)!1;
  lfdegree:=0;                       // degree of the full local factor
  fulldeg:=true;                     // local factor computed to full degree?
  
  for C in posgenquo do              // local factor - abelian part
                                     // Quotienting out components by geometric 
                                     // inertia action, equivalently, one in each
                                     // inertia orbit by the inertia stabiliser

    r0:=r[C`r]; 
    r1:=r[C`R];
    vprint CrvHyp,2: Sprintf("r0=%o r1=%o r1-r0=%o",
      PrintPadic(r0),PrintPadic(r1),PrintPadic(r1-r0));

    function act(sigma: abonly:=false)                    // sigma acts on Ck as 
      g:=GtoGr(sigma);                                    //   X -> aX + b
      a:=red((r[(C`R)^g]-r[(C`r)^g])/(r1-r0));            //   Y -> cY
      b:=red((r[(C`r)^g]-r0)/(r1-r0));  
      if abonly then return a,b; end if;
      c:=tamecharacter(sigma)^-(C`nu div 2) * a^-Degree(C`sq);   
        //! check first minus sign; does it matter? Is it +-1?
      vprint CrvHyp,3: "action>>",a,b,c;
      return a,b,c;
    end function;

    // Frobenius action

    kD:=Position(CompD,C`D);
    i:=Position(CompDorbitReps,kD);
    o:=CompDorbits[i];
    for j:=1 to Order(Frob) do
      if exists(gi){g: g in I | kD^CompDAct(Frob^j*g) eq kD} then
        Fr:=Frob^j*gi;       // modification of Frobenius by an inertia
        frobpower:=j;        // element that preserves our component
        vprintf CrvHyp,2: "Frob^%o fixes component #%o\n",j,kD;
        break;
      end if;
    end for;
                               
    vprint CrvHyp,2: "Quotienting: ",PrintCurve(C`Ck),"by",GroupName(C`IS);

    rootonCk:=func<j|red((r[j]-r0)/(r1-r0))>;

    Qc:=GeometricQuotient(C`Ck,C`IS,C`D,act,GtoGr,rootonCk);
    vprintf CrvHyp,1: "Quotient %o / %o = %o (g=%o)\n",
      PrintCurve(C`Ck),GroupName(C`IS),PrintCurve(Qc),Genus(Qc);

    if AllSubgroupInfo and (C`IS eq I) then
    for HD in Subgroups(G) do
      H:=HD`subgroup;
      HI:=H meet I;
      QH,yact:=GeometricQuotient(C`Ck,HI,C`D,act,GtoGr,rootonCk);
      ker:=[g: g in HI | [a,b,c] eq [k|1,0,1] where a,b,c is act(g)];
      resdeg:=Index(G,H) div Index(I,HI);
      assert exists(FrobH){F: F in H | F*Fr^-resdeg in I};

      a,b,c:=act(FrobH);
      aq:=a^(#HI div #ker); 
      X:=PR(k).1;
      inv:=&*{a*X+b where a,b:=act(g: abonly:=true): g in HI };
      qH:=#kK^resdeg;
      invq:=Polynomial([c^qH: c in Coefficients(inv)]);
      bq:=Evaluate(invq,b);
      cq:=c;
      loc:=FixedPointCount(QH,aq,bq,cq,qH,degree);
      vprintf CrvHyp,1: "/%-6o[%o%o] = g%o: %-20o loc=%-30o [f%o]\n",GroupName(H),
        GroupName(HI),
        yact select "-" else "+",Genus(QH),PrintCurve(QH),DelSpaces(loc),resdeg;
    end for;
    end if;
    
    ISker:=[g: g in C`IS | [a,b,c] eq [1,0,1] where a,b,c is act(g)];

    a,b,c:=act(Fr);

    aq:=a^(#C`IS div #ISker); 
    X:=PR(k).1;
    inv:=&*{a*X+b where a,b:=act(g: abonly:=true): g in C`IS};  // I in the paper
    invq:=Polynomial([c^#kK: c in Coefficients(inv)]);          
    bq:=Evaluate(invq,b);                                       // I^{(q)}(b)
    cq:=c;

    //! cq possibly wrong when yact=true - check and prove!

    vprint CrvHyp,2: Sprintf("Frob acts on the quotient as X->%o*X^%o+%o, Y->%o*Y^%o",
      aq,#kK,bq,cq,#kK);
 
    complocalfactor,full:=FixedPointCount(Qc,aq,bq,cq,#kK^frobpower,degree);
    localfactor*:=Evaluate(complocalfactor,PR(Q).1^frobpower);
      // frob permuting inertia orbits  ->   x->x^frobpower   in local factor
    lfdegree+:=2*Genus(Qc)*frobpower;
    if not full then fulldeg:=false; end if;
        
  end for;

  vprint CrvHyp,2: "Local factor (abelian part):",DelSpaces(localfactor);

  if lfdegree+2*Degree(loopchar) eq 2*g then
    loop_rep:=A!!LiftCharacter(loopchar,GtoGPts,G) * SP(K,1-#kK*x,2);       
    vprint CrvHyp,2: "Galois rep, toric part:",loop_rep;
    good_rep:=UnramifiedRepresentation(K,lfdegree,
      fulldeg select lfdegree else degree,localfactor);
    vprint CrvHyp,2: "Galois rep, good part:",good_rep;
    data`A:=good_rep+loop_rep;
  end if;
  
  localfactor*:=frobcharloops;
  lfdegree+:=Degree(frobcharloops);

  vprint CrvHyp,2: "Local factor:",DelSpaces(localfactor);

  tamecond:=2*g - lfdegree;
  conductor:=tamecond+wildcond;
  
  vprint CrvHyp,2: "Tame conductor:",tamecond;
  vprint CrvHyp,2: "Wild conductor:",wildcond;

  data`conductor:=conductor;     // conductor exponent
  data`tamecond:=tamecond;       //   = tame conductor exponent  
  data`wildcond:=wildcond;       //   + wild conductor exponent 
  data`localfactor:=localfactor; // local factor in Q[T]
  data`degree:=degree;           //   computed up to this degree
  data`rootnumber:=0;            // local root number; not implemented

  return data;

end function;


/****************** LOCALDATA AT GOOD PRIMES *******************/


function GoodLocalFactor(C,P: degree:=Infinity())  
  K:=BaseField(C);
  g:=Genus(C); 

  if Type(K) eq FldRat then 
    k:=GF(P);
    m:=map<Q->k|x:->x>;
  elif ISA(Type(K),FldNum) then
    k,r:=ResidueClassField(P); 
    O:=Integers(K);
    m:=func<x|r(O!x)>;
  elif Type(K) eq FldPad then
    k,m:=ResidueClassField(Integers(K));
  end if;    

  q:=#k;
  f1,f2:=HyperellipticPolynomials(C); 
  f1red:=Polynomial(k,[m(c): c in Coefficients(f1)]);
  f2red:=Polynomial(k,[m(c): c in Coefficients(f2)]);
  
  Cp:=HyperellipticCurve([f1red,f2red]);

  if degree eq 1 then return 1-(q+1-#Cp)*PR(Q).1; end if;

  // put together in a generating series for the zeta-function at P
  degree:=Min(degree,g);
  U<T>:=PowerSeriesRing(Q,degree+1);
  ser:=&+[#BaseChange(Cp,ext<k|n>)/n*T^n: n in [1..degree]];

  // its numerator is the L-factor
  f:=Exp(ser)*(1-T)*(1-q*T); 
  if degree lt g then return f; end if;
  f:=Polynomial(Coefficients(f));          // MW 15 Oct 12, use func eq
  f:=f+&+[Coefficient(f,2*g-d)*q^(d-g)*Parent(f).1^d : d in [g+1..2*g]];
  return f;

end function;


function LocalData_Good(C,P: degree:=Infinity()) 

  if degree ge Genus(C) then degree:=2*Genus(C); end if;

  loc:=(degree gt 0) select GoodLocalFactor(C,P: degree:=degree) else PR(Q)!1;

  K:=BaseField(C);
  if   Type(K) eq FldRat   then K:=pAdicField(P,5);
  elif ISA(Type(K),FldNum) then K:=Completion(K,P: Precision:=5);
  end if;

  data:=rec<localcurvedata|
    C:=C,              // C  = parent curve
    K:=K,              // base field
    P:=P,              // P  = prime at which we are working
    conductor:=0,      // conductor exponent
    tamecond:=0,       //   = tame conductor exponent  
    wildcond:=0,       //   + wild conductor exponent 
    localfactor:=loc,  // local factor in Q[T]
    degree:=degree,    //   computed up to this degree
    rootnumber:=1,     // local root number
                       // and Galois representation
    A:=UnramifiedRepresentation(K,2*Genus(C),degree,loc)
  >;  
  return data;
  
end function;


/********************** LOCALDATA AT 2 **********************/


function IsNumZero(c)
  return Abs(c) lt 10^-10;
end function;  


function IsZPoly(f)
  C:=ComplexField();
  if forall{c: c in Coefficients(f) | IsCoercible(C,c) and 
    IsNumZero(C!c-Round(Real(C!c)))} then   
      f:=PR(Q)![Round(Real(C!c)): c in Coefficients(f)];
      return true,f;
  else
      return false,_;
  end if;
end function;


function RootsOfRoots(f,n)  
  if Degree(f) eq 0 then return [PR(Q)|1]; end if;
  C:=ComplexField(20*Degree(f));
  R<X>:=PR(C);
  S:=[<[z[1]: z in Roots(X^n-1/u[1])],u[2]>: u in Roots(R!f)];
  list:={};
  for t in CartesianProduct([Multisets(Set(X[1]),X[2]): X in S]) do
    s:=&join{* u: u in t *};
    F:=&*[(1-u*X): u in s];
    ok,F:=IsZPoly(F);
    if not ok then continue; end if;
    Include(~list,F);
  end for;
  return SetToSequence(list);
end function;


function LocalDataWithRegularModel(C,P: degree:=Infinity()) 

  K:=BaseField(C);
  k:=Type(K) eq FldRat select GF(P) else ResidueClassField(P);
  p:=Characteristic(k);

  vprintf CrvHyp,1: "Local data at %o (degree %o)",P,degree;

  g:=Genus(C);
  degree:=Min(degree,2*g);

  if assigned C`LocalData and exists(D){D: D in C`LocalData | 
      (Type(D) eq Rec) and (D`P eq P)} 
    then R:=D`R;
    else vprintf CrvHyp,2: "Computing regular model at %o\n",P;
         R:=RegularModel(C,P: Warnings:=false); 
  end if;
  needext:=Degree(R`k,k);
  q:=#R`k;
  
  spldegs:=splitting_degrees(R); 
  numgeocomps:=&+spldegs;
  vdisc:=Valuation(Discriminant(C),P); 
  conductor:=vdisc-numgeocomps+1;            // Ogg
  T:=PowerSeriesRing(Q,degree+1).1;
  ser:=Exp(&+[Parent(T)|number_of_points_on_special_fibre(R,n)/n*T^n: 
    n in [1..degree]]);
  h0term:=1-T;                               // h0 could be to power?
  h2term:=&*[1-(q*T)^j: j in spldegs]; 
  localfactor:=PR(Q)!Eltseq(ser * h0term * h2term);
  x:=PR(Q).1;

  if needext gt 1 then                         // <- sometimes can descend back
    list:=RootsOfRoots(localfactor,needext);   //    the local factor uniquely
    error if #list gt 1,                       // <- but not always
      Sprintf("Can only compute the local factor at %o after a field extension;\n"*
        "try LSeries(C: LocalData:=[<%o,%o,f>]), f one of %o",
        p,p,conductor,DelSpaces(list));
    localfactor:=list[1];
  end if;

  tamecond:=2*g-Degree(localfactor);
  wildcond:=conductor-tamecond;

  data:=rec<localcurvedata|
    C:=C,                       // C  = parent curve
    K:=K,                       //   base field
    P:=P,                       // P  = prime at which we are working
    R:=R,                       // Regular model
    conductor:=conductor,       // conductor exponent
    tamecond:=tamecond,         //   = tame conductor exponent  
    wildcond:=wildcond,         //   + wild conductor exponent 
    localfactor:=localfactor,   // local factor in Q[T]
    degree:=degree,             //   computed up to this degree
    rootnumber:=0               // local root number - not implemented yet
  >;  
  return data;

end function;



/********************** LOCALDATA WRAPPER **********************/


procedure StoreLocalData(~C,D)
  if not assigned C`LocalData then
    C`LocalData:=[* D *]; return;
  end if;
  P:=func<d|Type(d) eq Tup select d[1] else d`P>;
  padic:=Type(BaseField(C)) eq FldPad;
  ok:=exists(n){n: n in [1..#C`LocalData] | padic or (P(C`LocalData[n]) eq P(D))};
  if ok then
    C`LocalData[n]:=D; return;
  else
    Append(~C`LocalData,D); return;
  end if;
end procedure;


// Main Local data wrapper 


function LocalDataGeneral(C, P: degree:=Infinity(), Precision:=20)  
  vprintf CrvHyp,1: "Local Data at %o, C: %o\n",PrintIdeal(P),PrintCurve(C);
  K:=BaseField(C);
  padic:=Type(K) eq FldPad;
  if assigned C`LocalData then 
    if exists(D)
       {D: D in C`LocalData | (Type(D) eq Tup) and ((D[1] eq P) or padic)} 
      then return LocalDataGeneral(D[2],D[3]: degree:=degree); end if;
    if exists(D)
       {D: D in C`LocalData | (Type(D) eq Rec) and ((D`P eq P) or padic)} 
      and D`degree ge degree then return D; end if;
  end if;

  f,g:=HyperellipticPolynomials(C);
  if Type(K) eq FldRat then 
    k:=GF(P); v:=func<x|Valuation(x,P)>;
  elif ISA(Type(K),FldNum) then
    k:=ResidueClassField(P); v:=func<x|Valuation(x,P)>;
  elif padic then
    k:=ResidueClassField(Integers(K)); v:=Valuation;
  else
    error "Base field is not Q, number field or extension of Qp";
  end if;    
  p:=Characteristic(k);
  q:=#k;

  vD:=v(Discriminant(C));
  int:=Min([v(x): x in Coefficients(f) cat Coefficients(g)]) ge 0;

  if int and (vD eq 0) then                         // good reduction
    D:=LocalData_Good(C,P: degree:=degree); 
    D`mindisc:=vD;
    StoreLocalData(~C,D); 
    return D;
  end if;

  if Type(K) eq FldRat then                         // /Q: Minimal model at p
    Cmin:=p eq 2 
      select MinimalWeierstrassModel(C)     // Keep RegularModel happy
      else pMinimalWeierstrassModel(C,p); 
    fmin,gmin:=HyperellipticPolynomials(Cmin);
    if (f ne fmin) or (g ne gmin) then
      StoreLocalData(~C,<P,Cmin,p>); 
      return LocalDataGeneral(Cmin,p: degree:=degree);
    end if;
    assert int;
  end if;

  // K=Q2 : coerce to Q

  if (p eq 2) and padic then
    error if AbsoluteDegree(K) ne 1, 
      "LocalData at 2 not implemented for non-trivial extensions of Q_2";
    f,g:=HyperellipticPolynomials(C);  
    fQ:=PR(Q)!f;
    gQ:=PR(Q)!g;
    CQ:=MinimalWeierstrassModel(HyperellipticCurve(fQ,gQ));
    StoreLocalData(~C,<P,CQ,p>); 
    return LocalDataGeneral(CQ,p: degree:=degree);
  end if;

  // p=2, K=Q or number field -> Regular model machinery

  if p eq 2 then
    error if not int, "Integral models not implemented over number fields";
    D:=LocalDataWithRegularModel(C,P: degree:=degree);
    if Type(K) eq FldRat then D`mindisc:=vD; end if;
    StoreLocalData(~C,D); 
    return D;
  end if;

  // p odd -> Semistable model machinery

  if Type(K) eq FldPad then
    D:=LocalDataWithSemistableModel(C: degree:=degree);
    StoreLocalData(~C,D); 
    return D;
  end if;

  for j in [1,2,5,15] do  
    prec:=j*Precision;
    if Type(K) eq FldRat then
      KP:=pAdicField(P,prec);
      CP:=BaseChange(C,KP);
    else 
      KP,m:=Completion(K,P: Precision:=prec);
      CP:=BaseChangeCurve(C,m);
      KPfin:=ChangePrecision(KP,prec);
      CP:=BaseChangeCurve(CP,func<x|KPfin!x>);
    end if;
    try
      D:=LocalDataWithSemistableModel(CP: degree:=degree); 
      ok:=true;
    catch e
      ok:=false;
      s:=e`Object;
    end try;   
    if not ok then 
      vprint CrvHyp,1: "Precision",prec,"insufficient; increasing precision";
      vprint CrvHyp,2: "error:",s;
      continue; 
    end if;
    if Type(K) eq FldRat then D`mindisc:=vD; end if;
    StoreLocalData(~C,<P,CP,p>); 
    StoreLocalData(~CP,D); 
    return D;
  end for;
  error Sprintf("Could not compute local data for %o at %o",PrintCurve(C),P);
    
end function;


/**************** INTRINSIC WRAPPERS: CONDUCTOR **********************/


intrinsic Conductor(C::CrvHyp[FldRat], p::RngIntElt) -> RngIntElt
{ Conductor exponent of a hyperelliptic curve C/Q at a prime p. }
  require IsPrime(p): "p must be a prime number";
  D:=LocalDataGeneral(C,p: degree:=0);
  return D`conductor;
end intrinsic; 


intrinsic Conductor(C::CrvHyp[FldNum], P::RngOrdIdl) -> RngIntElt
{ Conductor exponent of a hyperelliptic curve C over a number field
 at a prime ideal P}
  D:=LocalDataGeneral(C,P: degree:=0);
  return D`conductor;
end intrinsic; 


intrinsic ConductorExponent(E::CrvEll[FldPad]) -> RngIntElt
{ Conductor exponent of an elliptic curve E over a p-adic field. }
  loc:=LocalInformation(E);
  _,vdisc,vcond,cv,kod:=Explode(loc); 
  return vcond;
end intrinsic; 


intrinsic ConductorExponent(C::CrvHyp[FldPad]) -> RngIntElt
{ Conductor exponent of a hyperelliptic curve C over a p-adic field. }
  D:=LocalDataGeneral(C,0: degree:=0);
  return D`conductor;
end intrinsic; 


intrinsic Conductor(C::CrvHyp[FldPad]) -> FldPadElt
{ Conductor ideal pi^ConductorExponent(C) of a hyperelliptic curve C
 over a p-adic field. }
  K:=BaseField(C);
  D:=LocalDataGeneral(C,0: degree:=0);
  return UniformizingElement(K)^D`conductor;
end intrinsic; 


intrinsic Conductor(C::CrvHyp[FldRat]) -> RngIntElt
{ Conductor of a hyperelliptic curve C/Q. }
  K:=BaseField(C);
  if assigned C`Conductor then return C`Conductor; end if;
  Cmin:=MinimalWeierstrassModel(C);
  if assigned Cmin`Conductor then 
    C`Conductor:=Cmin`Conductor; return C`Conductor;
  end if;
  D:=Z!Discriminant(Cmin);
  if Valuation(D,2) ge 12 then
   "WARNING: Using Ogg's formula when v_2(D)>=12, no correctness guarantee";
  end if;
  N:=&*[p^Conductor(Cmin,p): p in PrimeDivisors(D)];
  Cmin`Conductor:=N;
  C`Conductor:=N;
  C`LocalData:=Cmin`LocalData;
  return N;
end intrinsic; 


intrinsic Conductor(C::CrvHyp[FldNum]) -> RngIntElt
{ Conductor of a hyperelliptic curve C over a number field. }
  if assigned C`Conductor then return C`Conductor; end if;

  K:=BaseField(C);
  O:=Integers(K);
  g,f:=HyperellipticPolynomials(C); 
  require forall{c: c in Coefficients(g) cat Coefficients(f)|IsCoercible(O,c)}:
    "Not a integral model";
    D:=ideal<Integers(K)|Discriminant(C)>;
  if AbsoluteNorm(D) eq 1 
    then N:=D;
    else fct:=Factorization(D);
         if exists{P: P in fct |
	           IsEven(AbsoluteNorm(P[1])) and Valuation(D,P[1]) ge 12} then
		   "WARNING: Using Ogg's formula when v_P(D)>=12 "
		   *"not guaranteed to be correct";
         end if;        
         N:=&*[P[1]^Conductor(C,P[1]): P in fct];
  end if;
  C`Conductor:=N;
  return N;
end intrinsic; 


/**************** INTRINSIC WRAPPERS: EULER FACTOR **********************/


intrinsic EulerFactor(C::CrvHyp[FldPad]: Degree:=Infinity()) -> RngUPolElt
{The Euler factor of a hyperelliptic curve defined over Qp}
 R:=PR(Z); if Degree ne Infinity() then R:=PowerSeriesRing(Z,Degree+1); end if;
 return R!LocalDataGeneral(C,0: degree:=Degree)`localfactor; end intrinsic; 

intrinsic
 EulerFactor(C::CrvHyp[FldRat], p::RngIntElt: Degree:=Infinity()) -> RngUPolElt
{The Euler factor of a hyperelliptic curve defined over Q at p}
 R:=PR(Z); if Degree ne Infinity() then R:=PowerSeriesRing(Z,Degree+1); end if;
 require IsPrime(p): "p must be a prime number";
 f,g:=HyperellipticPolynomials(C);
 if forall{c: c in Coefficients(f) cat Coefficients(g) | Valuation(c,p) ge 0}
     and Numerator(Discriminant(C)) mod p ne 0 
   then return R!GoodLocalFactor(C,p: degree:=Degree); 
   else return R!LocalDataGeneral(C,p: degree:=Degree)`localfactor; end if;
end intrinsic; 

intrinsic EulerFactor
(C::CrvHyp[FldNum], P::RngOrdIdl: Degree:=Infinity()) -> RngUPolElt
{The Euler factor of a hyperelliptic curve C over a number field
 at a prime ideal P}
 R:=PR(Z); if Degree ne Infinity() then R:=PowerSeriesRing(Z,Degree+1); end if;
 require IsPrime(P): "p must be a prime ideal";
 g,f:=HyperellipticPolynomials(C); 
  // Integral models over number fields not implemented yet
 require forall{c: c in Coefficients(g) cat Coefficients(f) |
    Valuation(c,P) ge 0}: "Model is not integral at P";
 if Valuation(Discriminant(C),P) eq 0 
    then return R!GoodLocalFactor(C,P: degree:=Degree); 
    else return R!LocalDataGeneral(C,P: degree:=Degree)`localfactor; end if;  
end intrinsic; 

intrinsic EulerFactor
(C::CrvHyp[FldNum], p::RngIntElt : Degree:=Infinity()) -> RngUPolElt
{The pth Euler factor of the given elliptic curve over a number field}
 require IsPrime(p): "p must be prime";
 R:=PR(Z); if Degree ne Infinity() then R:=PowerSeriesRing(Z,Degree+1); end if;
 x:=R.1; loc:=R!1;
 for P in AbsoluteDecomposition(BaseField(C),p) do
   I:=Ideal(P[1]); d:=AbsoluteInertiaDegree(I);
   if d gt Degree then continue; end if;
   loc*:=Evaluate(R!EulerFactor(C,I: Degree:=Floor(Degree/d)),x^d); end for;
 return loc;
 //return Polynomial([Coefficient(loc,i): i in [0..Min(_Degree(loc),Degree)]]);
end intrinsic;

/****************** HODGE STRUCTURES ******************/

intrinsic HodgeStructure(C::CrvHyp[FldRat]) -> HodgeStruc
{The Hodge structure of a hyperelliptic curve over the rationals}
  return Genus(C)*HodgeStructure([<0,1>,<1,0>]); 
end intrinsic;


intrinsic HodgeStructure(C::CrvHyp[FldNum]) -> HodgeStruc
{The Hodge structure of a hyperelliptic curve over a number field}
  return Genus(C)*Degree(BaseRing(C))*HodgeStructure([<0,1>,<1,0>]);
end intrinsic;


/********************** L-SERIES **********************/

intrinsic LSeries(C::CrvHyp[FldRat]: Precision:=0, 
  LocalData:=[* *], ExcFactors:=[* *], BadPrimes:=[* *]) -> LSer
{L-Series of a hyperelliptic curve over Q. 
 The user can force local factors at a finite set of primes with
 LocalData:=[* <p,vcond,localfactor>,... *]. Current implementation can only 
 compute the conductor at 2 when v_2(Delta)<12, using Ogg's formula.
 If this is not the case, either the local factor at 2 must be supplied
 in LocalData, or the use of Ogg's formula at 2 forced with
 LocalData:="Ogg" or [* <2,"Ogg"> *] }

  if Genus(C) eq 0 then // ignores LocalData
   return LSeries(1 : Precision:=Precision); end if;
  if Genus(C) eq 1 then // ignores LocalData
    return LSeries(Jacobian(GenusOneModel(C)) : Precision:=Precision); end if;

  if ExcFactors cmpne [* *] or BadPrimes cmpne [* *] then
    "WARNING: ExcFactors and BadPrimes are obsolete, use LocalData";
  end if;  
  if ExcFactors cmpeq "Ogg" then ExcFactors:=[* <2,"Ogg"> *]; end if;
  if BadPrimes cmpeq "Ogg" then BadPrimes:=[* <2,"Ogg"> *]; end if;
  if LocalData cmpeq "Ogg" then LocalData:=[* <2,"Ogg"> *]; end if;
  if Type(ExcFactors) eq SeqEnum then
   ExcFactors:=SequenceToList(ExcFactors); end if;
  if Type(BadPrimes) eq SeqEnum then
   BadPrimes:=SequenceToList(BadPrimes); end if;
  if Type(LocalData) eq SeqEnum then
   LocalData:=SequenceToList(LocalData); end if;
  require {Type(X): X in [* ExcFactors,BadPrimes,LocalData *]} eq {List}:
    "LocalData must be \"Ogg\" or a list [* <p,vcond,localfactor>,... *]";
  LocalData:=ExcFactors cat BadPrimes cat LocalData;
  require forall{D: D in LocalData | (Type(D) eq Tup) and 
    IsCoercible(Z,D[1]) and IsPrime(Z!D[1]) and 
    ((D cmpeq <D[1],"Ogg">) or IsCoercible(Parent(<2,1,PR(Q).1>),D))}:
    "LocalData must be \"Ogg\" or a list [* <p,vcond,localfactor>,... *]";

  f,g:=HyperellipticPolynomials(C);                // Global minimal model 
  Cmin:=MinimalWeierstrassModel(C); 
  fmin,gmin:=HyperellipticPolynomials(Cmin);
  if (f ne fmin) or (g ne gmin) then 
    L:=LSeries(Cmin: Precision:=Precision, LocalData:=LocalData);
    if assigned Cmin`LocalData then C`LocalData:=Cmin`LocalData; end if;
    return L;
  end if;
  
  genus:=Genus(C); 
  D:=Z!Discriminant(C); 
  vprint LSeries,1: "LSeries(CrvHyp), genus =",genus;
  vprint LSeries,1: "D =",Factorisation(D);
  badprimes:=PrimeDivisors(D);
  OggAt2:=exists{D: D in LocalData | D cmpeq <2,"Ogg">};
  LocalData:=SetToSequence({D: D in LocalData | #D eq 3});    
  error if exists(i){i: i in [1..#LocalData], j in [1..#LocalData] | 
    (i ne j) and LocalData[i][1] eq LocalData[j][1]},
    Sprintf("Local data at %o specified multiple times",LocalData[i][1]);
  excprimes:=[e[1]: e in LocalData];

  for p in badprimes do                            // bad primes, minus 
    if p in excprimes then continue; end if;       // those forced by LocalData
    vprint LSeries,1: "Local factor at",p;
    vdisc:=Valuation(D,p);
    error if (p eq 2) and (not OggAt2) and (vdisc ge 12),
      Sprintf("v_2(disc)=%o>=12, cannot use "*
              "Ogg's formula unless forced by LocalData:=\"Ogg\"",vdisc);
    loc:=LocalDataGeneral(C,p: degree:=0);
    Append(~LocalData,<p,loc`conductor,loc`localfactor>);
  end for;

  N:=&*[e[1]^e[2]: e in LocalData];       // note: e[3] not computed fully yet
  vprint LSeries,1: "Conductor = ",N;     //   because of degree:=0 above

  function LocalFactor(p,deg)
    if p in excprimes then 
      return LocalData[Position(excprimes,p)][3];
    elif p in badprimes then
      loc:=EulerFactor(C,p: Degree:=deg);                // it is computed now
      vprint LSeries,1: "Local factor at",p,"=",loc;
      return loc;
    else 
      return GoodLocalFactor(C,p: degree:=deg); 
    end if;
  end function;

  gamma := [0: j in [1..genus]] cat [1: j in [1..genus]];
  return LSeries(2,gamma,N,LocalFactor:Precision:=Precision,Name:=C,Parent:=C);
end intrinsic;


intrinsic LSeries
(C::CrvHyp[FldRat], K::FldNum : Precision:=0, LocalData:=[* *])-> LSer
{L-series associated to a hyperelliptic curve C/Q base changed
 to a number field K}
  L:=LSeries(C,PermutationCharacter(K) :
	     Precision:=Precision, LocalData:=LocalData);
  L`name:=<C," base changed to ",K>; return L;
end intrinsic;


intrinsic LSeries(C::CrvHyp[FldNum]: Precision:=0, LocalData:=[* *]) -> LSer
{L-series associated to a hyperelliptic curve over a number field}

  K:=BaseField(C);
  f,g:=HyperellipticPolynomials(C);

  // Curve is base change from Q -> Descend and twist
  if forall{c: c in Coefficients(f) cat Coefficients(g)| IsCoercible(Q,c)} then
    CQ:=BaseChangeCurve(C,func<x|Q!x>);
    return LSeries(CQ,K: Precision:=Precision, LocalData:=LocalData);
  end if;

  // Genus 0 and 1 - ignores LocalData
  if Genus(C) eq 0 then return LSeries(K : Precision:=Precision); end if;
  if Genus(C) eq 1 then 
    return LSeries(Jacobian(GenusOneModel(C)) : Precision:=Precision); end if;
  
  // General case: main invariants
  genus:=Genus(C);
  vprint LSeries,1: "LSeries(CrvHyp/NF), genus =",genus;
  O:=IntegerRing(K);
  N:=Conductor(C);      // checks model is integral
  NQ:=Abs(AbsoluteNorm(N));
  d:=AbsoluteDegree(K);
  gamma:=[0: i in [1..d*genus]] cat [1: i in [1..d*genus]];
  D:=O!Discriminant(C);

  // Process local data -> OggAt2, LocalData
  if LocalData cmpeq "Ogg" then 
    LocalData:=[* <P[1],"Ogg">: P in AbsoluteDecomposition(O,2) *]; end if;
  if Type(LocalData) eq SeqEnum then
    LocalData:=SequenceToList(LocalData); end if;
  require Type(LocalData) eq List:
    "LocalData must be \"Ogg\" or a list [* <P,vcond,localfactor>,... *]";
  I:=ideal<O|>;
  U:=Parent(I);
  require forall{D: D in LocalData | (Type(D) eq Tup) and 
    IsCoercible(U,D[1]) and IsPrime(Z!D[1]) and 
    ((D cmpeq <D[1],"Ogg">) or IsCoercible(Parent(<I,1,PR(Q).1>),D))}:
    "LocalData must be \"Ogg\" or a list [* <ideal,vcond,localfactor>,... *]";
  OggAt2:=[D[1]: D in LocalData | D[2] cmpeq "Ogg"];
  LocalData:=SetToSequence({D: D in LocalData | #D eq 3});    
  error if exists(i){i: i in [1..#LocalData], j in [1..#LocalData] | 
    (i ne j) and LocalData[i][1] eq LocalData[j][1]},
    Sprintf("Local data at %o specified multiple times",LocalData[i][1]);

  // Discriminant and badprimes
  fctD:=Factorization(ideal<O|D>);
  vprint LSeries,1: "D =",fctD;
  badprimes:=[D[1]: D in fctD];
  excprimes:=[e[1]: e in LocalData];

  for P in badprimes do                            // bad primes, minus 
    if P in excprimes then continue; end if;       // those forced by LocalData
    vprint LSeries,1: "Local factor at",P;
    k:=ResidueClassField(P);
    error if (Characteristic(k) eq 2)
              and (P notin OggAt2) and (Valuation(D,P) ge 12),
      "v_P(discriminant)>=12, cannot use "*
      "Ogg's formula unless forced by LocalData:=\"Ogg\"";
    loc:=LocalDataGeneral(C,P: degree:=0);
    Append(~LocalData,<P,loc`conductor,loc`localfactor>);
  end for;

  N:=&*[U| e[1]^e[2]: e in LocalData];    // note: e[3] not computed fully yet
  vprint LSeries,1: "Conductor = ",N;     //   because of degree:=0 above

  function LocalFactor_P(P,deg)
    if P in excprimes then 
      return LocalData[Position(excprimes,P)][3];
    elif P in badprimes then
      loc:=EulerFactor(C,P: Degree:=deg);                // it is computed now
      vprint LSeries,1: "Local factor at",P,"=",loc;
      return loc;
    else 
      return GoodLocalFactor(C,P: degree:=deg); 
    end if;
  end function;
  
  function LocalFactor_p(p,deg)
    R:=PowerSeriesRing(Q,deg+1); x:=R.1; // should be safe
    loc:=R!1;
    for P in AbsoluteDecomposition(K,p) do
      I:=Ideal(P[1]);
      d:=AbsoluteInertiaDegree(I);
      if d gt deg then continue; end if;
     // f:=LocalFactor_P(I,deg div d); loc*:=Evaluate(f,Parent(f).1^d);
      loc*:=Evaluate(R!LocalFactor_P(I,deg div d),x^d);
    end for;
    return loc;
  end function;

  NQ:=Abs(AbsoluteNorm(N));
  NL:=NQ*AbsoluteDiscriminant(O)^(2*genus);
  return LSeries(2,gamma,NL,LocalFactor_p:
		 Precision:=Precision,Name:=C,Parent:=C);
  
end intrinsic;


/*
////////////////////////////////////////////////////////////////////////
// Mark's hyperelliptic curves over number fields code

function hyp_good_nf(C,P,deg) // MW 14 Nov 12
 F,m:=ResidueClassField(P); q:=#F; _,p,f:=IsPrimePower(q);
 G:=Genus(C); if deg gt G*f then deg:=G*f; end if;
 if G eq 0 then return Polynomial([1]); end if;
 gh,fh:=HyperellipticPolynomials(C);
 gq:=Polynomial([m(x) : x in Coefficients(gh)]);
 if fh ne 0 then fq:=Polynomial([m(x) : x in Coefficients(fh)]);
 else fq:=0; end if; Cq:=HyperellipticCurve([gq,fq]);
 T:=PowerSeriesRing(Q,deg+1).1; lim:=deg div f;
 X:=[F]; for n in [2..lim] do Embed(F,GF(p,n*f)); X cat:=[GF(p,n*f)]; end for;
 ser:=&+[Parent(T)|#BaseChange(Cq,X[n])/n*T^n: n in [1..lim]]+O(T^(lim+1));
 res:=Exp(ser)*(1-T)*(1-q*T);
 if deg lt G*f then return Evaluate(res,T^f); end if;
 res:=Polynomial(Coefficients(res));
 res:=res+&+[Coefficient(res,2*G-d)*q^(d-G)*Parent(res).1^d : d in [G+1..2*G]];
 return Evaluate(res,Parent(res).1^f); end function;

intrinsic EulerFactor(C::CrvHyp[FldNum],P::RngOrdIdl : Degree:=0) -> RngElt
{The Euler factor of a hyperelliptic curve at a prime ideal P}
 require Valuation(Discriminant(C),P) eq 0: "Prime must be good";
 gh,fh:=HyperellipticPolynomials(C); CO:=Coefficients(gh) cat Coefficients(fh);
 require &and[Valuation(x,P) ge 0: x in CO]: "Model has denominators at P";
 q:=#ResidueClassField(P); _,p,f:=IsPrimePower(q);
 if Degree eq 0 then deg:=Genus(C)*2*f; else deg:=Degree; end if;
 return hyp_good_nf(C,P,deg); end intrinsic;

intrinsic EulerFactor(C::CrvHyp[FldNum],p::RngIntElt : Degree:=0) -> RngElt
{The pth Euler factor of the given elliptic curve over a number field}
 require IsPrime(p): "p must be prime";
 L:=[* EulerFactor(C,Ideal(P[1]) : Degree:=Degree) :
       P in AbsoluteDecomposition(BaseField(C),p) *];
 if &and[Type(x) eq RngUPolElt : x in L] then return &*[x : x in L]; end if;
 R:=PowerSeriesRing(Z,Degree+1); return &*[R!x : x in L]; end intrinsic;

function LocalConductorOgg(C,p) 
  R:=RegularModel(MinimalWeierstrassModel(C),p);
  spldegs:=splitting_degrees(R); 
  numgeocomps:=&+spldegs;
  vdisc:=Valuation(Discriminant(C),p); 
  vcond:=vdisc-numgeocomps+1; 
  return vcond; 
end function;
*/
