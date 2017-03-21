freeze;

// Change Log
//
// T. Fisher, April 2010 
//   * added version of FourDescent with input a genus one model
//   * FourDescent now uses the new minimisation and reduction
            
declare verbose FourDescent,3;
declare verbose QuotientFD,2;
import "utils.m": MatrixFromQF;
import "local_quartic.m":
        RealLabels,LocalPoints,GeneratorsForQp2,NFHeight,LocalImageSize;
import "reduce.m": lll_reduce; // ReduceFD;
// import "minimise.m": MinimiseFD;
import "quartics.m" : AQDirect;

Z:=Integers();
Q:=Rationals();

function MyValuation(n,p)
 if (p eq -1) then if (n lt 0) then return 1; else return 0; end if;
 else return Valuation(n,p) mod 2; end if; end function;

function GetQuarticForm(p)
 x:=Parent(p).1; A:=LeadingCoefficient(p); mc:=A^3;
 zz:=&+[(Coefficient(p,j)*mc*x^j) div A^j : j in [0..4]];
 A:=SquarefreeFactorization(A); return A,zz; end function;

function EpsilonToCover(epsilon) 
 K:=Parent(epsilon);
 assert Degree(K) eq 4;

 // to get nicer quadrics, we use a good basis of K
 // (the union of the LLL bases of each summand)
 Kam:=K`AbsoluteMap;
 eps := epsilon@Kam;
 Ksum := Codomain(Kam);
 n := NumberOfComponents(Ksum);
 fields := [Component(Ksum,i) : i in [1..n]];
 basis:=[K|];
 for i := 1 to n do
   Ki := fields[i];
   ZKi := Integers(Ki);
   Ii := &* [PowerIdeal(FieldOfFractions(ZKi)) | 
                   t[1]^(t[2] div 2) : t in Factorization(eps[i]*ZKi)];
   for b in Basis(LLL(Ii^-1)) do
     Append(~basis, (<j eq i select Ki!b else 0 : j in [1..n]>) @@Kam);
   end for;
 end for;

 KPol := PolynomialRing(K,4); 
 T := &+[KPol| basis[i]*KPol.i : i in [1..4]];
 S,R := CoefficientsAndMonomials(epsilon*T^2);
 QPol := PolynomialRing(Q,4);
 A := &+[QPol| Coefficient(S[i],2) * R[i] : i in [1 .. #R]];
 B := &+[QPol| Coefficient(S[i],3) * R[i] : i in [1 .. #R]];

 // Note: the choice of basis makes epsilon*T^2 integral

 return [MatrixFromQF(A), MatrixFromQF(B)]; 
end function;

function GO(p,N,qludge)
 qludgep:=p*MaximalOrder(qludge); 
 s:=LocalTwoSelmerMap(N,qludgep); deabs:=func<t|Vector(GF(2),Eltseq(t))>;
 e:=GeneratorsForQp2(p); _,emb:=quo<Codomain(s)|[s(ee) : ee in e]>;
 zz:=func<t|deabs(emb(s(t)))>; return N,zz; end function;

function PruneFactor(n,bp) F:=SeqFact([]);
 for p in bp do v:=Valuation(n,p : Check:=false);
  if v ne 0 then n:=n div p^v; F:=F*SeqFact([<p,v>]); end if; end for;
 return Factorisation(n)*F; end function;

function d4_alg(f,badp)

 a,T:=GetQuarticForm(f);
 if false and IsIrreducible(T) then // TO DO
    quoalg := NumberField(T);
    Qpi:={p*Integers() : p in badp};
 else
    Q:=Rationals();
    PQ:=PolynomialRing(Q);
    MOQ:=Integers();
    quoalg<t>,qmp:=quo<PQ|T>;
    Qpi:={ideal<MOQ | p> : p in badp};
/*
 else
    Qnf:=NumberField(Polynomial([0,1]) : DoLinearExtension);
    PQnf:=PolynomialRing(Qnf);
    MOQnf:=MaximalOrder(Qnf);
    quoalg<t>,qmp:=quo<PQnf|T>;
    Qpi:={ideal<MOQnf | p> : p in badp};
*/
 end if;

 vprintf FourDescent,1: "Computing 2-Selmer group in number field\n";
 LS2,L_to_LS2:=pSelmerGroup(quoalg,2,Qpi);
 vprintf FourDescent,1: "2-Selmer group size is 2^%o\n",Ngens(LS2);
 qstar_elts:={L_to_LS2(t) : t in {-1} join badp};
 LS2_without_qstar,starify:=quo<LS2|qstar_elts>;
 LS2wqs_length:=Ngens(LS2_without_qstar);
 vprintf FourDescent,1: "De-Q*'d 2-Selmer group size is 2^%o\n",LS2wqs_length;
 LS2_to_L:=Inverse(L_to_LS2); unstarify:=Inverse(starify);
 RB:=[LS2_to_L(unstarify(LS2_without_qstar.n)) : n in [1..LS2wqs_length]];
 vprintf FourDescent,2: "Unstarify done\n";
 ns:=[Z!Norm(t) : t in RB]; vprintf FourDescent,2: "Maps computed\n";
 fbase:={-1} join &join[{t[1] : t in PruneFactor(u,badp)}: u in ns];
 vala:=Vector(GF(2),[MyValuation(a,f) : f in fbase]);
 M:=Matrix(GF(2),[[MyValuation(n,f) : f in fbase]: n in ns]);
 ok,s,K:=IsConsistent(M,vala); if (not ok) then return false,_,_,_,_; end if;
 return true,s,K,RB,quoalg; end function;

function GetEpsilon(lb,RB,F) elt:=[RB[i] : i in [1 .. #RB] | lb[i] eq 1];
 if (#elt eq 0) then elt:=Parent(RB[1])!1; else elt:=&*elt; end if;
 return F!elt; end function;

function MakeExplicitMatrices(LS,RB,QA) ret:=[];
 for wx in LS do elt:=[RB[i] : i in [1 .. #RB] | wx[i] eq 1];
  if (#elt eq 0) then elt:=Parent(RB[1])!1; else elt:=&*elt; end if;
  redelt:=lll_reduce(EpsilonToCover(QA!elt)); Append(~ret,redelt);
 end for; return ret; end function;

function MakeExplicitMatrices2(root,kern,RB,QA)
 LS:=[]; for w in kern do Append(~LS,w+root); end for;
 return MakeExplicitMatrices(LS,RB,QA); end function;

procedure verbose_fiddle() d:=GetVerbose("FourDescent");
 if d eq 3 then
  SetVerbose("LocalQuartic",Max(GetVerbose("LocalQuartic"),1));
  SetVerbose("MinimiseFD",Max(GetVerbose("MinimiseFD"),1));
  SetVerbose("QISearch",Max(GetVerbose("QISearch"),1));
  SetVerbose("ReduceFD",Max(GetVerbose("ReduceFD"),1));
  SetVerbose("QuotientFD",Max(GetVerbose("QuotientFD"),1));
 end if; end procedure;

intrinsic FourDescent(S::[RngIntElt] : IgnoreRealSolubility:=false,
          RemoveTorsion:=false, RemoveGensEC:={}, RemoveGensHC:={}) -> SeqEnum
{Given [a,b,c,d,e], constructs the set of everywhere-locally-solvable
 four-covers for the two-covering y^2 = ax^4 + bx^3 + cx^2 + dx + e}
 require #S eq 5 : "Sequence must have 5 elements"; P:=PolynomialRing(Z);
 return FourDescent(P!Reverse(S): RemoveTorsion:=RemoveTorsion,
		    RemoveGensEC:=RemoveGensEC, RemoveGensHC:=RemoveGensHC,
		    IgnoreRealSolubility:=IgnoreRealSolubility); end intrinsic;

intrinsic FourDescent(H::CrvHyp[FldRat] : IgnoreRealSolubility:=false,
          RemoveTorsion:=false, RemoveGensEC:={}, RemoveGensHC:={}) -> SeqEnum
{Given a hyperelliptic curve, constructs the set of everywhere-locally-solvable
    2-coverings of it}
 f:=-Evaluate(DefiningPolynomial(H),[PolynomialRing(Rationals()).1,0,1]);
 return FourDescent(PolynomialRing(Integers())!f: RemoveTorsion:=RemoveTorsion,
		    RemoveGensEC:=RemoveGensEC, RemoveGensHC:=RemoveGensHC,
		    IgnoreRealSolubility:=IgnoreRealSolubility); end intrinsic;

intrinsic FourDescent(model::ModelG1 : IgnoreRealSolubility:=false,
          RemoveTorsion:=false, RemoveGensEC:={}, RemoveGensHC:={}) -> SeqEnum
{Given a genus one model of degree 2, constructs the set of everywhere-locally-solvable 2-coverings of it}
  require Degree(model) eq 2 : "Model should have degree 2";
  require BaseRing(model) cmpeq Integers() or BaseRing(model) cmpeq Rationals() :
    "Model should be defined over the rationals";
  model := Reduce(Minimise(model));
  P := PolynomialRing(Integers()); X:=P.1;
  f := Evaluate(Equation(model),[X,1]);
  return FourDescent(f: RemoveTorsion:=RemoveTorsion,
		    RemoveGensEC:=RemoveGensEC, RemoveGensHC:=RemoveGensHC,
		    IgnoreRealSolubility:=IgnoreRealSolubility); 
end intrinsic;

function d4_internal(f,ig_real) verbose_fiddle();
 vprintf FourDescent,1: "Minimised and reduced quartic is %o\n",f;
 lc:=LeadingCoefficient(f); E:=MinimalModel(AssociatedEllipticCurve(f));
 badp:=Set(PrimeDivisors(2*lc)) join
       Set([x[1] :  x in Factorization(Discriminant(f)) |
	     Gcd(4,TamagawaNumber(E,x[1])) ne 1]); // was x[2]>=1 (Stoll)
 vprintf FourDescent,1: "Bad primes are %o\n",badp;
 ok,root,gens,RB,QA:=d4_alg(f,badp);
 if not ok then vprint FourDescent,1: "Everything killed at the norm stage!";
  return [],_,_,_; end if;
 vprintf FourDescent,1:
  "Basis of %o Algebraic Generators found\n",Dimension(gens);
 if (QuarticNumberOfRealRoots(f) eq 4) and not ig_real then S:=Sign(lc);
  if (S eq +1) then
   b:=Vector(GF(2),[0,0,0,0]); gsrm:=Matrix(GF(2),[[1,0],[1,0],[0,1],[0,1]]);
  else b:=Vector(GF(2),[1,0,0,0]);
   gsrm:=Matrix(GF(2),[[1,0],[0,1],[0,1],[1,0]]); end if;
  RLM:=Matrix([Vector(GF(2),[(1-rr)/2 : rr in r]): r in RealLabels(RB)]);
  GM:=Matrix(Basis(gens)); GLRM:=GM*RLM*gsrm; gb:=(b+root*RLM)*gsrm;
  H,s,K:=IsConsistent(GLRM,gb);
  if H then root:=(s*GM)+root; gens:=K*GM;
  else vprintf FourDescent,1: "Infinite prime killed the Root\n";
   return [],_,_,_; end if;
  vprintf FourDescent,2:
   "Infinite prime leaves %o global Generators\n",Dimension(gens); end if;
 for p in badp do
  g,LF,LB:=LocalPoints(f,p); h:=hom<Parent(RB[1])->LF|LF.1>;
  RBLM:=Matrix([LB(h(e)): e in RB]); RL:=root*RBLM; GM:=Matrix(Basis(gens));
  GL:=GM*RBLM; GBL:=g[1];
  if (g[2] ne {}) then GS:=Matrix([b : b in g[2]]);
   GSRM:=Transpose(Matrix(Basis(Kernel(Transpose(GS)))));
   GLRM:=GL*GSRM; gb:=(GBL+RL)*GSRM; else GLRM:=GL; gb:=GBL+RL; end if;
  H,s,K:=IsConsistent(GLRM,gb);
  if H then root:=(s*GM)+root; gens:=K*GM;
  else vprintf FourDescent,1: "Prime %o killed the Root\n",p;
   return [],_,_,_; end if;
  vprintf FourDescent,2:
   "Prime %o leaves %o global Generators\n",p,Dimension(gens); end for;
  vprintf FourDescent,1: "Total of %o ELS four-covers\n",2^Dimension(gens);
 return root,gens,RB,QA; end function;

function IsNonzeroSquare(s) return (s ne 0) and IsSquare(s); end function;

function same(F,P,p,LIS,N,Q,beta) Fp:=GF(p); Z:=Integers();
 if Denominator(Rationals()!P[1]) mod p eq 0 then return false,_,_; end if;
 qludgep:=p*MaximalOrder(Q); //f2:=L^3*Evaluate(f,Parent(f).1/L);
 s,S:=LocalTwoSelmerMap(N,qludgep); M:=Codomain(s); c:=0;
 e:=GeneratorsForQp2(p); M2,emb:=quo<M|[s(ee) : ee in e]>; SHIFTS:={};
 deabs:=func<t|Vector(GF(2),Eltseq(t))>; zz:=func<t|deabs(emb(s(t)))>;
 while true do r:=Random(Fp); c:=c+1; if c ge 10 then return false,_,_; end if;
  while r eq 0 or not IsNonzeroSquare(Evaluate(F,r)) do
   r:=Random(Fp); end while;
  Oimage:=emb(s(Z!r-beta));
  H:=HyperellipticCurve(PolynomialRing(Fp)!F); Ep:=ChangeRing(Curve(P),Fp);
  C,m:=EllipticCurve(H,H![r,Sqrt(Evaluate(F,r))]); _,i:=IsIsomorphic(Ep,C);
  pt:=i(Ep!P); if pt[1] eq 0 then continue; end if; b:=true;
  try x:=Inverse(m)(pt)[1]; image:=emb(s(Z!x-beta));
   c4,c6:=Explode(cInvariants(Ep));
   if p mod 4 eq 1 and c6 eq 0 then PT:=i(Ep![Fp!-P[1],P[2]*Sqrt(Fp!-1)]);
    i1:=emb(s(Z!Inverse(m)(PT)[1]-beta));
    if i1 ne image then return false,_,_; end if; end if;
   if p mod 3 eq 1 and c4 eq 0 then r3:=(-1+Sqrt(Fp!-3))/2; assert r3^3 eq 1;
    PT:=i(Ep![r3*P[1],Fp!P[2]]); i1:=emb(s(Z!Inverse(m)(PT)[1]-beta));
    if i1 ne image then return false,_,_; end if;
    PT:=i(Ep![r3^2*P[1],Fp!P[2]]); i2:=emb(s(Z!Inverse(m)(PT)[1]-beta));
    if i2 ne image then return false,_,_; end if; end if;
  catch ERROR b:=false; end try;
 if b then return true,deabs(image+Oimage),zz; end if; end while; end function;

function HasKDivisionPoints(PT,f,n) f:=PolynomialRing(Rationals())!f;
 if #Roots(f) ne 0 then return #DivisionPoints(PT,n) ne 0; end if;
 if IsIrreducible(f) then K:=NumberField(f); EK:=ChangeRing(Curve(PT),K);
  return #DivisionPoints(EK!PT,n) ne 0; end if;
 F:=Factorization(f); K:=NumberField(F[1][1]); L:=NumberField(F[2][1]);
 EK:=ChangeRing(Curve(PT),K);
 if #DivisionPoints(EK!PT,n) eq 0 then return false; end if;
 EL:=ChangeRing(Curve(PT),L); return #DivisionPoints(EL!PT,n) ne 0;
 end function;

function twodep(gb,PTS,f) E:=Curve(Random(PTS)); M:=[]; gb:=Max([5,gb,#PTS]);
 D:=Integers()!Discriminant(E); p:=101; F2:=GF(2);
 PTS:=[v : v in PTS | HasKDivisionPoints(v,f,2) eq false];
 if #PTS eq 0 then return PTS; end if;
 while #M lt gb+#PTS do p:=NextPrime(p);
  if D mod p eq 0 then continue; end if;
  if LCM([Denominator(Rationals()!P[1]): P in PTS]) mod p eq 0
   then continue; end if;
  if #Roots(f,GF(p)) le 3 then continue; end if;
  Fp:=GF(p); Ep:=ChangeRing(E,Fp);
  DP:=[x : x in DivisionPoints(Ep!0,2) | x ne Ep!0];
  if #DP eq 3 then Remove(~DP,Random([1..3])); end if;
   for dp in DP do
    v:=[#DivisionPoints(Ep!pt+dp,2) ne 0 select F2!0 else F2!1 : pt in PTS];
    if &or[u ne 0 : u in v] then M:=M cat [v]; end if; end for; end while;
 B:=Basis(Kernel(Transpose(Matrix(M))));
 C:=[b: b in B | HasKDivisionPoints(v,f,2)
     where v:=&+[PTS[i]*w[i] : i in [1..#PTS]]
     where w:=ChangeUniverse(Eltseq(b),Integers())];
 if #C lt #B then return twodep(gb+5,Set(PTS),f); end if;
 if IsEmpty(C) then return PTS; end if;
 v:=Eltseq(Random(C)); Remove(~PTS,Min([t : t in [1..#v] | v[t] ne 0]));
 return twodep(gb,Set(PTS),f); end function;

function d4_remove(f,root,gens,RB,RG,QA)
 P:=twodep(5,RG,f); d:=Dimension(gens); // root is not used here??
 vprintf QuotientFD,1: "Quotienting by %o basis elements\n",#P;
 if d lt #P then vprintf FourDescent,1:
  "Quotienting kills the Root\n"; return false,gens; end if;
 if d eq #P then vprintf FourDescent,1 : "Quotienting leaves only the Root\n";
  return true,gens; end if; if #P eq 0 then return true,[]; end if;
 R:=RowSpace(One(MatrixAlgebra(GF(2),Dimension(gens)))); U:=Set(R);
 V:=[U : i in [1..#P]]; START:=2000; pp:=NextPrime(START); WARN:=START+2000;
 lc:=LeadingCoefficient(f); f_Q:=PolynomialRing(Rationals())!f;
 f2:=lc^3*Evaluate(f,Parent(f_Q).1/lc);
 Q:=NumberField(Polynomial([0,1]):DoLinearExtension);
 N<alpha>:=quo<PolynomialRing(Q)|f2>; beta:=alpha/lc;
 while true do pp:=NextPrime(pp);
  if pp gt WARN then WARN:=WARN+2000;
   vprintf QuotientFD,1:
     "WARNING: The function d4_remove in FourDescent is not terminating.\n"*
     "Attempting to use global method rather than the local one.\n"*
     "Try running FourDescent w/o RemoveTorsion and RemoveGens{EC/HC}.\n";
   for i in [1..#P] do if #V[i] le 1 then continue i; end if;
    k0:=Random(V[i]); C:=AssociativeArray(Universe(V[i]));
    for k in V[i] do
     A:=[RB[i] : i in [1 .. #RB] | (root+k*Matrix(Basis(gens)))[i] eq 1];
     C[k]:=Minimize(GenusOneModel(EpsilonToCover(QA!&*A))); end for;
    x:=P[i][1]; y:=P[i][2]; I:=cInvariants(Curve(P[i]))[1];
//  G:=Minimize(GenusOneModel([1,0,-x/6,y/27,I/12-x^2/432])); 
    G:=Minimize(GenusOneModel([1,0,-x/6,y/27,(I/36-x^2)/432]));
//  G:=GenusOneModel(2,P[i]); // would also work here
    assert exists(im){k : k in V[i] | IsEquivalent(AddCovers(G,C[k0]),C[k])};
    V[i]:={im-k0}; end for; break; end if;
  if Discriminant(f) mod pp eq 0 or lc mod pp eq 0 then continue; end if;
  LIS:=LocalImageSize(f,pp); if LIS eq 0 then continue; end if;
  fp:=PolynomialRing(GF(pp))!f; Ep:=ChangeRing(Curve(Random(P)),GF(pp));
  for i in [1..#P] do if #V[i] le 1 then continue i; end if; v:=#V[i];
   b,im,zz:=same(f,P[i],pp,LIS,N,Q,beta);
   if b then vprintf QuotientFD,2: "Prime %o: pt %o image: %o\n",pp,P[i],im;
    h:=hom<Parent(RB[1])->N|N.1>; RBLM:=Matrix([zz(h(e)): e in RB]);
    GL:=Matrix(Basis(gens))*RBLM; b,s,K:=IsConsistent(GL,im);
    if not b then vprintf QuotientFD,1: "Hmm no idea about prime %o\n",pp;
     continue; end if; // this fails in some cases ? // assert b;
    V[i]:=V[i] meet Set([s+k : k in K]);
    if v ne #V[i] then vprintf QuotientFD,1:
     "%o reduces Im(%o) to size %o\n",pp,P[i],#V[i];
     if #V[i] eq 1 then vprintf QuotientFD,2:
      "Image is %o\n",Random(V[i]); end if; end if; end if;
   if #V[i] eq 0 then "reduced V[i] size to zero??"; end if; end for;
  if &and[#v le 1: v in V] then break; end if; end while;
 W:=sub<R|[Random(v) : v in V | #v eq 1]>; //hope this termination suffices..
 return true,W*Matrix(Basis(gens)); end function;

intrinsic FourDescent(f::RngUPolElt[RngInt] : IgnoreRealSolubility:=false,
          RemoveTorsion:=false, RemoveGensEC:={}, RemoveGensHC:={}) -> SeqEnum
{Constructs the set of everywhere-locally-solvable covers for
 a two-covering y^2 = f(x)}
 require Degree(f) eq 4: "Polynomial must have degree 4"; b:=true; RG:={};
 require #Roots(PolynomialRing(Rationals())!f) eq 0: "Quartic has a root!";
 if #RemoveGensHC ne 0 then
  require Curve(Random(RemoveGensHC)) eq HyperellipticCurve(f):
    "Parent of RemoveGensHC must be the given Hyperelliptic Curve";
  E,m:=AssociatedEllipticCurve(f); RG join:={m(x) : x in RemoveGensHC}; end if;
 if #RemoveGensEC ne 0 then E:=AssociatedEllipticCurve(f);
  b,m:=IsIsomorphic(Curve(Random(RemoveGensEC)),E);
  require b: "Parent of RemoveGensEC must be the AssociatedEllipticCurve";
  RG join:={m(x) : x in RemoveGensEC}; end if;
 f:=QuarticReduce(QuarticMinimise(f));
 root,gens,RB,QA:=d4_internal(f,IgnoreRealSolubility);
 if root cmpeq [] then return []; end if;
 bp:=SetToSequence(Set(PrimeDivisors(2*LeadingCoefficient(f))
		       cat [x[1] : x in Factorization(Discriminant(f))]));
 if RemoveTorsion then T,m:=TorsionSubgroup(AssociatedEllipticCurve(f));
  G:=SylowSubgroup(T,2); RG join:={m(g) : g in Generators(G)}; end if;
 if #RG ne 0 then b,T:=d4_remove(f,root,gens,RB,RG,QA); else T:=[]; end if;
 if not b then return []; end if;
 if T cmpne [] then q,m:=quo<gens|T>; mi:=Inverse(m);
  gens:=sub<gens|[mi(x) : x in Generators(q)]>;
  vprintf FourDescent,1:
  "Quotienting leaves %o four-covers\n",2^Dimension(gens); end if;
 mats:=MakeExplicitMatrices2(root,gens,RB,QA);
 mats := [[ChangeRing(M,Rationals()): M in MM]: MM in mats];
 models := [GenusOneModel(MM): MM in mats];
 vprintf FourDescent,1: "Minimising four-coverings\n";
 vtime FourDescent,1:
 models := [Minimise(model): model in models];
 vprint FourDescent,1: "Reducing four-coverings\n";
 vtime FourDescent,1:
 models := [Reduce(model): model in models];
 return [Curve(x) : x in models]; end intrinsic;
