freeze;

import "small_classno.m": SC,NZ; 
import "FourDesc/utils.m" : QFFromMatrix;

function check_manin(E) E:=MinimalModel(E);
 if RootNumber(E) eq -1 then return 1; end if;
 I,t:=IsogenousCurves(E); if #I eq 1 then return 1; end if;
 for i in [1..#I] do if E eq I[i] then w:=i; break; end if; end for;
 N:=Conductor(E); if N eq 11 and w eq 1 then return 5; end if;
 if IsSquare(N-64) and IsPrime(N) and w eq 1 then return 2; end if;
 if N eq 14 and (w eq 1 or w eq 2) then return 3; end if;
 if N eq 27 and (w eq 1 or w eq 2) then return 3; end if;
 if N eq 15 or N eq 17 then
  if w eq 1 then return 4; elif w eq 2 or w eq 3 then return 2; end if; end if;
 if N eq 20 and (w eq 1 or w eq 3) then return 2; end if;
 if N eq 21 and w eq 1 then return 2; end if;
 if N eq 32 and w ne 4 then return 2; end if;
 if N eq 80 and w eq 3 and t eq 6 then return 2; end if;
 if w ne 1 then return 1; end if;
 if (N eq 24 or N eq 40 or N eq 48 or N eq 64 or N eq 80)
  then return 2; end if; if t ne 2 and t ne 9 and t ne 4 then return 1; end if;
 if N eq 128 and cInvariants(E)[1] eq 112 then return 2; end if;
 if Valuation(N,2) eq 2 and IsPrime(N div 4) and IsSquare((N div 4)-4)
  and cInvariants(E)[1] eq Discriminant(E)-16 and t eq 2 then return 2; end if;
 if Valuation(N,2) eq 4 and IsPrime(N div 16) and IsSquare((N div 16)-4)
  and cInvariants(E)[1] eq Discriminant(E)-16 and t eq 2 then return 2; end if;
 if w ne 1 then return 1; end if;
 if t eq 4 and cInvariants(E)[1] eq Discriminant(E)+16 then
  b,P:=IsSquare(Discriminant(E)+64);
 if b then P:=Integers()!(P-8); Q:=P+16;
  if P mod 4 eq 1 then P:=-P; Q:=-Q; end if; assert Discriminant(E) eq P*Q;
   bp,p:=IsPrimePower(Abs(P)); bq,q:=IsPrimePower(Abs(Q)); b:=bp and bq;
  if b and (p mod 4 eq 3 or q mod 4 eq 3) then return 2;
  end if; end if; end if;
 if t ne 9 then return 1; end if;
 x:=PolynomialRing(Rationals()).1; r:=Roots(x^4-24*x-cInvariants(E)[1]);
 r:=[x[1]-3 : x in r]; r:=[x : x in r | Discriminant(E) eq x*(x^2+9*x+27)];
 if #r eq 0 then return 1; end if; r:=Integers()!r[1];
 if not IsPrimePower(r^2+9*r+27) then return 1; end if;
 if &and[f[1] mod 6 ne 1 : f in Factorization(r)] then return 3;
 else return 1; end if; end function;

intrinsic ManinConstant(E::CrvEll[FldRat]) -> RngIntElt
{Gives the conjectural Manin constant [for X0(N)]
 for a rational elliptic curve E of conductor N.}
 return check_manin(E); end intrinsic;

function lambda_at_p(E,p)
 n:=Valuation(Discriminant(E),p : Check:=false);
 K:=KodairaSymbol(E,p : Check:=false);
 if K eq KodairaSymbol("II") or K eq KodairaSymbol("II*")
  then return [n/12]; end if;
  if K eq KodairaSymbol("III") then return [n/12,(n-3)/12]; end if;
  if K eq KodairaSymbol("III*") then return [n/12,(n-9)/12]; end if;
  if K eq KodairaSymbol("IV") then return [n/12,(n-4)/12]; end if;
  if K eq KodairaSymbol("IV*") then return [n/12,(n-8)/12]; end if;
  if K eq KodairaSymbol("In") then R:=[];
   for i in [0..Floor(n/2)] do R:=R cat [(n/12)-(i/2)+(i^2/(2*n))]; end for;
   return R; end if;
  if K eq KodairaSymbol("I0*") then return [n/12,(n-6)/12]; end if;
  if K eq KodairaSymbol("In*") then
   m:=StringToInteger(Substring(S,2,#S-2)) where S is Sprint(K);
   return [n/12,m/12+(n-m-6)/12,-m/24+(n-m-6)/12]; end if;
  error "Incorrect KodairaSymbol?"; end function;

function lambdas(E,prec) S:=[0];
 for p in BadPrimes(E) do
  S:=[a+b : a in S,
       b in [s*2*Log(RealField(prec)!p) : s in lambda_at_p(E,p)]]; end for;
  return S; end function;

function MakeD(D)
 if (D mod 4 ne 1) then return 4*D; else return D; end if; end function;

function check(D,N : fund:=false) if D ge 0 then return false; end if;
 if fund and not IsFundamental(D) then return false; end if;
 return IsSquare(Integers(4*N)!D); end function;

function check_ec(D,pl,E) // pl factorisation [<p1,e1>, ...]
 if not IsFundamental(D) then return false; end if;
 if D ge 0 then return false; end if;
 for j in pl do k:=KroneckerSymbol(D,j[1]);
  if (k ne 1 and j[2] gt 1) then return false; end if;
  if (j[2] eq 1 and k eq -1) then return false; end if;
  if (k eq 0 and FrobeniusTraceDirect(E,j[1]) ne -1) then return false; end if;
 end for; return true; end function;

intrinsic HeegnerDiscriminants
(E::CrvEll[FldRat],lo::RngIntElt,hi::RngIntElt :
 Fundamental:=false, Strong:=false) -> SeqEnum
{Find Heegner discriminants for an elliptic curve in a given range.}
 if Strong then FAC:=Factorization(Conductor(E));
  if lo lt 0 then return [d : d in [lo..hi] | check_ec(d,FAC,E)];
  else return [-d : d in [lo..hi] | check_ec(-d,FAC,E)]; end if; end if;
 N:=Conductor(E);
 if lo lt 0 then return [d : d in [lo..hi] | check(d,N : fund:=Fundamental)];
 else return [-d : d in [lo..hi] | check(-d,N : fund:=Fundamental)]; end if;
end intrinsic;

intrinsic HeegnerDiscriminants
(N::RngIntElt,lo::RngIntElt,hi::RngIntElt : Fundamental:=false)  -> SeqEnum
{Find Heegner discriminants in a given range for a given level.}
 require N ge 0: "Level must be positive";
 if lo lt 0 then return [d : d in [lo..hi] | check(d,N : fund:=Fundamental)];
 else return [-d : d in [lo..hi] | check(-d,N : fund:=Fundamental)]; end if;
end intrinsic;

function matapply(f,A) a,b,c:=Explode(Eltseq(f));
 W,X,Y,Z:=Explode(A); Q:=W*Z-X*Y; c1:=(a*W^2+b*Y*W+c*Y^2) div Q;
 c2:=((2*a*X+b*Z)*W+(b*Y*X+2*c*Z*Y)) div Q; c3:=(a*X^2+b*Z*X+c*Z^2) div Q;
 return QuadraticForms(Discriminant(f))!<c1,c2,c3>; end function;

function atk_leh(Q,N)
  Y:=N; Z:=Q; X:=Integers()!(-1/(Integers(Q)!(N div Q))); W:=(X*N+Q) div Q;
  return [W,X,Y,Z]; end function;

function myroots(f,p,v) fp:=ChangeRing(f,GF(p));
 if fp eq 0 then R:=[<x,1> : x in GF(p)]; else R:=Roots(fp); end if;
 if v eq 1 then return [r[1] : r in R]; end if; T:=[];
 for r in R do u:=Integers()!r[1];
 S:=myroots(ExactQuotient(Evaluate(f,u+p*Parent(f).1),p),p,v-1);
 T cat:=[u+p*Integers()!s : s in S]; end for; return T; end function;

function qc_solve(f) m:=#BaseRing(Parent(f)); FAC:=Factorization(m);
 A:={0}; m:=1; f:=ChangeRing(f,Integers());
 for t in FAC do R:=myroots(f,t[1],t[2]); C:=[Integers()!r : r in R];
 A:=&join{{ChineseRemainderTheorem([a,c],[m,t[1]^t[2]]) : a in A} : c in C};
 m*:=t[1]^t[2]; end for; return A; end function;

function GetSolutions(q,m)
 if m gt 100 then
  return qc_solve(ChangeRing(Polynomial(Reverse(q)),Integers(m))); end if;
 return [x: x in [0..m-1] | (q[1]*x^2+q[2]*x+q[3]) mod m eq 0]; end function;

function zsum(E,X) if #X eq 0 then return E![0,1,0]; end if; T:=X[1][2];
 for i in [2..#X] do T:=T-&*[X[j][1] : j in [1..i]]*X[i][2]; end for;
 return T; end function;

function period(E,Q,eps) AL:=atk_leh(Q,Conductor(E));
 s:=9+Max(0,-Ceiling(Log(10,RealPeriod(E))));
 s:=Max(s,9+Max(0,-Ceiling(Log(10,Imaginary(Periods(E)[2])))));
 pt1:=-AL[4]/AL[3]+ComplexField(s)!Sqrt(-AL[4])/AL[3];
 pt2:=(AL[1]*pt1+AL[2])/(AL[3]*pt1+AL[4]);
 mp:=ModularParametrization(E,[pt1,pt2]); tors:=mp[1]-eps*mp[2];
 return tors; end function;

intrinsic HeegnerTorsionElement(E::CrvEll[FldRat],Q::RngIntElt) -> PtEll
{Compute the period of an Atkin-Lehner operator for an elliptic curve}
 M,m:=MinimalModel(E);
 N:=Conductor(M); require N mod Q eq 0 and GCD(N div Q,Q) eq 1:
 "Q must divide the conductor N with gcd(Q,N/Q)=1";
 if check_manin(M) ne 1 then
  "Warning: The X0-Manin constant is probably not 1."; end if;
 if Q eq 1 then return E!0; end if; BA:=BestApproximation;
 if #TorsionSubgroup(M) eq 1 then return E!0; end if;
 pd:=period(M,Q,&*[RootNumber(M,f[1]) : f in Factorization(Q)])*check_manin(M);
 rp,ip:=Explode(Periods(M : Precision:=Precision(pd))); rp:=Real(rp);
 pd:=pd-ip*Round(Imaginary(pd)/Imaginary(ip)); pd:=pd-rp*Round(Real(pd)/rp);
 if Abs(Real(pd)) lt rp/10 and Abs(Imaginary(pd)) lt Abs(Imaginary(ip)/3)
 then return E!0; end if; u:=[Real(x) : x in EllipticExponential(M,pd)];
 return Inverse(m)(M![BA(u[1],10),BA(u[2],10)]); end intrinsic;

function ALx(N,FN,arr)
 return &*[FN[x][1]^Valuation(N,FN[x][1]) : x in arr]; end function;

function largest_square_divisor(n) if n eq 1 then return 1; end if;
 return &*[f[1]^(f[2] div 2) : f in Factorization(n)]; end function;

function get_bs(N,D)
 WQ:=[fac[1] : fac in Factorization(Gcd(D,N)) | Valuation(D,fac[1]) le 1];
 if Gcd(D,N) mod 4 eq 2 and Valuation(D,2) le 3 then WQ cat:=[2]; end if;
 wQ:=[q^Valuation(N,q) : q in WQ]; if #wQ eq 0 then wQ:=[Integers()|]; end if;
 FN:=Factorization(N div &*wQ); FN:=[f : f in FN | Gcd(D,f[1]) eq 1];
 aL:=[x[1]^Valuation(N,x[1]) : x in FN];
 if #aL eq 0 then aL:=[Integers()|]; end if;
 _,BAD:=Valuation(N div (&*aL*&*wQ),2); bad:=Factorization(BAD);
 v2:=Valuation(N,2); _,oa:=Valuation(&*aL,2); _,oq:=Valuation(&*wQ,2);
 bs:=[Integers()!x : x in AllSquareRoots(Integers(oa)!D)];
 two:=[Integers()!x : x in AllSquareRoots(Integers(4*2^v2)!D)];
 T:=[Integers()!x : x in SetToSequence(Set([Integers(2*2^v2)!x : x in two]))];
 sr:=Integers()!Sqrt(Integers(oq)!D); BS:=[];
 for bd in bad do r:=0; m:=bd[1]^bd[2];
  while r eq 0 do r:=Integers()!Random(AllSquareRoots(Integers(m)!D));
   if bd[2] eq 1 then break; end if; end while;
  sr:=ChineseRemainderTheorem([sr,r],[oq,m]); oq*:=m; end for;
 for t in T do
  BS cat:=[ChineseRemainderTheorem([b,t],[oa,2*2^v2]) : b in bs]; end for;
 bs:=[ChineseRemainderTheorem([b,sr],[oa*2*2^v2,oq]) : b in BS];
 return bs,WQ,wQ,aL,FN; end function;

function GetForms(E,D,pair,use_wQ,use_AL,ignore_torsion)
 if pair and not ignore_torsion then
  error "Must ignore_torsion when using pairing"; end if;
 fr:=[]; fl:=[];  QD:=QuadraticForms(D); h:=ClassNumber(QD); N:=Conductor(E);
 bs,WQ,wQ,aL,FAC:=get_bs(N,D); if #WQ eq 0 then use_wQ:=false; end if;
 if not use_AL then bs:=[bs[1]]; end if; b0:=bs[1];
 if #FAC eq 0 then use_AL:=false; end if; FN:=Factorization(N);
 rn:=[RootNumber(E,x[1]) : x in FN]; wQs:=[]; ws:=[]; acs:=[]; wQT:=[];
 if (use_AL or use_wQ) and not ignore_torsion and #TorsionSubgroup(E) ne 1
  then AL:=[atk_leh(ALx(N,FN,Remove([1..#FN],i)),N) : i in [1..(#FN)-1]];
  if RootNumber(E) eq +1 then rn:=[-x : x in rn]; end if;
  if RootNumber(E) eq +1 then Append(~AL,atk_leh(N,N)); end if;
  s:=9+Max(0,-Ceiling(Log(10,RealPeriod(E))));
  s:=Max(s,9+Max(0,-Ceiling(Log(10,Imaginary(Periods(E)[2])))));
  t1:=[-e[4]/e[3]+ComplexField(s)!Sqrt(-e[4])/e[3] : e in AL];
  t2:=[(AL[i][1]*t1[i]+AL[i][2])/(AL[i][3]*t1[i]+AL[i][4]) : i in [1..#AL]];
  if #t1 ne 0 and #t2 ne 0 then mp:=ModularParametrization(E,t1 cat t2);
  else mp:=[]; end if;
  tors:=[mp[i]-rn[i]*mp[i+#AL] : i in [1..#AL]];
  if RootNumber(E) eq +1 then tors[#AL]:=mp[#AL]+mp[2*#AL]; end if;
  rp,ip:=Explode(Periods(E)); T:=[]; rp:=Real(rp);
  tors:=[x-ip*Round(Imaginary(x)/Imaginary(ip)) : x in tors];
  tors:=[x-rp*Round(Real(x)/rp) : x in tors];
  for t in tors do
   if Abs(Real(t)) lt rp/10 and Abs(Imaginary(t)) lt Abs(Imaginary(ip)/3)
    then T cat:=[E![0,1,0]];
   else u:=[Real(x) : x in EllipticExponential(E,t)];
    T cat:=[E![BestApproximation(u[1],10),BestApproximation(u[2],10)]];
    end if; end for;
  if RootNumber(E) eq -1 then T:=[-t : t in T];
  else t:=T[#T]; T:=[T[i]+T[#T]*rn[i] : i in [1..(#T)-1]]; T cat:=[t]; end if;
    /* sigh, this is a mess [to compute T for the largestprime]
      I compute that phi(tau)=ep*eq*phi(Wpq(tau))-ep*eq*Tq+Tp
      where Tp=-ep*phi(Wp(ioo)), and we know Tp for all other p and TN
      Thus I get that Tpq=Tp-ep*eq*Tq and iterate  (p,q can be composite) */
  if RootNumber(E) eq -1 then T cat:=[E![0,1,0]]; end if; t:=T[1];
   /* first compute t for N/biggestprime then get TP as TN-ep*T_{N/p} */
  if RootNumber(E) eq +1 then rn:=[-x : x in rn]; end if;
  for i in [2..(#FN)-1] do t:=t-T[i]*&*[rn[j] : j in [1..i]]; end for;
  T[#T]:=T[#T]-rn[#FN]*t; //was T[#T]:=T[#T]-RootNumber(E)*t; ??!
  if #T eq 1 and RootNumber(E) eq +1 then T[1]:=t; end if;
 else T:=[E![0,1,0] :  i in [1..#FN]]; end if; //done with torsion
 if RootNumber(E) eq +1 then T:=[rn[i]*T[i] : i in [1..#FN]]; end if; //??!
 dF:=[x : x in WQ | RootNumber(E,x) eq +1]; //maybe ap=-1
 DIV:=[1]; drn:=[RootNumber(E,x) : x in dF]; F:=aL; rnDIV:=[];
 if use_wQ and #dF ne 0 then DIV:=[&*x : x in Subsets(Set(dF))]; end if;
 for i in [1..#bs] do b:=bs[i]; eps:=1; Q:=1;
  for j in [1..#F] do PE:=F[j];
   if PE mod 2 eq 0 then pe:=2*PE; else pe:=PE; end if;
   if (b-b0) mod pe ne 0 then Q*:=PE; eps*:=rn[j]; end if; end for;
  acs[i]:=(b^2-D) div (4*N);
  for k in [1..#DIV] do wQs[i+(k-1)*#bs]:=atk_leh(DIV[k]*Q,N);
   ws[i+(k-1)*#bs]:=eps; end for; end for; Ps:=[x[1] : x in FN];
 for a in [1..1000000] do if a eq 1000000 then assert false; end if;
  for i in [1..#bs] do /* could use a different method */
   b:=bs[i]; ac:=acs[i]; S:=GetSolutions([N,b,ac],a);
   for s in S do
    ac:=((b+2*N*s)^2-D) div (4*N); f:=QD!<N*a,(b+2*N*s),ac div a>;
    if Gcd(Eltseq(f)) ne 1 then continue; end if;
    for d in [1..#DIV] do w:=ws[i+(d-1)*#bs];
     AL:=wQs[i+(d-1)*#bs]; g:=matapply(f,AL); gr:=Reduction(g); Q:=AL[4];
     if not gr in fr then
      Z:=zsum(E,[<rn[i],T[i]> : i in [1..#FN] | Q mod Ps[i] eq 0]);
      if pair eq true then gri:=Reduction(QD!<g[1] div N,-g[2],g[3]*N>);
       if gr ne gri then Append(~fr,gri); w:=2*w;
       end if; end if;
      Append(~fr,gr); Append(~fl,<f,w,Z>); if #fr eq h then break a; end if;
      end if; end for; end for; end for; end for;
 return fl[#fl][1][1] div N,[Eltseq(x[1]) : x in fl],
	  [x[2] : x in fl],[x[3] : x in fl]; end function;

procedure close(c,N,~m0,~c0,~d0,u,v)
 if c le 0 then return; end if; d:=Round(-c*u); t:=1+2*Floor(d+c*u);
 while Gcd(c*N,d) ne 1 do d:=d-t; t:=-Sign(t)*(Abs(t)+1); end while;
 r:=(c*u+d)^2+c^2*v; if r lt m0 then m0:=r; c0:=c;d0:=d; end if; end procedure;

function coh(f,N) a,b,c:=Explode(Eltseq(f)); assert a mod N eq 0;
 u:=-b/(2*a/N); v:=(4*a*c-b^2)/(2*a/N)^2; c0:=0; d0:=1; m0:=1; L:=Sqrt(m0/v);
 if L le 1 then return DiagonalMatrix([1,1]); end if; c:=0;
 cf:=ContinuedFraction(u); PN:=[0,1]; QN:=[1,0]; V:=[1,0,0,1];
 for i in [1..#cf] do Append(~PN,PN[#PN-1]+cf[i]*PN[#PN]); end for;
 for i in [1..#cf] do Append(~QN,QN[#QN-1]+cf[i]*QN[#QN]); end for;
 Remove(~PN,1); Remove(~PN,1); Remove(~QN,1); Remove(~QN,1); i:=1;
 while i le #QN do d:=-PN[i]; c:=QN[i]; close(c+2,N,~m0,~c0,~d0,u,v);
  close(c-1,N,~m0,~c0,~d0,u,v); close(c+1,N,~m0,~c0,~d0,u,v);
  close(c,N,~m0,~c0,~d0,u,v); close(c-2,N,~m0,~c0,~d0,u,v); i:=i+1; end while;
 g,a0,b0:=XGCD(d0,-N*c0); V:=[d0,-b0,-c0*N,a0];
 if V eq [1,0,0,1] then return Matrix(2,2,V); end if;
 return Matrix(2,2,V)*coh(matapply(f,V),N); end function;

function ambig(D,x) Q:=QuadraticForms(D);
 if D mod 4 eq 1 then return Q!<x,x,(x^2-D) div (4*x)>; end if;
 if D mod 4 eq 0 and IsOdd(x) then return Q!<x,0,-D div (4*x)>; end if;
 if D mod 16 eq 12 then return Q!<2,2,(4-D) div 8>;
 else v:=Valuation(D,2); return Q!<2^(v-2),0,-D div 2^v>; end if; end function;

function get_forms_internal(N,D,AL,use_pairing) pr:=(2*N) div &*AL;
 Ps:=[Integers()|x : x in AL | Gcd([N,D,x]) ne 1];
 Q:=[&*x : x in Subsets(Set(Ps))]; QD:=QuadraticForms(D);  Qs:={ambig(D,1)};
 A:=[&*x : x in Subsets(Set([Integers()|x : x in AL | Gcd([N,D,x]) eq 1]))];
 ALL:=AllSquareRoots(Integers(4*N)!D); if #ALL eq 0 then return []; end if;
 Qs join:={Reduction(&*x) : x in Subsets({ambig(D,x) : x in Ps}) | #x ne 0};
 b:=Integers()!ALL[1]; F:=QD!<N,b,(b^2-D) div (4*N)>; fr:={}; fl:=[];
 aL:=[<Integers()!Integers(2*N)!matapply(F,atk_leh(q,N))[2],q> : q in A];
 G,m:=ClassGroup(QuadraticForms(D)); S:=SylowSubgroup(G,2);
 QQs:=[G!x : x in S | m(x) in Qs]; Qs:=[m(x) : x in QQs];
 h:=#G; LIMIT:=Floor((h/#QQs)*5+10);
 if not IsFundamental(D) then LIMIT:=10^8; end if;
 for a in [1..LIMIT] do
  for al in aL do b:=al[1]; S:=GetSolutions([N,b,(b^2-D) div (4*N)],a);
   for s in S do f:=QD!<N*a,(b+2*N*s),((b+2*N*s)^2-D) div (4*N*a)>;
    if Gcd(Eltseq(f)) ne 1 then continue; end if; w:=1;
    g:=matapply(f,atk_leh(al[2],N)); gr:=Reduction(g);
    if not gr in fr then gri:=gr;
     if use_pairing eq true then gri:=Reduction(QD!<g[1] div N,-g[2],g[3]*N>);
     if not gr in [gri*am : am in Qs] then w:=2; end if; end if;
     for am in Qs do Include(~fr,gr*am); Include(~fr,gri*am); end for;
     Append(~fl,<f,w*#QQs,al[2]>); if #fr eq h then break a; end if; end if;
   end for; end for; end for;
 if #fr ne h then LE:=Set([m(g) : g in G]) diff fr;
  vprintf Heegner,2: "Using second method to find forms at %o\n",LIMIT;
  while #LE ne 0 do ran:=Random(LE); r:=ran*F^(-1);
   while Gcd(r[1],N) ne 1 do r:=r*Matrix([[0,1],[-1,1]]);
    r:=r*Matrix([[1,Random([-3..3])],[0,1]]); end while; C:=Composition(r,F);
   I:=[<D*coh(D,N) where D:=matapply(C,atk_leh(al[2],N)),al[2]> : al in aL];
   X:=I[w] where _,w:=Min([i[1][1] : i in I]); w:=1;
   g:=matapply(X[1],atk_leh(X[2],N)); gr:=Reduction(g); gri:=gr; // gr eq ran;
   if use_pairing eq true then gri:=Reduction(QD!<g[1] div N,-g[2],g[3]*N>);
    if not gr in [gri*am : am in Qs] then w:=2; end if; end if;
   for am in Qs do Exclude(~LE,gr*am); Exclude(~LE,gri*am); end for;
   Append(~fl,<X[1],w*#QQs,X[2]>); end while; end if;
 Sort(~fl,func<x,y|(x[1][1]-y[1][1])*10^20+(x[1][2]-y[1][2])>);
 assert &+[x[2] : x in fl] eq h; return fl; end function;

function get_forms(N,D,AL)
 return [f[1] : f in get_forms_internal(N,D,AL,false)]; end function;

function get_forms_ec(E,D,use_pairing,use_wQ,use_AL,ignore_torsion)
 if use_pairing and not ignore_torsion then
  error "Must ignore torsion when using pairing"; end if;
 N:=Conductor(E);  Z:=Integers(); AL:=[Z|]; wQ:=[Z|];
 FN:=Factorization(N); Q:=QuadraticForms(D);
 if use_AL then AL:=[Z| f[1]^f[2] : f in FN | Gcd(f[1],D) eq 1]; end if;
 if use_wQ then
  wQ:=[Z| f[1]^f[2] : f in FN | Gcd(f[1],D) ne 1 and Valuation(D,f[1]) le 1];
  if Gcd(D,N) mod 4 eq 2 and Valuation(D,2) le 3 then wQ cat:=[2]; end if;
 end if; //might be useful in more circumstances for p^2|gcd(D,N) ?!
 ALL:=AL cat wQ; G:=get_forms_internal(N,D,ALL,use_pairing); K:=[];
 if use_AL or use_wQ then
  RN:=[x : x in ALL | RootNumber(E,w) eq -1 where _,w:=IsPrimePower(x)];
  G:=[<t[1],t[2]*w,t[3]>
      where w:=&*[Z| -1 : y in RN | t[3] mod y eq 0] : t in G]; end if;
 if (use_AL or use_wQ) and not ignore_torsion and #TorsionSubgroup(E) ne 1
 then AL:=[atk_leh(ALx(N,FN,Remove([1..#FN],i)),N) : i in [1..(#FN)-1]];
  rn:=[RootNumber(E,x[1]) : x in FN];
  if RootNumber(E) eq +1 then rn:=[-x : x in rn]; end if;
  if RootNumber(E) eq +1 then Append(~AL,atk_leh(N,N)); end if;
  s:=9+Max(0,-Ceiling(Log(10,RealPeriod(E))));
  s:=Max(s,9+Max(0,-Ceiling(Log(10,Imaginary(Periods(E)[2])))));
  t1:=[-e[4]/e[3]+ComplexField(s)!Sqrt(-e[4])/e[3] : e in AL];
  t2:=[(AL[i][1]*t1[i]+AL[i][2])/(AL[i][3]*t1[i]+AL[i][4]) : i in [1..#AL]];
  if #t1 ne 0 and #t2 ne 0 then mp:=ModularParametrization(E,t1 cat t2);
  else mp:=[]; end if;
  tors:=[mp[i]-rn[i]*mp[i+#AL] : i in [1..#AL]];
  if RootNumber(E) eq +1 then tors[#AL]:=mp[#AL]+mp[2*#AL]; end if;
  rp,ip:=Explode(Periods(E)); T:=[]; rp:=Real(rp);
  tors:=[x-ip*Round(Imaginary(x)/Imaginary(ip)) : x in tors];
  tors:=[x-rp*Round(Real(x)/rp) : x in tors];
  for t in tors do
   if Abs(Real(t)) lt rp/10 and Abs(Imaginary(t)) lt Abs(Imaginary(ip)/3)
    then T cat:=[E![0,1,0]];
   else u:=[Real(x) : x in EllipticExponential(E,t)];
    T cat:=[E![BestApproximation(u[1],10),BestApproximation(u[2],10)]];
    end if; end for;
  if RootNumber(E) eq -1 then T:=[-t : t in T];
  else t:=T[#T]; T:=[T[i]+T[#T]*rn[i] : i in [1..(#T)-1]]; T cat:=[t]; end if;
    /* sigh, this is a mess [to compute T for the largestprime]
      I compute that phi(tau)=ep*eq*phi(Wpq(tau))-ep*eq*Tq+Tp
      where Tp=-ep*phi(Wp(ioo)), and we know Tp for all other p and TN
      Thus I get that Tpq=Tp-ep*eq*Tq and iterate  (p,q can be composite) */
  if RootNumber(E) eq -1 then T cat:=[E![0,1,0]]; end if; t:=T[1];
   /* first compute t for N/biggestprime then get TP as TN-ep*T_{N/p} */
  if RootNumber(E) eq +1 then rn:=[-x : x in rn]; end if;
  for i in [2..(#FN)-1] do t:=t-T[i]*&*[rn[j] : j in [1..i]]; end for;
  T[#T]:=T[#T]-rn[#FN]*t; //was T[#T]:=T[#T]-RootNumber(E)*t; ??!
  if #T eq 1 and RootNumber(E) eq +1 then T[1]:=t; end if;
  if RootNumber(E) eq +1 then T:=[rn[i]*T[i] : i in [1..#FN]]; end if; //??!
  KT:=[]; Z:=Integers();
  for s in G do
   Q:=&*[Z | x[1]^x[2] : x in FN | s[3] mod x[1] eq 0];
   KT cat:=[zsum(E,[<rn[i],T[i]> : i in [1..#FN] | s[3] mod FN[i][1] eq 0])];
   end for;
 else KT:=[E!0 :  i in [1..#G]]; end if; //done with torsion
 return G[#G][1][1] div N,[Eltseq(t[1]) : t in G],[t[2] : t in G],KT;
 end function;

intrinsic HeegnerForms(E::CrvEll[FldRat],D::RngIntElt :
  UsePairing:=false,UseAtkinLehner:=true,Use_wQ:=true,IgnoreTorsion:=false)
 -> SeqEnum
{Return some Heegner Forms for a given elliptic curve and discriminant,
 and also multiplicities and torsion contributions}
 require IsDiscriminant(D): "D must be a discriminant";
 require D lt 0: "Discriminant is not negative";
 require check_manin(E) eq 1: "The X0-Manin constant is probably not 1. "
                            * "Use the strong Weil curve instead of E.";
 require IsSquare(Integers(4*Conductor(E))!D):
  "The discriminant D does not satisfy the Heegner hypothesis, " *
  "that D should be a square modulo 4*N(E)";
 M,m:=MinimalModel(E);
 _,b,c,d:=get_forms_ec(M,D,UsePairing,Use_wQ,UseAtkinLehner,IgnoreTorsion);
 Q:=QuadraticForms(D); b:=[Q!u : u in b]; i:=1;
 return [<b[i],c[i],Inverse(m)(d[i])> : i in [1..#b]]; end intrinsic;

intrinsic HeegnerForms(N::RngIntElt,D::RngIntElt : AtkinLehner:=[Integers()|])
 -> SeqEnum[QuadBinElt]
{Return Heegner Forms representatives for a given level and discriminant.
 The fixed square root is chosen to minimise the maximal leading coefficient.
 The AtkinLehner option allows multiple square roots to be used.}
 require IsDiscriminant(D): "D must be a discriminant";
 require D lt 0: "Discriminant is not negative";
 require N gt 0: "Level must be positive";
 require IsSquare(Integers(4*N)!D):
  "The discriminant D does not satisfy the Heegner hypothesis, " *
  "that D should be a square modulo 4*N";
 require &and[N mod x eq 0 and GCD(N div x,x) eq 1
	     and IsPrimePower(x) : x in AtkinLehner]:
  "AtkinLehner can only have prime powers that exactly divide N";
 require &and[Valuation(Gcd(D,N),w) le 1 where
	     _,w:=IsPrimePower(x) : x in AtkinLehner]:
  "AtkinLehner primes need to have valuation<=1 in gcd(D,N)";
 return get_forms(N,D,AtkinLehner); end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],f::QuadBinElt : Precision:=0,Traces:=[]) -> FldComElt
{}
 require Discriminant(f) lt 0: "Form must be positive definite";
 require Precision ge 0: "Precision must be nonnegative";
 if Precision eq 0 then C:=ComplexField();
 else C:=ComplexField(Precision); end if;
 a,b,c:=Explode(Eltseq(f)); tau:=(-b+Sqrt(C!(b^2-4*a*c)))/(2*a);
 return ModularParametrization(E,tau : Traces:=Traces); end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],f::QuadBinElt,B::RngIntElt : Precision:=0,Traces:=[])
 -> FldComElt
{Compute the modular parametrization of a point in the upper-half-plane
 associated to a positive definite binary quadratic form (using B terms)}
 require Discriminant(f) lt 0: "Form must be positive definite";
 require Precision ge 0: "Precision must be nonnegative";
 if Precision eq 0 then C:=ComplexField();
 else C:=ComplexField(Precision); end if;
 a,b,c:=Explode(Eltseq(f)); tau:=(-b+Sqrt(C!(b^2-4*a*c)))/(2*a);
 return ModularParametrization(E,tau,B : Traces:=Traces); end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],Z::[FldComElt] : Traces:=[]) -> SeqEnum
{}
 C<I>:=Universe(Z);
 B:=Max([Ceiling(-Precision(C)/Log(Abs(Exp(2*Pi(C)*I*z)))*Log(10)) : z in Z]);
 if B lt 1000 then B:=1000; end if; TR:=Traces;
 if #TR gt 10 then TRB:=NthPrime(#TR)+1; else TRB:=1; TR:=[]; end if;
 if B gt TRB then InternalFactorizationTableInit(Ceiling(B+1+2*Sqrt(B)));
  TR:=TR cat [FrobeniusTraceDirect(E,p) : p in PrimesInInterval(TRB+1,B)];
 end if;
 return [ModularParametrization(E,z : Traces:=TR) : z in Z]; end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],Z::[FldComElt],B::RngIntElt : Traces:=[]) -> SeqEnum
{Compute the modular parametrization map for an elliptic curve for a
 sequence of upper-half-plane points (using B terms)}
 if B lt 1000 then B:=1000; print "Using 1000 terms"; end if; TR:=Traces;
 if #TR gt 10 then TRB:=NthPrime(#TR)+1; else TRB:=1; TR:=[]; end if;
 if B gt TRB then InternalFactorizationTableInit(Ceiling(B+1+2*Sqrt(B)));
  TR:=TR cat [FrobeniusTraceDirect(E,p) : p in PrimesInInterval(TRB+1,B)];
 end if;
 return [ModularParametrization(E,z,B : Traces:=TR) : z in Z]; end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],F::[QuadBinElt],B::RngIntElt : Traces:=[], Precision:=0)
 -> SeqEnum
{}
 require Discriminant(F[1]) lt 0: "Form must be positive definite";
 require Precision ge 0: "Precision must be nonnegative";
 if Precision eq 0 then C:=ComplexField();
 else C:=ComplexField(Precision); end if;
 Z:=[(-b+Sqrt(C!(b^2-4*a*c)))/(2*a) where a,b,c:=Explode(Eltseq(f)) : f in F];
 return ModularParametrization(E,Z,B : Traces:=Traces); end intrinsic;

intrinsic ModularParametrization
(E::CrvEll[FldRat],F::[QuadBinElt] : Traces:=[], Precision:=0) -> SeqEnum
{Compute the modular parametrization map for an elliptic curve for a
 sequence of upper-half-plane points corresponding to the given binary
 quadratic forms (using B terms)}
 require Discriminant(F[1]) lt 0: "Form must be positive definite";
 require Precision ge 0: "Precision must be nonnegative";
 if Precision eq 0 then C:=ComplexField();
 else C:=ComplexField(Precision); end if;
 Z:=[(-b+Sqrt(C!(b^2-4*a*c)))/(2*a) where a,b,c:=Explode(Eltseq(f)) : f in F];
 return ModularParametrization(E,Z : Traces:=Traces); end intrinsic;

function heegner_discriminant(E,c: AVOID:={})
 F:=Factorisation(Conductor(E)); D:=[]; sct:=1;
 while (#D lt c and sct le 32) do
  for j in SC[sct] do d:=MakeD(-j);
   if (not (d in AVOID)) and (check_ec(d,F,E))
    then Append(~D, <d,sct>); if (#D eq c) then return D; end if; end if;
  end for; sct:=1+sct; end while; return D; end function;

function HDExtend(E,D,c) F:=Factorisation(Conductor(E)); i:=1;
 while (#D lt c and i le #NZ) do dt:=-NZ[i];
  if (check_ec(dt,F,E))
   then Append(~D,<dt,ClassNumber(dt)>);
   if (#D eq c) then return D; end if; end if; i:=i+1; end while;
 d:=-10001; while (#D lt c) do
  if IsSquarefree(d) or (d mod 4 eq 0 and IsSquarefree(d div 4)) then
   dt:=MakeD(d);
   if (check_ec(dt,F,E))
     then Append(~D,<dt,ClassNumber(dt)>);
     if (#D eq c) then return D; end if; end if; end if;
 d:=d-1; end while; return D; end function;

function ParameterGoodness(E,prec,B,nf,d) // work on this!!
 NT:=AnalyticRankNumberOfTerms(QuadraticTwist(E,d));
 return Max(B,NT)*nf; end function;

function HeegnerParameters(E,prec: chances:=40) F:=Log(10.0)/Pi(RealField());
 N:=Conductor(E); tries:=20; hd:=heegner_discriminant(E,chances);
 if #hd lt tries then hd:=HDExtend(E,hd,tries); end if;
 BEST:=SequenceToList([<10^20,[]> : I in [1..chances]]);
 wbf,wbfi:=Max([t[1] : t in BEST]); nbf:=0;
 for dd in hd do a,aL,aM:=get_forms_ec(E,dd[1],true,true,true,true);
  i:=1; while true do if i+1 gt #aM then break; end if;
   if aL[i] eq aL[i+1] then Remove(~aL,i+1); aM[i]+:=aM[i+1]; Remove(~aM,i+1);
   else i+:=1; end if; end while;
  for i in [1..#aM] do
   if aM[i] eq 0 then Remove(~aL,i); Remove(~aM,i); end if; end for;
  fom:=Max(10000,Ceiling(prec*a*N*F/Sqrt(-dd[1])));
  fom:=ParameterGoodness(E,prec,fom,#aM,dd[1]);
  if (fom le wbf) then nbf:=1+nbf;
   vprintf Heegner,2: "Discriminant %o has quality %o\n", dd, fom;
   eventual:=<dd[1],aL,aM>; BEST[wbfi]:=<fom,<dd[1],aL,aM>>;
   wbf,wbfi:=Max([t[1] : t in BEST]); end if; end for;
 BEST:=[BEST[i] : i in [1..Min(nbf,chances)]];
 Sort(~BEST,func<a,b|a[1]-b[1]>); return [t[2] : t in BEST]; end function;

function AppropriatePrecision(E,xht,COV)
 if Type(COV) eq CrvEll then d:=1; gb:=24.0;
 elif Type(COV) eq CrvHyp then d:=3; gb:=36.0;
 elif Type(COV) eq Crv then d:=12; gb:=48.0;
 else "Bad type of Cover it seems"; assert false; end if;
 nhb:=SiksekBound(E)+xht; return Ceiling((nhb/d+gb)/Log(10)); end function;

function DivT(E,pt,m)
 t,map:=TorsionSubgroup(E); g:=SetToSequence(map(Generators(t)));
 if IsEmpty(g) then return pt/m; end if;
 if #g eq 1 then for i in [0..(Order(g[1])-1)] do
  ok,d:=IsDivisibleBy(pt+i*g[1],m);
  if ok then return d; end if; end for; end if;
 if #g eq 2 then
  for i in [0..(Order(g[1])-1)] do for j in [0..(Order(g[2])-1)] do
   ok,d:=IsDivisibleBy(pt+i*g[1]+j*g[2],m); if ok then return d; end if;
   end for; end for; end if; return false; end function;

function HPInternal2(E,N,dd,aL,aM,L,xht,TR,twN,COV)
 om2:=Abs(Imaginary(Periods(E)[2]))*2*(Discriminant(E) lt 0 select 2 else 1);
 nonL:=Sqrt(Abs(dd))*(&*[TamagawaNumber(E,p) : p in BadPrimes(E)])/
	(om2*#TorsionSubgroup(E)^2)*2^#Factorization(Gcd(N,dd));
 if (dd eq -3) then nonL:=9*nonL; end if;
 if (dd eq -4) then nonL:=4*nonL; end if; //roots of unity
 if L ne 0 then ind2:=L*nonL;
  vprintf Heegner,1: "square of index is %o\n",ind2; idx:=Round(Sqrt(ind2));
  vprintf Heegner,1: "Quad field %o, With pairings, %o terms : a[] = %o\n",
		     dd,#aL,[f[1] div N : f in aL];
 vprintf Heegner,3: "Forms are %o\n", aL;
 vprintf Heegner,3: "Weights are %o\n", aM;
 midx:=Gcd(idx,Exponent(TorsionSubgroup(E))); idx:=idx*midx; end if;
 if L eq 0 then vprintf Heegner,1: "Will determine index internally...\n";
  midx:=Exponent(TorsionSubgroup(E)); idx:=0; end if; ok:=false;
 prec:=AppropriatePrecision(E,RealField()!xht,COV);
 if idx eq 0 then i8:=Ceiling(8*Sqrt(-dd)); else i8:=8*idx; end if;
 xvm:=AbsoluteValue
	(Real(EllipticExponential(E,ComplexField()!Periods(E)[1]/i8)[1]));
 prec+:=Ceiling(Log(1+RealField()!xvm)/Log(10)); prec:=Max(prec,9);
 while not ok do C<I>:=ComplexField(prec); nonL:=RealField(prec)!nonL;
  vprintf Heegner,1: "Using precision %o digits\n",prec;
  zlist:=[C!(Exp(Pi(C)*I*(n[2]+Sqrt(C!dd))/n[1])) : n in aL];
  if E cmpeq COV then LAM:=lambdas(E,prec) cat [nonL];
  else LAM:=[nonL]; end if; P:=Periods(E : Precision:=prec);
  prodcp:=&*[TamagawaNumber(E,p) : p in BadPrimes(E)]; T:=#TorsionSubgroup(E);
  ap:=RealField(prec)!Real(P[1])*(Discriminant(E) gt 0 select 2 else 1);
  htmult:=2*T^2/(prodcp*ap); Append(~LAM,htmult);
  worst_z:=Max([1/(1-Abs(z)) : z in zlist]);
  vprintf Heegner,2: "Worst Z <= 1 - 1/%o\n",Ceiling(worst_z);
  vprintf Heegner,3: "zlist is %o\n",zlist;
  B:=Ceiling(prec*Log(10.0)*worst_z); B:=Max(B,10000); EX:=[B,idx,midx,dd,twN];
  if #TR eq 0 then return B; end if; // JustParams
  vprintf Heegner,1: "Taking %o terms \n",B;
  ok,HP:=InternalHeegnerFunction(E,aM cat EX,zlist,TR,LAM,COV);
  if not ok then "Failed to find Heegner point on cover"; return false; end if;
  if Height(HP) eq 0 then "Got a torsion point --- problem with cover?";
   return false,_; end if;
  if not ok then print "Increasing Precision"; end if;
  prec:=Ceiling(prec*Sqrt(2)); end while;
 ht:=Height(HP); vprintf Heegner,1: "Found a point %o of height %o\n",HP,ht;
 m:=BestApproximation(Sqrt(xht/ht),100);
 if Type(m) eq FldRatElt then
  return true,DivT(E,Numerator(m)*HP,Denominator(m));
 else return true,m*HP; end if; end function;

function consider_cover(E,ht,desc_pos)
 if desc_pos eq false then return E; end if;
 return E; end function;

intrinsic HeegnerIndex(E::CrvEll[FldRat],D::RngIntElt) -> FldReElt
{Compute the Heegner index for a given discriminant}
 require check_ec(D,Factorization(Conductor(E)),E) :
  "Discriminant must satisfy the (strong) Heegner hypothesis";
 r,Lv:=AnalyticRank(E); require r eq 1: "Analytic rank must be 1";
 r,LD:=AnalyticRank(QuadraticTwist(E,D)); if r ne 0 then return 0.0; end if;
 rp,ip:=Explode(Periods(E)); vol:=rp*Imaginary(ip);
 cp:=&*[TamagawaNumber(E,p) : p in BadPrimes(E)]; N:=Conductor(E);
 if Discriminant(E) gt 0 then cp:=cp*2; end if; T:=#TorsionSubgroup(E);
 u:=2; if D eq -3 then u:=6; end if; if D eq -4 then u:=4; end if;
 return Sqrt(rp/4/vol*cp*Sqrt(-D)/T^2*LD*(u/2)^2*(2^#Factorization(Gcd(D,N))));
 end intrinsic;

function HPInternal
(E,NB,D,COV,desc_pos,TR : JustReturnHeegnerParameters:=false ) 
 N:=Conductor(E);
 if N ge 10^12 then print "Conductor is too large"; return false,_; end if;
 if (RootNumber(E) ne -1) then print "Curve must have odd functional equation";
  return false,_; end if;
 if #TR gt 10 then TRB:=NthPrime(#TR)+1; else TRB:=1; TR:=[]; end if;
 NT:=AnalyticRankNumberOfTerms(E);
 vprintf Heegner,2: "Computing L'(E,1) : Conductor is %o, Terms: %o\n",N,NT;
 if NT gt 2^30 then NT:=2^30; end if;
 if NT gt TRB then InternalFactorizationTableInit(Ceiling(NT+2*Sqrt(NT)));
  TR:=TR cat [FrobeniusTraceDirect(E,p) : p in PrimesInInterval(TRB+1,NT)];
  TRB:=NT; end if;
 rk,Ls1:=AnalyticRank(E : Traces:=TR);
 if (rk ne 1) then print "Curve must have analytic rank equal to 1";
  return false,_; end if;
 Ep:=Periods(E); TP:=&*[TamagawaNumber(E,p) : p in BadPrimes(E)];
 T:=#TorsionSubgroup(E); om:=Ep[1]*(Discriminant(E) gt 0 select 2 else 1);
 xht:=Real(Ls1*T^2/(TP*om));
 vprintf Heegner,1: "Heegner point height is %o\n",xht;
 if NB gt 0 then pts:=Points(E: Bound:=NB); ht:=10^100; ok:=false;
  for pt in pts do h:=Height(pt);
   if h ge 0.00001 and h le ht then PT:=pt; ht:=h; ok:=true; end if; end for;
  if ok then vprintf Heegner,1: "Found a point %o of height %o\n",PT,ht;
   m:=BestApproximation(Sqrt(xht/ht),100);
   if Type(m) eq FldRatElt then
    return true,DivT(E,Numerator(m)*PT,Denominator(m));
   else return true,m*PT; end if; end if; end if;
 if COV cmpeq 0 then COV:=consider_cover(E,xht,desc_pos); end if;
 prec:=AppropriatePrecision(E,RealField()!xht,COV); i8:=32; // 8*index?!
 xvm:=AbsoluteValue(Real(EllipticExponential(E,ComplexField()!Ep[1]/i8)[1]));
 prec+:=Ceiling(Log(1+RealField()!xvm)/Log(10));
 if JustReturnHeegnerParameters then
  return HeegnerParameters(E,prec),xht; end if;
 if D ne 0 then _,aL,aM:=get_forms_ec(E,D,true,true,true,true); i:=1;
  while true do if i+1 gt #aM then break; end if;
   if aL[i] eq aL[i+1] then Remove(~aL,i+1); aM[i]+:=aM[i+1]; Remove(~aM,i+1);
   else i+:=1; end if; end while;
  for i in [1..#aM] do if aM[i] eq 0 then Remove(~aL,i); Remove(~aM,i);
   end if; end for; HP:=[<D,aL,aM>];
 else vprint Heegner,1: "Picking quadratic field ..."; // Exclude rank 0 tw
  HP:=HeegnerParameters(E,prec); end if; ok:=false;
 for ee in HP do dd,aL,aM:=Explode(ee);
  vprintf Heegner,1: "Calculating L-function for quadratic twist by %o",dd;
  Qt:=QuadraticTwist(E,dd); twN:=Conductor(Qt);
  NT:=AnalyticRankNumberOfTerms(Qt); vprintf Heegner,1: " Terms: %o\n",NT;
  if NT gt 2^30 then NT:=2^30; end if;
  if NT gt TRB then InternalFactorizationTableInit(Ceiling(NT+2*Sqrt(NT)));
   TR:=TR cat [FrobeniusTraceDirect(E,p) : p in PrimesInInterval(TRB+1,NT)];
   TRB:=NT; end if;
  r,L:=AnalyticRankQuadraticTwist(E,dd : Traces:=TR);
  if (r ne 0) then
   vprintf Heegner,2: "Twist has analytic rank %o\n",r; continue; end if;
  b,pt:=HPInternal2(E,N,dd,aL,aM,L,xht,TR,twN,COV);
  if not b then vprintf Heegner,2: "Failure with %o\n",dd; end if;
  if b then return b,pt; end if; end for;
 "All twists had rank > 0 or failed!"; return false,_; end function;

intrinsic HeegnerPointNumberOfTerms(E::CrvEll[FldRat] 
        : NaiveSearch:=1000, Cover:=0, DescentPossible:=true, Traces:=[])
       -> RngIntElt, RngIntElt  
{The number of coefficients of the L-series of E that would need 
to be computed in HeegnerPoint(E) using the "best quality" discriminant
(which is also returned, followed by the smallest possible number of terms, 
and the corresponding discriminant).}
  HeegnerParams,xht:=HPInternal(E, NaiveSearch,0,Cover,DescentPossible,Traces 
                               : JustReturnHeegnerParameters);
  HP:=HeegnerParams; Discs:=[hp[1] : hp in HeegnerParams];
 if Cover cmpne 0 then
  if Type(Cover) eq CrvHyp then
   require Degree(Cover) eq 4 and IsIsomorphic(AssociatedEllipticCurve(Cover), E):
    "Hyperelliptic cover is not of genus 1 or does not cover E";
  elif Type(Cover) eq Crv and IsQuadricIntersection(Cover) then
   require IsIsomorphic(AssociatedEllipticCurve(Cover), E):
    "Quadric Intersection does not cover E";
  else require false: "Cover must be a 2-cover or a 4-cover"; end if; end if;
 if Cover cmpeq 0 then Cover:=E; end if;
 return HPInternal2(E,Conductor(E),HP[1][1],HP[1][2],HP[1][3],
		    0,xht,[],0,Cover),HP[1][1]; end intrinsic;

function has_2torsion_image(C) E,m:=AssociatedEllipticCurve(C);
 G,g:=TorsionSubgroup(E); S:=SylowSubgroup(G,2);
 I:=[&+[S| u : u in U] : U in Subsets(Set(Generators(S))) | #U ne 0];
 if Type(C) eq CrvHyp then T:=[TwoCoverPullback(C,g(i)) : i in I];
 else T:=[FourCoverPullback(C,g(i)) : i in I]; end if;
 J := &cat T; return not IsEmpty(J); end function;

intrinsic HeegnerPoint
(E::CrvEll[FldRat] : NaiveSearch:=1000, Discriminant:=0, Cover:=0,
 DescentPossible:=true, IsogenyPossible:=true, Traces:=[]) -> BoolElt,PtEll
{Compute a rational Heegner point on an elliptic curve of rank 1 over
 the rationals. Assumes the Manin constant is 1 (which is conjectured in
 this case) The point will be Sqrt(#Sha)*Generator in general.}
 M,_,mmap:=MinimalModel(E);
 if IsogenyPossible then C:=IsogenousCurves(M);
  _,a:=Min([ConjecturalRegulator(F,1.0) : F in C]);
  if ConjecturalRegulator(M,1.0) gt ConjecturalRegulator(C[a],1.0)*1.01 then
   vprintf Heegner: "Using isogenous curve %o\n",C[a];
   if Cover cmpne 0 then print "Ignoring given cover!"; Cover:=0; end if;
   I:=C[a]; _,imap:=IsIsogenous(I,M);
  else I:=M; _,imap:=IsIsomorphic(I,M); end if;
 else I:=M; _,imap:=IsIsomorphic(I,M); end if;
 if Discriminant ne 0 then D:=Discriminant;
  require D lt 0: "Discriminant is not negative";
  require IsFundamental(D): "Discriminant is not fundamental";
  require check_ec(D,Factorization(Conductor(I)),I):
    "Discriminant does not satisfy the (strong) Heegner hypothesis!"; end if;
 if Cover cmpne 0 then
  if Type(Cover) eq CrvHyp then
   require Degree(Cover) eq 4 and AssociatedEllipticCurve(Cover) eq I:
    "Hyperelliptic cover is not of genus 1 or does not cover E";
  elif Type(Cover) eq Crv and IsQuadricIntersection(Cover) then
   require AssociatedEllipticCurve(Cover) eq I:
    "Quadric Intersection does not cover E";
  else require false: "Cover must be a 2-cover or a 4-cover"; end if; end if;
 opr:=GetPrecision(RealField()); SetDefaultRealFieldPrecision(30);
 b,pt:=HPInternal(I,NaiveSearch,Discriminant,Cover,DescentPossible,Traces);
 SetDefaultRealFieldPrecision(opr); if b eq false then return false,_; end if;
 return true,mmap(imap(pt)); end intrinsic;

intrinsic HeegnerPoint
(H::CrvHyp[FldRat] : NaiveSearch:=10000, Discriminant:=0, Traces:=[])
 -> BoolElt,PtHyp
{Compute a rational Heegner Point on a 2-cover of rational rank 1 elliptic
 curve. Assumes the Manin constant is 1 (which is conjectured in this case)}
 f:=-Evaluate(DefiningPolynomial(H),[PolynomialRing(Rationals()).1,0,1]);
 return HeegnerPoint
 (f : NaiveSearch:=NaiveSearch, Discriminant:=Discriminant, Traces:=Traces);
 end intrinsic;

intrinsic HeegnerPoint
 (f::RngUPolElt[FldRat] : NaiveSearch:=10000, Discriminant:=0, Traces:=[])
 -> BoolElt,PtHyp
{Compute a rational Heegner Point on a 2-cover of rational rank 1 elliptic
 curve. Assumes the Manin constant is 1 (which is conjectured in this case)}
 require Degree(f) eq 4: "Polynomial must be of degree 4";
 require #Roots(f) eq 0: "Polynomial must have no rational roots";
 H:=HyperellipticCurve(f); E,m:=AssociatedEllipticCurve(H);
 if has_2torsion_image(H) then "Cover has a torsion image in E/2E";
  return false,_; end if;
 if Conductor(E) ge 10^12 then print "Conductor is too large";
  return false,_; end if;
 if NaiveSearch gt 0 then P:=SetToSequence(Points(H : Bound:=NaiveSearch));
  b,r:=IsSquare(LeadingCoefficient(f)); if b then P cat:=[H![1,r,0]]; end if;
  b,r:=IsSquare(Coefficient(f,0)); if b then P cat:=[H![0,r,1]]; end if;
 else P:=[]; end if; P:=[x : x in P | Height(m(x)) ne 0];
 if #P ne 0 then HP:=m(P[1]); xht,r:=ConjecturalRegulator(E : Precision:=5);
  if r ne 1 then print "Curve does not have rank 1"; return false,_; end if;
  ht:=Height(HP); vprintf Heegner,1: "Found a point %o of height %o\n",HP,ht;
  u:=BestApproximation(Sqrt(xht/ht),100);
  if Type(u) eq FldRatElt then pt:=DivT(E,Numerator(u)*HP,Denominator(u));
  else pt:=u*HP; end if; return true,TwoCoverPullback(H,pt)[1]; end if;
  b,pt:=HeegnerPoint
  (E : Cover:=H, Discriminant:=Discriminant,
   DescentPossible:=false, IsogenyPossible:=false, Traces:=Traces);
 if not b then return b,_; end if; return true,TwoCoverPullback(H,pt)[1];
 end intrinsic;

intrinsic HeegnerPoint
(C::Crv[FldRat] : NaiveSearch:=10000, Discriminant:=0, Traces:=[])
 -> BoolElt,Pt
{Compute a rational Heegner Point on a 2-cover of rational rank 1 elliptic
 curve. Assumes the Manin constant is 1 (which is conjectured in this case)}
 require IsQuadricIntersection(C): "Curve is not a quadric intersection";
 require IsSingular(C) eq false: "Quadric intersection is singular";
 if has_2torsion_image(C) then "4-cover has a torsion image in E/2E";
  return false,_; end if;
 if has_2torsion_image(AssociatedHyperellipticCurve(C)) then
  "2-cover has a torsion image in E/2E"; return false,_; end if;
 E,m:=AssociatedEllipticCurve(C);
 if Conductor(E) ge 10^12 then print "Conductor is too large";
  return false,_; end if;
 if NaiveSearch gt 0 then P:=Points(C : Bound:=NaiveSearch);
 else P:=[]; end if; P:=[x : x in P | Height(m(x)) ne 0];
 if #P ne 0 then HP:=m(P[1]); xht:=ConjecturalRegulator(E : Precision:=5);
  ht:=Height(HP); vprintf Heegner,1: "Found a point %o of height %o\n",HP,ht;
  u:=BestApproximation(Sqrt(xht/ht),100);
  if Type(u) eq FldRatElt then pt:=DivT(E,Numerator(u)*HP,Denominator(u));
  else pt:=u*HP; end if; return true,FourCoverPullback(C,pt)[1]; end if;
 b,pt:=HeegnerPoint
  (E : Cover:=C, Discriminant:=Discriminant,
   DescentPossible:=false, IsogenyPossible:=false, Traces:=Traces);
 if not b then return b,_; end if; return true,FourCoverPullback(C,pt)[1];
 end intrinsic;

function realroots(f) R:=Roots(f);
 if #R ne 0 then p:=Precision(R[1][1]); L:=1/10^(p/2);
  R:=[Real(r[1]) : r in R | Abs(Imaginary(r[1])) lt L*Abs(Real(r[1]))]; end if;
 return R; end function;

function EtoD(f,xv,yv) prec:=Precision(xv);
 U:=ComplexField(prec); P:=PolynomialRing(Rationals()); x:=P.1;
 E,m:=AssociatedEllipticCurve(f); DE:=DefiningEquations(m);
 t:=Evaluate(DE[1]/DE[3],3,1); LHS:=Numerator(t);
 L:=&+[Rationals()!Coefficient(Coefficient(LHS,1,i),2,0)*x^i : i in [0..4]]
     +Rationals()!Coefficient(LHS,2,2)*P!f;
 C:=PolynomialRing(U); R:=realroots(C!L-xv*C!f);
 q:=PolynomialRing(U,3)!DE[1]; ans:=[]; q2:=PolynomialRing(U,3)!DE[2];
 for x in R do y:=Sqrt(Evaluate(ChangeRing(f,U),x));
  if IsReal(y) then yp:=U!Evaluate(Evaluate(Evaluate(q2,1,x),2,y),3,1)/y^3;
   ym:=U!-Evaluate(Evaluate(Evaluate(q2,1,x),2,-y),3,1)/y^3;
   if Abs(yv-yp) gt Abs(yv-ym) then y:=-y; end if;
   ans:=ans cat [[x,y]]; end if; end for; return ans; end function;

function UN(f,i) F:=BaseRing(Parent(f)); x := PolynomialRing(F).1;
 return &+[F!Coefficient(f,i,d)*x^d : d in [0..Degree(f,i)]]; end function;

function DtoC_triv(f,xv,yv) e,d,c,b,a:=Explode(Coefficients(f));
 F<A,B,C,D>:=ProjectiveSpace(BaseRing(f),3); prec:=Precision(xv);
 f1:=D^2-(a*C^2+b*C*B+c*A*C+d*B*A+e*A^2); f2:=A*C-B^2; S:=Curve(F,[f1,f2]);
 return S,[[1,xv,xv^2,yv]]; end function;

function DtoC(QI,xv,yv) prec:=Precision(xv);
 _,M:=IsQuadricIntersection(QI); M1,M2:=Explode(M); U:=ComplexField(prec);
 A:=MatrixAlgebra(U,4); P4<a,b,c,d>:=PolynomialRing(U,4); v:=[a,b,c,d];
 M1:=A!M1; M2:=A!M2; M3:=M1*M2^(-1)*M1; M4:=M2*M1^(-1)*M2;
 q1:=Evaluate(QFFromMatrix(v,M1),1,1); q2:=Evaluate(QFFromMatrix(v,M2),1,1);
 q3:=QFFromMatrix(v,M3)*Determinant(M2)/Determinant(M1)+xv*QFFromMatrix(v,M4);
 q3:=Evaluate(q3,1,1); R1:=Resultant(q1,q2,2); R2:=Resultant(q1,q3,2);
 res:=Resultant(R1,R2,3); ans:=[];
 for r in realroots(UN(res,4)) do p3:=Evaluate(R2,4,r);
  for s in realroots(UN(p3,3)) do p2:=Evaluate(Evaluate(q1,4,r),3,s);
   for t in realroots(UN(p2,2)) do
    e1:=Abs(U!Evaluate(Evaluate(Evaluate(q1,4,r),3,s),2,t));
    e2:=Abs(U!Evaluate(Evaluate(Evaluate(q2,4,r),3,s),2,t));
    e3:=Abs(U!Evaluate(Evaluate(Evaluate(q3,4,r),3,s),2,t));
    if Max([e1,e2,e3]) lt 10^(-prec div 2) then ans cat:=[[1,t,s,r]]; end if;
    end for; end for; end for; return ans; end function;

function lift_pt(QI,x0,y0,z0)
 p:=Precision(x0); R:=ComplexField(3*p); x0:=R!x0; y0:=R!y0; z0:=R!z0;
 P<t,u>:=PolynomialRing(R,2); v:=Vector([1,x0,t,u]);
 M1,M2:=Explode(A) where _,A:=IsQuadricIntersection(QI);
 M1:=ChangeRing(M1,P); M2:=ChangeRing(M2,P);
 p1:=InnerProduct(v,v*M1); p2:=InnerProduct(v,v*M2);
 res:=UN(Resultant(p1,p2,t),2); Br:=10000; Bs:=10000; Z0:=z0; Y0:=y0;
 for r in realroots(res) do
  if Abs(r-Z0) lt Br then
   for s in realroots(UN(Evaluate(p1,u,r),1)) do
    if Abs(s-Y0) lt Bs then z0:=r; Br:=Abs(Z0-z0); y0:=s; Bs:=Abs(Y0-y0);
    end if; end for; end if; end for; return x0,y0,z0; end function;

function doit(QI,x0,y0,z0)
 R:=Parent(x0); F<a,b>:=PolynomialRing(R,2); G := PolynomialRing(F); t := G.1;
 m1,m2:=Explode(A) where _,A:=IsQuadricIntersection(QI);
 M1:=ChangeRing(m1,G); M2:=ChangeRing(m2,G); p:=Precision(x0);
 v:=Vector([1,x0+t,y0+a*t,z0+b*t]); c:=Coefficient;
 F1:=F!c(InnerProduct(v,v*M1),1); G1:=F!c(InnerProduct(v,v*M2),1);
 mat:=Matrix(2,2,[[R!c(c(F1,a,1),b,0),R!c(c(F1,b,1),a,0)],
		  [R!c(c(G1,a,1),b,0),R!c(c(G1,b,1),a,0)]]);
 mi:=-Transpose(mat^(-1));
 L:=Vector([R!c(c(F1,a,0),b,0),R!c(c(G1,a,0),b,0)])*mi;
 v:=Vector([1,x0+t,y0+L[1]*t+a*t^2,z0+L[2]*t+b*t^2]);
 F2:=F!c(InnerProduct(v,v*M1),2); G2:=F!c(InnerProduct(v,v*M2),2);
 L2:=Vector([R!c(c(F2,a,0),b,0),R!c(c(G2,a,0),b,0)])*mi; H:=10^(p div 3);
 while H gt 10 do
  M:=Matrix(4,4,
  [[1/H^3,-x0/H^2,((x0*L[1])-y0)/H,-L2[2]/L2[1]*((x0*L[1])-y0)+(x0*L[2])-z0],
   [0,1/H^2,-L[1]/H,L2[2]/L2[1]*L[1]-L[2]],[0,0,1/H,-L2[2]/L2[1]],[0,0,0,1]]);
  M:=M*H^3;
  M:=Matrix(4,4,[[Round(Real(x)) : x in Eltseq(M[1])],
		 [Round(Real(x)) : x in Eltseq(M[2])],
 	         [Round(Real(x)) : x in Eltseq(M[3])],
 		 [Round(Real(x)) : x in Eltseq(M[4])]]);
  a,b:=LLL(M : Delta:=0.999);
  for i in [1..4] do w:=ChangeRing(b[i],Rationals());
  if InnerProduct(w,w*m1) eq 0 and InnerProduct(w,w*m2) eq 0 then
  return true,w; end if; end for; H:=H div 10; end while; return false,_;
 end function;

function ihd2(X,z,idx) E,m:=AssociatedEllipticCurve(X); W:=Precision(z);
 vprintf Heegner,2: "Cover is %o\n",X;
 rp:=RealPeriod(E : Precision:=W); ip:=Periods(E : Precision:=W)[2];
 f:=HyperellipticPolynomials(X);
 for i in [1..idx] do u:=(z+i*rp)/idx;
  vprintf Heegner,2: "Doing coset %o\n",i;
  xv,yv:=Explode(EllipticExponential(E,ComplexField(W)!u)); Ds:=EtoD(f,xv,yv);
  for d in Ds do S,Cpts:=DtoC_triv(f,d[1],d[2]);
   for p in Cpts do
    x0,y0,z0:=lift_pt(S,p[2],p[3],p[4]); b,pt:=doit(S,x0,y0,z0);
    if b then pt:=Eltseq(pt); pt:=[pt[3],pt[2],pt[1],pt[4]];
     T,n:=QuadricIntersection(X); pt:=T!pt; // A and C are switched
     PT:=m(n(pt)); if Height(PT) ne 0.0 then return true,PT; end if;
     end if; end for; end for; end for;
 if Discriminant(E) lt 0 then return false,_; end if;
 for i in [1..idx] do u:=(z+i*rp)/idx+ip/2;
  vprintf Heegner,2: "On egg: doing coset %o\n",i;
  xv,yv:=Explode(EllipticExponential(E,ComplexField(W)!u)); Ds:=EtoD(f,xv,yv);
  for d in Ds do S,Cpts:=DtoC_triv(f,d[1],d[2]);
   for p in Cpts do
    x0,y0,z0:=lift_pt(S,p[2],p[3],p[4]); b,pt:=doit(S,x0,y0,z0);
    if b then pt:=Eltseq(pt); pt:=[pt[3],pt[2],pt[1],pt[4]];
     T,n:=QuadricIntersection(X); pt:=T!pt; // A and C are switched
     PT:=m(n(pt)); if Height(PT) ne 0.0 then return true,PT; end if;
     end if; end for; end for; end for;
 return false,_; end function;

function ihd4(X,z,idx) E,m:=AssociatedEllipticCurve(X); W:=Precision(z);
 rp:=RealPeriod(E : Precision:=W); ip:=Periods(E : Precision:=W)[2];
 f:=HyperellipticPolynomials(AssociatedHyperellipticCurve(X));
 for i in [1..idx] do u:=(z+i*rp)/idx;
  vprintf Heegner,2: "Doing coset %o\n",i;
  xv,yv:=Explode(EllipticExponential(E,ComplexField(W)!u)); Ds:=EtoD(f,xv,yv);
  for d in Ds do Cpts:=DtoC(X,d[1],d[2]);
   for p in Cpts do
    x0,y0,z0:=lift_pt(X,p[2],p[3],p[4]); b,pt:=doit(X,x0,y0,z0);
    if b then pt:=X!Eltseq(pt); PT:=m(pt);
     if Height(PT) ne 0.0 then return true,PT; end if; end if;
    end for; end for; end for;
 if Discriminant(E) lt 0 then return false,_; end if;
 for i in [1..idx] do u:=(z+i*rp)/idx+ip/2;
  vprintf Heegner,2: "On egg: doing coset %o\n",i;
  xv,yv:=Explode(EllipticExponential(E,ComplexField(W)!u)); Ds:=EtoD(f,xv,yv);
  for d in Ds do Cpts:=DtoC(X,d[1],d[2]);
   for p in Cpts do
    x0,y0,z0:=lift_pt(X,p[2],p[3],p[4]); b,pt:=doit(X,x0,y0,z0);
    if b then pt:=X!Eltseq(pt); PT:=m(pt);
     if Height(PT) ne 0.0 then return true,PT; end if; end if;
    end for; end for; end for; return false,_; end function;

function get_hyp_model(F,pt)
 _,a,b,c:=Explode(Reverse(Coefficients(F)));
 f:=Polynomial(Reverse([1,0,-2*b,-8*c,b^2-4*a*c]));
 g:=4*Polynomial(Reverse([1,a,b,c])); H:=f-pt[1]*g;
 q:=&*[h[1] : h in Factorization(H)]; assert Degree(q) eq 2;
 E:=EllipticCurve([0,a,0,b,c]); K<x,y>:=FunctionField(E);
 w:=y/(x-pt[1]); v:=Evaluate(q,x)/(x-pt[1]);
 v0:=v^2; C4:=Coefficient(Numerator(Coefficients(v0*(x-pt[1])^2)[1]),4);
 v1:=v^2-C4*w^4; C2:=Coefficient(Numerator(Coefficients(v1*(x-pt[1]))[1]),2);
 v2:=v^2-C4*w^4-C2*w^2;
 HC:=HyperellipticCurve(Polynomial([Rationals()!v2,0,C2,0,C4]));
 return ReducedModel(HC); end function;

function my_GOM(hc)
 return GenusOneModel(Reverse(Eltseq(HyperellipticPolynomials(hc))));
 end function;

intrinsic
InternalHeegnerDescent(X::Sch,z::FldReElt,i::RngIntElt) -> BoolElt,PtEll
{}
 vprintf Heegner,1: "Doing descent stage, index of %o\n",i;
 vprintf Heegner,2: "zvalue is %o\n",z;
 if Dimension(Ambient(X)) eq 3 then return ihd4(X,z,i);
 else
  E:=AssociatedEllipticCurve(X); P:=PolynomialRing(Rationals()); t:=P.1;
  C,m:=CubicModel(E); _,a2,_,a4,a6:=Explode(aInvariants(C));
  f:=Polynomial([a6,a4,a2,1]); K<s>:=quo<P|f>;
  DP:=[p : p in DivisionPoints(C!0,2) | p ne E!0];
  Y:=[my_GOM(X)+my_GOM(get_hyp_model(f,p)) : p in DP];
  b,P:=ihd2(X,z,i); if b then return b,P; end if;
  for y in Y do b,P:=ihd2(HyperellipticCurve(y),z,2*i); // kludge with 2*i ?!
   if b then return b,P; end if; end for;
 return false,_; end if; end intrinsic;
