
freeze;

declare verbose HypGeomWild, 1;

import "identify_t1.m" : get_wild_t1,get_euler_t1;

Z:=Integers(); Q:=Rationals(); PSR:=PowerSeriesRing;
teich:=func<x|x*Exp(-Log(x^(p-1))/(p-1)) where p:=Prime(Parent(x))>;

function tame_euler(X,t,p,m,PREC) x:=PolynomialRing(Z).1; w:=Weight(X);
 if m eq 1 then res:=1-p^((1+w-Multiplicity(X`cycB cat X`cycA,1)) div 2)*x;
  return PREC lt Degree(X) select PSR(Q,PREC+1)!res else res; end if;
 f:=1; while p^f mod m ne 1 do f:=f+1; end while;
 if f gt PREC then return 1+O(PSR(Q,PREC+1).1^(PREC+1)); end if;
 if p^f gt 2^25 then error "p^f is too large"; end if; // practical limit
 if p^f gt 2^28 then error "p^f is too large"; end if; // limit on C code
 e:=EulerPhi(m); mx:=Max([Binomial(e,d)*p^(d*X`weight/2) : d in [0..e]]);
 pr:=Ceiling(Log(2*Floor(mx+1.01))/Log(p)); K:=pAdicField(p,pr);
 if p eq 2 then T:=1; else T:=teich(t*X`Mvalue*K.1); end if;
 KK:=pAdicQuotientRing(p,pr); T:=KK!T; q:=p^f; assert (q-1) mod m eq 0;
 Y:=(q-1) div m; E:=[Y*d : d in [1..m-1] | Gcd(d,m) eq 1] cat [pr]; // pr hack
 R:=HypgeomMotExtract(X`fps,X`Garray,(Z!T) mod (p^pr),p^f,X`dvalue,E);
 Sort(~R); R:=[K!R[f*(i-1)+1] : i in [1..#R div f]];
 x:=PolynomialRing(Universe(R)).1; ans:=&*[x^f-r : r in R];
 res:=Polynomial(Reverse(ChangeUniverse(Coefficients(ans),Z)));
 return PREC lt Degree(X) select PSR(Q,PREC+1)!res else res; end function;
// why are these over Q ??

function getf(p,m) if m eq 1 then return 1; end if;
 f:=1; while p^f mod m ne 1 do f:=f+1; end while; return f; end function;

function ef_tame(X,t,p,PREC) v,t0:=Valuation(t,p);
 if PREC eq 0 then PREC:=Degree(X); end if;
 AB:=Set([x : x in (v gt 0 select X`cycA else X`cycB) | v mod x eq 0]);
 if #AB eq 0 then return PolynomialRing(Z)!1; end if;
 o:=Max([getf(p,m) : m in AB]); if o le PREC then PREC:=10000; end if;
 res:=&*[tame_euler(X,t0,p,m,PREC) : m in AB]; return res; end function;

function tame_cond(X,t,p) v:=Valuation(t,p);
 AB:=Set([x : x in (v gt 0 select X`cycA else X`cycB) | v mod x eq 0]);
 return Degree(X)-&+[Z|EulerPhi(d) : d in AB]; end function;

function hgm_trace(X,q,t) b,p,f:=IsPrimePower(q);
 pr:=Ceiling(Log(2*Floor(Degree(X)*q^(X`weight/2)+1))/Log(p));
 K:=pAdicField(p,pr);
 if p eq 2 then T:=1; else T:=teich(t*X`Mvalue*K.1); end if;
 KK:=pAdicQuotientRing(p,pr); T:=KK!T;
 if q ne 2 then
  s:=HypgeomMotHelper(X`fps,X`Garray,(Z!T) mod (p^pr),p^f,pr,X`dvalue);
  else s:=0; end if; // sum is empty when q is 2;
 return Integers()!((q^X`dvalue+s)*KK!(1/(1-q))); end function;

////////////////////////////////////

// need to be fixed for A/B switch

function doit_odddeg(H) A:=H`cycA; B:=H`cycB; // Phi_2 in A, Phi_1 in B
 if 1 in A then T:=A; A:=B; B:=T; end if;
 X:=&*[Z|&*PrimeFactors(a) : a in A |
	Valuation(a,2) eq 0 and a ne 1 and IsPrimePower(a)];  // odd alpha
 X*:=&*[Z|2 : a in A | a ge 4 and IsPowerOf(a,2)];
 Y:=&*[Z|&*PrimeFactors(b div 2) : b in B |
	Valuation(b,2) eq 1 and b ne 2 and IsPrimePower(b div 2)]; // even beta
 Y*:=&*[Z|2 : b in B | b ge 4 and IsPowerOf(b,2)];
 return (-1)^((#H`alpha-1) div 2)*X*Y; end function;
/* this is \prod_v v^Gamma[v] with Gamma from (alpha,beta+1/2) */

function doit_evendeg_oddwt(X) A:=X`cycA; B:=X`cycB; // Phi_1 in B, even mult
 if 1 in A then T:=A; A:=B; B:=T; end if;
 X:=&*[Z|&*PrimeFactors(a) : a in A |
	Valuation(a,2) eq 0 and a ne 1 and IsPrimePower(a)];  // odd alpha
 X*:=&*[Z|2 : a in A | a ge 4 and IsPowerOf(a,2)]; 
 Y:=&*[Z|&*PrimeFactors(b) : b in B |
	Valuation(b,2) eq 0 and b ne 1 and IsPrimePower(b)];  // odd beta
 Y*:=&*[Z|2 : b in B | b ge 4 and IsPowerOf(b,2)]; 
 return (-1)^(Multiplicity(B,1) div 2)*X*Y; end function; 
/* FRV notes this is \prod_v v^Gamma[v] */

function doit_evendeg_evenwt(H) A:=H`cycA; B:=H`cycB; // Phi_1 in B, odd mult
 if 1 in A then T:=A; A:=B; B:=T; end if;
 X:=&*[Z|&*PrimeFactors(a div 2) : a in A |
	Valuation(a,2) eq 1 and a ne 2 and IsPrimePower(a div 2)]; // ev alpha
 X*:=&*[Z|2 : a in A | a ge 4 and IsPowerOf(a,2)]; 
 Y:=&*[Z|&*PrimeFactors(b) : b in B |
	Valuation(b,2) eq 0 and b ne 1 and IsPrimePower(b)]; // odd beta
 Y*:=&*[Z|2 : b in B | b ge 4 and IsPowerOf(b,2)]; 
 return -(-1)^(#H`alpha div 2)*(-1)^((Multiplicity(B,1)-1) div 2)*X*Y;
 end function;
/* this is 2*\prod_v v^Gamma[v] with Gamma from (alpha+1/2,beta) */

function doit_evendeg(X)
 return IsOdd(Weight(X))
  select doit_evendeg_oddwt(X) else doit_evendeg_evenwt(X); end function;

function doit_degree(X)
 return IsOdd(Degree(X)) select doit_odddeg(X) else doit_evendeg(X);
 end function;

function ef_mul(X,t,p,Precision,Check : t1:=false) deg:=Degree(X);
 if t1 then ef:=get_euler_t1(X,p);
  if not Type(ef) eq BoolElt then return PolynomialRing(Z)!ef; end if; end if;
 if IsOdd(deg) then // necessarily even weight
  if Precision eq 0 then prec:=deg div 2; else prec:=Precision; end if;
  eps:=KroneckerCharacter(doit_odddeg(X))(p);
  lim:=(deg div 2)-(eps eq -1 select 1 else 0);
  if not Check then PREC:=Min(prec,lim); else PREC:=prec; end if;
  P:=PowerSeriesRing(Rationals(),PREC+1); T:=P.1;
  f:=Exp(-&+[P|Integers()!hgm_trace(X,p^i,t)*T^i/i : i in [1..PREC]]);
  if PREC eq lim then g:=Polynomial(Coefficients(f));
   if (eps eq +1) then lim:=lim-1; end if;
   for d in [0..lim] do g:=g+eps*Parent(g).1^(deg-1-d)*Coefficient(g,d)
			        *p^((X`weight*(deg-1-2*d)) div 2); end for;
  else g:=f; end if;
 else // even degree, could be either weight
  if Check then
   if Precision eq 0 then PREC:=deg-1; else PREC:=Precision; end if;
   P:=PowerSeriesRing(Rationals(),PREC+1); T:=P.1; lim:=PREC+1;
   f:=Exp(-&+[P|Integers()!hgm_trace(X,p^i,t)*T^i/i : i in [1..PREC]]); g:=f;
  else // use functional equation // ok with t=1 ?
   if Precision eq 0 then prec:=(deg-2) div 2; else prec:=Precision; end if;
   lim:=(deg-2) div 2; PREC:=Min(prec,lim);
   P:=PowerSeriesRing(Rationals(),Max(2,PREC+1)); T:=P.1;
   eps:=KroneckerCharacter(doit_evendeg(X))(p);
   f1:=1-eps*T*p^(X`weight div 2);
   f:=Exp(-&+[P|Integers()!hgm_trace(X,p^i,t)*T^i/i : i in [1..PREC]]);
   if PREC eq lim then g:=Polynomial(Coefficients(f/f1+O(T^(PREC+1))));
    for d in [0..lim-1] do g:=g+1*Parent(g).1^(deg-2-d)*Coefficient(g,d)
   			         *p^(((X`weight)*(deg-2-2*d)) div 2); end for;
    g:=g*Polynomial(Coefficients(f1)); else g:=f; end if; end if; end if;
 if t1 then P:=Parent(g); // f1 not defined when Check is used!
  if IsOdd(Weight(X)) then g:=P!(g/P!Polynomial(Coefficients(f1))); end if;
  return Type(P) eq RngUPol select PolynomialRing(Z)!g else g; end if;
 v,t0:=Valuation(t-1,p); w:=Weight(X);
 if IsEven(Weight(X)) and IsEven(v) then m1:=Multiplicity(X`cycB,1);
  K:=(-1)^((m1-1) div 2)*2*&*[Abs(x) : x in GammaList(X)]; T:=Parent(g).1;
  g:=g*(1-KroneckerCharacter(K*t0)(p)*p^(w div 2)*T); end if;
 return Type(g) eq RngUPolElt select PolynomialRing(Z)!g else g; end function;

////////////////////////////////////

R:=PolynomialRing(Integers());

function ef_good(X,t,p,Precision,Check) deg:=Degree(X); // 2 is never good
 if Precision eq 0 then prec:=(deg+1) div 2; else prec:=Precision; end if;
 d:=Evaluate(X`char,t);
 if d eq 0 then eps:=0; else eps:=KroneckerCharacter(d)(p); end if;
 if deg mod 2 eq 1 then lim:=(deg-1) div 2;
 else lim:=deg div 2-(eps eq -1 select 1 else 0); end if;
 if not Check then PREC:=Min(prec,lim); else PREC:=prec; end if;
 P:=PowerSeriesRing(Rationals(),PREC+1); T:=P.1;
 PSRZ:=PowerSeriesRing(Integers(),PREC+1);
 f:=Exp(-&+[P|Integers()!hgm_trace(X,p^i,t)*T^i/i : i in [1..PREC]]);
 if PREC ne lim then return PSRZ!f; end if; g:=Polynomial(Coefficients(f));
 if deg mod 2 eq 0 and (eps eq +1) then lim:=lim-1; end if;
 for d in [0..lim] do g:=g+(-1)^deg*eps*Parent(g).1^(deg-d)*Coefficient(g,d)
			           *p^((X`weight*(deg-2*d)) div 2); end for;
 return PolynomialRing(Z)!g; end function;

function ef_fake(X,t,p,Precision) deg:=Degree(X); // utility, don't use func eq
 if Precision eq 0 then prec:=deg; else prec:=Precision; end if;
 PREC:=prec; P:=PowerSeriesRing(Rationals(),PREC+1); T:=P.1;
 f:=Exp(-&+[P|Integers()!hgm_trace(X,p^i,t)*T^i/i : i in [1..PREC]]);
 if PREC ne deg then return f; end if;
 return PolynomialRing(Z)!Polynomial(Coefficients(f)); end function;

forward wild_euler;
AbsPrec:=Precision;
intrinsic EulerFactor
(X::HypGeomData,t::RngQZElt,p::RngIntElt :
 Degree:=0,Precision:=0,Check:=false,Fake:=false) -> .
{The pth Euler factor of the hypergeometic motive specialised at t}
 require t ne 0: "t must not be 0";
 if Precision ne 0 then Degree:=Precision; end if; // hack, "Degree" is right
 require (#X`alpha-#X`beta) mod (p-1) eq 0: "p-1 must divide alpha/beta diff";
 require Type(Degree) eq RngIntElt and Degree ge 0: "Degree error";
 require IsPrime(p): "p must be a prime";
 if Fake then require Valuation(MValue(X)*t,p) eq 0: "v_p(Mt) must be 0";
  return ef_fake(X,t,p,Degree); end if;
 F:=function(u) if Type(u) eq RngUPolElt then return R!u; end if;
                if Type(u) eq RngIntElt and u eq 1 then return R!1; end if;
                return PSR(Integers(),AbsPrec(Parent(u)))!u; end function;
 if Valuation(X`bad,p) ne 0 then return F(wild_euler(X,t,p)); end if;
 require Valuation(X`bad,p) eq 0: "p cannot divide cyclotomic data";
 if Valuation(t,p) ne 0 then return F(ef_tame(X,t,p,Degree)); end if;
 if #X`alpha ne #X`beta then return F(ef_good(X,t,p,Degree,Check)); end if; //?
 if t eq 1 then return F(ef_mul(X,1,p,Degree,Check : t1:=true)); end if;
 if Valuation(Numerator(t-1),p) ne 0 then return F(ef_mul(X,t,p,Degree,Check));
 else return F(ef_good(X,t,p,Degree,Check)); end if; end intrinsic;

///////////////////////////////// WILD /////////////////////////////////

function new_wild_factor(H,t,p) vp:=Valuation(MValue(H),p);
 rA:=[x : x in H`cycA | x mod p ne 0]; rB:=[x : x in H`cycB | x mod p ne 0];
 pH:=HypergeometricData(rA,rB : SameSize:=false);
 if Valuation(t*p^vp-1,p) gt 0 then ef:=ef_mul(pH,t*p^vp,p,Degree(H),true);
 else ef:=EulerFactor(pH,t*p^vp,p : Check,Degree:=Degree(H)); end if;
 ef:=PolynomialRing(Rationals())!Polynomial(Coefficients(ef));
 lc:=LeadingCoefficient(ef);  if ef eq 1 then return 1; end if;
 if Abs(lc) ne p^Valuation(lc,p) then return 1; end if;
 s:=Floor(Min([Valuation(Coefficient(ef,i),p)/i : i in [1..Degree(ef)]]));
 ef:=Evaluate(ef,Parent(ef).1/p^s); lc:=LeadingCoefficient(ef); 
 vc:=Valuation(lc,p); df:=Degree(ef);
 if df eq 0 or (2*vc) mod df ne 0 then return ef; end if;
 if IsEven(Weight(H)) then if vc mod df ne 0 then return ef; end if;
  ef:=Evaluate(ef,Parent(ef).1/p^(vc div df));
  assert Abs(LeadingCoefficient(ef)) eq 1;
  return Evaluate(ef,Parent(ef).1*p^(Weight(H) div 2)); end if;
 ef:=Evaluate(ef,Parent(ef).1/p^(vc div df));
 return Evaluate(ef,Parent(ef).1*p^(Weight(H) div 2)); end function;

function is_pcongruent(X,Y,p) // vprintf HypGeomWild: "is_pcongruent %o\n",p;
 A1,B1:=CyclotomicData(X); A2,B2:=CyclotomicData(Y);
 A1:=&cat[[p^v : i in [1..EulerPhi(y)]] where v,y:=Valuation(x,p) : x in A1];
 A2:=&cat[[p^v : i in [1..EulerPhi(y)]] where v,y:=Valuation(x,p) : x in A2];
 B1:=&cat[[p^v : i in [1..EulerPhi(y)]] where v,y:=Valuation(x,p) : x in B1];
 B2:=&cat[[p^v : i in [1..EulerPhi(y)]] where v,y:=Valuation(x,p) : x in B2];
 Sort(~A1); Sort(~A2); Sort(~B1); Sort(~B2);
 if (A1 eq A2 and B1 eq B2) then return true,true; end if;
 if (A1 eq B2 and A2 eq B1) then return true,false; end if;
return false,_; end function;

function sibling_data(X,t,p) vprintf HypGeomWild: "sibling_data at %o\n",p;
 d:=Degree(X); HD:=PossibleHypergeometricData(d : Weight:=0);
 for h in HD do H:=HypergeometricData(h);
  if Weight(H) ge 1 then continue; end if;
  if Weight(H) eq 0 and #H`Glist ne 3 then continue; end if;
  b,s:=is_pcongruent(X,H,p);
  if b then if not s then t:=1/t; end if;
   a:=-H`Glist[1]; b:=-H`Glist[2]; e:=Gcd(a,b);
   M:=MValue(H); u:=1/M/t; y:=PolynomialRing(Rationals()).1;
   Ks:=[NumberField(f[1] : DoLinearExtension) :
        f in Factorization(y^a*(1-y)^b-u)];
   Ls:=[NumberField(f[1] : DoLinearExtension) : f in Factorization(y^e-u)];
   vn:=&+[Valuation(Discriminant(Integers(K)),p) : K in Ks];
   vd:=&+[Valuation(Discriminant(Integers(L)),p) : L in Ls];
   return vn-vd,R!1,[* Ks,Ls *]; end if; end for;
 return 0,R!1,_; end function;

function frv_guess(X,v,p) vprintf HypGeomWild: "Using frv_guess at %o\n",p;
 spin:=func<N|&*[d^(d*MoebiusMu(N div d)) : d in Divisors(N)]>;
 Mn:=&*[spin(x) : x in X`cycA]; Md:=&*[spin(y) : y in X`cycB];
 vn:=Valuation(Mn,p); vd:=Valuation(Md,p); m:=vn-vd;
 vprintf HypGeomWild: "FRV guess: v=%o vn=%o vd=%o m=%o p=%o\n",v,vn,vd,m,p;
 if v le 0 and v le m then return vn+Degree(X); end if;
 if v gt 0 and v le m then return vn+Degree(X)-v; end if;
 if v gt 0 and v gt m then return vd+Degree(X); end if;
 if v le 0 and v gt m then return vd+Degree(X)+v; end if;
 assert false; end function;

function try_onep(X,t,p) A,B:=CyclotomicData(X);
 vprintf HypGeomWild: "Using try_onep at %o\n",p;
 if &or[a mod (p^2) eq 0 : a in A cat B] then return false,_,_,_; end if;
 if not &or[a mod p eq 0 : a in A cat B] then return false,_,_,_; end if;
 sA:=[Valuation(a,p) : a in A]; sB:=[Valuation(b,p) : b in B];
 if Max(sA cat sB) ge 2 then return false,_,_,_; end if;
 if Multiplicity(sA,1) gt 1 then return false,_,_,_; end if;
 if Multiplicity(sB,1) gt 1 then return false,_,_,_; end if;
 sA:=Set(sA); sB:=Set(sB);
 if not 1 in sA join sB then return false,_,_,_; end if;
 if 1 in sA meet sB then return false,_,_,_; end if;
 if 1 in sA and 0 in sA then return false,_,_,_; end if;
 if 1 in sB and 0 in sB then return false,_,_,_; end if;
 if 1 in sB then t:=1/t; end if;
 k,u:=Valuation(t,p); l:=Valuation(u-1,p);
 vprintf HypGeomWild: "try_onep p:%o t:%o k:%o u:%o l:%o\n",p,t,k,u,l;
 if k lt 0 then if Valuation(k,p) eq 0 then return true,2*p-1,R!1,_; end if;
  if Integers(p^2)!(u^(p-1)-(p+1)) ne 0 then return true,p,R!1,_; end if;
  return false,_,_,_; end if;
 if k ge p+1 then return false,_,_,_; end if; // tame
 if k eq p then return false,_,_,_; end if; // good
 if k ge 1 and k le p-1 then return true,2*p-1-k,R!1,_; end if;
 if k eq 0 and l ge 1 then if IsOdd(l) then return true,p+1,R!1,_; end if;
  return false,_,_,_; end if;
 if k eq 0 and l eq 0 then
  if Integers(p^2)!(u^(p-1)+p*u^(p-2)-(p+1)) ne 0
   then return true,p,R!1,_; end if;
  return false,_,_,_; end if; end function;

function standard_euler(w,d,p) x:=PolynomialRing(Integers()).1;
 return 1-p^((w*d) div 2)*x^d; end function;

function wild_euler(X,t,p)
 if t eq 1 then ef:=get_euler_t1(X,p);
  if not Type(ef) eq BoolElt then return PolynomialRing(Z)!ef; end if; end if;
 f:=new_wild_factor(X,t,p); if f ne 1 then return PolynomialRing(Z)!f; end if;
 spin:=func<N|&*[d^(d*MoebiusMu(N div d)) : d in Divisors(N)]>;
 Mn:=&*[spin(x) : x in X`cycA]; Md:=&*[spin(y) : y in X`cycB];
 vn:=Valuation(Mn,p); vd:=Valuation(Md,p); vt:=Valuation(1/t,p);
 Sa,Sb:=CyclotomicData(X); vv:=vt-vn+vd; PR:=PolynomialRing(Integers());
 if vv le 0 then
  EF:=&*[PR | standard_euler(Weight(X)-Multiplicity(Sa,a)+1,EulerPhi(a),p) :
	a in Set(Sa) | vv mod a eq 0 and a mod p ne 0]; end if;
 if vv gt 0 then
  EF:=&*[PR | standard_euler(Weight(X)-Multiplicity(Sb,b)+1,EulerPhi(b),p) :
	b in Set(Sb) | vv mod b eq 0 and b mod p ne 0]; end if;
 return EF; end function;

function wild_cond(X,t,p)
 b,v,E,_:=try_onep(X,1/t,p); if b then return v,E,_; end if;
 f:=wild_euler(X,t,p); if Degree(f) eq Degree(X) then return 0,f,_; end if;
 spin:=func<N|&*[d^(d*MoebiusMu(N div d)) : d in Divisors(N)]>;
 Mn:=&*[spin(x) : x in X`cycA]; Md:=&*[spin(y) : y in X`cycB];
 vn:=Valuation(Mn,p); vd:=Valuation(Md,p); vt:=Valuation(1/t,p);
 Sa,Sb:=CyclotomicData(X); vv:=vt-vn+vd;
 if vv le 0 then
  ew:=&+[Z | EulerPhi(a) : a in Sa | vv mod p eq 0 and a mod p eq 0];
  e:=&+[Z | EulerPhi(a) : a in Set(Sa) | vv mod a eq 0 and a mod p ne 0];
  return frv_guess(X,vt,p)-e-ew; end if;
 if vv gt 0 then
  ew:=&+[Z | EulerPhi(b) : b in Sb | vv mod p eq 0 and b mod p eq 0];
  e:=&+[Z | EulerPhi(b) : b in Set(Sb) | vv mod b eq 0 and b mod p ne 0];
  return frv_guess(X,vt,p)-e-ew; end if;
 fp,E,_:=sibling_data(X,t,p);
 if fp eq 0 then vprintf HypGeomWild: "Still have no idea at %o\n",p; end if;
 return fp,E,_; end function;

////////////////////////////////////////////////////////////////////////

function hodge_struc_HGt1(X)
 w:=X`weight; f:=Numerator(X`hodge); d:=#X`alpha;
 if w eq 0 then HS:=HodgeStructure([]);
 else HS:=&+[(Z!Coefficient(f,i))*HodgeStructure([<i,w-i,0>,<w-i,i,0>]) :
 	     i in [0..(w-1) div 2]]; end if;
 if IsEven(w) then w2:=w div 2; c:=Z!Coefficient(f,w2);
  HS:=HS+(c div 2)*HodgeStructure([<w2,w2,0>,<w2,w2,1>]); // silly hack
  if IsOdd(c) then HS:=HS+HodgeStructure([<w2,w2,0>]); end if; end if;
 if IsOdd(w) then w2:=(w-1) div 2;
  HS:=HS-HodgeStructure([<w2,w2+1,2>,<w2+1,w2,2>]); end if;
 if IsEven(w) and IsEven(d) then
  HS:=HS-HodgeStructure([<w2,w2,0>,<w2,w2,1>]); // needs to be worked out
  HS:=HS+HodgeStructure([<w2,w2,doit_evendeg_evenwt(X) gt 0 xor d mod 4 eq 0
                                select 0 else 1>]); end if;
 if IsEven(w) and IsOdd(d) then
  m1:=Multiplicity(HS`A,<w2,w2,1>); m0:=Multiplicity(HS`A,<w2,w2,0>);
  HS:=HS-m1*HodgeStructure([<w2,w2,1>])-m0*HodgeStructure([<w2,w2,0>]);
  if m0 gt m1 then m0:=m0-1; else m1:=m1-1; end if;
  HS:=HS+m1*HodgeStructure([<w2,w2,1>])+m0*HodgeStructure([<w2,w2,0>]);
  end if; return HS; end function;

function hodge_struc_HG(X,t) if t eq 1 then return hodge_struc_HGt1(X); end if;
 GAMMA:=[]; f:=Numerator(X`hodge);
 for i in [0..(Degree(f)-1) div 2] do
  GAMMA cat:=[[0-i,1-i] : c in [1..Z!Coefficient(f,i)]]; end for;
 if IsEven(Degree(f)) then d:=Degree(f) div 2; c:=Z!Coefficient(f,d);
  if not 1 in X`cycB then t:=1/t; end if; // alpha/beta swapping
  if IsOdd(c) then // odd degree
   if t ge 0 and t le 1 then cp:=(c-1) div 2; cm:=(c+1) div 2;
   else cp:=(c+1) div 2; cm:=(c-1) div 2; end if; end if;
  if IsEven(c) then // even degree
   if t le 1 then cp:=c div 2; cm:=c div 2;
   else cp:=(c div 2)+1; cm:=(c div 2)-1; end if; end if;
  if IsOdd(X`dvalue+(X`weight div 2)) then zz:=cp; cp:=cm; cm:=zz; end if;
  GAMMA cat:=[[0-d : i in [1..cp]]];
  GAMMA cat:=[[1-d : i in [1..cm]]]; end if;
 return HodgeStructure(X`weight,&cat GAMMA); end function;

intrinsic HodgeStructure(H::HypGeomData,t::RngQZElt) -> HodgeStruc
{The Hodge structure of hypergeometric data at t}
 require #H`alpha eq #H`beta: "Hypergeometric data must be balanced";
 require t ne 0: "t cannot be 0"; return hodge_struc_HG(H,t); end intrinsic;

intrinsic HodgeStructure(H::HypGeomData) -> HodgeStruc
{The Hodge structure of odd weight hypergeometric data}
 require #H`alpha eq #H`beta: "Hypergeometric data must be balanced";
 require IsOdd(Weight(H)): "Weight must be odd, else specify t";
 return hodge_struc_HG(H,2); end intrinsic;

function lseries_t1(X,BAD,GAMMA,PR,ZETA,SE)
 BP,z:=get_wild_t1(X); if ZETA eq 0 then ZETA:=z; end if;
 for p in Keys(BP) do
  if IsDefined(BAD,p) and BP[p] ne BAD[p] then
   "WARNING: Ignoring BadPrime info at",p; end if; BAD[p]:=BP[p]; end for;
 cf:=function(p,d) if IsDefined(BAD,p) then return BAD[p][2]; end if;
                   if X`bad mod p eq 0 then return wild_euler(X,1,p); end if;
                   return ef_mul(X,1,p,d,false : t1:=true); end function;
 if #X`alpha eq 1 then return LSeries(1); end if;
 if #X`alpha eq 2 and Weight(X) eq 1 then return LSeries(1); end if;
 if #GAMMA ne 0 then HS:=HodgeStructure(X`weight,GAMMA);
 else HS:=hodge_struc_HGt1(X); end if;
 WILD_PRIMES:=Set(PrimeFactors(X`bad));
 K:=Keys(BAD); N:=&*[Integers() | p^BAD[p][1] : p in K];
 N*:=&*[Integers() | p^Degree(HS) : p in WILD_PRIMES | not p in K];
 S:=<"L-function for parameter t=1 of ",X>;
 L:=LSeries(HS,N,cf : Parent:=X,Name:=S,Precision:=PR);
 if ZETA ne 0 then T:=Translate(RiemannZeta(),(L`weight-1)/2);
  if Degree(L) eq ZETA then L:=LProduct([<T,ZETA>]);
  else L:=LProduct([<L/T^ZETA,1>,<T,ZETA>]); end if; end if;
 L`SAVE:=AssociativeArray();
 cf2:=function(p,d,L) /* How-to: beat Magma imported values vis-a-vis locals */
  if IsDefined(L`SAVE,p) and d le L`SAVE[p][1] then return L`SAVE[p][2];end if;
  f:=cf(p,d); if p le SE then L`SAVE[p]:=<Max(d,Degree(f)),f>; end if;
  return f; end function;
 cf3:=function(p,d) return cf2(p,d,L); end function;
 L`cffun:=cf3; return L; end function;

function unknown_lseries(X,t,BadPrimes,GAMMA,PR,ZETA,SE)
 BAD:=AssociativeArray();
 for DATA in BadPrimes do u:=DATA;
  if u[3] eq 1 then u:=<u[1],u[2],PolynomialRing(Integers())!1>; end if;
  BAD[u[1]]:=<u[2],u[3]>; end for;
 if t eq 1 then return lseries_t1(X,BAD,GAMMA,PR,ZETA,SE); end if;
 cf:=function(p,d) if IsDefined(BAD,p) then return BAD[p][2]; end if;
                   return EulerFactor(X,t,p : Precision:=d); end function;
 WILD_PRIMES:=Set(PrimeFactors(X`bad));
 Poo:={f[1] : f in Factorization(Denominator(t))} diff WILD_PRIMES;
 P0:={f[1] : f in Factorization(Numerator(t))} diff WILD_PRIMES;
 P1:={f[1] : f in Factorization(Numerator(t-1))} diff WILD_PRIMES;
 K:=Keys(BAD); N:=&*[Integers() | p^BAD[p][1] : p in K];
 N*:=&*[Integers() | p^wild_cond(X,t,p) : p in WILD_PRIMES | not p in K];
 N*:=&*[Integers() | p^tame_cond(X,t,p) : p in Poo | not p in K];
 N*:=&*[Integers() | p^tame_cond(X,t,p) : p in P0 | not p in K];
 M:=[Integers() | p : p in P1 | not p in K];
 if IsEven(Weight(X)) then M:=[p : p in M | IsOdd(Valuation(t-1,p))]; end if;
 if #M ne 0 then N*:=&*M; end if;
 if #GAMMA eq 0 then GAMMA:=hodge_struc_HG(X,t);
 else GAMMA:=HodgeStructure(X`weight,GAMMA); end if;
 S:=<"L-function for parameter ",t," of ",X>;
 L:=LSeries(GAMMA,N,cf : Parent:=X,Name:=S,Precision:=PR);
 if ZETA ne 0 then T:=Translate(RiemannZeta(),(L`weight-1)/2);
  if Degree(L) eq ZETA then L:=LProduct([<T,ZETA>]);
  else L:=LProduct([<L/T^ZETA,1>,<T,ZETA>]); end if; end if;
 L`SAVE:=AssociativeArray();
 cf2:=function(p,d,L) /* How-to: beat Magma imported values vis-a-vis locals */
  if IsDefined(L`SAVE,p) and d le L`SAVE[p][1] then return L`SAVE[p][2];end if;
  f:=cf(p,d); if p le SE then L`SAVE[p]:=<Max(d,Degree(f)),f>; end if;
  return f; end function;
 cf3:=function(p,d) return cf2(p,d,L); end function;
 L`cffun:=cf3; return L; end function;

function PrimeFactors(x)
 if Type(x) eq FldRatElt then return
  PrimeFactors(Numerator(x)) join PrimeFactors(Denominator(x)); end if;
 return {t[1] : t in Factorization(x)}; end function;

function perm_char(F) // permutation character of an algebra
 return &+[PermutationCharacter(NumberField(f[1])) : f in Factorization(F)];
 end function;

function lseries_common_part(C,t) x:=PolynomialRing(Rationals()).1;
 A:=[* &+[MoebiusMu(c div e)*perm_char(x^e-t) : e in Divisors(c)] : c in C *];
 if #A eq 0 then return LSeries(1); end if;
 return &*[LSeries(rep) : rep in A]; end function;

IDENTIFY:=Identify; PREC:=Precision;
function get_lseries0(X,t,BadPrimes,GAMMA,P,Identify,ZETA,SE)
 if #X`alpha eq 0 then return LSeries(1); end if;
 if Identify then
  if t eq 1 then A:=IDENTIFY(X,1); 
   if Type(A) ne BoolElt then return LSeries(A : Precision:=P); end if; end if;
  if X`weight eq 0 and t ne 1 then A:=ArtinRepresentation(X,t);
   if Type(A) ne BoolElt then return LSeries(A : Precision:=P); end if; end if;
  if #X`alpha eq 2 and X`weight eq 1 and t ne 1 then
   return LSeries(EllipticCurve(X,t) : Precision:=P); end if;
  if X`weight eq 1 and t ne 1 then T:=IDENTIFY(X,t);
   if Type(T) in {CrvHyp,CrvEll} then return LSeries(T : Precision:=P); end if;
   if Type(T) eq SeqEnum then return &*[LSeries(X : Precision:=P) : X in T];
    end if; end if; end if;
 KNOWN_BAD:=PrimeFactors(X`bad); GIVEN_BAD:={x[1] : x in BadPrimes};
 if not (KNOWN_BAD subset GIVEN_BAD) and (t ne 1 or Degree(X) gt 6) then
  "WARNING: Guessing wild prime information"; end if;
 return unknown_lseries(X,t,BadPrimes,GAMMA,P,ZETA,SE); end function;

function get_lseries(X,t,BadPrimes,GAMMA,P,Identify,ZETA,SE)
 L:=get_lseries0(X,t,BadPrimes,GAMMA,P,Identify,ZETA,SE);
 if not (&and[Valuation(Conductor(L),p[1]) eq p[2] : p in BadPrimes]
	 and &and [EulerFactor(L,p[1] : Integral) eq p[3] : p in BadPrimes])
  then "WARNING: Ignoring given BadPrimes"; end if; return L; end function;

function default_twist(X)
 function f(c) if c eq 1 then return 1; end if; b,p:=IsPrimePower(c);
  if not b then return 1; end if; if p eq 2 then return 2; end if;
  return p*(-1)^((p-1) div 2); end function;
 return &*[Z|f(c) : c in X`cycA cat X`cycB]; end function;

intrinsic LSeries (X::HypGeomData,t::RngQZElt :
		   BadPrimes:=[],GAMMA:=[],HodgeStructure:=false,
		   Identify:=true,Precision:=0,Weight01:=false,
		   SaveEuler:=false,
		   QuadraticTwist:=false,ZetaOrder:=0,PoleOrder:=0) ->LSer,LSer
{The L-series of a hypergeometric motive specialised at t}
 require t ne 0: "t must not be 0"; HS:=HodgeStructure; // t eq 1 separately?
 require #X`alpha eq #X`beta: "Number oF ALPHA and BETA must be equal";
 require Type(HS) in {HodgeStruc,BoolElt}: "Bad Hodge structure";
 require Type(HS) eq BoolElt or HS`w eq Weight(X): "Bad wt in Hodge Structure";
 require Type(Precision) eq RngIntElt and Precision ge 0:
 "Precision must be a nonnegative integer";
 if Precision eq 0 then Precision:=PREC(0.5); end if; P:=Precision;
 if Type(HS) eq HodgeStruc then GAMMA:=GammaFactors(HS`w,HS`A); end if;
 require #GAMMA eq 0 or (Type(GAMMA) eq SeqEnum and Universe(GAMMA) eq Z):
  "GAMMA not SeqEnum[Z]";
 require #GAMMA eq 0 or #GAMMA eq #X`alpha or t eq 1:
  "GAMMA not the right length";
 require &and[IsPrime(b[1]) : b in BadPrimes]: "Not a prime in BadPrimes";
 require &and[IsCoercible(Z,b[2]) : b in BadPrimes]: "BadPrime N not in Z?";
 require &and[b[2] ge 0 : b in BadPrimes]: "BadPrime conductors must be >= 0";
 require Type(PoleOrder) eq RngIntElt and PoleOrder ge 0: "PoleOrder invalid";
 require Type(ZetaOrder) eq RngIntElt and ZetaOrder ge 0: "ZetaOrder invalid";
 if SaveEuler cmpeq false then SaveEuler:=0; end if;
 if SaveEuler cmpeq true then SaveEuler:=10^10; end if; SE:=SaveEuler;
 require Type(SE) eq RngIntElt and SE ge 0: "SaveEuler must be in Z and >= 0";
 L:=get_lseries(X,t,BadPrimes,GAMMA,P,Identify,Max(PoleOrder,ZetaOrder),SE);
 if Weight01 cmpeq true then L:=Translate(L,-(MotivicWeight(L) div 2)); end if;
 if Type(Weight01) eq RngIntElt then
  require IsOdd(Weight01): "When integral, Weight01 must be odd";
  z:=Multiplicity(X`alpha cat X`beta,0);
  r:=Integers()!((-Weight01+MotivicWeight(L)-z)/2); L:=Translate(L,-r); end if;
 C:=lseries_common_part(X`common,t); chi:=KroneckerCharacter(1);
 if Type(QuadraticTwist) eq BoolElt and QuadraticTwist eq true then
  chi:=KroneckerCharacter(default_twist(X)); end if;
 if Type(QuadraticTwist) in {RngIntElt,FldRatElt} then
  require QuadraticTwist ne 0: "Cannot twist by 0";
  chi:=KroneckerCharacter(QuadraticTwist); end if;
 if Type(QuadraticTwist) eq GrpDrchElt then
  require Order(QuadraticTwist) le 2: "Must be a quadratic character";
  chi:=QuadraticTwist; end if;
 if Order(chi) ne 1 then L:=TensorProduct(L,LSeries(chi),BadPrimes); end if;
 return L,C; end intrinsic; // also twist C?

intrinsic Character(X::HypGeomData,t::RngQZElt) -> GrpDrchElt
{Given a hypergeometric motive and a rational parameter, return the
 associated Dirichlet character (over Q) in its local functional equation}
 require t ne 0: "t cannot be 0";
 if IsOdd(Weight(X)) then return KroneckerCharacter(1); end if;
 if t eq 1 then return KroneckerCharacter(doit_degree(X)); end if;
 e:=Evaluate(X`char,t); return KroneckerCharacter(e); end intrinsic;

////////////////////////////////////////////////////////////////////////

Z:=Integers();
function L1(B,q,r)
 return Multiplicity([FractionalPart(b+r/(q-1)) : b in B],0); end function;

function L0(A,B,p,f,r) q:=p^f;
 return f*(L1(B,q,0)-L1(A,q,0))/2
  +&+[FractionalPart(p^i*(a+r/(q-1))) : a in A,i in [0..f-1]]
  -&+[FractionalPart(p^i*(b+r/(q-1))) : b in B,i in [0..f-1]]; end function;

teich:=func<x|x*Exp(-Log(x^(p-1))/(p-1)) where p:=Prime(Parent(x))>;

function Cqr(A,B,d,p,f,r,t,Qp) q:=p^f;
 Av:=&*[Gamma(Qp!FractionalPart(p^i*(a+r/(q-1)))) : i in [0..f-1], a in A];
 Bv:=&*[Gamma(Qp!FractionalPart(p^i*(b+r/(q-1)))) : i in [0..f-1], b in B];
 l0:=Z!L0(A,B,p,f,r); l1:=Z!L1(B,p^f,r); return (Av/Bv)*(-1)^l0,l0-f*l1;
 end function;

function get_trace(A,B,d,p,f,t,Qp)
 q:=p^f; C0,v:=Cqr(A,B,d,p,f,0,t,Qp); u:=p^(f*d); T:=teich(t*Qp.1);
 for r in [1..q-2] do Cr,w:=Cqr(A,B,d,p,f,r,t,Qp);
  u:=u+T^r*(Cr/C0)*p^(d*f+w-v); end for; return u/(1-q); end function;

intrinsic HypergeometricTraceK
(A::SeqEnum[RngQZElt],B::SeqEnum[RngQZElt],t::RngQZElt,q::RngIntElt
 : Precision:=5) -> FldPadElt
{Given arrays of rationals for alphas and betas and a prime power q
 and a (rational) specialization t, return the HypergeometricTrace}
 require IsCoercible(Z,2*&+A): "ALPHA must have a half-integral sum";
 require IsCoercible(Z,2*&+B): "BETA must have a half-integral sum";
 require IsCoercible(Z,&+A+&+B+Multiplicity(A cat B,0)/2):
 "ALPHA and BETA yield non-integral terms";
 require Type(Precision) eq RngIntElt and Precision ge 1: "Bad precision";
 require q ge 2: "q must be at least 2"; b,p,f:=IsPrimePower(q);
 require b: "q must be a prime power"; Qp:=pAdicField(p,Precision);
 A:=Sort([FractionalPart(a) : a in A]); B:=Sort([FractionalPart(b) : b in B]);
 s:=0; T:=FunctionField(Rationals()).1; F:=Parent(t)!0;
 S:=[<x,0> : x in A] cat [<1-x,1> : x in B]; Sort(~S);
 for i in [1..2*#A] do
  if S[i][2] eq 0 then F:=F+T^s; s:=s+1; else s:=s-1; end if; end for;
 d:=Degree(Denominator(F)); return get_trace(A,B,d,p,f,t,Qp); end intrinsic;
