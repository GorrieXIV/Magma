
freeze;

/* Symmetric powers of L-functions of elliptic curves, see Martin/Watkins */

function bad_type(E,p)
 if Valuation(Denominator(jInvariant(E)),p) ne 0 then
  if Valuation(cInvariants(E)[1],p) ne 0 then return -1; else return 1; end if;
  end if;
 v:=Valuation(Discriminant(E),p); if v eq 0 then return 0; end if;
 if p ge 5 then d:=12 div Gcd(12,v);
  if p mod d eq 1 then return d; else return -d; end if; end if;
 if p eq 3 then v3:=Valuation(Conductor(E),3);
  if IsOdd(v3) then return 12; end if; vd:=Valuation(Discriminant(E),3);
  if v3 eq 2 then if IsOdd(vd) then return -4; else return 2; end if; end if;
  assert v3 eq 4; if vd mod 4 eq 0 then r:=3; else r:=6; end if;
  c4,c6:=Explode(ChangeUniverse(cInvariants(MinimalTwist(E)),Integers()));
  if c4 mod 27 eq 9 then
   if c6 mod 243 eq 108 or c6 mod 243 eq 135 then return r;
   else return -r; end if;
  else if c4 mod 81 eq 27 then return r; else return -r; end if; end if;
 end if; assert p eq 2;
 M:=MinimalTwist(E); c4,c6:=Explode(ChangeUniverse(cInvariants(M),Integers()));
 w2:=Valuation(Conductor(M),2); v2:=Valuation(Conductor(E),2);
 if w2 eq 0 then return 2; end if;
 if w2 eq 2 then return v2 eq 2 select -3 else -6; end if;
 if w2 eq 3 or w2 eq 7 then return 24; end if;
 if w2 eq 5 then return 8; end if;
 if w2 eq 8 and Valuation(c6,2) ge 9 then return 8; end if;
 if c4 mod 128 eq 32 then return -4; else return 4; end if; end function;
// bad type is an integer, plus a sign telling if you get +/- in bad Euler

function tc(g,m)
 if g eq 3 then return m mod 2 eq 0
  select m-2*(m div 6) else m+1-2*((m+3) div 6); end if;
 if m mod 2 eq 1 then return m+1; end if;
 if g eq 2 then return 0; end if;
 if g eq 4 then return m-2*(m div 4); end if;
 if g eq 6 then return m-2*(m div 6); end if;
 if g eq 8 then
  return m mod 4 eq 0 select m-(m div 4) else m+1-(m div 4); end if;
 if g eq 12 then mr:=m mod 12;
  if mr eq 0 or mr eq 4 or mr eq 8 then return m-(m div 6); end if;
  if mr eq 2 or mr eq 6 or mr eq 10 then return m+1-(m div 6); end if; end if;
 if g eq 24 then mr:=m mod 12;
  if mr eq 0 or mr eq 6 or mr eq 8 then return m-(m div 12); end if;
  if mr eq 2 or mr eq 4 or mr eq 10 then return m+1-(m div 12); end if; end if;
 end function;

function get_cond(E,p,bt,m) if bt eq 0 then return 0; end if;
 if bt eq 1 then return m; end if; // mult
 if bt eq -1 then if p ne 2 then return m mod 2 eq 1 select m+1 else m; end if;
  v2:=Valuation(Conductor(E),2)-2;
  return m mod 2 eq 1 select (m+1)+(m+1)*(v2 div 2) else m; end if;
 if p ge 5 or Gcd(p,bt) eq 1 then return tc(Abs(bt),m); end if;
 bt:=Abs(bt);
 if p eq 3 then if bt eq 3 or bt eq 6 then return tc(bt,m)+tc(3,m); end if;
  v:=Valuation(Conductor(E),3)-2; return tc(12,m)+((v*tc(3,m)) div 2); end if;
 v2:=Valuation(Conductor(E),2)-2;
 if bt eq 2 or bt eq 6 then return tc(bt,m)+(v2 div 2)*tc(2,m); end if;
 if bt eq 4 then return tc(bt,m)+2*tc(4,m)+tc(2,m); end if;
 if bt eq 8 then
  if v2 eq 3 then return tc(bt,m)+tc(8,m)+(tc(2,m) div 2); end if;
  if v2 eq 4 then return tc(bt,m)+tc(8,m)+tc(2,m); end if;
  if v2 eq 6 then return tc(bt,m)+tc(8,m)+tc(4,m)+tc(2,m); end if; end if;
 if bt eq 24 then
  if v2 eq 1 then return tc(bt,m)+((2*tc(8,m)+tc(2,m)) div 6); end if;
  if v2 eq 2 then return tc(bt,m)+((2*tc(8,m)+4*tc(2,m)) div 6); end if;
  if v2 eq 4 then return tc(bt,m)+((2*tc(8,m)+10*tc(2,m)) div 6); end if;
  if v2 eq 5 then return tc(bt,m)+((10*tc(8,m)+5*tc(2,m)) div 6); end if;
 end if; end function;

R34p:=[+1,+1,-1,+1,+1,+1]; R34n:=[-1,-1,-1,-1,-1,+1];
R6p:=[+1,-1,-1,-1,+1,+1]; R6n:=[-1,+1,-1,+1,-1,+1];

function get_sign(E,p,m,bt) if m mod 2 eq 0 then return 1; end if;
 if bt eq 1 then return RootNumber(E,p)^m; end if;
 if bt eq -1 then return RootNumber(E,p)^((m+1) div 2); end if;
 if p ge 5 then return RootNumber(E,p)^(tc(Abs(bt),m) div 2); end if;
 if p eq 3 then
  if Abs(bt) eq 3 or Abs(bt) eq 4 then return +1; end if;
  if Abs(bt) eq 2 then return (-1)^((m+1) div 2); end if;
  if bt eq 12 then i:=((m+1) div 2) mod 6; if i eq 0 then i:=6; end if;
   return RootNumber(E,3) eq 1 select R34p[i] else R34n[i]; end if;
  i:=((m+1) div 2) mod 6; if i eq 0 then i:=6; end if;
  return RootNumber(E,3) eq 1 select R6p[i] else R6n[i]; end if;
 if p eq 2 then eta:=1;
  if m mod 8 eq 3 and IsOdd(Valuation(Conductor(E),2)) then eta:=-1; end if;
  return eta*RootNumber(E,2)^(tc(Abs(bt),m) div 2); end if; end function;

function TBIN(a,b) x:=Binomial(a-b+1,b)-Binomial(a-b-1,b-2);
                   if b mod 2 eq 1 then x:=-x; end if; return x; end function;

function prim_part(cm) if cm eq -27 or cm eq -12 then return 3; end if;
 if cm eq -8 or cm eq -4 or cm eq -16 then return 2; end if;
 if cm eq -28 then return 7; end if; return -cm; end function;

function cond_expo(cm) if cm eq -16 or cm eq -4 then return 2; end if;
 if cm eq -8 then return 3; end if; return 1; end function;

function NAME(m) S:="th"; m:=m mod 100;
 if m lt 20 and m gt 10 then return "th"; end if;
 if m mod 10 eq 1 then S:="st"; elif m mod 10 eq 2 then S:="nd";
 elif m mod 10 eq 3 then S:="rd"; else S:="th"; end if;
 return S; end function;

function bad_ef(E,p,m,bt) P:=PolynomialRing(Integers()); x:=P.1; pm:=p^m;
 if bt eq 1 then return (1-FrobeniusTraceDirect(E,p)^m*x); end if;
 if bt eq -1 then return m mod 2 eq 1 select P!1 else 1-x; end if;
 if bt eq -3 and m mod 2 eq 1 then
  return (1+p^m*x^2)^((m+1-tc(3,m)) div 2); end if;
 if bt lt 0 or bt ge 8 then if m mod 2 eq 1 then return P!1; end if;
  m2:=m div 2; beta:=m+1-tc(Abs(bt),m); am:=Ceiling(beta/2); bm:=beta-am;
  return (1-(-p)^m2*x)^am*(1+(-p)^m2*x)^bm; end if;
 if bt eq 2 then M:=MinimalTwist(E); ap:=FrobeniusTraceDirect(M,p);
 else if p eq 3 then ap:=3; end if; if p eq 2 then ap:=2; end if;
      if p ge 5 then W:=WeierstrassModel(E); a:=aInvariants(W);
       v4:=Valuation(a[4],p); v6:=Valuation(a[5],p);
       if 3*v4 gt 2*v6 then Ep:=EllipticCurve([0,a[5]/p^v6]); end if;
       if 3*v4 eq 2*v6 then Ep:=EllipticCurve([a[4]/p^v4,a[5]/p^v6]); end if;
       if 3*v4 lt 2*v6 then Ep:=EllipticCurve([a[4]/p^v4,0]); end if;
       ap:=FrobeniusTraceDirect(Ep,p); end if; end if; F:=P!1;
 for i in [0..(m-1) div 2] do
  if (2*i-m) mod bt ne 0 then continue; end if; s:=m-2*i; s2:=s div 2;
  ti:=&+[Integers()| TBIN(s,s2-k)*ap^(2*k)*p^(s2-k) : k in [0..s2]];
  if s mod 2 eq 1 then ti:=ti*ap; end if; F*:=(1-ti*p^i*x+pm*x^2); end for;
 if m mod 2 eq 0 then F*:=(1-p^(m div 2)*x); end if; return F; end function;

function sympow_ecq_cm(LE,m,prec,cm) x:=PolynomialRing(Integers()).1;
 function FUNC(p,ap,s) s2:=s div 2; pm:=p^m; i:=(m-s) div 2;
  if ap eq 0 and s mod 2 eq 0 then return 1-p^s*x^2; end if;
  t:=&+[Integers()| TBIN(s,s2-k)*ap^(2*k)*p^(s2-k) : k in [0..s2]];
  if s mod 2 eq 1 then t:=t*ap; end if; return (1-t*x+p^s*x^2); end function;
 E:=MinimalModel(LE`parent); A:=LSeries(1); BAD:=BadPrimes(E);
 for s in [m..1 by -2] do HS:=HodgeStructure([<s,0,2>,<0,s,2>]); N:=1;
  function cf(p,d)
   if not p in BAD then return FUNC(p,FrobeniusTraceDirect(E,p),s); end if;
   s2:=s div 2; bt:=bad_type(E,p); ef1:=bad_ef(E,p,s,bt);
   if s eq 1 then return EulerFactor(E,p); end if;
   if s gt 2 then ef2:=bad_ef(E,p,s-2,bt); else ef2:=1-x; end if;
   ef2:=Evaluate(ef2,p*x);
   if s mod 4 eq 0 then
    ef1:=ef1/(1-p^s2*x); ef2:=ef2/(1-KroneckerCharacter(cm)(p)*p^s2*x); end if;
   if s mod 4 eq 2 then
    ef2:=ef2/(1-p^s2*x); ef1:=ef1/(1-KroneckerCharacter(cm)(p)*p^s2*x); end if;
   return Parent(x)!(ef1/ef2); end function;
  for p in BAD do bt:=bad_type(E,p);
   f:=get_cond(E,p,bt,s); if s gt 2 then f:=f-get_cond(E,p,bt,s-2); end if;
   if s mod 4 eq 0 and p eq prim_part(cm) then f:=f+cond_expo(cm); end if;
   if s mod 4 eq 2 and p eq prim_part(cm) then f:=f-cond_expo(cm); end if;
   N:=N*p^f; end for;
  L:=LSeries(HS,Integers()!N,cf : Precision:=prec);
  L`name:=<s,NAME(s)*" Grossenchar power for ",E>;
  A:=A*Translate(L,(m-s) div 2); end for;
 if m mod 4 eq 0
  then A:=A*Translate(RiemannZeta(:Precision:=prec),m div 2); end if;
 if m mod 4 eq 2 then
  A:=A*Translate(LSeries(KroneckerCharacter(cm) : Precision:=prec),m div 2);
  end if;
 A`name:=<m,NAME(m)*" symmetric power (cm) of ",LE>; return A; end function;

function sympow_ecq(L,m,prec)
 wt:=m+1; E:=MinimalModel(L`parent); b,cm:=HasComplexMultiplication(E);
 if b then return sympow_ecq_cm(L,m,prec,cm); end if;
 g:=[1-i : i in [1..(wt div 2)]] cat [2-i : i in [1..(wt div 2)]];
 if wt mod 2 eq 1 then g cat:=[-2*(m div 4)]; end if;
 BAD:=BadPrimes(E); N:=1; e:=-KroneckerSymbol(-2,m);
 for p in BAD do bt:=bad_type(E,p); N*:=p^get_cond(E,p,bt,m);
  e*:=get_sign(E,p,m,bt); end for; if m mod 2 eq 0 then e:=+1; end if;
 P:=PolynomialRing(Integers()); x:=P.1;
 /************************/
 function f(p,d) pm:=p^m;
  if not p in BAD then ap:=FrobeniusTraceDirect(E,p); F:=P!1;
   for i in [0..(m-1) div 2] do s:=m-2*i; s2:=s div 2;
     ti:=&+[Integers()| TBIN(s,s2-k)*ap^(2*k)*p^(s2-k) : k in [0..s2]];
     if s mod 2 eq 1 then ti:=ti*ap; end if; F*:=(1-ti*p^i*x+pm*x^2); end for;
    if m mod 2 eq 0 then F*:=(1-p^(m div 2)*x); end if; return F; end if;
  bt:=bad_type(E,p); return bad_ef(E,p,m,bt); end function;
 /************************/
 if m mod 10 eq 1 then S:="st "; elif m mod 10 eq 2 then S:="nd ";
 elif m mod 10 eq 3 then S:="rd "; else S:="th "; end if;
 name:=<m,S*"symmetric power of ",L>;
 return LSeries(wt,g,N,f : Sign:=e,Name:=name, Precision:=prec); end function;

function sympow_ec(L,m,prec)
 if BaseField(L`name) eq Rationals() then return sympow_ecq(L,m,prec); end if;
 "Not yet done for EC over non-rational fields"; assert false; end function;

////////////////////////// TRY Sym^m E/K ///////////////////////
//                                                            //
////////////////////////////////////////////////////////////////

function bad_typeK(E,P) _,E:=LocalInformation(E,P); // local minimal model
 if Valuation(jInvariant(E),P) lt 0 then // (potentially) multiplicative
  if Valuation(cInvariants(E)[1],P) ne 0 then return -1; else return 1; end if;
  end if;
 v:=Valuation(Discriminant(E),P); if v eq 0 then return 0; end if;
 b,p,f:=IsPrimePower(Norm(P)); assert b;
 if p ge 5 then d:=12 div Gcd(12,v); if d eq 2 then return 2; end if;
  v4,v6:=Explode([Valuation(c,P) : c in cInvariants(E)]);
  if v4 ge 2 and v6 ge 3 then v4:=v4-2; v6:=v6-3; end if; // get minimal twist
  assert v4 ge 1 and v6 ge 1; C,m:=Completion(BaseRing(E),P);
  if v4 ge v6 then return IsSquare(m(-3)) select d else -d;
  else assert v4 eq 1; b,s:=IsSquare(m(3));
   if b then return IsSquare(-7+4*s) select d else -d; end if;
   return IsSquare(m(-3)) select d else -d; end if; end if;

// I don't think I really checked this at p=2,3 : taken from Kraus in part
// could use InertiaGroup in RngLocA? Probably difficult, plus need full Galois

 if p eq 2 then f:=DivisionPolynomial(E,3); C,m:=Completion(BaseRing(E),P);
  R:=Roots(f,C); if #R eq 4 then return 2; end if; r:=6;
  if #R eq 2 then ro:=Root(m(Discriminant(E)),3);
   return IsSquare(cInvariants(E)[1]-12*ro) select 2 else 4; end if;
  if #R eq 1 then F:=Factorization(f,C)[2][1]; l:=LocalInformation(E,P)[5];
   if l eq KodairaSymbol("IV") or l eq KodairaSymbol("IV*") then r:=3; end if;
   return IsSquare(Discriminant(F)) select r else -r; end if;
  F:=Factorization(f,C);
  if #F eq 2 then g:=F[1][1]; h:=F[2][1];
   if not IsSquare(Discriminant(g)*Discriminant(h)) then return -4; end if;
   r:=Root(m(Discriminant(E)),3);
   return IsSquare(cInvariants(E)[1]-12*r) select 2 else 4; end if;
  a,b,c,d,e:=Explode(Coefficients(f));
  g:=Polynomial([-c^2-d*(a^2-4*b),a*c-4*d,-b,1]); R:=Roots(g,C);
  if #R eq 0 then return 24; end if; if #R eq 3 then return -4; end if;
  F:=Factorization(g,C); D2:=ConstantCoefficient(F[1][1])^2-4*e;
  D1:=Discriminant(F[2][1]); return IsSquare(D1*D2) select 4 else 8; end if;

 if p eq 3 then C,m:=Completion(BaseRing(E),P); AB:=true; // NEED SIGN
  dp2:=DivisionPolynomial(E,2); R:=Roots(dp2,C);
  if #R eq 0 and not IsSquare(C!Discriminant(dp2)) then AB:=false; end if;
  if #R eq 3 then _,dp4:=DivisionPolynomial(E,4); FAC:=Factorization(dp4,C);
   SQ:=[Discriminant(f[1]) : f in FAC | Degree(f[1]) eq 2];
   if #SQ ne 0 then AB:=&and[IsSquare(sq/SQ[1]) : sq in SQ]; end if; end if;
  if #R eq 1 then _,dp4:=DivisionPolynomial(E,4); FAC:=Factorization(dp4,C);
   Q2:=[Discriminant(f[1]) : f in FAC | Degree(f[1]) eq 2];
   Q4:=[f : f in FAC | Degree(f[1]) eq 4];
   if #Q4 eq 0 then AB:=&and[IsSquare(sq/Q2[1]) : sq in Q2];
   else disc:=Discriminant(Q4[1]);
    if IsSquare(disc) then AB:=false; // C2 x C2
    else a,b,c,d,e:=Explode(Coefficients(Q4[1]));
         g:=Polynomial([-c^2-d*(a^2-4*b),a*c-4*d,-b,1]); R:=Roots(g);
         if #R eq 1 then F:=Factorization(g); // one root for resolvent
          D2:=ConstantCoefficient(F[1][1])^2-4*e; D1:=Discriminant(F[2][1]);
          if not IsSquare(D1*D2) then AB:=false; // dihedral, else C4 + Quad
          elif #Q2 eq 1 and not IsSquare(Q2[1]*D1) then AB:=false; end if;
         end if; end if; end if; end if;
  w:=AB select +1 else -1;
  vd:=Valuation(Discriminant(E),P); l:=LocalInformation(E,P)[5];
  if l eq KodairaSymbol("I0*") then assert vd eq 6; return 2; end if;
  if l eq KodairaSymbol("III") then assert vd eq 3; return 4*w; end if;
  if l eq KodairaSymbol("III*") then assert vd eq 9; return 4*w; end if;
  if vd mod 4 eq 0 then return 3*w; end if;
  if vd mod 4 eq 2 then return 6*w; end if;
  return 12; end if; end function;

function get_condK(E,P,bt,m) if bt eq 0 then return 0; end if;
 if bt eq 1 then return m; end if; _,p:=IsPrimePower(Norm(P));
 if bt eq -1 then if m mod 2 eq 0 then return m; end if;
  if p ne 2 then return m+1; end if; v2:=Valuation(Conductor(E),2);
  assert v2 mod 2 eq 0; return (m+1)*(v2 div 2); end if; // have to think
 if p ge 5 or Gcd(p,bt) eq 1 then return tc(Abs(bt),m); end if;
"Not done for wild types over K yet"; assert false;
// should be able to use RngLocA and repeated RamificationGroup
 bt:=Abs(bt);
 if p eq 3 then if bt eq 3 or bt eq 6 then return tc(bt,m)+tc(3,m); end if;
  v:=Valuation(Conductor(E),3)-2; return tc(12,m)+((v*tc(3,m)) div 2); end if;
 v2:=Valuation(Conductor(E),2)-2;
 if bt eq 2 or bt eq 6 then return tc(bt,m)+(v2 div 2)*tc(2,m); end if;
 if bt eq 4 then return tc(bt,m)+2*tc(4,m)+tc(2,m); end if;
 if bt eq 8 then
  if v2 eq 3 then return tc(bt,m)+tc(8,m)+(tc(2,m) div 2); end if;
  if v2 eq 4 then return tc(bt,m)+tc(8,m)+tc(2,m); end if;
  if v2 eq 6 then return tc(bt,m)+tc(8,m)+tc(4,m)+tc(2,m); end if; end if;
 if bt eq 24 then
  if v2 eq 1 then return tc(bt,m)+((2*tc(8,m)+tc(2,m)) div 6); end if;
  if v2 eq 2 then return tc(bt,m)+((2*tc(8,m)+4*tc(2,m)) div 6); end if;
  if v2 eq 4 then return tc(bt,m)+((2*tc(8,m)+10*tc(2,m)) div 6); end if;
  if v2 eq 5 then return tc(bt,m)+((10*tc(8,m)+5*tc(2,m)) div 6); end if;
 end if; end function;

function get_signK(E,P,m,bt) if m mod 2 eq 0 then return 1; end if;
 w:=RootNumber(E,P);
 if bt eq 1 then return w^m; end if;
 if bt eq -1 then return w^((m+1) div 2); end if;
 _,p,f:=IsPrimePower(Norm(P));
 if p ge 5 then return w^(tc(Abs(bt),m) div 2); end if;
 if p eq 3 then
  if bt in [2,3,-4,4,6] then return w^(tc(Abs(bt),m) div 2); end if;
  v3:=Valuation(Conductor(E),P);
  if bt in [-3,-6] then assert v3 mod 2 eq 0;
   a:=v3 div 2; b:=(bt eq -3) select 0 else 1;
   if m mod 12 in [1,9] then return w;
   elif m mod 12 in [3,7] then return (-1)^(a+b);
   elif m mod 12 eq 5 then return w*(-1)^(a+b); else return 1; end if; end if;
  assert bt eq 12;
  if IsOdd(f) then return m mod 6 in [1,3] select w else (-1)^(v3*(m+1) div 6);
  else if m mod 6 eq 1 then return w*(-1)^((m-1) div 6);
       elif m mod 6 eq 3 then return w*(-1)^((m+3) div 6);
       elif m mod 6 eq 5 then return (-1)^((m+5) div 6); end if; end if;
  end if; assert p eq 2;
 if bt in [2,3,-4,4,6,-6] then return w^(tc(Abs(bt),m) div 2); end if;
 v2:=Valuation(Conductor(E),P);
 if bt eq -3 then a:=v2 div 2; assert v2 mod 2 eq 0;
  if m mod 12 in [1,9] then return w;
  elif m mod 12 in [3,7] then return (-1)^a;
  elif m mod 12 eq 5 then return w*(-1)^a; else return 1; end if; end if;
 if bt eq 8 then wm:=w^((m+1) div 2);
  if IsEven(f) or m mod 8 ne 3 then return wm; end if;
  return wm*(-1)^v2; end if;
 if bt eq 24 then wm:=w^((m+1) div 2); if IsEven(f) then return wm; end if;
  w8:=wm; if m mod 8 eq 3 then w8:=w8*(-1)^v2; end if;
  // note that v2 and the conductor over a cubic extension have same parity
  v2m:=get_condK(E,P,bt,m); return w8*(-1)^v2m; end if; end function;

intrinsic SymmetricPowerK(L::LSer,m::RngIntElt) -> LSer
{ Given the L-series of an elliptic curve over K,
  return the L-series for the m-th symmetric power of it.}
 require Type(L`name) eq CrvEll: "Must be L-series of an elliptic curve";
 require ISA(Type(BaseField(L`name)),FldNum):
  "Elliptic curve must be defined over a number field";
 require m gt 0: "Given symmetric power must be positive";
 if m eq 1 then return L; end if;
 E:=L`name; K:=BaseField(E); C:=Conductor(E); O:=IntegerRing(K); wt:=m+1;
 g:=[1-i : i in [1..(wt div 2)]] cat [2-i : i in [1..(wt div 2)]];
 if wt mod 2 eq 1 then g cat:=[-2*(m div 4)]; end if;
 g:=&cat[g : i in [1..AbsoluteDegree(K)]];
 a1,a2,a3,a4,a6:=Explode(aInvariants(E));
 PR := PolynomialRing(Integers()); x := PR.1; OK:=IntegerRing(K);

 /********************************/
 function locPgen(P,p,d)
  locinf,EM:=LocalInformation(E,P);
  a1,a2,a3,a4,a6:=Explode(aInvariants(EM)); cond:=locinf[3];
  F,m:=ResidueClassField(P); q:=#F; if q gt p^d then return P!1; end if;
  _,p,f:=IsPrimePower(q);
  if cond gt 1 then return PR!1; end if;    // additive
  if cond eq 1 then                        // multiplicative
     return 1-((#Roots(PolynomialRing(F)![1,m(a1),m(-a2)]) ne 0)
	       select 1 else -1)*x^f; end if;
  ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
  return 1-ap*x^f+q*x^(2*f); // good reduction, original model was bad
  end function;
 /********************************/
 function locPgood(P,d)
  F,m:=ResidueClassField(P); q:=#F;  _,p,f:=IsPrimePower(q);
  if q gt p^d then return PR!1; end if;
  ap:=q+1-#EllipticCurve([F|m(a1),m(a2),m(a3),m(a4),m(a6)]);
  return [ap,q,f]; end function;
 /********************************/

function bad_eulerK(E,P,m,BT) return 0; end function;

 BAD:=[f[1] : f in Factorization(Conductor(E))]; N:=1;
 e:=-KroneckerSymbol(-2,m); // true in general over K ?
 BT:=[* <P,bad_typeK(E,P)> : P in BAD *];
 for B in BT do P,bt:=Explode(B); N*:=P^get_condK(E,P,bt,m);
  e*:=get_signK(E,P,m,bt); end for; if m mod 2 eq 0 then e:=+1; end if;

 /************************/
 function twotom(a,m) ap,q,f:=Explode(a); qm:=q^m; F:=P!1;
  for i in [0..(m-1) div 2] do s:=m-2*i; s2:=s div 2;
   ti:=&+[Integers()| TBIN(s,s2-k)*ap^(2*k)*q^(s2-k) : k in [0..s2]];
   if s mod 2 eq 1 then ti:=ti*ap; end if;
   F*:=(1-ti*q^i*x^f+qm*x^(2*f)); end for;
  if m mod 2 eq 0 then F*:=(1-q^(m div 2)*x^f); end if; return F; end function;

 function fK(P,d : Precision:=0)
  if P in BAD then return bad_eulerK(E,P,m,BT);
  else A:=locPgood(P,d); if A eq 1 then return 1; end if;
       return twotom(A,m); end if; end function;
// need to think about d-behaviour, in twotom

 function f(p,d : Precision:=0)
  return &*[fK(P[1],d) : P in Decomposition(OK,p)]; end function;

 /************************/
 e:=0; poles:=[]; name:=<m,"th symmetric power of ",L>;
 if m mod 4 eq 0 and HasComplexMultiplication(L`name) then
  poles:=[m/2+1]; end if; // multi-poles when CM field is in K ?!
 // no idea about Discriminant(OK) here
 L:=LSeries(wt,g,N*Discriminant(OK),f : Sign:=e,Poles:=poles,Name:=name);
 L`cffunck:=fK; L`degreeK:=<m+1,K>; L`condK:=N;
 L`hodgeK:=  // no idea about stuff here
   [* <[i,m-i,i ne m-i select 2 else (m div 2) mod 2],ip> :
      i in [0..m], ip in InfinitePlaces(K) *];
 end intrinsic;

