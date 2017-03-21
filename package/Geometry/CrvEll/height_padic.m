freeze;

declare verbose pAdicHeight,2;

import "../CrvHyp/kedlaya.m" : FrobeniusMatrixEll;

intrinsic EisensteinTwo
(E::CrvEll[FldRat],p::RngIntElt : Precision:=0) -> FldPadElt
{ Compute the p-adic E2 function of an elliptic curve over Q.
  Requires p to be good, ordinary, and > 4. The default precision is 20.}
 require IsPrime(p) : "p must be prime";
 require p ge 5: "p must be at least 5";
 require not p in BadPrimes(E): "p cannot be a bad prime";
 require #ChangeRing(E,GF(p)) ne p+1: "p cannot be supersingular";
 OP:=Precision; if OP eq 0 then OP:=20; end if;
 require Type(OP) eq RngIntElt and OP ge 1:
  "Precision must be a positive integer";
 F:=FrobeniusMatrixEll(E,p,OP)^OP; return -12*F[1][2]/F[2][2]; end intrinsic;

////////////////////////////////////////////////////////////////////////

function funcW(E,prec,R) // pAdicRing isfaster than pAdicField here
 a1,a2,a3,a4,a6:=Explode([R!x : x in aInvariants(E)]);
 _<t>:=PowerSeriesRing(R,prec); // Laurent to get the Precision type right
 w:=t^3+a1*t^4+(a1^2+a2)*t^5+(a1^3+2*a1*a2+a3)*t^6+O(t^7); PREC:=[prec];
 while PREC[1] ge 8 do PREC:=[(PREC[1]+1) div 2] cat PREC; end while;
 PREC:=Reverse(PREC);
 while #PREC ne 0 do wp:=PREC[#PREC]; Prune(~PREC);
  w:=ChangePrecision(w,wp); w2:=w^2;
  w:=w-(-t^3+(1-a1*t-a2*t^2)*w-(a3+a4*t+a6*w)*w2)/
       (1-a1*t-a2*t^2-(a3+a4*t)*(2*w)-3*a6*w2); end while;
 return w; end function;

function fint(F)
 c,e:=Coefficients(F); FF:=FieldOfFractions(Parent(c[1])); c:=[FF!x : x in c];
 for i in [1..#c] do
  if e+i eq 0 then c[i]:=0; else c[i]/:=(e+i); end if; end for;
 return (Parent(F)!c)*(Parent(F).1)^(1+e); end function;

function fint2(F,p,r) c,e:=Coefficients(F); s:=p^r;
 return (Parent(F)![c[i]*(s/(e+i)) : i in [1..#c]])*Parent(F).1^(e+1);
 end function;

function brent(C,n) // old function
 R<t>:=PowerSeriesRing(Universe(C),n); F:=R!1+O(t); f:=R!C; w:=1;
 while w le n do w+:=w;
  F:=ChangePrecision(F,Min(w,n)); G:=fint(Derivative(F)/F-f);
 F:=F*(1-G); end while; return F; end function;

function brent(C,n) // can rings be used here, with the fint? not really faster
 PAR:=Parent(C[1]); p:=Prime(PAR); r:=Ilog(p,n+1);
 U:=pAdicRing(p,Precision(PAR)+r); C:=ChangeUniverse(C,U);
 R<t>:=PowerSeriesRing(U,n); F:=R!1+O(t); f:=R!C; w:=1; s:=p^r; PREC:=[n];
 while PREC[1] gt 1 do PREC:=[(PREC[1]+1) div 2] cat PREC; end while;
 PREC:=Reverse(PREC);
 while #PREC ne 0 do wp:=PREC[#PREC]; Prune(~PREC);
  F:=ChangePrecision(F,wp); G:=fint2(R!(Derivative(F)/F)-f,p,r); F:=F*(s-G);
  F:=R![U!((Integers()!c) div s) : c in Coefficients(F)]; end while;
 return F; end function;

function sigma(E,E2,p,N)
 assert N ge 4; assert p ge 5; assert IsPrime(p); u:=Cputime();
 K:=pAdicRing(p,N-3); A:=aInvariants(E); // need p-adic fields for fint
 assert &and[Valuation(a,p) ge 0 : a in A];
 a1,a2,a3,a4,a6:=Explode([K!x : x in A]);
 T:=Cputime(); w:=funcW(E,N+4,K);
 vprintf pAdicHeight: "Wfunc: %os\n",Cputime(T);
 T:=Cputime();
 t:=Parent(w).1; y:=-1/w; x:=-t*y;
 s:=Derivative(x)/(2*y+a1*x+a3); c:=(a1^2+4*a2-K!Integers()!E2)/12;
 h:=-1/t-s*(a1/2+fint((x+c)*s));
 C:=[pAdicRing(p,N-2)!Rationals()!Coefficient(h,i) : i in [0..N-1]];
 C[1]:=pAdicRing(p,N-2)!(aInvariants(E)[1]/2);
 T:=Cputime(); theta:=brent(C,N-1);
 vprintf pAdicHeight: "Brent: %os\n",Cputime(T);
 C:=[pAdicField(p,N-1)!Rationals()!Coefficient(theta,i) : i in [0..N-2]];
 C:=[ChangePrecision(C[i],Max(N-i-Valuation(C[i]),1)) : i in [1..#C]];
 Z<t>:=PowerSeriesRing(pAdicField(p,N-1),N);
 vprintf pAdicHeight: "Sigma function Total: %os\n",Cputime(u);
 return t*(Z!C); end function;

function modLmult_new(E,a,b,d,m,L)
 if m eq 1 then return a,b,d; end if; ZL:=Integers(L);
 a1,a2,a3,a4,a6:=Explode([ZL!x : x in aInvariants(E)]);
 a1*:=d; a2*:=d^2; a3*:=d^3; a4*:=d^4; a6*:=d^6; T:=2*b+a1*a+a3; 
 b2:=a1^2+4*a2; b4:=a1*a3+2*a4; b6:=a3^2+4*a6;
 b8:=a1^2*a6+4*a2*a6-a1*a3*a4+a2*a3^2-a4^2;
 B4:=6*a^2+b2*a+b4; B6:=4*a^3+b2*a^2+2*b4*a+b6;
 B8:=3*a^4+b2*a^3+3*b4*a^2+3*b6*a+b8;

 M:=m; TAR:=[]; while M ge 8 do TAR cat:=[M]; M:=M div 2; end while;
 G:=[ZL!1,-1,B8,B6^2-B4*B8] cat [0 : i in [5..9]]; H:=[ZL!0 : i in [1..9]];
 G[5]:=B6^2*G[4]*G[2]^3-G[1]*G[3]^3; G[6]:=G[3]*(G[1]*G[4]^2-G[5]*G[2]^2);
 G[7]:=G[5]*G[3]^3-B6^2*G[2]*G[4]^3; G[8]:=G[4]*(G[2]*G[5]^2-G[6]*G[3]^2);
 G[9]:=B6^2*G[6]*G[4]^3-G[3]*G[5]^3;

 if m ge 4 then u:=M;
  if u eq 4 then H[1]:=0; for i in [1..8] do H[i+1]:=G[i]; end for; end if;
  if u eq 5 then for i in [1..9] do H[i]:=G[i]; end for; end if;
  if u eq 6 then for i in [1..8] do H[i]:=G[i+1]; end for;
   H[9]:=G[5]*(G[3]*G[6]^2-G[7]*G[4]^2); end if;
  if u eq 7 then for i in [1..7] do H[i]:=G[i+2]; end for;
   H[8]:=G[5]*(G[3]*G[6]^2-G[7]*G[4]^2); H[9]:=G[7]*G[5]^3-B6^2*G[4]*G[6]^3;
   end if;
  G:=H;
  while #TAR ne 0 do u:=TAR[#TAR];
   if u mod 4 eq 0 then
    for i in [1..5] do H[2*i-1]:=G[2+i]*(G[i]*G[3+i]^2-G[4+i]*G[1+i]^2);
     end for;
    H[2]:=B6^2*G[5]*G[3]^3-G[2]*G[4]^3; H[4]:=G[6]*G[4]^3-B6^2*G[3]*G[5]^3;
    H[6]:=B6^2*G[7]*G[5]^3-G[4]*G[6]^3; H[8]:=G[8]*G[6]^3-B6^2*G[5]*G[7]^3;
   end if;
   if u mod 4 eq 2 then
    for i in [1..5] do H[2*i-1]:=G[2+i]*(G[i]*G[3+i]^2-G[4+i]*G[1+i]^2);
     end for;
    H[2]:=G[5]*G[3]^3-B6^2*G[2]*G[4]^3; H[4]:=B6^2*G[6]*G[4]^3-G[3]*G[5]^3;
    H[6]:=G[7]*G[5]^3-B6^2*G[4]*G[6]^3; H[8]:=B6^2*G[8]*G[6]^3-G[5]*G[7]^3;
   end if;
   if u mod 4 eq 1 then
    for i in [1..4] do H[2*i]:=G[3+i]*(G[1+i]*G[4+i]^2-G[5+i]*G[2+i]^2);
     end for;
    H[1]:=B6^2*G[5]*G[3]^3-G[2]*G[4]^3; H[3]:=G[6]*G[4]^3-B6^2*G[3]*G[5]^3;
    H[5]:=B6^2*G[7]*G[5]^3-G[4]*G[6]^3; H[7]:=G[8]*G[6]^3-B6^2*G[5]*G[7]^3;
    H[9]:=B6^2*G[9]*G[7]^3-G[6]*G[8]^3; end if;
   if u mod 4 eq 3 then
    for i in [1..4] do H[2*i]:=G[3+i]*(G[1+i]*G[4+i]^2-G[5+i]*G[2+i]^2);
     end for;
    H[1]:=G[5]*G[3]^3-B6^2*G[2]*G[4]^3; H[3]:=B6^2*G[6]*G[4]^3-G[3]*G[5]^3;
    H[5]:=G[7]*G[5]^3-B6^2*G[4]*G[6]^3; H[7]:=B6^2*G[8]*G[6]^3-G[5]*G[7]^3;
    H[9]:=G[9]*G[7]^3-B6^2*G[6]*G[8]^3; end if;
   Prune(~TAR); G:=H; end while; for i in [1..5] do H[i]:=G[i+2]; end for;
  else "really small case ",m;
   G:=[0] cat G; for i in [1..5] do H[i]:=G[m-2+i]; end for; end if;

 psim:=H[3]; psimp1:=H[4]; psimm1:=H[2];
 if m mod 2 eq 0 then psim*:=T; else psimp1*:=T; psimm1*:=T; end if;
 theta:=a*psim^2-psimp1*psimm1;
 omega2:=psim*(a1*theta+a3*psim^2); omega1:=H[1]*H[4]^2-H[5]*H[2]^2;
 if m mod 2 eq 1 then omega1*:=T; end if; omega:=-(omega1+omega2)/2;
 return theta,omega,psim*d; end function;

intrinsic pAdicHeight
(P::PtEll[FldRat],p::RngIntElt : Precision:=0, E2:=0) -> FldPadElt
{ Computes the p-adic height of a point on an elliptic curve over Q to
  the given absolute precision. The prime must be good, ordinary,
  and at least 5. The default precision is 20.}
 require IsPrime(p) : "p must be prime";
 require p ge 5: "p must be at least 5";
 E:=Curve(P); require not p in BadPrimes(E): "p cannot be a bad prime";
 OP:=Precision; if OP eq 0 then OP:=20; end if;
 require Type(OP) eq RngIntElt and OP ge 1:
  "Precision must be a positive integer";
 n1:=#ChangeRing(E,GF(p)); require n1 ne p+1: "p cannot be supersingular";
 require Discriminant(E) eq Discriminant(MinimalModel(E)):
  "E must be given by a model with minimal discriminant";
 require &and[Valuation(a,p) ge 0 : a in aInvariants(E)]:
  "Coefficients of E must be p-integral";
 if Order(P) ne 0 then return pAdicField(p,OP)!0; end if;
 if OP lt 3 then OP:=3; end if;
 n2:=LCM([TamagawaNumber(E,p) : p in BadPrimes(E)]); n:=LCM(n1,n2);
 Q:=n2*P; m:=n div n2; MM:=OP+2*Valuation(n,p);
 a:=Numerator(Q[1]); b:=Numerator(Q[2]); _,d:=IsSquare(Denominator(Q[1]));
 if E2 eq 0 then
  if OP eq 2 then E2:=1;
  else t:=Cputime(); E2:=EisensteinTwo(E,p : Precision:=MM-2);
       vprintf pAdicHeight: "E2: %os\n",Cputime(t); end if; end if;
 a,b,d:=modLmult_new(E,a,b,d,m,p^MM); s:=sigma(E,E2,p,1+MM);
 a:=Integers()!a; b:=Integers()!b; d:=Integers()!d;
 e:=-a/b*Evaluate(s/Parent(s).1,-d*a/b); if n1 eq p then OP:=OP+1; end if;
 r:=2/(p-1)*Log(e^(p-1)); return (pAdicField(p,OP)!r)/n^2; end intrinsic;

intrinsic pAdicHeightPairingMatrix
(S::[PtEll[FldRat]],p::RngIntElt : Precision:=0, E2:=0) -> FldPadElt
{ Computes the p-adic height matrix of the given points on an elliptic curve
  over Q to the given absolute precision The prime must be good, ordinary,
  and at least 5. The default precision is 20, and the precision is for
  the points involved, so some might be lost in the determinant step}
 require IsPrime(p) : "p must be prime";
 require p ge 5: "p must be at least 5";
 OP:=Precision; if OP eq 0 then OP:=20; end if;
 require Type(OP) eq RngIntElt and OP ge 1:
  "Precision must be a positive integer";
 E:=Curve(Universe(S));
 require not p in BadPrimes(E): "p cannot be a bad prime";
 n1:=#ChangeRing(E,GF(p)); require n1 ne p+1: "p cannot be supersingular";
 require Discriminant(E) eq Discriminant(MinimalModel(E)):
  "E must be given by a model with minimal discriminant";
 require &and[Valuation(a,p) ge 0 : a in aInvariants(E)]:
  "Coefficients of E must be p-integral";
 K:=pAdicField(p,OP);
 M:=MatrixAlgebra(K,#S)!0; if #S eq 0 then return M; end if;
 n2:=LCM([TamagawaNumber(E,p) : p in BadPrimes(E)]); n:=LCM(n1,n2);
 MM:=OP+2*Valuation(n,p); E2:=EisensteinTwo(E,p : Precision:=Max(1,MM-2));
 for i in [1..#S] do
  M[i][i]:=pAdicHeight(S[i],p : Precision:=OP,E2:=E2); end for;
 for i in [1..#S] do for j in [i+1..#S] do
  M[i][j]:=M[i][i]+M[j][j]-K!pAdicHeight(S[i]+S[j],p : Precision:=OP,E2:=E2);
  M[i][j]/:=-2; M[j][i]:=M[i][j]; end for; end for; return -M;  end intrinsic;

PREC:=Precision;

intrinsic pAdicRegulator
(S::[PtEll[FldRat]],p::RngIntElt : Precision:=0, E2:=0) -> FldPadElt
{ Computes the p-adic height matrix of the given points on an elliptic curve
  over Q to the given absolute precision The prime must be good, ordinary,
  and at least 5. The default precision is 20, and the precision is for
  the points involved, so some might be lost in the determinant step}
 OP:=Precision; if OP eq 0 then OP:=20; end if;
 M:=pAdicHeightPairingMatrix(S,p:Precision:=OP+1,E2:=E2)/p;
 if #S eq 0 then return 1; end if; // is this correct?
 d:=Denominator(ChangeRing(M,Rationals()));
 D:=Determinant(ChangeRing(M*d,pAdicRing(p,PREC(BaseRing(Parent(M))))));
 D:=(pAdicField(p,PREC(BaseRing(Parent(M))))!D)/d^#S;
 w:=0; v:=OP-AbsolutePrecision(D);
 while v gt 0 do w:=w+v; // printf "Adding %o extra precision at %o\n",w,p;
  M:=pAdicHeightPairingMatrix(S,p:Precision:=OP+w+1,E2:=E2)/p;
  d:=Denominator(ChangeRing(M,Rationals()));
  D:=Determinant(ChangeRing(M*d,pAdicRing(p,PREC(BaseRing(Parent(M))))));
  D:=(pAdicField(p,PREC(BaseRing(Parent(M))))!D)/d^#S;
  v:=OP-AbsolutePrecision(D); end while; return D; end intrinsic;

/*
procedure padic_expand(x) p:=Prime(Parent(x));
 for v in [Valuation(x)..AbsolutePrecision(x)-1] do
  u:=x/p^v; a:=(Integers()!u) mod p;
  printf "%o*%o^%o + ",a,p,v; x:=x-a*p^v; end for;
  printf "O(%o^%o)\n",p,AbsolutePrecision(x); end procedure;
*/
