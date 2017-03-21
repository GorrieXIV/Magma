freeze;

//////////////////////////////////////////////////////////////////////////
// Two descent for elliptic curves over Q
// This is an efficient implementation 
// (relative to the old one, at least)
// by Mark Watkins
//////////////////////////////////////////////////////////////////////////

declare attributes CrvEll : TwoSelmerGroup, TwoSelmerGroupRemoveTorsion;

two_selmer_rec := recformat<group, map, two_desc>; // for caching

/************************************************************************/

function HALVE_IT(P) D:=DivisionPoints(P,2);
 if #D eq 0 then return false,P; else return true,D[1]; end if; end function;

function iHintsEC(E) T:=DivisionPoints(E!0,2);
 if #T eq 1 then return [],0,0; // use that 1st return value is point at oo
 elif #T eq 2 then b:=true; P:=T[2]; i:=0;
  while b do b,P:=HALVE_IT(P); i:=i+1; end while; return [P],i,0; end if;
 P1:=T[3]; P2:=T[4]; b1:=true; b2:=true; i1:=0; i2:=0;
 while b2 do b2,P2:=HALVE_IT(P2); i2:=i2+1;
  if b1 then b1,P1:=HALVE_IT(P1); i1:=i1+1; end if;
  if not b2 then
   if not b1 then b2,P2:=HALVE_IT(P1+P2);
   else t:=b1; b1:=b2; b2:=t; t:=P1; P1:=P2; P2:=t; end if; end if;
 end while; return [P1,P2],i2,i1; end function;

/************************************************************************/

function muat2(s) Q:=Rationals(); Z:=Integers();
 s:=Q!s; v:=Valuation(s,2); u:=(Z!(s/2^v)) mod 8;
 return [v mod 2,u div 4,((u-1) div 2) mod 2]; end function;

function mu5(u,w,s)
 v:=Valuation(Norm(u),2) div 2; u:=(u/2^v)^3;
 b:=Trace((u-1)/2*s)/Trace(w*s); a:=(u-1)/2-b*w;
 a:=Rationals()!a; b:=Rationals()!b;
 assert IsOdd(Denominator(a)); assert IsOdd(Denominator(b));
 a:=Integers()!Numerator(a) mod 2; b:=Integers()!Numerator(b) mod 2;
 u:=u*3^a*(1+2*w)^b; t:=Trace((u-1)/4);
 return [v mod 2,a,b,(Numerator(Rationals()!t)) mod 2]; end function;

function mu2(u,w) assert Valuation(Norm(w),2) eq 1;
 vv:=Valuation(Norm(u),2); u:=u/4^(vv div 4)/w^(vv mod 4); r:=[vv mod 2,0,0,0];
 v2:=Valuation(Norm(u-1),2); if v2 eq 1 then u:=u/(1+w); r[2]:=1; end if;
 v3:=Valuation(Norm(u-1),2); if v3 eq 2 then u:=u/(1+w)^2; end if;
 v4:=Valuation(Norm(u-1),2); if v4 eq 3 then u:=u/(1+w^3); r[4]:=1; end if;
 v5:=Valuation(Norm(u-1),2); if v5 eq 4 then r[3]:=1; end if; return r;
 end function;

function mumu2(u,s,f)
 s:=s-Trace(s)/2; v2:=Valuation(Norm(s),2); s:=s/2^(v2 div 2);
 r:=Discriminant(f); r:=r/4^(Valuation(r,2) div 2); r:=(Integers()!r) mod 8;
 if r eq 5 then return mu5(u,(3+s)/2,s); end if;
 if r mod 2 eq 1 then w:=s+1; else w:=s; end if;
 return mu2(u,w); end function;

function ok2(u,vv,s)
 uu:=(u-1)/2; a:=0; b:=0; Q:=Rationals();
 while true do
  v:=Valuation(Norm(s+a),2); b1:=(s+a)/2^v;
  if Valuation(Norm(b1-1),2) mod 2 eq 0 then break; end if; a:=a+1; end while;
 while true do
  v:=Valuation(Norm(s^2+b),2); b2:=(s^2+b)/2^v;
  if Valuation(Norm(b2-1),2) mod 2 eq 0 and Valuation(Norm(b2-b1),2) mod 2 eq 0
   then break; end if; b:=b+1; end while;
 E:=Eltseq(uu); E cat:=[0 : i in [#E..2]]; r2:=Q!(E[3]/Eltseq(b2)[3]);
 uu:=uu-r2*b2;
 E:=Eltseq(uu); E cat:=[0 : i in [#E..1]]; r1:=Q!(E[2]/Eltseq(b1)[2]);
 r0:=Q!(uu-r1*b1); 
 v0:=Numerator(r0) mod 2; v1:=Numerator(r1) mod 2; v2:=Numerator(r2) mod 2;
 u:=u*3^v0*(1+2*b1)^v1*(1+2*b2)^v2; t:=Trace((u-1)/4); 
 return [vv mod 2,v0,v1,v2,Numerator(Q!t) mod 2]; end function;

function mu2map3U(u,s) Q:=Rationals();
 v:=Valuation(Norm(u),2) div 3; u:=u/2^v;
 if Numerator(Q!Norm(u-1)) mod 2 eq 0 then return ok2(u,v,s); end if;
 uu:=u*(s)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 uu:=u*(s^2)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 uu:=u*(s+s^2)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 uu:=u*(1+s^2)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 uu:=u*(1+s)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 uu:=u*(1+s+s^2)^2;
 if Numerator(Q!Norm(uu-1)) mod 2 eq 0 then return ok2(uu,v,s); end if;
 assert false; end function;

function mu2map3(u,s)
 s:=s-Trace(s)/3; v2:=Valuation(Norm(s),2); s:=s/2^(v2 div 3);
 if v2 mod 3 eq 0 then return mu2map3U(u,s); end if;
 if v2 mod 3 eq 2 then s:=s^2/2; end if;
 vv:=Valuation(Norm(u),2); u:=u/4^(vv div 6)/s^(vv mod 6);
 v2:=Valuation(Norm(u-1),2); if v2 eq 1 then u:=u/(1+s); end if;
 v3:=Valuation(Norm(u-1),2); if v3 eq 2 then u:=u/(1+s)^2; end if;
 v4:=Valuation(Norm(u-1),2); if v4 eq 3 then u:=u/(1+s^3); end if;
 v5:=Valuation(Norm(u-1),2); if v5 eq 4 then u:=u/(1+s^3)^2; end if;
 v5:=Valuation(Norm(u-1),2); if v5 eq 4 then u:=u/(1+s^2+s^3)^2; end if;
 v6:=Valuation(Norm(u-1),2); if v6 eq 5 then u:=u/(1+s^5); end if;
 v7:=Valuation(Norm(u-1),2);
 return [vv mod 2,
	 v2 eq 1 select 1 else 0,v4 eq 3 select 1 else 0,
	 v6 eq 5 select 1 else 0,v7 eq 6 select 1 else 0]; end function;

function ARRnon0(A) return not &and[x eq 0 : x in A]; end function;

function wxyz2(u,R,f,W,s,F)
 if #R eq 3 then
  V:=&cat[Valuation(u-r) gt W/3 select
     	 muat2(Evaluate(Derivative(f),r)) else muat2(u-r) : r in R]; end if;
 if #R eq 1 then
  V:=Valuation(u-R[1]) gt W/3 select
	muat2(Evaluate(Derivative(f),R[1])) else muat2(u-R[1]);
  V cat:=mumu2(u-s,s,F); end if;
 if #R eq 0 then V:=mu2map3(u-s,s); end if;
 return ChangeUniverse(V,GF(2)); end function;

function IOD2C(I) R,f,W,ta,s,F:=Explode(I);
 x:=Parent(f).1; PZ:=PolynomialRing(Integers()); f:=PZ!f; X:=PZ.1;
 t:=2^(Valuation(LeadingCoefficient(f),2)+2); // Stoll bug? he has t=4
 g:=PZ!Reverse(Eltseq(f)); u:=2^(Valuation(LeadingCoefficient(g),2)+2);
 A:=[<PZ!(t^Degree(f)*Evaluate(f,x/t)),0,1/t,0,true>]; EQ:=ExactQuotient;
 while not IsEmpty(A) do last:=A[#A]; Prune(~A);
  f,xi0,a,d,b:=Explode(last); df:=Derivative(f);
  for xi in GF(2) do fx:=Evaluate(f,xi); xi1:=Integers()!xi;
   if fx eq 0 then fx1:=Evaluate(df,xi);
    if fx1 eq 0 then
     if Evaluate(f,Integers(4)!xi1) eq 0 then
      A:=[<EQ(Evaluate(f,xi1+2*X),4),xi0+a*xi1,2*a,d+1,b>] cat A; end if;
    else //fx1 ne 0
     xi1+:=Integers()!Evaluate(f,Integers(4)!xi1);
     xi1+:=Integers()!(4+Evaluate(f,Integers(8)!xi1));
     A:=[<EQ(Evaluate(f,xi1+8*X),4),xi0+a*xi1,8*a,d+1,b>] cat A; end if;
   else // fx ne 0
    for xi2 in [Integers(8) | xi1+i : i in [0,2,4,6]] do
     if Evaluate(f,xi2) eq 1 then u:=xi0+a*Integers()!xi2;
      if b then te:=wxyz2(u,R,f,W,s,F);
               if ARRnon0(te) and not te in ta then return ta cat [te]; end if;
      end if; end if; end for; end if; end for; end while;
 assert false; return [ta]; end function;

function at_2C3(f,L,R,W) Q:=Rationals(); K:=Parent(L[1]);
 Kp:=pAdicField(2,W); G:=iHintsEC(ChangeRing(EllipticCurve(f),Kp)); U:=[];
 T:=[&cat[Valuation(g[1]-r) gt W/3 select
      muat2(Evaluate(Derivative(f),r)) else muat2(g[1]-r) : r in R] : g in G];
 T:=[ChangeUniverse(t,GF(2)) : t in T];
 T cat:=[Eltseq(Vector(T[1])+Vector(T[2]))];
 T:=IOD2C(<R,f,W,T,0,0>); Remove(~T,3); assert #T eq 3;
 for l in L do e:=Polynomial(Eltseq(l)); V:=[];
  for r in R do u:=Evaluate(e,r); k:=0; v:=Valuation(u);
   while v gt W/3 or Q!u eq 0 do k:=k+2; e2:=Polynomial(Eltseq(l/(K.1-Q!r)^k));
    u:=Evaluate(e2,r); v:=Valuation(u); end while; V cat:=muat2(u); end for;
  U cat:=[V]; end for; assert #G eq 2;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=ChangeRing(Vector(T[3]),GF(2));
 t4:=t1+t2; t5:=t1+t3; t6:=t2+t3; t7:=t1+t2+t3;
 U:=[s : t in [t1,t2,t3,t4,t5,t6,t7] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_2C1(f,L,R,W) Q:=Rationals(); K:=Parent(L[1]);
 Kp:=pAdicField(2,W); G:=iHintsEC(ChangeRing(EllipticCurve(f),Kp));
 U:=[]; g:=G[1]; r:=R[1]; assert #G eq 1;
 F:=[P[1] : P in Factorization(PolynomialRing(Kp)!f) | Degree(P[1]) eq 2][1];
 T:=Valuation(g[1]-r) gt W/3 select
	muat2(Evaluate(Derivative(f),r)) else muat2(g[1]-r);
 FP:=Polynomial(ChangeUniverse(Eltseq(F),Q));
 NF<z>:=NumberField(FP);
 T cat:=mumu2((Q!g[1])-z,z,FP); T:=[ChangeUniverse(T,GF(2))];
 T:=IOD2C(<R,f,W,T,z,FP>); assert #T eq 2;
 for l in L do e:=Polynomial(Eltseq(l)); V:=[];
  u:=Evaluate(e,r); k:=0; v:=Valuation(u);
  while v gt 2*W/3 do k:=k+2; e2:=Polynomial(Eltseq(l/(K.1-Q!r)^k));
   u:=Evaluate(e2,r); v:=Valuation(u); end while;
  V:=muat2(u); FF:=ChangeRing(F,Rationals()); k:=0; FF:=Evaluate(FF,K.1);
  E:=Eltseq(l); u:=&+[E[i]*z^(i-1) : i in [1..#E]]; v:=Valuation(Norm(u),2);
  while v gt 2*W/3 do k:=k+2; E:=Eltseq(l/FF^k);
   u:=&+[E[i]*z^(i-1) : i in [1..#E]]; v:=Valuation(Norm(u),2); end while;
  V cat:=mumu2(u,z,FP); U cat:=[V]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=t1+t2; U:=[s : t in [t1,t2,t3] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_2C0(f,L,R,W) K:=Parent(L[1]);
 U:=[mu2map3(l,K.1) : l in L]; T:=IOD2C(<[],f,W,[],K.1,0>); assert #T eq 1;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2));
 U:=[s : t in [t1] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_2C(f,L,W) R:=Roots(f,pAdicField(2,W));
 if #R eq 3 then return at_2C3(f,L,[r[1] : r in R],W); end if;
 if #R eq 1 then return at_2C1(f,L,[R[1][1]],W); end if;
 return at_2C0(f,L,[],W); end function;

/************************************************************************/

function muCmap3(w,s)
 n:=Norm(w); v:=Valuation(n,3); s:=s-Trace(s)/3; assert Trace(s) eq 0;
 v2:=Valuation(Norm(s),3);
 while v2 eq 0 do s:=s+1; v2:=Valuation(Norm(s),3); end while;
 if v2 mod 3 eq 0 and (Integers()!Norm(s+3)) mod 27 eq 0 then
  return [v mod 2,IsSquare(GF(3)!(n/3^v)) select 0 else 1]; end if;
 s:=s/3^(v2 div 3); if v2 mod 3 eq 2 then s:=s^2/3; end if;
 N:=Numerator(Norm(w/9^(v div 6)/s^(v mod 6)-1));
 return [v mod 2,N mod 3 eq 0 select 0 else 1]; end function;

function muCmap(w,p,s) if p eq 3 then return muCmap3(w,s); end if;
 n:=Norm(w); v:=Valuation(n,p); s:=s-Trace(s)/3; assert Trace(s) eq 0;
 v2:=Valuation(Norm(s),p);
 if v2 mod 3 eq 0 then
  return [(v div 3) mod 2,IsSquare(GF(p)!(n/p^v)) select 0 else 1]; end if;
 s:=s/p^(v2 div 3); if v2 mod 3 eq 2 then s:=s^2/p; end if;
 u:=Trace(w/(p^2)^(v div 6)/s^(v mod 6))/3;
 return [v mod 2,IsSquare(GF(p)!u) select 0 else 1]; end function;

function mumap(u,p) v:=Valuation(u);
 return [v mod 2,IsSquare(u/p^v) select 0 else 1]; end function;

function munmap(u,p,s)
 n:=Norm(u); v:=Valuation(n,p); s:=s-Trace(s)/2; v2:=Valuation(Norm(s),p);
 if v2 mod 2 eq 1 then s:=s/p^(v2 div 2);
  t:=Trace(u/s^(v mod 4)/(p^2)^(v div 4))/2;
  return [v mod 2,IsSquare(GF(p)!t) select 0 else 1]; end if;
 return [(v div 2) mod 2,IsSquare(GF(p)!(n/p^v)) select 0 else 1];
 end function;

function at_pC3(f,L,p,R,W) Q:=Rationals(); K:=Parent(L[1]);
 Kp:=pAdicField(p,W); G:=iHintsEC(ChangeRing(EllipticCurve(f),Kp)); U:=[];
 T:=[&cat[Valuation(g[1]-r) gt W/3 select
     mumap(Evaluate(Derivative(f),r),p) else mumap(g[1]-r,p) : r in R]
	 : g in G];
 for l in L do e:=Polynomial(Eltseq(l)); V:=[];
  for r in R do u:=Evaluate(e,r); k:=0; v:=Valuation(u);
   while v gt W/3 or Q!u eq 0 do k:=k+2; e2:=Polynomial(Eltseq(l/(K.1-Q!r)^k));
    u:=Evaluate(e2,r); v:=Valuation(u); end while;
   V cat:=[v mod 2,IsSquare(u/p^v) select 0 else 1]; end for;
  U cat:=[V]; end for; assert #G eq 2;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=t1+t2; U:=[s : t in [t1,t2,t3] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_pC1(f,L,p,R,W) Q:=Rationals(); K:=Parent(L[1]);
 Kp:=pAdicField(p,W); G:=iHintsEC(ChangeRing(EllipticCurve(f),Kp));
 U:=[]; assert #G eq 1; g:=G[1]; r:=R[1];
 F:=[P[1] : P in Factorization(PolynomialRing(Kp)!f) | Degree(P[1]) eq 2][1];
 T:=Valuation(g[1]-r) gt W/3 select
	mumap(Evaluate(Derivative(f),r),p) else mumap(g[1]-r,p);
 NF<z>:=NumberField(Polynomial(ChangeUniverse(Eltseq(F),Q)));
 T cat:=munmap((Q!g[1])-z,p,z); T:=[T];
 for l in L do e:=Polynomial(Eltseq(l)); V:=[];
  u:=Evaluate(e,r); k:=0; v:=Valuation(u);
  while v gt 2*W/3 do k:=k+2; e2:=Polynomial(Eltseq(l/(K.1-Q!r)^k));
   u:=Evaluate(e2,r); v:=Valuation(u); end while;
  V:=mumap(u,p); FF:=ChangeRing(F,Rationals()); k:=0; FF:=Evaluate(FF,K.1);
  E:=Eltseq(l); u:=&+[E[i]*z^(i-1) : i in [1..#E]]; v:=Valuation(Norm(u),p);
  while v gt 2*W/3 do k:=k+2; E:=Eltseq(l/FF^k);
   u:=&+[E[i]*z^(i-1) : i in [1..#E]]; v:=Valuation(Norm(u),p); end while;
  V cat:=munmap(u,p,z); U cat:=[V]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2));
 U:=[s : t in [t1] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_pC0(f,L,p,R,W) K:=Parent(L[1]);
 U:=[muCmap(l,p,K.1) : l in L];
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 return Matrix(Basis(Image(Matrix(K)))); end function;

function at_pC(f,L,p,W) if p eq 2 then return at_2C(f,L,W); end if;
 R:=Roots(f,pAdicField(p,W));
 if #R eq 3 then return at_pC3(f,L,p,[r[1] : r in R],W); end if;
 if #R eq 1 then return at_pC1(f,L,p,[R[1][1]],W); end if;
 return at_pC0(f,L,p,[],W); end function;

/* ================================================================ */

/* ================================================================ */

function at_ooL(L,f) r1,r2,r3:=Explode([r[1] : r in Roots(f)]);
 M:=Matrix(3,#L,[[l[1]-r1 lt 0 select GF(2)!1 else GF(2)!0 : l in L],
		 [l[2]-r2 lt 0 select GF(2)!1 else GF(2)!0 : l in L],
		 [l[3]-r3 lt 0 select GF(2)!1 else GF(2)!0 : l in L]]);
 if r2 lt r3 and r2 lt r1 then v:=Vector([GF(2)!1,0,1]); end if;
 if r3 lt r2 and r3 lt r1 then v:=Vector([GF(2)!1,1,0]); end if;
 if r2 gt r1 and r3 gt r1 then v:=Vector([GF(2)!0,1,1]); end if;
 N:=Transpose(M); b,s,K:=IsConsistent(N,v);
 if b then B:=Basis(K) cat [s]; else B:=Basis(Kernel(N)); end if;
 return Matrix(B); end function;

function at_ooQ(L,f) D:=Discriminant(f);
 if D lt 0 then
  M:=Matrix(1,#L,[[l[1] lt 0 select GF(2)!1 else GF(2)!0 : l in L]]);
  return Matrix(Basis(Kernel(Transpose(M)))); end if;
 E:=[Eltseq(l[2]): l in L]; H:=Max([Height(e) : e in &cat E] cat [Abs(D)]);
 E:=[Polynomial(e) : e in E]; W:=Ceiling(4*Log(H)/Log(10)+50);
 r1,r2:=Explode([r[1] : r in Roots(f,RealField(W))]);
 M:=Matrix(3,#L,[[l[1] lt 0 select GF(2)!1 else GF(2)!0 : l in L],
		 [Evaluate(e,r1) lt 0 select GF(2)!1 else GF(2)!0 : e in E],
		 [Evaluate(e,r2) lt 0 select GF(2)!1 else GF(2)!0 : e in E]]);
 if r1 lt r2 and r1 lt 0 then v:=Vector([GF(2)!1,0,1]); end if;
 if r2 lt r1 and r2 lt 0 then v:=Vector([GF(2)!1,1,0]); end if;
 if r1 gt 0 and r2 gt 0 then v:=Vector([GF(2)!0,1,1]); end if;
 N:=Transpose(M); b,s,K:=IsConsistent(N,v);
 if b then B:=Basis(K) cat [s]; else B:=Basis(Kernel(N)); end if;
 return Matrix(B); end function;

function at_ooC(L,f) D:=Discriminant(f);
 E:=[Eltseq(l): l in L]; H:=Max([Height(e) : e in &cat E] cat [Abs(D)]);
 E:=[Polynomial(e) : e in E]; W:=Ceiling(4*Log(H)/Log(10)+50);
 if D lt 0 then r1:=Roots(f,RealField(W))[1][1];
  M:=Matrix(1,#L,[[Evaluate(e,r1) lt 0 select GF(2)!1 else GF(2)!0 : e in E]]);
  return Matrix(Basis(Kernel(Transpose(M)))); end if;
 r1,r2,r3:=Explode([r[1] : r in Roots(f,RealField(W))]);
 M:=Matrix(3,#L,[[Evaluate(e,r1) lt 0 select GF(2)!1 else GF(2)!0 : e in E],
		 [Evaluate(e,r2) lt 0 select GF(2)!1 else GF(2)!0 : e in E],
		 [Evaluate(e,r3) lt 0 select GF(2)!1 else GF(2)!0 : e in E]]);
 if r2 lt r3 and r2 lt r1 then v:=Vector([GF(2)!1,0,1]); end if;
 if r3 lt r2 and r3 lt r1 then v:=Vector([GF(2)!1,1,0]); end if;
 if r2 gt r1 and r3 gt r1 then v:=Vector([GF(2)!0,1,1]); end if;
 N:=Transpose(M); b,s,K:=IsConsistent(N,v);
 if b then B:=Basis(K) cat [s]; else B:=Basis(Kernel(N)); end if;
 return Matrix(B); end function;

/************************************************************************/

function wxyz(X,R,Kp,F,W)
 u:=X-R[1]; v:=Valuation(u); Z:=Integers();
 if v gt W/3 then u:=Kp!Evaluate(Derivative(F),R[1]); v:=Valuation(u); end if;
 x:=Z!(u/2^v); V:=[v,x div 4,((x-1) div 2)];
 u:=X-R[2]; v:=Valuation(u);
 if v gt W/3 then u:=Kp!Evaluate(Derivative(F),R[2]); v:=Valuation(u); end if;
 x:=Z!(u/2^v); V cat:=[v,x div 4,((x-1) div 2)];
 u:=X-R[3]; v:=Valuation(u);
 if v gt W/3 then u:=Kp!Evaluate(Derivative(F),R[3]); v:=Valuation(u); end if;
 x:=Z!(u/2^v); V cat:=[v,x div 4,((x-1) div 2)];
 return Eltseq(ChangeRing(ChangeRing(Vector(V),GF(2)),Z)); end function;

function IOD2Q2(I) R,Kp,f,W,ta:=Explode(I);
 x:=Parent(f).1; PZ:=PolynomialRing(Integers()); f:=PZ!f; X:=PZ.1;
 t:=2^(Valuation(LeadingCoefficient(f),2)+2); // Stoll bug? he has t=4
 g:=PZ!Reverse(Eltseq(f)); u:=2^(Valuation(LeadingCoefficient(g),2)+2);
 A:=[<PZ!(t^Degree(f)*Evaluate(f,x/t)),0,1/t,0,true>]; EQ:=ExactQuotient;
 while not IsEmpty(A) do last:=A[#A]; Prune(~A);
  f,xi0,a,d,b:=Explode(last); df:=Derivative(f);
  for xi in GF(2) do fx:=Evaluate(f,xi); xi1:=Integers()!xi;
   if fx eq 0 then fx1:=Evaluate(df,xi);
    if fx1 eq 0 then
     if Evaluate(f,Integers(4)!xi1) eq 0 then
      A:=[<EQ(Evaluate(f,xi1+2*X),4),xi0+a*xi1,2*a,d+1,b>] cat A; end if;
    else //fx1 ne 0
     xi1+:=Integers()!Evaluate(f,Integers(4)!xi1);
     xi1+:=Integers()!(4+Evaluate(f,Integers(8)!xi1));
     A:=[<EQ(Evaluate(f,xi1+8*X),4),xi0+a*xi1,8*a,d+1,b>] cat A; end if;
   else // fx ne 0
    for xi2 in [Integers(8) | xi1+i : i in [0,2,4,6]] do
     if Evaluate(f,xi2) eq 1 then u:=xi0+a*Integers()!xi2;
      if b then te:=wxyz(u,R,Kp,f,W);
               if ARRnon0(te) and not te in ta then return ta cat [te]; end if;
      end if; end if; end for; end if; end for; end while;
 assert false; return [ta]; end function;

function at_2Q2(f,L,W,r)
 Kp:=pAdicField(2,W); F:=f*Parent(f).1; K<s>:=Parent(L[1][2]); Q:=Rationals();
 G:=iHintsEC(ChangeRing(EllipticCurve(F),Kp)); T:=[]; U:=[]; Z:=Integers();
 for g in G do T cat:=[wxyz(g[1],[0,r[1],r[2]],Kp,F,W)]; end for;
 T cat:=[Eltseq(ChangeRing(ChangeRing(Vector(T[1])+Vector(T[2]),GF(2)),Z))];
 T:=IOD2Q2(<[0,r[1],r[2]],Kp,F,W,T>); Remove(~T,3); assert #T eq 3;
 for l in L do v:=Valuation(Kp!l[1]);
  x:=Z!(l[1]/2^v); V:=[v,x div 4,((x-1) div 2)];
  e:=Polynomial(Eltseq(l[2])); u:=Evaluate(e,r[1]); k:=0; v:=Valuation(u);
  while v gt W/3 or Q!u eq 0 do k:=k+2;
   e:=Polynomial(Eltseq(l[2]/(s-Q!r[1])^k));
   u:=Evaluate(e,r[1]); v:=Valuation(u); end while;
  x:=Z!(u/2^v); V cat:=[v,x div 4,((x-1) div 2)];
  u:=Evaluate(e,r[2]); k:=0; v:=Valuation(u);
  while v gt W/3 or Q!u eq 0 do k:=k+2;
   e:=Polynomial(Eltseq(l[2]/(s-Q!r[2])^k));
   u:=Evaluate(e,r[2]); v:=Valuation(u); end while;
  x:=Z!(u/2^v); V cat:=[v,x div 4,((x-1) div 2)]; U cat:=[V]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=ChangeRing(Vector(T[3]),GF(2));
 t4:=t1+t2; t5:=t1+t3; t6:=t2+t3; t7:=t1+t2+t3;
 U:=[s : t in [t1,t2,t3,t4,t5,t6,t7] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_pQ2(f,L,p,W,r) if p eq 2 then return at_2Q2(f,L,W,r); end if;
 Kp:=pAdicField(p,W); F:=f*Parent(f).1; K<s>:=Parent(L[1][2]); Q:=Rationals();
 G:=iHintsEC(ChangeRing(EllipticCurve(F),Kp)); T:=[]; U:=[]; Z:=Integers();
 for g in G do // T cat:=[wxyz(g[1],[0,r[1],r[2]],Kp,F)];
  u:=g[1]; v:=Valuation(u);
  if v gt W/3 then u:=Kp!Coefficient(f,0); v:=Valuation(u); end if;
  V:=[v mod 2,IsSquare(u/p^v) select 0 else 1];
  u:=g[1]-r[1]; v:=Valuation(u);
  if v gt W/3 then u:=Kp!Evaluate(Derivative(F),r[1]); v:=Valuation(u); end if;
  V cat:=[v mod 2,IsSquare(u/p^v) select 0 else 1];
  u:=g[1]-r[2]; v:=Valuation(u);
  if v gt W/3 then u:=Kp!Evaluate(Derivative(F),r[2]); v:=Valuation(u); end if;
  V cat:=[v mod 2,IsSquare(u/p^v) select 0 else 1];
  T cat:=[V]; end for;
 for l in L do v:=Valuation(Kp!l[1]);
  V:=[v mod 2,IsSquare((Kp!l[1])/p^v) select 0 else 1];
  e:=Polynomial(Eltseq(l[2])); u:=Evaluate(e,r[1]); k:=0; v:=Valuation(u);
  while v gt W/3 or Q!u eq 0 do k:=k+2;
   e:=Polynomial(Eltseq(l[2]/(s-Q!r[1])^k));
   u:=Evaluate(e,r[1]); v:=Valuation(u); end while;
  V cat:=[v mod 2,IsSquare(u/p^v) select 0 else 1];
  u:=Evaluate(e,r[2]); k:=0; v:=Valuation(u);
  while v gt W/3 or Q!u eq 0 do k:=k+2;
   e:=Polynomial(Eltseq(l[2]/(s-Q!r[2])^k));
   u:=Evaluate(e,r[2]); v:=Valuation(u); end while;
  V cat:=[v mod 2,IsSquare(u/p^v) select 0 else 1];
  U cat:=[V]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=t1+t2; U:=[s : t in [t1,t2,t3] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function abcd(I) lcoeff,W,u1,u2,r,t0,w:=Explode(I); Z:=Integers();
 v:=Valuation(u1); if v gt W/3 then u1:=lcoeff; v:=Valuation(u1); end if;
 x:=Z!(u1/2^v); V:=[v,x div 4,((x-1) div 2)];
 if r eq 5 then V cat:=mu5(u2,(3+t0)/2,t0); else V cat:=mu2(u2,w); end if;
 return ChangeUniverse(V,GF(2)); end function;

function IOD2Q(f,func,I) lcoeff,W,r,t0,w,s,ta,Kp:=Explode(I);
 x:=Parent(f).1; PZ:=PolynomialRing(Integers()); f:=PZ!f; X:=PZ.1;
 t:=2^(Valuation(LeadingCoefficient(f),2)+2); // Stoll bug? he has t=4
 g:=PZ!Reverse(Eltseq(f)); u:=2^(Valuation(LeadingCoefficient(g),2)+2);
 A:=[<PZ!(t^Degree(f)*Evaluate(f,x/t)),0,1/t,0,true>]; EQ:=ExactQuotient;
 while not IsEmpty(A) do last:=A[#A]; Prune(~A);
  f,xi0,a,d,b:=Explode(last); df:=Derivative(f);
  for xi in GF(2) do fx:=Evaluate(f,xi); xi1:=Integers()!xi;
   if fx eq 0 then fx1:=Evaluate(df,xi);
    if fx1 eq 0 then
     if Evaluate(f,Integers(4)!xi1) eq 0 then
      A:=[<EQ(Evaluate(f,xi1+2*X),4),xi0+a*xi1,2*a,d+1,b>] cat A; end if;
    else //fx1 ne 0
     xi1+:=Integers()!Evaluate(f,Integers(4)!xi1);
     xi1+:=Integers()!(4+Evaluate(f,Integers(8)!xi1));
     A:=[<EQ(Evaluate(f,xi1+8*X),4),xi0+a*xi1,8*a,d+1,b>] cat A; end if;
   else // fx ne 0
    for xi2 in [Integers(8) | xi1+i : i in [0,2,4,6]] do
     if Evaluate(f,xi2) eq 1 then u:=xi0+a*Integers()!xi2;
      if b then te:=func(<lcoeff,W,Kp!u,u-s,r,t0,w>); // need to expand ta
              if ARRnon0(te) and not te in ta then return ta cat [te]; end if;
      end if; end if; end for; end if; end for; end while;
 assert false; return [ta]; end function;

function at_2Q0(f,L,p,W)
 Kp:=pAdicField(p,W); F:=f*Parent(f).1; K<s>:=Parent(L[1][2]); Q:=Rationals();
 G:=iHintsEC(ChangeRing(EllipticCurve(F),Kp)); T:=[]; U:=[];
 t0:=K![Coefficient(f,1)/2,1]; assert Trace(t0) eq 0; assert #G eq 1;
 v2:=Valuation(Norm(t0),p); t0:=t0/p^(v2 div 2);
 r:=Discriminant(f); r:=r/4^(Valuation(r,2) div 2); r:=(Integers()!r) mod 8;
 if IsOdd(r) then w:=t0+1; else w:=t0; end if; lcoeff:=Kp!Coefficient(f,0);
 for g in G do T cat:=[abcd(<lcoeff,W,g[1],(Q!g[1])-s,r,t0,w>)]; end for;
 T:=[ChangeUniverse(t,GF(2)) : t in T];
 T:=IOD2Q(F,abcd,<lcoeff,W,r,t0,w,s,T,Kp>); assert #T eq 2;
 for l in L do U cat:=[abcd(<0,W,Kp!l[1],l[2],r,t0,w>)]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2)); t2:=ChangeRing(Vector(T[2]),GF(2));
 t3:=t1+t2; U:=[s : t in [t1,t2,t3] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function eval_pQ0(p,v2,t0,u)
 if v2 mod 2 ne 0 then v:=Valuation(Norm(u),p);
  t:=Trace(u/t0^(v mod 4)/(p^2)^(v div 4)/2);
  return [v mod 2,IsSquare(GF(p)!t) select 0 else 1];
 else n:=Norm(u); v:=Valuation(n,p);
  return [(v div 2) mod 2,IsSquare(GF(p)!(n/p^v)) select 0 else 1]; end if;
end function;

function deval_pQ0(p,u)
 K<s>:=Parent(u); f:=MinimalPolynomial(s); t0:=K![Coefficient(f,1)/2,1];
 v2:=Valuation(Norm(t0),p); t0:=t0/p^(v2 div 2); assert Trace(t0) eq 0;
 return eval_pQ0(p,v2,t0,u); end function;

function at_pQ0(f,L,p,W) if p eq 2 then return at_2Q0(f,L,p,W); end if;
 Kp:=pAdicField(p,W); F:=f*Parent(f).1; K<s>:=Parent(L[1][2]); Q:=Rationals();
 G:=iHintsEC(ChangeRing(EllipticCurve(F),Kp)); T:=[]; U:=[];
 t0:=K![Coefficient(f,1)/2,1]; assert Trace(t0) eq 0;
 v2:=Valuation(Norm(t0),p); t0:=t0/p^(v2 div 2);
 for g in G do u:=g[1]; v:=Valuation(u);
  if v gt W/3 then u:=Kp!Coefficient(f,0); v:=Valuation(u); end if;
  V:=[v mod 2,IsSquare(u/p^v) select 0 else 1]; u:=(Q!g[1])-s;
  V cat:=eval_pQ0(p,v2,t0,u); T cat:=[V]; end for;
 for l in L do v:=Valuation(l[1],p);
  V:=[v mod 2,IsSquare(GF(p)!(l[1]/p^v)) select 0 else 1]; u:=l[2];
  V cat:=eval_pQ0(p,v2,t0,u); U cat:=[V]; end for;
 N:=ChangeRing(Matrix(U),GF(2)); K:=Basis(Kernel(N));
 t1:=ChangeRing(Vector(T[1]),GF(2));
 U:=[s : t in [t1] | b where b,s:=IsConsistent(N,t)];
 return Matrix(Basis(Image(Matrix(K cat U)))); end function;

function at_pQ(f,L,p,W) r:=[r[1] : r in Roots(f,pAdicField(p,W))];
 if #r eq 0 then return at_pQ0(f,L,p,W); else return at_pQ2(f,L,p,W,r); end if;
 end function;

////////////////////////////////////////////////////////////////////////

function eseq(x)
 e:=Eltseq(x); e cat:=[0 : i in [#e..1]]; return e; end function;

function final_crtQ(L) if #L eq 0 then return L; end if;
 f:=MinimalPolynomial((Parent(L[1][2])).1); e,d:=Explode(Eltseq(f));
 Y:=PolynomialRing(Rationals()); y:=Y.1; Z<z>:=quo<Y|y*Y!f>;
 L:=[(a-c)/e*z^2+(d*(a-c)+b*e)/e*z+a
	  where a:=l[1] where c,b:=Explode(eseq(l[2])) : l in L];
 return L; end function;

/* ================================================================ */

function F2_algQ(S,M)
 if NumberOfColumns(M) eq 0 then return [Parent(S[1])|]; end if;
 Ln:=[]; for j in [1..NumberOfRows(M)] do x:=<1,1>;
          for u in [1..NumberOfColumns(M)] do
	   if M[j][u] ne 0 then x:=<x[1]*S[u][1],x[2]*S[u][2]>;
            end if; end for;
          Ln:=Ln cat [x]; end for; return Ln; end function;

function F2_algC(S,M)
 if NumberOfColumns(M) eq 0 then return [Parent(S[1])|]; end if;
 Ln:=[]; for j in [1..NumberOfRows(M)] do x:=1;
          for u in [1..NumberOfColumns(M)] do
           if M[j][u] ne 0 then x:=x*S[u]; end if; end for;
          Ln:=Ln cat [x]; end for; return Ln; end function;

/* ================================================================ */

function all_elim(L,ALL,ELIM) PRUNE:=[];
 vprintf TwoDescent,2: "Images\n%o\n",ALL;
 vprintf TwoDescent,2: "Eliminate\n%o\n",ELIM;
 for v in ELIM do
  PRUNE cat:=[Prune(Eltseq(Basis(Kernel(Matrix(ALL cat [v])))[1]))]; end for;
 vprintf TwoDescent,2: "Linear combos\n%o\n",PRUNE;
 E:=EchelonForm(Matrix(PRUNE)); vprintf TwoDescent,2: "Echelon\n%o\n",E;
 m:=[Min([i : i in [1..#Eltseq(e)] | Eltseq(e)[i] ne 0]) :
	  e in Rows(E) | not IsZero(e)];
 vprintf TwoDescent,2: "Throwing out these basis elements: %o\n",m;
 L:=[L[i] : i in [1..#L] | not i in m]; return L; end function;

function local_sol(L,P,f,at_oo,at_p,F2_alg,S,T)
 T:=at_oo(L,f)*T; L:=F2_alg(S,T); vprintf TwoDescent: "At oo: %o\n",#L;
 if #L eq 0 then return L,T; end if; D:=Discriminant(f*Parent(f).1);
 for p in P do b:=true; W:=4*Valuation(D,p)+25;
  while b do try U:=at_p(f,L,p,W); b:=false;
   catch ERROR W:=5+Ceiling(W*1.25); b:=true;
   vprintf TwoDescent: "Need more precision at %o\n",p; end try; end while;
  T:=U*T;
  if NumberOfRows(T) eq 0 then
   vprintf TwoDescent: "At %o: 0\n",p; return [Parent(L[1])|],T; end if;
  L:=F2_alg(S,T); vprintf TwoDescent: "At %o: %o\n",p,#L; end for;
 return L,T; end function;

function doF3(E,f,P,PTS) K<s>:=NumberField(f);
 S:=&join{{F[1] : F in Factorization(p*IntegerRing(K))} : p in P};
 vprintf TwoDescent: "Computing pSelmerGroup\n";
 // (TO DO: this is still too slow!) // SRD
 G,mm,mmraw,B,BP:=pSelmerGroup(2,S:Raw,Nice);
 vprintf TwoDescent: "Done computing pSelmerGroup -- computing maps\n";
 EV:=Matrix([G.i@mmraw: i in [1..Ngens(G)]]); // exponent vectors
 L:=NiceRepresentativesModuloPowers(EV,Eltseq(B),2:Primes:=BP);
 ChangeUniverse(~L,K);
 Lo:=L; vprintf TwoDescent: "H^1: %o\n",#L;
 N:=[Norm(l) : l in L];
 M:=Matrix([[GF(2)!((1-Sign(n))/2): n in N]] cat
           [[GF(2)!Valuation(n,p) : n in N] : p in P]);
 T:=Matrix(Basis(Kernel(Transpose(M)))); L:=F2_algC(Lo,T);
 vprintf TwoDescent: "Norm: %o\n",#L;
 L,T:=local_sol(L,P,f,at_ooC,at_pC,F2_algC,Lo,T);
 // T is an inclusion map from G (abstract) to pSelmerGroup
 // So Transpose(T) is a quo map from pSelmerGroup to G
 // C:=Codomain(mm); S,mS:=sub<C|[C!Eltseq(r) : r in Rows(T)]>;
 r:=RootNumber(E); if (-1)^#L ne r then L; E; assert false; end if;
 if #L eq 0 or #PTS eq 0 then return L; end if; K:=Parent(L[1]);
 vprintf TwoDescent: "Eliminating 2-torsion (if asked) and given generators\n";
 ALL:=[Eltseq(mm(l)) : l in L]; ELIM:=[Eltseq(mm(pt[1]-K.1)) : pt in PTS];
 // Q,mQ:=quo<S|[C!e : e in ELIM]>;
 // this needs to be seriously Magma-fied...
 // map should be mQ(mm(x)@@mS) mapping x to Q
 // and Q should be thing that is kept around, not the all_elim version
 return all_elim(L,ALL,ELIM); end function;

function myval(e,P) e:=Rationals()!e;
 return [GF(2)!Valuation(e,p) : p in P] cat [e gt 0 select 0 else 1];
end function;

function ck2(U,s,f) if U[1] ne 0 then return U; end if;
 return <Evaluate(Derivative(f),0),U[2]>; end function;

function doF2(E,f,P,PTS) K<s>:=NumberField(f);
 S:=&join{{f[1] : f in Factorization(p*IntegerRing(K))} : p in P};
 vprintf TwoDescent: "Computing pSelmerGroup\n"; //SRD
 G,mm,mmraw,B,BP:=pSelmerGroup(2,S:Raw,Nice);
 vprintf TwoDescent: "Done computing pSelmerGroup -- computing maps\n";
 EV:=Matrix([G.i@mmraw: i in [1..Ngens(G)]]); // exponent vectors
 L:=NiceRepresentativesModuloPowers(EV,Eltseq(B),2:Primes:=BP);
 L:=[<1,K!l> : l in L] cat [<p,K!1> : p in P] cat [<-1,K!1>];
 Lo:=L; vprintf TwoDescent: "H^1: %o\n",#L;
 N:=[l[1]*Norm(l[2]) : l in L];
 M:=Matrix([[GF(2)!((1-Sign(n))/2): n in N]] cat
           [[GF(2)!Valuation(n,p) : n in N] : p in P]);
 T:=Matrix(Basis(Kernel(Transpose(M)))); L:=F2_algQ(Lo,T);
 vprintf TwoDescent: "Norm: %o\n",#L;
 L,T:=local_sol(L,P,f,at_ooQ,at_pQ,F2_algQ,Lo,T);
 r:=RootNumber(E); if (-1)^#L ne -r then L; E; assert false; end if;
 if #L eq 0 or #PTS eq 0 then BLAH:=final_crtQ(L); return BLAH; end if;
 E2:=EllipticCurve(f*Parent(f).1); b,i:=IsIsomorphic(E,E2); assert b;
 vprintf TwoDescent,2: "Using model %o\n",E2;
 PTS:=[i(p) : p in PTS]; vprintf TwoDescent,2: "Mod-out images %o\n",PTS;
 vprintf TwoDescent: "Eliminating 2-torsion (if asked) and given generators\n";
 ALL:=[Eltseq(mm(l[2])) cat myval(l[1],P) : l in L];
 ELIM:=[Eltseq(mm(pt[1]-K.1)) cat
	      (pt[1] ne 0 select myval(pt[1],P) else myval(Evaluate(f,0),P))
	       : pt in PTS];
 // same as above, with input from user, want to decompose into quad+linear
 // use mm on quad and the above myval() on the linear part
 // final_crtQ is only for reps in algebra rather than <f,g> form
 return final_crtQ(all_elim(L,ALL,ELIM)); end function;

function crtit(a,b,A,B) c:=Coefficient(A,0); d:=Coefficient(B,0);
 return (-(b-a)/(d-c))*A+a; end function;

function ck1(U,s,f,m)
  return <U[i] eq 0 select Evaluate(Derivative(f),m(s)[i]) else U[i] :
	     i in [1..3]>; end function;

function final_crtL(L,R,s) x:=PolynomialRing(Rationals()).1;
 return
  final_crtQ([<l[1],Evaluate(crtit(l[2],l[3],x-R[2],x-R[3]),s)> : l in L]);
end function;

function doF1(E,f,P,PTS) A:=P cat [-1];
 FAC:=Factorization(f); F2:=FAC[2][1]; F3:=FAC[3][1];
 F2:=Evaluate(F2,Parent(f).1-Coefficient(FAC[1][1],0));
 F3:=Evaluate(F3,Parent(f).1-Coefficient(FAC[1][1],0)); F:=F2*F3;
 Q:=PolynomialRing(Rationals()); K<s>:=quo<Q|F>;
 L:=[<p,K!1> : p in A] cat [<1,Evaluate(crtit(1,p,F2,F3),s)> : p in A];
 L cat:=[<1,Evaluate(crtit(p,1,F2,F3),s)> : p in A];
 N:=[l[1]*Norm(l[2]) : l in L]; vprintf TwoDescent: "H^1: %o\n",#L;
 M:=Matrix([[GF(2)!((1-Sign(n))/2): n in N]] cat
           [[GF(2)!Valuation(n,p) : n in N] : p in P]);
 T:=Matrix(Basis(Kernel(Transpose(M)))); Lo:=L; L:=F2_algQ(Lo,T);
 vprintf TwoDescent: "Norm: %o\n",#L;
 L,T:=local_sol(L,P,F,at_ooQ,at_pQ,F2_algQ,Lo,T);
 r:=RootNumber(E); if (-1)^#L ne r then L; E; assert false; end if;
 if #L eq 0 or #PTS eq 0 then return final_crtQ(L); end if;
 r2:=-Coefficient(F2,0); r3:=-Coefficient(F3,0); Q:=Rationals(); R:=[0,r2,r3];
 L:=[<l[1],Q!Evaluate(Polynomial(Eltseq(l[2])),r2),
       Q!Evaluate(Polynomial(Eltseq(l[2])),r3)> : l in L];
 vprintf TwoDescent: "Eliminating 2-torsion (if asked) and given generators\n";
 f:=Parent(f).1*F2*F3; E2:=EllipticCurve(f); b,i:=IsIsomorphic(E,E2); assert b;
 vprintf TwoDescent,2: "Using model %o\n",E2;
 PTS:=[i(p) : p in PTS]; vprintf TwoDescent,2: "Mod-out images %o\n",PTS;
 ALL:=[&cat[l[i] ne 0 select myval(l[i],P)
                      else myval(Evaluate(Derivative(f),R[i]),P) :
	    i in [1..3]] : l in L];
 ELIM:=[&cat[pt[1] ne R[i] select myval(pt[1]-R[i],P)
                           else myval(Evaluate(Derivative(f),R[i]),P) :
	     i in [1..3]] : pt in PTS];
 // same as above, with input from user, want to decompose into lin+lin+lin
 // use the above myval() on the linear parts
 // final_crtL is only for reps in algebra rather than <f,g.h> form
 return final_crtL(all_elim(L,ALL,ELIM),R,s); end function;

function itwo_desc(E,T2p)
 A:=aInvariants(E); f:=Polynomial([A[5],A[4],A[2],1]); FAC:=Factorization(f);
 P:=[p : p in BadPrimes(E) | p ne 2 and IsEven(TamagawaNumber(E,p))] cat [2];
 // Note: using the Tamagawa test saved a few percent when I tried it.
 // Tamagawa itself took negligible time.  SRD, April 2012.
 if #FAC eq 1 then RET:=doF3(E,f,P,T2p); end if;
 if #FAC eq 2 then g:=Evaluate(FAC[2][1],Parent(f).1-Coefficient(FAC[1][1],0));
  RET:=doF2(E,g,P,T2p); end if;
 if #FAC eq 3 then RET:=doF1(E,f,P,T2p); end if;
 if #RET eq 0 then RET:=[quo<Parent(f)|f>|]; end if; return RET; end function;

function two_desc(E,rt,rg)
 if assigned E`TwoSelmerGroup and not rt and IsEmpty(rg) then
  return E`TwoSelmerGroup`two_desc; end if;
 M:=CubicModel(MinimalModel(E)); b,m:=IsIsomorphic(E,M); assert b;
 vprintf TwoDescent,2: "Using model %o\n",M;
 if (rt eq true) then T2,T2m:=TorsionSubgroup(M);
  T2p:={T2m(x) : x in Generators(T2)}; else T2p:={}; end if;
 T2p join:={m(g) : g in rg}; T2p:=[x : x in T2p | x ne M!0];
 if #T2p ne 0 then vprintf TwoDescent,2: "Mod-out images %o\n",T2p; end if;
 L:=itwo_desc(M,T2p); 
 if not rt and IsEmpty(rg) then
  E`TwoSelmerGroup := rec<two_selmer_rec|two_desc:=L>; end if;
 return L; end function;

import "twodesc_nf.m" : parametrization, minimise_and_reduce;

function KtoC(e) K:=Rationals(); A:=Parent(e);
 // Write down arbitrary square using appropriate basis (03-10, SRD)
 // (seems always worthwhile for the time saved in minimization).
 // TO DO:
 // For very large discriminants, factorization could be a problem
 // if e is a product of several elements and if large primes came
 // into those elements during the NiceReps process; in that case,
 // the best thing would be to recompute NiceReps for e directly.

 if ISA(Type(A), FldAlg) then 
  ZA:=Integers(A); 
  f:=Factorization(e*ZA);
  I:=&*[PowerIdeal(ZA)| t[1]^(t[2] div 2) : t in f | t[2] div 2 ne 0];
  bas:=Basis(I^-1); 
 else 
     // bas:=[A|A.1^2,A.1,1]; 

     // finally implemented this case properly, Oct 2012, SRD

     AA, mAA := AbsoluteAlgebra(A);
     ee := e @ mAA;
     AA0 := AA ! < AA[i]!0 : i in [1..NumberOfComponents(AA)] >;

     bas := [A|];

     for i := 1 to NumberOfComponents(AA) do
         F := AA[i];
         ZF := Integers(F);
         I := &* [ PowerIdeal(FieldOfFractions(ZF))
                 | t[1]^(t[2] div 2) 
                 : t in Factorization(ee[i]*ZF)
                 | t[2] div 2 ne 0 ];
         for b in Basis(I^-1) do
             bb := AA0;
             bb[i] := b;
             Append(~bas, bb @@ mAA);
         end for;
     end for;

 end if;

 P1:=PolynomialRing(A,4); h:=hom<A->P1 | P1.4>;
 u:=P1.1; v:=P1.2; w:=P1.3; h2:=hom<P1->P1 | h,u,v,w,P1.4>;
 sqN:=(u*bas[1]+v*bas[2]+w*bas[3])^2; thQ:=e*sqN; h2thQ:=h2(thQ);
 q1:=Coefficient(h2thQ,P1.4,1); q2:=Coefficient(h2thQ,P1.4,2);
 vprintf TwoDescent,2 : "Parameterisation is %o=0, %o=-z^2\n",q2,q1;
 Q3:=PolynomialRing(K,3); PS:=ProjectivePlane(K);
 h3:=hom<P1->Q3 | Q3.1,Q3.2,Q3.3,1>; c:=Conic(PS,h3(q2));
 uu:=parametrization(c); Q:=-Evaluate(h3(q1),uu);
 vprintf TwoDescent,2: "pre-reduction param %o\n",Q;
 Q:=minimise_and_reduce(Q); return HyperellipticCurve(Q); end function;

intrinsic TwoDescent
(E::CrvEll[FldRat] : WithMaps:=true,RemoveTorsion:=false,RemoveGens:={})
 -> SeqEnum[CrvHyp], SeqEnum[Map]
{Two-descent function for elliptic curves over Q}
 if #RemoveGens ne 0 then require Curve(Random(RemoveGens)) eq E:
  "Generators must be on curve"; end if;
 L:=two_desc(E,RemoveTorsion,RemoveGens);
 if #L eq 0 then if WithMaps then return [],[]; else return []; end if; end if;
 S:=[]; C:=CartesianProduct([GF(2) : i in [1..#L]]);
 vprintf TwoDescent: "Computing hyperelliptic models\n";
 for c in C do cc:=[Integers()!s : s in c];
  if &and[s eq 0 : s in cc] then continue; end if;
  Append(~S,&*[L[i]^cc[i] : i in [1..#L]]); end for;
 A:=[KtoC(s): s in S]; 
 if WithMaps then
  M:=[m where _,m:=AssociatedEllipticCurve(a) : a in A]; // slow with E vararg 
  M:=[Expand(m*i) where _,i:=IsIsomorphic(Codomain(m),E) : m in M];
  return A,M; else return A; end if; end intrinsic;

intrinsic TwoSelmerGroup
  (E::CrvEll[FldRat] : Bound:=-1,Fields:=false,Hints:={},Raw:=false,
                       RemoveTorsion:=false, RemoveGens:={}) -> GrpAb, Map

{The 2-Selmer group of the elliptic curve E over Q.
(Note: if old optional arguments are given, old code is called)}

 // cache
 if IsEmpty(RemoveGens) then
    if RemoveTorsion then
       bool, rec := HasAttribute(E, "TwoSelmerGroupRemoveTorsion");
       if bool and assigned rec`group then
          return rec`group, rec`map;
       end if;
    else // not RemoveTorsion
       bool, rec := HasAttribute(E, "TwoSelmerGroup");
       if bool and assigned rec`group then
          return rec`group, rec`map;
       end if;
    end if;
 end if;

 if not IsEmpty(RemoveGens) then
    require IsIdentical(Curve(Universe(RemoveGens)), E) :
            "RemoveGens must contain points of the first argument";
 end if;

 // acknowledge obselete options by using the slowest available method
 if Bound ne -1 or Fields or #Hints ne 0 or Raw then
    Q:=NumberField(Polynomial([0,1]):DoLinearExtension);
    return TwoSelmerGroup
           (BaseChange(E,Q):Bound:=Bound,Fields:=Fields,Hints:=Hints,Raw:=Raw);
 end if;

 // main
 L:=two_desc(E,RemoveTorsion,RemoveGens);
 G:=AbelianGroup([2 : i in [1..#L]]); U:=Universe(L);
 if Type(U) eq FldNum then
  f:=DefiningPolynomial(U); else f:=Modulus(U); end if;
 A<theta>:=quo<Parent(f)|f>;
 if #L eq 0 then Gmap:=map<A->G|x:->1,g:->1>;
 else retval:=func<g| A!Eltseq(&*[L[i]^Eltseq(g)[i] : i in [1..#L]])>;
      Gmap:=map<A->G|x:->x,g:->retval(g)>; end if;
 // x->x : forward map is garbage
 // could use mm map from pSelmerGroup, but that's in something larger than G

 // cache
 if IsEmpty(RemoveGens) then
    if RemoveTorsion then
       E`TwoSelmerGroupRemoveTorsion :=
          rec<two_selmer_rec|group:=G,map:=Gmap,two_desc:=L>;
    else
       E`TwoSelmerGroup :=
          rec<two_selmer_rec|group:=G,map:=Gmap,two_desc:=L>;
    end if;
 end if;

 return G,Gmap;
 
end intrinsic;

intrinsic TwoCover(theta::RngUPolResElt:E:=0) -> CrvHyp, Map
{ Returns a hyperelliptic degree 4 curve associated to an element in a
    cubic Univariate Quotient Polynomial Algebra over Q (see TwoSelmerGroup)}
 require Degree(Modulus(Parent(theta))) eq 3:
 "Univariate quotient polynomial algebra must be cubic";
 require BaseField(Parent(theta)) cmpeq Rationals():
 "Base Field of algebra must be the rationals";
 require Norm(theta) ne 0: "Element must have non-zero norm";
 require IsSquare(Norm(theta)): "Theta must have square norm";
 require IsSquarefree(Modulus(Parent(theta))): "Modulus must be squarefree";
 if E cmpeq 0 then E:=EllipticCurve(Modulus(Parent(theta))); end if;
 H:=KtoC(theta); _,m:=AssociatedEllipticCurve(H:E:=E);
 return H,m; end intrinsic;

intrinsic TwoCover(theta::FldNumElt:E:=0) -> CrvHyp, Map
{ Returns a degree 4 hyperelliptic curve associated to an element
  in a cubic number field (see TwoSelmerGroup)}
 require Degree(Parent(theta)) eq 3: "Number field must be cubic";
 Q:=quo<PolynomialRing(Rationals())|DefiningPolynomial(Parent(theta))>;
 return TwoCover(Q!Eltseq(theta):E:=E); end intrinsic;

intrinsic TwoCover(P::PtEll) -> CrvHyp
{ Given a point on an elliptic curve, return a 2-cover corresponding to it }
 if IsZero(P) then return HyperellipticCurve(Curve(P)); end if;
 x:=P[1]; y:=P[2]; I:=cInvariants(Curve(P))[1];
 return HyperellipticCurve([1,0,-x/6,y/27,I/12-x^2/432]); end intrinsic;
