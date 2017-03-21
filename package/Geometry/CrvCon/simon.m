freeze;

import "bosma.m" : class2part,trivform,addit;
declare verbose IsotropicSubspace,3;

ZZ:=Integers(); QQ:=Rationals();

function qfsig(M) D:=Diagonalization(ChangeRing(M,Rationals())); r:=0; s:=0;
 for i in [1..Degree(Parent(D))] do
  if D[i][i] gt 0 then r:=r+1; else s:=s+1; end if; end for;
 return r,s; end function;

function Div(M,p) n:=Degree(Parent(M));
 return MatrixAlgebra(ZZ,n)!((MatrixAlgebra(Rationals(),n)!M)/p); end function;

function ExtendToUnimodular(cc)
 vv:=[[Integers()!x : x in Eltseq(w)] : w in cc];
 v,_,u:=SmithForm(Matrix(vv)); u:=u^(-1); return u; end function;

function FpIsotropic(M) n:=Degree(Parent(M)); R:=BaseRing(M);
 if n eq 1 then return M,DiagonalMatrix([1]); end if;
 if n eq 2 then b,r:=IsSquare(-Determinant(M));
  if b then s:=[ZZ!-M[1][2]+ZZ!r,ZZ!M[1][1]]; c:=Gcd(s);
   if c eq 0 then U:=MatrixAlgebra(ZZ,2)!1; 
   else s:=[ZZ!(z/c) : z in s]; U:=ExtendToUnimodular([s]); end if;
   M:=U*M*Transpose(U); return M,U; end if;
  return M,DiagonalMatrix([1,1]); end if;
 L := PolynomialRing(R); x := L.1; MA:=MatrixAlgebra(L,n);
 while true do t:=[L!Random(R) : i in [1..n]]; w:=Random([1..n]); t[w]:=x;
  Q:=InnerProduct(Vector(t)*(MA!MatrixAlgebra(R,n)!M),Vector(t));
  if Q eq 0 then t[w]:=1; elif IsCoercible(R,Q) then continue;
  else ROO:=Roots(Q); if #ROO eq 0 then continue; end if;
   t[w]:=ROO[1][1]; end if;
  if Norm(ChangeRing(Vector(t),ZZ)) eq 0 then continue; end if;
  U:=ExtendToUnimodular([t]); M:=U*M*Transpose(U); break; end while;
 w:=-1; for i in [2..n] do if M[1,i] ne 0 then w:=i; break; end if; end for;
 SwapColumns(~M,2,w); SwapRows(~M,2,w); SwapRows(~U,2,w);
 for i in [3..n] do q:=-M[1,i]/M[1,2];
  AddRow(~M,q,2,i); AddColumn(~M,q,2,i); AddRow(~U,q,2,i); end for;
 _,V:=FpIsotropic(Submatrix(M,3,3,n-2,n-2));
 V:=DiagonalJoin(DiagonalMatrix([1,1]),V);
 return V*M*Transpose(V),V*U; end function;

function FpIso(M) n:=Degree(Parent(M)); M,T:=FpIsotropic(M);
 for i:= 3 to n by 2 do if M[i][i] eq 0 then j:=(i+1) div 2;
  SwapColumns(~M,i,j); SwapRows(~M,i,j); SwapRows(~T,i,j); end if; end for;
 return M,T; end function; // needs Determinant to be nonzero mod p

function min1(M,p,v,n)
 while true do Mp:=MatrixAlgebra(GF(p),n)!M; d:=Dimension(Kernel(Mp));
  if d eq n then M:=Div(M,p); v:=v-n; else break; end if;
  vprintf IsotropicSubspace,3: "min1 p:%o v:%o\n",p,v; end while;
 return M,v; end function;

function min2(M,p,v,n,T) W:=MatrixAlgebra(ZZ,n);
 while true do Mp:=MatrixAlgebra(GF(p),n)!M; K:=Kernel(Mp); d:=Dimension(K);
  if d lt v then U:=ExtendToUnimodular(Basis(K));
   M:=U*M*Transpose(U); T:=U*T; N:=Div(Submatrix(M,1,1,d,d),p);
   Np:=MatrixAlgebra(GF(p),d)!N; K:=Kernel(Np); e:=Dimension(K);
   U:=ExtendToUnimodular(Basis(K));
   U:=DiagonalJoin(U,MatrixAlgebra(ZZ,n-d)!1); M:=U*M*Transpose(U); T:=U*T;
   U:=DiagonalMatrix([1/p :  i in [1..e]] cat [1 : i in [1..n-e]]);
   M:=W!(U*M*U); T:=U*T; v:=v-2*e; else break; end if;
  vprintf IsotropicSubspace,3: "min2 p:%o v:%o\n",p,v; end while;
 Mp:=MatrixAlgebra(GF(p),n)!M; K:=Kernel(Mp); d:=Dimension(K);
 if d ne 0 then U:=ExtendToUnimodular(Basis(K));
  M:=U*M*Transpose(U); T:=U*T; end if; return M,T,v,d; end function;

function min3(M,p,v,n,d,T)
 vprintf IsotropicSubspace,3: "min3 p:%o v:%o d:%o\n",p,v,d;
 U:=DiagonalMatrix([1 :  i in [1..d]] cat [p : i in [1..n-d]]);
 M:=Div(U*M*U,p); v:=v+n-2*d; d:=n-d; return M,U*T,v,d; end function;

function min4(M,p,v,n,d,T) N:=Div(Submatrix(M,1,1,d,d),p);
 L := PolynomialRing(GF(p)); x := L.1;
 MA:=MatrixAlgebra(L,d); W:=MatrixAlgebra(ZZ,n);
 vprintf IsotropicSubspace,3: "min4 p:%o v:%o d:%o\n",p,v,d;
 while true do
  t:=[L!Random(GF(p)) : i in [1..d]]; w:=Random([1..d]); t[w]:=x;
  Q:=InnerProduct(Vector(t)*(MA!MatrixAlgebra(GF(p),d)!N),Vector(t));
  if Q eq 0 then t[w]:=1; elif IsCoercible(GF(p),Q) then continue;
  else ROO:=Roots(Q); if #ROO eq 0 then continue; end if;
   t[w]:=ROO[1][1]; end if;
  if Norm(ChangeRing(Vector(t),ZZ)) eq 0 then continue; end if;
  U:=ExtendToUnimodular([t]); U:=DiagonalJoin(U,MatrixAlgebra(ZZ,n-d)!1);
  M:=U*M*Transpose(U); T:=U*T;
  U:=DiagonalMatrix([1/p] cat [1 : i in [1..n-1]]);
  M:=W!(U*M*U); T:=U*T; v:=v-2; break; end while;
 return M,T,v; end function;

function min5(M,p,n,T)
 N:=Div(Submatrix(M,1,1,2,2),p); W:=MatrixAlgebra(ZZ,n);
 if N[1][1] mod p eq 0 then U:=DiagonalMatrix([1/p] cat [1 : i in [1..n-1]]);
  M:=W!(U*M*U); T:=U*T; return M,T,0; end if;
 b,r:=IsSquare(GF(p)!-Determinant(N)); v:=2;
 if b then s:=[ZZ!-N[1][2]+ZZ!r,ZZ!N[1][1]]; c:=Gcd(s);
  vprintf IsotropicSubspace,3: "min5 p:%o\n",p; v:=0;
  if c eq 0 then U:=MatrixAlgebra(ZZ,2)!1;
  else s:=[ZZ!(z/c) : z in s]; U:=ExtendToUnimodular([s]); end if;
  U:=DiagonalJoin(U,MatrixAlgebra(ZZ,n-2)!1); M:=U*M*Transpose(U); T:=U*T;
  U:=DiagonalMatrix([1/p] cat [1 : i in [1..n-1]]);
  M:=W!(U*M*U); T:=U*T; end if; return M,T,v; end function;

function min6(M,p,v,n,d,T)
 B:=ChangeRing(Submatrix(M,d+1,d+1,n-d,n-d),GF(p)); b:=Degree(Parent(B));
 if IsOdd(b) then m:=(b-1) div 2;
 elif IsSquare((-1)^(b div 2)*Determinant(B)) then m:=b div 2;
 else m:=(b div 2)-1; end if;
 if (IsOdd(n) and d eq v and d eq 1 and 2*m eq n-d) or
   (IsEven(n) and d eq v and d eq 2 and 2*m eq n-d) then _,U:=FpIso(B);
  vprintf IsotropicSubspace,3: "min6 p:%o v:%o d:%o\n",p,v,d;
  U:=DiagonalJoin(MatrixAlgebra(ZZ,d)!1,U); M:=U*M*Transpose(U); T:=U*T;
  U:=DiagonalMatrix([1 : i in [1..d+m]] cat [p : i in [1..n-d-m]]);
  M:=Div(U*M*U,p); T:=U*T; v:=0; end if; return M,T,v; end function;

function straighten(M,p,n)
 Mp:=MatrixAlgebra(GF(p),n)!M; K:=Kernel(Mp); d:=Dimension(K);
 if d ne 0 then vprintf IsotropicSubspace,3: "straighten p:%o\n",p;
  return d,ExtendToUnimodular(Basis(K)); end if;
 return d,MatrixAlgebra(QQ,n)!1; end function;

function minimization(M)
 vprint IsotropicSubspace,1: "Doing minimization in IsotropicSubspace";
 D:=Determinant(M); vprintf IsotropicSubspace,2: "Determinant is %o\n",D;
 FAC:=Factorization(D); n:=Degree(Parent(M));
 W:=MatrixAlgebra(ZZ,n); T:=MatrixAlgebra(QQ,n)!1;
 for f in FAC do p:=f[1]; v:=f[2];
  vprintf IsotropicSubspace,2: "Minimizing at %o\n",p;
  M,v:=min1(M,p,v,n); M,T,v,d:=min2(M,p,v,n,T);
  if IsOdd(n) and d eq v and IsEven(d) and d ge 2 then
   M,T,v,d:=min3(M,p,v,n,d,T); end if;
  d,U:=straighten(M,p,n); M:=U*M*Transpose(U); T:=U*T;
  while d eq v and d ge 3 do M,T,v:=min4(M,p,v,n,d,T);
   d,U:=straighten(M,p,n); M:=U*M*Transpose(U); T:=U*T; end while;
  if d eq v and d eq 2 then M,T,v:=min5(M,p,n,T); end if;
  d,U:=straighten(M,p,n); M:=U*M*Transpose(U); T:=U*T;
  if d ne 0 then M,T:=min6(M,p,v,n,d,T); end if;
  M,U:=LLLGram(W!M : Isotropic:=true, Delta:=0.999); T:=U*T; end for;
 if #FAC eq 0 then M,U:=LLLGram(W!M : Isotropic, Delta:=0.999); T:=U*T; end if;
 return M,T,FAC; end function;

function clean(v) v:=[QQ!x : x in Eltseq(v)];
 m:=LCM([Denominator(e) : e in v]);
 v:=[m*e : e in v]; g:=GCD([Numerator(e) : e in v]);
 return Vector([ZZ!(e/g) : e in v]); end function;

function wi(M,p) // change from {-1,1} to GF(2)
 return WittInvariant(M,p) eq -1 select GF(2)!1 else GF(2)!0; end function;

function final_clean(A,T) n:=Degree(Parent(A));
 vprintf IsotropicSubspace,1: "Extracting solutions in IsotropicSubspace\n";
 O:=[i : i in [1..n] | A[i][i] eq 1]; Z:=[i : i in [1..n] | A[i][i] eq 0];
 N:=[i : i in [1..n] | A[i][i] eq -1]; R:=[];
 while #O ne 0 and #N ne 0 do
  R cat:=[clean(T[O[1]]+T[N[1]])]; Remove(~N,1); Remove(~O,1); end while;
 while #Z ne 0 do v:=Z[1];
  _,w:=Max([Abs(x) : x in Eltseq(A[v])]); Remove(~Z,1);
  for j in [1..#Z] do if Z[j] eq w then Remove(~Z,j); break; end if; end for;
  V:=clean(T[v]); W:=clean(T[w]);
  if Norm(V) lt Norm(W) then R cat:=[V]; else R cat:=[W]; end if; end while;
 return R; end function;

function doit4(M,FAC,D,T) b:=[]; n:=Degree(Parent(M));
 vprintf IsotropicSubspace,1: "Case of dimension 4 in IsotropicSubspace\n";
 for i in [1..n] do
  if M[i][i] eq 0 then w:=clean(T[i]);
   if b cmpeq [] then b:=w;
   else if Norm(w) lt Norm(b) then b:=w; end if; end if; end if; end for;
 if b cmpne [] then return [b]; end if;
 for f in FAC do if Valuation(D,f[1]) eq 2 then
  vprintf IsotropicSubspace,2: "No %o-adic solution\n",f[1];
  return []; end if; end for;
 FAC:=FAC*Factorization(4); DIAG:=Diagonalization(M);
 W:=Vector([wi(DIAG,f[1]) : f in FAC]); d:=4*D;
 if D mod 8 eq 1 and W[1] eq 0 then // witt at 2 is +1, so 0 encoded
  vprint IsotropicSubspace,2: "No 2-adic solution"; return []; end if;
 H:=[HilbertSymbol(-1,-4*D,f[1]) : f in FAC];
 H:=Vector([x lt 0 select GF(2)!1 else GF(2)!0 : x in H]);
 I:=[HilbertSymbol(2,-4*D,f[1]) : f in FAC];
 I:=Vector([x lt 0 select GF(2)!1 else GF(2)!0 : x in I]);
 gens:=class2part(d,FAC); if gens eq [] then gens:=[trivform(d)]; end if;
 G:=[Matrix([[u[1],u[2] div 2],[u[2] div 2,u[3]]]) : u in gens];
 DIAG:=[Diagonalization(g) : g in G];
 U:=Matrix([[wi(x,f[1]) : f in FAC] : x in DIAG]); b,s:=IsConsistent(U,W+H);
 if b then f:=addit(s,gens); 
  vprintf IsotropicSubspace,2: "Case 1: IsotropicSubspace form is %o\n",f;
  Q2:=-Matrix([[f[1],f[2] div 2],[f[2] div 2,f[3]]]);
 else b,s:=IsConsistent(U,W+H+I); assert b; f:=addit(s,gens);
  vprintf IsotropicSubspace,2: "Case 2: IsotropicSubspace form is %o\n",f;
  if IsEven(f[1]) then
   Q2:=-Matrix([[f[1] div 2,f[2] div 2],[f[2] div 2,2*f[3]]]);
  elif IsEven(f[3]) then
   Q2:=-Matrix([[f[3] div 2,-f[2] div 2],[-f[2] div 2,2*f[1]]]);
  else a:=f[1]+f[2]+f[3]; b:=f[2]+2*f[3]; c:=f[3];
   Q2:=-Matrix([[a div 2,b div 2],[b div 2,2*c]]); end if; end if;
 vprint IsotropicSubspace,2: "Joining binary form to given form";
 Q6:=DiagonalJoin(M,Q2); N,U:=minimization(Q6);
 F:=Matrix(final_clean(N,U*DiagonalJoin(T,MatrixAlgebra(QQ,2)!1)));
 vprint IsotropicSubspace,2: "Intersecting with desired subspace";
 E:=Basis(Kernel(Submatrix(F,1,5,3,2))*F);
 return [clean(Vector([x[i] : i in [1..4]])) : x in E]; end function;

function doitodd(M,T,s) b:=[]; n:=Degree(Parent(M));
 vprintf IsotropicSubspace: "Case of odd dim %o in IsotropicSubspace\n",n;
 M,U:=minimization(M); T:=U*T; D:=Determinant(M); FAC:=Factorization(D);
 vprintf IsotropicSubspace,2: "Determinant is %o\n",D;
 H:=[-HilbertSymbol((2*(-1)^(((n-1) div 2)+s)),f[1],f[1]) : f in FAC];
 FAC:=FAC*Factorization(8);
 H:=Vector([x lt 0 select GF(2)!1 else GF(2)!0 : x in H]); d:=-8*Abs(D);
 gens:=class2part(d,FAC); if gens eq [] then gens:=[trivform(d)]; end if;
 G:=[Matrix([[u[1],u[2] div 2],[u[2] div 2,u[3]]]) : u in gens];
 DIAG:=[Diagonalization(g) : g in G];
 U:=Matrix([[wi(x,f[1]) : f in FAC | f[1] ne 2] : x in DIAG]);
 b,sol:=IsConsistent(U,H); assert b; f:=addit(sol,gens);
 vprintf IsotropicSubspace,2: "IsotropicSubspace form is %o\n",f;
 Q2:=-Matrix([[f[1],f[2] div 2],[f[2] div 2,f[3]]]);
 vprint IsotropicSubspace,2: "Joining binary form to given form";
 M:=DiagonalJoin(M,Q2); T:=DiagonalJoin(T,MatrixAlgebra(QQ,2)!1);
 vprint IsotropicSubspace,2: "Minimizing joined form";
 for f in FAC do if f[1] eq 2 then continue; end if;
  d,U:=straighten(M,f[1],n+2); M:=U*M*Transpose(U);
  M,T,v:=min5(M,f[1],n+2,U*T); d,U:=straighten(M,f[1],n+2);
  M:=U*M*Transpose(U); T:=U*T; end for;
 d,U:=straighten(M,2,n+2); M:=U*M*Transpose(U);
 M,T:=min6(M,2,Valuation(Determinant(M),2),n+2,d,U*T);
 m:=Max([Ilog(10,1+Abs(x)) : x in Eltseq(M)]);
 vprintf IsotropicSubspace,2: "About to LLL, entries of %o digits\n",m;
 M,U:=LLLGram(M : Isotropic:=true,Delta:=0.999);
 assert IsDiagonal(M) and Abs(Determinant(M)) eq 1;
 F:=Matrix(final_clean(M,U*T));
 vprint IsotropicSubspace,2: "IsotropicSubspace: Subspace intersection";
 E:=Basis(Kernel(Submatrix(F,1,n+1,NumberOfRows(F),2))*F);
 return [clean(Vector([x[i] : i in [1..n]])) : x in E]; end function;

function vec(i,n)
  v:=Vector([0 : i in [1..n]]); v[i]:=1; return v; end function;

function doit(M) D:=Determinant(M); n:=Degree(Parent(M));
 if n eq 3 and D ne 0 then vprint IsotropicSubspace: "Dim 3: using conic code";
  b,P:=HasPoint(Conic(M)); if not b then return []; end if;
  return [Vector(Eltseq(P))]; end if;
 if D eq 0 then K:=Kernel(M); T:=ExtendToUnimodular(Basis(K));
  M:=T*M*Transpose(T); r:=Rank(M); N:=Submatrix(M,n-r+1,n-r+1,r,r);
  S:=[Vector([0 : i in [1..n-r]] cat Eltseq(x)) : x in doit(N)];
  S cat:=[vec(i,n) : i in [1..n-r]]; return [s*T : s in S]; end if;
 r,s:=qfsig(M);
 if r eq 0 or s eq 0 then vprintf IsotropicSubspace,1:
  "No Real Solution in IsotropicSubspace\n"; return []; end if;
 if r lt s then M:=-M; r:=s; s:=n-r; end if;
 vprintf IsotropicSubspace,2: "IsotropicSubspace: Signature is %o %o\n",r,s;
 if n eq 2 and not IsSquare(-D) then vprintf IsotropicSubspace,2:
 "IsotropicSubspace: Non-square determinant in dim 2\n"; return []; end if;
 M,T,FAC:=minimization(M); D:=Determinant(M);
 vprintf IsotropicSubspace,2 : "Minimization has det %o factored as %o\n",D,
   [<p[1],Valuation(D,p[1])> : p in FAC | Valuation(D,p[1]) ne 0];
 F:=Factorization(1); for f in FAC do v:=Valuation(D,f[1]);
  if v ne 0 then F*:=Factorization(f[1]^v); end if; end for;
 if n eq 4 and IsSquare(Abs(D)) then
  if Abs(D) ne 1 then
   vprintf IsotropicSubspace: "Dim 4 not ELS : Det=%o\n",D; return []; end if;
  vprint IsotropicSubspace,1: "IsotropicSubspace: Dim 4 unimodular case";
  return final_clean(M,T); end if;
 if n eq 4 then return doit4(M,F,D,T); end if;
 if Abs(D) eq 1 then
  vprintf IsotropicSubspace,2: "IsotropicSubspace: unimodular minimization\n";
  vprintf IsotropicSubspace,1: "Expected IsotropicSubspace size is %o\n",s;
  return final_clean(M,T); end if;
 if IsOdd(n) then
  vprintf IsotropicSubspace,1: "IsotropicSubspace size is %o\n",Min(r,s-2)+2;
  return doitodd(M,T,s); end if;
 vprintf IsotropicSubspace,1: "IsotropicSubspace: even dimension case\n";
 M:=DiagonalJoin(M,Matrix([[-1]])); T:=DiagonalJoin(T,Matrix([[QQ!-1]]));
 vprintf IsotropicSubspace,1: "Taking direct sum with [-1]\n";
 for f in F do d,U:=straighten(M,f[1],n+1); M:=U*M*Transpose(U);
  M,T:=min6(M,f[1],f[2],n+1,d,U*T); end for;
 D:=Determinant(M); FF:=Factorization(1);
 if r eq s then M:=-M; r:=s; s:=n+1-r;
  vprintf IsotropicSubspace,1: "IsotropicSubspace size is at least %o\n",r-2;
 elif r eq s+2 then
  vprintf IsotropicSubspace,1: "IsotropicSubspace size is at least %o\n",s-1;
 else vprintf IsotropicSubspace,1: "IsotropicSubspace size is %o\n",s; end if;
 if Abs(D) eq 1 then
  vprint IsotropicSubspace,2: "IsotropicSubspace: minimization is unimodular";
  M,U:=LLLGram(M : Isotropic:=true, Delta:=0.999);
  sol:=Matrix(final_clean(M,U*T));
 else for f in F do v:=Valuation(D,f[1]);
  if v ne 0 then FF*:=Factorization(f[1]^v); end if; end for;
  sol:=Matrix(doitodd(M,T,s+1)); end if;
 vprint IsotropicSubspace,2: "IsotropicSubspace: Subspace intersection";
 E:=Basis(Kernel(Submatrix(sol,1,n+1,NumberOfRows(sol),1))*sol);
 return [clean(Vector([x[i] : i in [1..n]])) : x in E]; end function;

function improve(M,S) d:=#S; n:=Nrows(M);
 X:=U^(-1) where _,_,U:=SmithForm(Matrix(S)); MT:=X*M*Transpose(X);
 vprintf IsotropicSubspace,1: "Dimension of Simon's space is %o\n",d;
 for i in [1..d] do for j in [i+d+1..n] do
  if j eq i+d or (MT[i][i+d] eq 0 and MT[i][j] eq 0) then continue; end if;
  _,a,b:=XGCD(MT[i][i+d],MT[i][j]);
  T:=U^(-1) where _,_,U:=SmithForm(Matrix([[a,b]])); I:=Parent(M)!1;
  I[i+d][i+d]:=T[1][1]; I[i+d][j]:=T[1][2]; I[j][i+d]:=T[2][1];
  I[j][j]:=T[2][2]; MT:=I*MT*Transpose(I); X:=I*X; end for;
  for j in [i+d+1..n] do
   u:=-MT[i][j] div MT[i][i+d]; AddRow(~MT,u,i+d,j); AddColumn(~MT,u,i+d,j);
   AddRow(~X,u,i+d,j); end for; end for; // assert X*M*Transpose(X) eq MT;  
 vprintf IsotropicSubspace,2: "Calling IsotropicSubspace on submatrix\n";
 assert n-2*d eq 4; IndentPush();
 U:=IsotropicSubspace(Submatrix(MT,2*d+1,2*d+1,n-2*d,n-2*d)); IndentPop();
 if Dimension(U) ne 0 then assert Dimension(U) eq 1;
  vprintf IsotropicSubspace,1: "Dimension increases by 1 to %o\n",d+1;
  v:=Basis(U)[1]; w:=Vector([0 : i in [1..2*d]] cat Eltseq(v));
  w:=w*X; assert (w,w*M) eq 0; S:= S cat [w];
  assert &and[(S[i],S[j]*M) eq 0 : i,j in [1..#S]];
  else vprint IsotropicSubspace,1: "Simon's space is maximal"; end if;
 return S; end function;

function callit(M) S:=doit(M); if #S eq 0 then return S; end if; r,s:=qfsig(M);
 if r eq s and #S lt s-1 then S:=improve(M,S); end if;
 if r eq s+2 and #S le s-1 then S:=improve(M,S); end if;
 if r eq s-2 and #S le r-1 then S:=improve(M,S); end if;
 M:=Matrix(S); n:=NumberOfRows(M);
 vprintf IsotropicSubspace,1: "IsotropicSubspace: reducing solution sizes\n";
 L:=LLL(M : Delta:=0.999); return [L[i] : i in [1..n]]; end function;

intrinsic IsotropicSubspace(M::MtrxSpcElt) -> ModTupRng
{Use Simon's algorithm to find an isotropic subspace of large
 (likely maximal) dimension corresponding to the quadratic form
 of the given symmetric matrix.} //'
 require IsSymmetric(M): "Matrix must be symmetric";
 require BaseRing(M) eq ZZ or BaseRing(M) eq QQ: "Matrix must be over Z or Q";
 n:=Degree(Parent(M)); if n eq 0 then return RSpace(Integers(),0); end if;
 M:=ChangeRing(M*LCM([Denominator(x) : x in Eltseq(ChangeRing(M,QQ))]),ZZ);
 I:=callit(M); R:=RSpace(Integers(),NumberOfRows(M));
 S:=sub<R|I>; return S; end intrinsic;

intrinsic IsotropicSubspace(f::RngMPolElt) -> ModTupRng
{Use Simon's algorithm to find an isotropic subspace of large
 (likely maximal) dimension corresponding to the given quadratic form.}//'
 return IsotropicSubspace(SymmetricMatrix(f)); end intrinsic;
