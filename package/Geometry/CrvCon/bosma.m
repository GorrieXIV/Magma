freeze;

Z:=Integers();
function KS(a,b) k:=KroneckerSymbol(a,b);
 if k eq 1 then return GF(2)!0; end if; return GF(2)!1; end function;

function sqrt(g,FAC) //problem at 2 ?! what if middle coeff is odd?
 a:=g[1]; b:=g[2] div 2; c:=g[3]; d:=a*c-b^2; FAC:=FAC/Factorization(4);
 m:=ChineseRemainderTheorem
        ([Gcd(a,f[1]) eq 1 select Z!Sqrt(Integers(f[1]^f[2])!a)
                           else Z!(-b/Sqrt(Integers(f[1]^f[2])!c)) : f in FAC],
        [f[1]^f[2]: f in FAC]);
 n:=ChineseRemainderTheorem
        ([Gcd(a,f[1]) ne 1 select Z!Sqrt(Integers(f[1]^f[2])!c)
                           else Z!(-b/Sqrt(Integers(f[1]^f[2])!a)) : f in FAC],
        [f[1]^f[2]: f in FAC]);
 M:=-Adjoint(SymmetricMatrix([(n^2-c)/d,(m*n+b)/d,(m^2-a)/d,n,m,d]));
 C,T:=LLLGram(MatrixAlgebra(Integers(),3)!M : Isotropic:=true,Delta:=0.999);
 if C[1][1] eq 1 then Q:=Matrix([[-1,0,1],[1,1,-1],[0,-1,1]]);
 else assert false; end if; T:=Q*T; v:=Transpose(T)[3];
 if v[1] lt 0 then v:=-v; end if;
 if v[1] mod 2 ne 0 then return Parent(g)![v[1],2*v[2],2*v[3]];
 else return Parent(g)![v[3],-2*v[2],2*v[1]]; end if; end function;

function evalit(k,f) if k eq -1 then k:=-4; end if;
 a:=f[1]; if Gcd(k,a) eq 1 then return KS(k,a); end if;
 c:=f[3]; if Gcd(k,c) eq 1 then return KS(k,c); end if;
 assert false; return 0; end function;

function trivform(d) Q:=QuadraticForms(d);
 if d mod 4 eq 0 then return Q!<1,0,-d div 4>; end if;
 return Q!<1,1,(-d+1) div 4>; end function; // only need even d

function addit(m,A) S:=trivform(Discriminant(A[1])); m:=Eltseq(m);
 for i in [1..#m] do if m[i] ne 0 then S:=Composition(S,A[i]); end if; end for;
 return Reduction(S); end function;

function class2part(D,FAC) assert D mod 4 eq 0 or D mod 4 eq 1;
 if D eq -4 then return [],[]; end if;
 if IsOdd(D) then D:=D*4;
  if FAC ne [] then FAC:=FAC*Factorization(4); end if; end if;
 Q:=QuadraticForms(D); if FAC eq [] then FAC:=Factorization(D); end if;
 if D lt 0 then neg:=true; else neg:=false; end if; d:=1; F:=[];
 for x in FAC do p:=x[1]; v:=x[2]; if IsOdd(v) then d:=d*p; end if;
  if IsOdd(p) then F cat:=[p]; end if; end for;
 F:=[p mod 4 eq 1 select p else -p : p in F];
 if d mod 4 ne 1 then d:=d*4; end if; if neg then d:=-d; end if;
 d:=Discriminant(Integers(QuadraticField(D)));  // cheat!
 _,f:=IsSquare(D div d); if F eq [] then u:=d; else u:=d div &*F; end if;
 if u ne 1 then F cat:=[u]; end if;
 G:=[x[1] mod 4 eq 1 select x[1] else -x[1] :
      x in FAC | d mod x[1] ne 0 and IsOdd(x[1])] cat F;
 if (d mod 8 eq 0 and IsEven(f)) or (IsOdd(d) and f mod 4 eq 0)
  then G cat:=[-4]; end if;
 if (d mod 8 eq 4 and f mod 4 eq 0) then G cat:=[8]; end if;
 if (IsOdd(d) and f mod 8 eq 0) then G cat:=[-4,8]; end if; A:=[];
 for x in FAC do p:=x[1]; v:=x[2]; if p eq 2 then continue; end if;
  if D mod 4 eq 1 then A cat:=[Q!<p^v,p^v,(p^v-D/p^v) div 4>];
  else A cat:=[Q!<p^v,0,-D div (4*p^v)>]; end if; end for;
 if D mod 4 eq 0 and D mod 16 ne 4 then
  if D mod 16 eq 12 then A cat:=[Q!<2,2,(4-D) div 8>];
  else v:=Valuation(D,2); A cat:=[Q!<2^(v-2),0,-D div (2^v)>]; end if;
  if D mod 32 eq 0 then A cat:=[Q!<4,4,1-D div 16>]; end if; end if;
 // A:=SetToSequence(Set([Reduction(a) : a in A])); // -192 bug
 s:=0; pr:=0; n:=#A; H:=[2 : i in [1..n]];
 while true do
  M:=Transpose(Matrix([[evalit(c,f) : f in A] : c in G]));
  _,_,T:=SmithForm(Matrix(Basis(Kernel(M)))); T:=T^(-1); r:=Rank(M);
  for k in [n-pr+1..n] do 
   v:=Vector([GF(2)!0 : i in [1..n]]); v[k]:=1; s:=Solution(T,v);
   c:=n; while s[c] eq 0 do c:=c-1; end while;
   T[c]:=&+[(Z!s[i])*T[i] : i in [1..n]]; end for;
  if r eq n-1 then break; end if; I:=H;
  for i in [n-r+1..n] do _,b:=Max(Eltseq(ChangeRing(T[i],Z)));
   I[i]:=H[b]; end for; H:=I;
  A:=[addit(T[i],A) : i in [1..n]];
  for i in [1..n-r] do A[i]:=Reduction(sqrt(A[i],FAC)); H[i]:=H[i]*2; end for;
  pr:=r; end while;
 M:=Transpose(Matrix([[evalit(c,f) : f in A] : c in G]));
 _,_,T:=SmithForm(Matrix(Basis(Kernel(M)))); T:=T^(-1);
 _,m:=Max(Eltseq(ChangeRing(T[1],Z))); Remove(~A,m); Remove(~H,m);
 return A,H; end function;

function odd_shift(f) a,b,c:=Explode(Eltseq(f)); assert IsEven(b);
 if IsEven(a) then t:=a; a:=c; c:=t; end if;
 if IsOdd(c) then c:=a+b+c; b:=b+2*a; end if;
 if IsEven(a) and IsEven(c) then a:=a div 2; b:=b div 2; c:=c div 2; 
  return Reduction(QuadraticForms(b^2-4*a*c)!<a,b,c>); end if;
 assert b mod 2 eq 0; assert c mod 4 eq 0; b:=b div 2; c:=c div 4;
 return Reduction(QuadraticForms(b^2-4*a*c)!<a,b,c>); end function;

intrinsic QuadraticClassGroupTwoPart(D::RngIntElt : Factorization:=[])
  -> GrpAb, Map
{Use the Bosma-Stevenhagen algorithm to compute the 2-part
 of the class group of a discriminant.}
 require D mod 4 eq 0 or D mod 4 eq 1: "D must be a discriminant";
 if Factorization ne [] then require Type(Factorization) eq RngIntEltFact:
  "Factorization must be given as a RngIntEltFact";
  require &*Factorization eq Abs(D): "Factorization is not of D"; end if;
 F,O:=class2part(D,[]); if IsOdd(D) then F:=[odd_shift(f) : f in F]; end if;
 G:=AbelianGroup(O); Q:=QuadraticForms(D);
 function grump(g) e:=Eltseq(g);
  return Reduction(&*[Q | F[i]^e[i] : i in [1..#e]]); end function;
 return G,map<G->Q|g:->grump(g)>; end intrinsic;

intrinsic QuadraticClassGroupTwoPart(O::RngQuad : Factorization:=[])
  -> GrpAb, Map
{Use the Bosma-Stevenhagen algorithm to compute the 2-part
 of the class group of a quadratic ring.}
 return QuadraticClassGroupTwoPart
         (Discriminant(O) : Factorization:=Factorization); end intrinsic;

intrinsic QuadraticClassGroupTwoPart(K::FldQuad : Factorization:=[])
  -> GrpAb, Map
{Use the Bosma-Stevenhagen algorithm to compute the 2-part
 of the class group of a quadratic field.}
 return QuadraticClassGroupTwoPart
         (Discriminant(K) : Factorization:=Factorization); end intrinsic;
