freeze;
 
declare verbose MinimiseFD,2;
import "utils.m": ExtendToUnimodular,QFFromMatrix,SL2Apply,ApplyMatrix,
                  ApplyTransform,LinearFactors,PolynomialApply;
import "quartics.m": AQDirect;
import "quartmin.m": QuarticMinimiseOnceAtPrime;
import "find_point.m": Pencilise;

function HasObviousBox(A,p)
 uu:=&join{&join{{{x,y} : y in [1..4] | z[x,y] mod p ne 0}:
		 x in [1..4]} : z in A};
 cols:=[i : i in [1..4] | &and[i in r : r in uu]];
 if (cols ne []) then r:=cols[1];
  M4:=DiagonalMatrix([1,1,1,1]); M4[r,r]:=p;
  M2:=DiagonalMatrix([1/p, 1/p]); T:=<M2, M4>; return true,T; end if;
 return false,_,_; end function;
    
T0:=<DiagonalMatrix(Rationals(),[1,1]),DiagonalMatrix(Rationals(),[1,1,1,1])>;

function CombineTransform(T1,T2)
 return <T2[1]*T1[1], T1[2]*T2[2]>; end function;

function BoxMinimiseK2(u, p)    // case where dim of common kernel is 2
 F:=FiniteField(p); FP := PolynomialRing(F); x := FP.1;
 FPP<lambda,mu>:=PolynomialRing(F,2);
 hl:=hom<FPP -> FP | x,1>; hr:=hom<FPP -> FP | 1,x>;
 MS:=MatrixAlgebra(F,4); MS2:=MatrixAlgebra(FPP,4);
 MZ:=MatrixAlgebra(Integers(),4);
 result:=u; At:=MS!u[1]; Bt:=MS!u[2]; CK:=Kernel(At) meet Kernel(Bt);
 t:=Basis(CK); eb:=ExtendBasis(t,VectorSpace(F,4));
 K1:=MS!&cat [Eltseq(k): k in eb];
 K2:=MS2![1,0,0,0,0,1,0,0,0,0,lambda,mu,0,0,0,1];
 At2:=K1*At*Transpose(K1);  At3:=K2*MS2!At2*Transpose(K2);
 Bt2:=K1*Bt*Transpose(K1);  Bt3:= K2*MS2!Bt2*Transpose(K2);
 AX:=At3[3,3];  BX:=Bt3[3,3]; g:=GCD(AX,BX); done:=false;
 if (p eq 2 and g eq 0) then
  K2:=MS![1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]; done:=true;
 else
  if (g ne 1) then done:=true;
   if (Degree(hr(g)) ne 0) then R:=Roots(hr(g));
    if (R eq []) then done:=false;
    else K2:=MS![1,0,0,0,0,1,0,0,0,0,1,R[1][1],0,0,0,1]; end if;
   else R:=Roots(hl(g));
    if (R eq []) then done:=false;
     else R:=[t[1]: t in R];
      if (R[1] ne 0) then K2:=MS![1,0,0,0,0,1,0,0,0,0,R[1],1,0,0,0,1];
       else K2:=MS![1,0,0,0,0,1,0,0,0,0,0,1,0,0,1,0]; end if; end if;
     end if; end if; end if;
 if done eq true then
  K3:=MZ!(K2*K1); K4:=DiagonalMatrix([1,1,1,p])*K3;
  up:=ApplyMatrix(K4,u); return up,1; end if;
 K0:=<T0[1],MZ!K1>;
 K4:=<DiagonalMatrix([1/p,1/p]),DiagonalMatrix([1,1,p,p])>;
 Kcomp:=CombineTransform(K4,K0); mamble:=ApplyTransform(Kcomp, u);
 return mamble,0; end function;

function SL2MinimiseAtPrime(A, p)
 minimiser:=DiagonalMatrix(Rationals(),[1,1]); F:=GF(p); oldA:=A;    
 v1:=Matrix([[F!a : a in Eltseq(b)] : b in A]);
 while Rank(v1) ne 2 do u:=Basis(Kernel(v1));
  if Rank(v1) eq 0 then
   A:=SL2Apply(DiagonalMatrix([1/p,1/p]),A);
   minimiser:= DiagonalMatrix([1/p,1/p]) * minimiser;
  else // rank is 1
   tt:=[Integers()!k : k in Eltseq(u[1])];
   tmat:=ChangeRing(c, Rationals()) where a,b,c is SmithForm(Matrix([tt]));
   tmat[1,1]/:=p; tmat[1,2]/:=p; A:=SL2Apply(tmat,A);
   minimiser:=tmat*minimiser; end if;
  v1:=Matrix([[F!a : a in Eltseq(b)] : b in A]); end while;
 M:=MatrixAlgebra(Integers(),4); return [M!a:a in A],<minimiser,T0[2]>;
end function;

function BoxMinimiseK1(fd_in, p)
 MS:=MatrixAlgebra(GF(p),4); k1:=Kernel(MS!fd_in[1]); k2:=Kernel(MS!fd_in[2]);
 CK:=k1 meet k2; k1b:=Complement(k1,CK); k2b:=Complement(k2,CK);
 bas:=[Basis(CK)[1],Basis(k1b)[1],Basis(k2b)[1]]; bas:=ExtendToUnimodular(bas);
 t_canonical:=<T0[1],bas>; fd_canon1:=ApplyTransform(t_canonical,fd_in);
 At2:=MS!fd_canon1[1]; Bt2:=MS!fd_canon1[2];
 if (At2[3,3] eq 0 and Bt2[2,2] eq 0 and Bt2[2,3] eq 0 and Bt2[3,3] eq 0) then
  pm:=<T0[1],DiagonalMatrix([1,1,1,p])>;
  fd_tmp:=ApplyTransform(pm, fd_canon1);
  result,tx:=SL2MinimiseAtPrime(fd_tmp,p);
  fd_final:=ApplyTransform(tx, fd_tmp); return fd_final,1;
 else
  if (At2[3,3] ne 0) then sc:=-At2[4,3]/At2[3,3];
   r:=DiagonalMatrix([1,1,1,1]); r[3,4]:=sc;
   fd_step2:=ApplyMatrix(r,fd_canon1);
  else fd_step2:=fd_canon1; end if;
  ok,trans:=HasObviousBox(fd_step2,p); assert ok;
  return ApplyMatrix(trans,fd_step2),1; end if; end function;

function Flip(fd, p)
 for i in [1..2] do for j in [1..2] do for k in [1..2] do
  fd[i][j,k] div:=p; fd[i][2+j,2+k]*:=p;
 end for; end for; end for; return fd; end function;

function MinimiseFDOnceAtPrime(fd_in,Q,p)
 g:=Gcd([Integers()!x : x in Eltseq(fd_in[1]) cat Eltseq(fd_in[2])]);
 if g ne 1 then T:=<DiagonalMatrix([1/g,1/g]),T0[2]>;
  return false,ApplyTransform(T,fd_in),Q div g^4; end if;
 a,b,Q:=QuarticMinimiseOnceAtPrime(Q,p); if a then return true,fd_in,Q; end if;
 t_mgr:=<b,T0[2]>; fd_mgr:=ApplyTransform(t_mgr,fd_in); 
 M:=MatrixAlgebra(GF(p),4); MZ:=MatrixAlgebra(Integers(),4);
 P := PolynomialRing(GF(p)); x := P.1; PF:=FunctionField(GF(p));
 Mxy:=MatrixAlgebra(P,4); MFxy:=MatrixAlgebra(PF,4);
 genmat:=x*Mxy!fd_mgr[1]+Mxy!fd_mgr[2]; genrank:=Rank(MFxy!genmat);
 if (genrank eq 0) then T:=<DiagonalMatrix([1/p,1/p]),T0[2]>;
  return false,ApplyTransform(T,fd_mgr),Q div p^4; end if; assert genrank ne 4;
 ck:=&meet[Kernel(M!t) : t in fd_mgr]; kerdim:=Dimension(ck);
 vprintf MinimiseFD,2: "MinimiseFD: kerdim %o genrank %o\n",kerdim,genrank;
 if (genrank eq 1) then ig:=ExtendToUnimodular(Basis(ck));
  Tn:=<DiagonalMatrix([1/p,1/p]),DiagonalMatrix([1,1,1,p])*ig>;
 return false,ApplyTransform(Tn,fd_mgr),Q div p^2; end if;
 if (genrank eq 2 and kerdim eq 1) then
  NF,x:=BoxMinimiseK1(fd_mgr,p); return false,NF,Q div p^2; end if;
 if (genrank eq 2 and kerdim eq 2) then
  NF,x:=BoxMinimiseK2(fd_mgr,p); return false,NF,Q*p^(2*x); end if;
 if (genrank eq 3 and kerdim eq 1) then
  sigpow:=Valuation(GCD(Coefficients(Q)),p : Check:=false);
  vprintf MinimiseFD,2: "MinimiseFD: sigpow %o\n",sigpow;
  if (sigpow ge 2) then mat:=(ExtendToUnimodular(Basis(ck)));
   m2:=DiagonalMatrix([1,p,p,p])*mat;
   u3:=ApplyTransform(<DiagonalMatrix([1/p^2,1/p^2]),m2>,fd_mgr);
   return false,u3,Q div p^2;
  else
   if (Rank(M!fd_mgr[1]) eq 2) then
    em:=<T0[1],ExtendToUnimodular(ExtendBasis(Basis(ck),Kernel(M!fd_mgr[1])))>;
   else em:=<T0[1], ExtendToUnimodular(Basis(ck))>; end if;
   fd_t:=ApplyTransform(em, fd_mgr);  _<w,x,y,z>:=PolynomialRing(GF(p),4);
   elf1:=LinearFactors(QFFromMatrix([w,x,y,z], M!fd_t[1]));
   elf2:=LinearFactors(QFFromMatrix([w,x,y,z], M!fd_t[2]));
   a:=elf1 cat elf2; assert #a ne 0; linfac:=a[1];
   T:=[Coefficient(linfac, x, 1) : x in [1..4]];
   mm:=#[k : k in T | k ne 0]; assert mm eq 1;
   _,ix:=Max(T); a:=MZ!1; a[ix,ix]:=p;
   fd_out:=ApplyTransform(<DiagonalMatrix([1/p^2,1/p^2]),a>,fd_t);
   return false,fd_out,Q div p^2; end if; end if;
 if (genrank eq 3 and kerdim eq 0) then t:=0;
  a:=fd_mgr[1]; b:=fd_mgr[2]; newgen:=[]; term:=[];
  if (Rank(M!b) eq 3) then newgen:=[b]; term:=[[0,1]]; end if;
  while (t le p and #newgen lt 2) do r:=Rank(M!(a+t*b));
   if (r eq 3) then Append(~newgen,a+t*b); Append(~term,[1,t]); end if;
   t:=1+t; end while; assert #newgen eq 2;
  a:=newgen[1]; b:=newgen[2]; tX:=<Matrix(term),T0[2]>;
  va:=Basis(Kernel(M!a))[1]; vb:=Basis(Kernel(M!b))[1];
  unimat:=ExtendToUnimodular([va,vb]);
  tY:=<T0[1],unimat>; tZ:=<T0[1],DiagonalMatrix([1,1,p,p])>;
  t_total:=CombineTransform(tZ,CombineTransform(tY,tX));
  return false,ApplyTransform(t_total,fd_mgr),
	 PolynomialApply(Matrix(term),Q)*p^4; end if; end function;

function MinimiseFDAtPrime(fd,Q,p) ok:=false;
 while not ok do ok,fd,Q:=MinimiseFDOnceAtPrime(fd,Q,p); end while;
 return fd,Q; end function;

function MinimiseFD(FD,bp) fd,i:=Explode(FD); fd:=Pencilise(fd);
 vprintf MinimiseFD,1: "Minimising QI #%o\n",i; Q:=AQDirect(fd);
 dq:=Discriminant(Q); bp:=[<p,Valuation(dq,p : Check:=false)> : p in bp];
 Sort(~bp,func<x,y|y[2]-x[2]>); bp:=[x : x in bp | x[2] ge 12];
 for k in bp do
  vprintf MinimiseFD,1: "Minimising at %o: valuation %o\n",k[1],k[2];
  fd,Q:=MinimiseFDAtPrime(fd,Q,k[1]); end for; return fd; end function;
