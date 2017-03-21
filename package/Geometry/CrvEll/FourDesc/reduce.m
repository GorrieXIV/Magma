freeze;
 
declare verbose ReduceFD,3;

import "utils.m" : fnz, ApplyMatrix;
import "stoll_reduce.m": Covariant;
import "find_point.m": Pencilise;

function dyadic_rep(x) if x eq 0 then return 0;
 else return a*2^b where a,b:=MantissaExponent(x); end if; end function;

function N2Norm(fd) return &+[&+[r^2: r in Eltseq(s)]:s in fd]; end function;

function LLLReduce(A) u:=Eltseq(A[1]); v:=Eltseq(A[2]);
 M:=Eltseq(LLL(Matrix([u,v]) : Delta:=0.999));
 return [Matrix(4,4,[M[i] : i in [1..16]]),Matrix(4,4,[M[i] : i in [17..32]])];
end function;

function lll_reduce(uu)
 vprintf ReduceFD,1: "%o: About to LLLReduce\n",Log(N2Norm(uu));
 while true do
  _,t:=LLLGram(MatrixAlgebra(Integers(),4)!uu[1] : Delta:=0.999);
  vv:=ApplyMatrix(t,uu);
  if N2Norm(vv) lt N2Norm(uu) then uu:=vv; else break; end if;
  vprintf ReduceFD,1: "iLLLReduced has norm %o\n",Log(N2Norm(uu));

  vv:=LLLReduce(uu); if N2Norm(vv) lt N2Norm(uu) then uu:=vv; end if;
  vprintf ReduceFD,1: "LLLReduced has norm %o\n",Log(N2Norm(vv));

  end while; return uu; end function;

function SRCompare(b,a)
 if Abs(a[2]) ne Abs(b[2]) then return Abs(b[2])-Abs(a[2]);
 else return Abs(b[3])-Abs(a[3]); end if; end function;

function StollReduce(M,qr)
 C,qr:=Covariant(M[1],M[2],qr); vprintf ReduceFD,2: "Have covariant\n";
 C:=Matrix(4,4,[[dyadic_rep(x) : x in Eltseq(C[1])],
		[dyadic_rep(x) : x in Eltseq(C[2])],
		[dyadic_rep(x) : x in Eltseq(C[3])],
		[dyadic_rep(x) : x in Eltseq(C[4])]]);
 C:=LCM([Denominator(Rationals()!x) : x in Eltseq(C)])*C;
 _,b:=LLLGram(MatrixAlgebra(Integers(),4)!C : Delta:=0.999);
 mf:=ApplyMatrix(b,M); vprintf ReduceFD,2: "Covariant LLL-reduced\n";
 d0:=[<i,mf[1][i,i], mf[2][i,i]> : i in [1..4]]; Sort(~d0, SRCompare);
 tm:=MatrixAlgebra(Integers(),4)!0; 
 for i in [1..4] do tm[i][d0[i][1]]:=1; end for; mf:=ApplyMatrix(tm,mf);
 for m in [1,2] do
  if fnz([mf[m][i,i] : i in [1..4]]) lt 0 then mf[m]:=-mf[m]; end if; end for;
 s:=[Sign(mf[1][1,j]) : j in [1..4]];
 if s[2] eq 0 then s[2]:=Sign(mf[2][1,2]); end if;
 if s[3] eq 0 then s[3]:=Sign(mf[2][1,3]); end if;
 if s[4] eq 0 then s[4]:=Sign(mf[2][1,4]); end if;
 s:=[-t^2+t+1 : t in s];  // send [-1,0,1] to [-1,1,1]
 tm:=DiagonalMatrix(s); return ApplyMatrix(tm,mf),qr; end function;

function ReduceFD(FD,qr)
 fd,i:=Explode(FD); vprintf ReduceFD,1: "Reducing QI #%o\n",i;
 fd:=Pencilise(fd); tar:={}; step:=0; uu:=fd;
 while not (uu in tar and step ge 2) do
  if (step mod 2 eq 0) then tar join:={uu};
   vprintf ReduceFD,1: "%o: About to LLLReduce\n",Log(N2Norm(uu));
   while true do
    vprintf ReduceFD,3: "iLLLReduced has norm %o\n",Log(N2Norm(uu));
    vv:=LLLReduce(uu); if N2Norm(vv) lt N2Norm(uu) then uu:=vv; end if;
    _,t:=LLLGram(MatrixAlgebra(Integers(),4)!uu[1] : Delta:=0.999);
    vprintf ReduceFD,3: "LLLReduced has norm %o\n",Log(N2Norm(vv));
    vv:=ApplyMatrix(t,uu);
    if N2Norm(vv) lt N2Norm(uu) then uu:=vv; else break; end if; end while;
  else vprintf ReduceFD,1:"%o: About to StollReduce\n",Log(N2Norm(uu));
   uu,qr:=StollReduce(uu,qr); end if; step:=1+step; end while;
 return LLLReduce(uu),qr; end function;
