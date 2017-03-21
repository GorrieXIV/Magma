freeze;

import "simon.m" : callit;

procedure RANDOMISE(~L,~T)
 vprint IsotropicLLL,1: "Randomising the Gram matrix"; n:=NumberOfRows(L);
 for i in [1..n] do
  a:=Random([1..n]); b:=Random([1..n]);
  SwapRows(~L,a,b); SwapColumns(~L,a,b); SwapRows(~T,a,b);
  a:=Random([1..n]); b:=Random([1..n]); q:=Random([-1..1]);
  if a ne b then
  AddRow(~L,q,a,b); AddColumn(~L,q,a,b); AddRow(~T,q,a,b); end if; end for;
 end procedure;

procedure random_indefinite(~G,~U)
 while true do E:=OrthogonalizeGram(Submatrix(G,1,1,5,5));
  u:=[E[i][i] : i in [1..5] | E[i][i] gt 0];
  if #u ne 0 and #u ne 5 then break; end if; w:=Random([6..NumberOfRows(G)]);
  SwapRows(~G,5,w); SwapColumns(~G,5,w); SwapRows(~U,5,w); end while;
 end procedure;

function finalize(G,K,U)
 vprintf IsotropicLLL,1: "Determinant of 5x5 matrix is %o\n",Determinant(K);
 sol:=Matrix([Eltseq(callit(K)[1]) cat [0 : i in [6..NumberOfRows(G)]]]);
  _,_,X:=SmithForm(sol); U:=X^(-1)*U;
 return true,U; end function;

intrinsic InternalILLLHelper(I::MtrxSpcElt,e::RngIntElt) -> BoolElt,AlgMatElt
{} vprintf IsotropicLLL,1: "Using InternalILLLHelper\n";
 G:=Submatrix(I,1,1,e,e); U:=IdentityMatrix(Integers(),e); u:=G[e][e];
 if Abs(u) eq 1 then vprintf IsotropicLLL,1: "Have a good entry of size 1\n";
  for i in [1..e-1] do x:=-I[i][i]*u;
   if x gt 0 then r:=Round(Sqrt(x)); else r:=0; end if;
   AddRow(~G,r,e,i); AddColumn(~G,r,e,i); AddRow(~U,r,e,i); end for;
  SwapRows(~G,1,e); SwapColumns(~G,1,e); SwapRows(~U,1,e);
  while true do random_indefinite(~G,~U); K:=Submatrix(G,1,1,5,5);
   if Determinant(K) ne 0 then return finalize(G,K,U); end if;
   end while; end if;
 while true do
  while true do
   O,T:=OrthogonalizeGram(G); norms:=[<O[i][i],i> : i in [1..e]];
   pos:=[f : f in norms | f[1] gt 0]; neg:=[f : f in norms | f[1] lt 0];
   if #pos eq 0 or #neg eq 0 then return false,_; end if;
   if #pos gt #neg then m,w:=Max([f[1] : f in neg]); w:=neg[w][2];
   else m,w:=Min([f[1] : f in pos]); w:=pos[w][2]; end if; assert O[w][w] eq m;
   vprintf IsotropicLLL,1: "Good orthogonalised Gram entry is %o\n",m;
   if Abs(m) lt 10^20 then break; end if;
   RANDOMISE(~G,~U); G,V:=LLLGram(G : Delta:=0.999); U:=V*U; end while;
  _,_,X:=SmithForm(Matrix(T[w])); U:=X^(-1)*U; G:=X^(-1)*G*Transpose(X^(-1));
  norms:=[<G[i][i],i> : i in [1..e]]; p:=[f : f in norms | f[1] gt 0];
  n:=[f : f in norms | f[1] lt 0]; z:=[f : f in norms | f[1] eq 0];
  if #z ne 0 then vprint IsotropicLLL,1: "Found a zero"; return true,U; end if;
  if #pos gt #neg then m,w:=Max([f[1] : f in n]); w:=n[w][2];
  else m,w:=Min([f[1] : f in p]); w:=p[w][2]; end if; assert G[w][w] eq m;
  SwapRows(~G,1,w); SwapColumns(~G,1,w); SwapRows(~U,1,w);
  for j in [2..5] do _,w:=Min([Abs(G[1][i]) : i in [j..e]]); w:=w+j-1;
   SwapRows(~G,j,w); SwapColumns(~G,j,w); SwapRows(~U,j,w); end for;
  random_indefinite(~G,~U); K:=Submatrix(G,1,1,5,5); d:=Abs(Determinant(K));
  if d lt 10^30 and d ne 0 then return finalize(G,K,U); end if;
  end while; end intrinsic;




