
freeze;

//Copyright (c) 2011-13, Xavier Caruso and David Lubicz, Mark Watkins
//All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
//   * Redistributions of source code must retain the above copyright notice,
// this list of conditions and the following disclaimer.
//   * Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED
// TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
// PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
// LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
// NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

////////////////////////////////////////////////////////////////////////

/* Mark's setup for user-defined types */

declare type SpMatRng[SpMat];

declare attributes SpMatRng: R,r,c; // the SpRng
declare attributes SpMat: S,M; // the parent SpMatRng and matrix

intrinsic SpMatrixSpace(S::SpRng,r::RngIntElt,c::RngIntElt) -> SpMatRng
{Given a S^nu_p slope ring, construct the matrix space with r rows and c cols}
 require r ge 0: "The number of rows must be at least 0";
 require c ge 0: "The number of columns must be at least 0";
 if <r,c> in Keys(S`B) then return S`B[<r,c>]; end if;
 R:=New(SpMatRng); R`R:=S; R`r:=r; R`c:=c; S`B[<r,c>]:=R; return R;
 end intrinsic;

intrinsic ZeroMatrix(S::SpMatRng) -> SpMat
{The zero matrix of a S^nu_p matrix ring}
 M:=New(SpMat); M`S:=S; M`M:=ZeroMatrix(S`R`R,S`r,S`c);
 return M; end intrinsic;

intrinsic IdentityMatrix(S::SpMatRng) -> SpMat
{The identity matrix of a S^nu_p matrix ring (of square dimensions)}
 require S`r eq S`c: "IdentityMatrix only valid for square matrices";
 M:=New(SpMat); M`S:=S; M`M:=IdentityMatrix(S`R`R,S`r);
 return M; end intrinsic;

intrinsic IdentityMatrix(R::SpRng,n::RngIntElt) -> SpMat
{The n-by-n identity matrix for a S^nu_p ring}
 M:=New(SpMat); M`S:=SpMatrixSpace(R,n,n); M`M:=IdentityMatrix(R`R,n); 
 return M; end intrinsic;

intrinsic ZeroMatrix(R::SpRng,n::RngIntElt) -> SpMat
{The n-by-n zero matrix for a S^nu_p ring}
 M:=New(SpMat); M`S:=SpMatrixSpace(R,n,n); M`M:=ZeroMatrix(R`R,n,n); 
 return M; end intrinsic;

intrinsic ZeroMatrix(R::SpRng,r::RngIntElt,c::RngIntElt) -> SpMat
{The r-by-c zero matrix for a S^nu_p ring}
 M:=New(SpMat); M`S:=SpMatrixSpace(R,r,c); M`M:=ZeroMatrix(R`R,r,c); 
 return M; end intrinsic;

intrinsic 'eq'(S1::SpMatRng,S2::SpMatRng) -> BoolElt
{Whether or not two matrix rings are equal}
 return S1`R eq S2`R and S1`r eq S2`r and S1`c eq S2`c; end intrinsic;
intrinsic 'ne'(S1::SpMatRng,S2::SpMatRng) -> BoolElt
{Whether or not two matrix rings are not equal}
 return not (S1 eq S2); end intrinsic;

intrinsic SpMatrix(A::SeqEnum[SeqEnum[SpElement]]) -> SpMat
{Given a sequence of equal-length sequences of S^nu_p elements, make a matrix}
 require #A ge 1: "The sequence cannot be empty"; r:=#A; c:=#A[1];
 S:=Set([#a : a in A]); require #S eq 1: "Each sequence must have same length";
 M:=New(SpMat); M`M:=Matrix(r,c,[[a`f : a in b] : b in A]);
 M`S:=SpMatrixSpace(Parent(A[1][1]),r,c); end intrinsic;

intrinsic SpMatrix(v::SeqEnum[SpVec]) -> SpMat
{Given a sequence of equal length vectors over S^nu_p, construct a matrix}
 U:=Universe(v); A:=ChangeUniverse(&cat[Eltseq(e) : e in v],U`R);
 return SpMatrix(#v,U`d,A); end intrinsic;

intrinsic SpMatrix(r::RngIntElt,c::RngIntElt,A::SeqEnum[SpElement]) -> SpMat
{Given a sequence of r*c S^nu_p elements, construct the r-by-c matrix}
 require #A eq r*c: "Wrong number of elements in array";
 require HasUniverse(A): "Element array must have a universe";
 M:=New(SpMat); M`M:=Matrix(r,c,[Universe(A)`R | a`f : a in A]);
 M`S:=SpMatrixSpace(Universe(A),r,c); return M; end intrinsic;

intrinsic Transpose(M::SpMat) -> SpMat {The transpose matrix}
 X:=New(SpMat); X`M:=Transpose(M`M);
 X`S:=SpMatrixSpace(M`S`R,M`S`c,M`S`r); return X; end intrinsic;

intrinsic HasUniverse(A::SeqEnum) -> BoolElt,.
{Whether a sequence has a universe. If so, return said universe}
 try U:=Universe(A); return true,U; catch e return false,_; end try;
 end intrinsic;

intrinsic 'eq'(S1::SpMat,S2::SpMat) -> BoolElt {Whether inputs are equal}
 return S1`S eq S2`S and IsWeaklyZero(S1-S2); end intrinsic;
intrinsic 'eq'(M::SpMat,x::.) -> BoolElt {Generic equality (tries coercion)}
 return M eq (M`S)!x; end intrinsic;
intrinsic 'eq'(x::.,M::SpMat) -> BoolElt {Generic equality (tries coercion)}
 return M eq (M`S)!x; end intrinsic;

intrinsic 'ne'(S1::SpMat,S2::SpMat) -> BoolElt {Whether inputs are not equal}
 return not (S1 eq S2); end intrinsic;
intrinsic 'ne'(M::SpMat,x::.) -> BoolElt {Generic nonequality (tries coercion)}
 return M ne (M`S)!x; end intrinsic;
intrinsic 'ne'(x::.,M::SpMat) -> BoolElt {Generic nonequality (tries coercion)}
 return M ne (M`S)!x; end intrinsic;

intrinsic Print(M::SpMat) {}
 printf "%o",M`M; return;
 R:=Rows(M); if #R eq 0 then printf "Matrix with zero rows"; return; end if;
 if M`S`c eq 0 then printf "Matrix with zero columns"; return; end if;
 for r in Rows(M) do printf "%o\n",r; end for; end intrinsic;

intrinsic Print(R::SpMatRng) {}
 printf "SpMatrixSpace of %o by %o matrices over %o",R`r,R`c,R`R;
 end intrinsic;

intrinsic Rows(M::SpMat) -> SeqEnum {The sequence of rows of the matrix}
 return [SpSpace(M`S`R,Ncols(M`M))| // need to define Ambient, also if null
         SpVector([(M`S`R)!x : x in Eltseq(c)]) : c in Rows(M`M)];
 end intrinsic;

intrinsic Eltseq(M::SpMat) -> SeqEnum {The sequence of elements of the matrix}
 return [M`S`R!c : c in Eltseq(M`M)]; end intrinsic;

intrinsic LeadingTerms(M::SpMat) -> Mtrx
{The matrix of leading terms (as power series) of a S^nu_p matrix}
 return Matrix(Nrows(M`M),Ncols(M`M),[LeadingTerm(e) : e in Eltseq(M)]);
 end intrinsic;
intrinsic WeierstrassTerms(M::SpMat) -> Mtrx
{The matrix of Weierstrass terms (as power series) of a S^nu_p matrix}
 return Matrix(Nrows(M`M),Ncols(M`M),[WeierstrassTerm(e) : e in Eltseq(M)]);
 end intrinsic;

intrinsic GaussValuations(M::SpMat) -> SeqEnum
{A sequence of sequences of Gauss valuations for S^nu_p matrix elements}
 return [[GaussValuation(e) : e in Eltseq(r)] : r in Rows(M)]; end intrinsic;
intrinsic WeierstrassDegrees(M::SpMat) -> SeqEnum
{A sequence of sequences of Weierstrass degrees for S^nu_p matrix elements}
 return [[WeierstrassDegree(e) : e in Eltseq(r)]:r in Rows(M)]; end intrinsic;

intrinsic Parent(M::SpMat) -> SpMatRng {The parent ring of the matrix}
 return M`S; end intrinsic;
intrinsic Nrows(M::SpMat) -> RngIntElt {The number of rows of the matrix}
 return M`S`r; end intrinsic;
intrinsic Ncols(M::SpMat) -> RngIntElt {The number of columns of the matrix}
 return M`S`c; end intrinsic;

intrinsic IsWeaklyZero(M::SpMat) -> BoolElt {Whether the matrix is weakly zero}
 return &and[IsWeaklyZero(M`S`R!c) : c in Eltseq(M`M)]; end intrinsic;

intrinsic '+'(M1::SpMat,M2::SpMat) -> SpMat {The sum of the inputs}
 require M1`S eq M2`S: "Matrices must be over same SpMatRing";
 M:=New(SpMat); M`M:=M1`M+M2`M; M`S:=M1`S; return M; end intrinsic;

intrinsic '-'(M1::SpMat) -> SpMat {The negation of the input}
 M:=New(SpMat); M`M:=-M1`M; M`S:=M1`S; return M; end intrinsic;

intrinsic '-'(M1::SpMat,M2::SpMat) -> SpMat {The difference of the inputs}
 require M1`S eq M2`S: "Matrices must be over same SpMatRing";
 M:=New(SpMat); M`M:=M1`M-M2`M; M`S:=M1`S; return M; end intrinsic;

intrinsic '*'(M1::SpMat,M2::SpMat) -> SpMat {The product of the inputs}
 require M1`S`R eq M2`S`R: "Underlying SpRng must be the same";
 require M1`S`c eq M2`S`r: "Rows and columns are not compatible";
 M:=New(SpMat); M`M:=M1`M*M2`M; M`S:=SpMatrixSpace(M1`S`R,M1`S`r,M2`S`c);
 return M; end intrinsic;

intrinsic '*'(e::SpElement,M::SpMat) -> SpMat {Multiplication by a scsalar}
 require e`S eq M`S`R: "Underlying SpRng must be the same";
 X:=New(SpMat); X`M:=e`f*M`M; X`S:=SpMatrixSpace(M`S`R,M`S`r,M`S`c);
 return X; end intrinsic;
intrinsic '*'(M::SpMat,e::SpElement) -> SpMat {"}//"
 require e`S eq M`S`R: "Underlying SpRng must be the same";
 X:=New(SpMat); X`M:=e`f*M`M; X`S:=SpMatrixSpace(M`S`R,M`S`r,M`S`c);
 return X; end intrinsic;

intrinsic '*'(e::.,M::SpMat) -> SpMat {Generic mult (tries coercion)}
 return (M`S`R!e)*M; end intrinsic;
intrinsic '*'(M::SpMat,e::.) -> SpMat {Generic mult (tries coercion)}
 return (M`S`R!e)*M; end intrinsic;

intrinsic '/'(M::SpMat,e::SpElement) -> SpMat {Division by a scalar}
 require e`S eq M`S`R: "Underlying SpRng must be the same";
 r:=Nrows(M`M); c:=Ncols(M`M); U:=Eltseq(M`M);
 return SpMatrix(r,c,[u/e : u in U]); end intrinsic;

intrinsic '/'(M::SpMat,e::.) -> SpMat {Generic div (tries coercion)}
 return M/(M`S`R!e); end intrinsic;
 
intrinsic '^'(x::SpMat,n::RngIntElt) -> SpMat {The nth power of x}
 require x`S`r eq x`S`c: "Matrix must be square";
 M:=New(SpMat); M`M:=x`M^n; M`S:=x`S; return M; end intrinsic;

intrinsic IsCoercible(S::SpMatRng,x::.) -> . {}
 if ISA(Type(x),Mtrx) then M:=x; b:=&and[IsCoercible(S`R,x) : x in Eltseq(M)];
  if not b then return b,"Matrix does not coerce"; end if;
  if Nrows(x) ne S`r or Ncols(x) ne S`c then
   return false,"Matrix has wrong dimensions"; end if;
  CM:=Matrix(Nrows(M),Ncols(M),[S`R`R | S`R`R!x : x in Eltseq(M)]);
  X:=New(SpMat); X`M:=CM; X`S:=S; return true,X; end if;
 if Type(x) eq SpMat then return IsCoercible(S,x`M); end if;
 if Type(x) in {RngIntElt,FldRatElt,FldPadElt,RngPadElt,
	       SnuElement,SpElement,RngSerPowElt} then
  if x eq 0 then return true,ZeroMatrix(S); end if;
  if S`r ne S`c then return false,"Scalar is not nonsquare matrix"; end if;
  b,e:=IsCoercible(S`R,x);
  if not b then return b,"Element does not coerce into SpRng"; end if;
  return true,e*IdentityMatrix(S); end if;
 return false,"Invalid type for coercion into SpMatRng"; end intrinsic;

////////////////////////////////////////////////////////////////////////

function row_echelon(S,M,b) R:=S`R; r:=Nrows(M); c:=Ncols(M);
 if b then T:=IdentityMatrix(R`R,r); end if; p:=1;
 for j in [1..c] do u:=p;
  while u le r and IsWeaklyZero(R!M[u,j]) do u:=u+1; end while;
  if u gt r then continue; end if; // column has nothing but zeros
  SwapRows(~M,u,p); if b then SwapRows(~T,u,p); end if; i:=p+1;
  while i le r do
   if not IsWeaklyZero(R!M[i,j]) then
    _,_,A,B,C,D:=ExtendedGcd(R!M[p,j],R!M[i,j]);
    A:=A`f; B:=B`f; C:=C`f; D:=D`f; // A*M[p,j]+B*M[i,j]=G, C*M[p,j]+D*M[i,j]=0
    Np:=A*M[p]+B*M[i]; Ni:=C*M[p]+D*M[i]; M[i]:=Ni; M[p]:=Np;
    if b then Np:=A*T[p]+B*T[i]; Ni:=C*T[p]+D*T[i];
              T[i]:=Ni; T[p]:=Np; end if; end if;
   i:=i+1; end while; p:=p+1; end for;
 for i in [1..r] do j:=1; // make pivots be polynomials of proper shape
  while j le c and IsWeaklyZero(R!M[i,j]) do j:=j+1; end while;
  if j gt c then continue; end if; // row is all zeros
  ud:=R.1^WeierstrassDegree(R!M[i,j]); q:=Quotrem(ud,R!M[i,j]);
  M[i]:=q`f*M[i]; if b then T[i]:=q`f*T[i]; end if; end for;
 if b then return S!M,SpMatrixSpace(R,r,r)!T;
 else return S!M,_; end if; end function;

intrinsic EchelonForm(M::SpMat : Transform:=false) -> SpMat,SpMat
{The echelon form E of M, with an optional transform T such that E=TM}
 return row_echelon(M`S,M`M,Transform); end intrinsic;

function hermite_form(S,M,b)
 R:=S`R; r:=Nrows(M); c:=Ncols(M);
 if r eq 0 or c eq 0 then
  if b then return M,SpMatrixSpace(R,r,r)!IdentityMatrix(R`R,r);
  else return M,_,0; end if; end if;
  E,T:=row_echelon(S,M,b); E:=E`M; if b then T:=T`M; end if;
 // Find the pivot in each row, make entries above it be polys of less deg
 for i in [1..r] do p:=1;
  while p le c and IsWeaklyZero(R!E[i,p]) do p:=p+1; end while;
  if p gt c then continue; end if; // row is all zeros
  for j in [1..i-1] do q:=Quotrem(R!E[j,p],R!E[i,p]); q:=q`f;
   E[j]:=E[j]-q*E[i]; if b then T[j]:=T[j]-q*T[i]; end if; end for; end for;
 if b then return S!E,SpMatrixSpace(R,r,r)!T;
 else return S!E,_; end if; end function;

intrinsic HermiteForm(M::SpMat : Transform:=false) -> SpMat,SpMat
{The Hermite form H of M, with an optional transform T such that H=TM}
 return hermite_form(M`S,M`M,Transform); end intrinsic;

function smith_final(S,X,P,Q,b)  R:=S`R; ro:=Nrows(X); co:=Ncols(X);
 for i in [1..ro],j in [1..co] do
  if i ne j then assert IsWeaklyZero(R!X[i,j]); end if; end for;
 for i in [1..Min(ro,co)-1] do
  if IsWeaklyZero(R!X[i+1,i+1]) then continue; end if;
  q,r:=Quotrem(R!X[i+1,i+1],R!X[i,i]); if r eq 0 then continue; end if;
  X:=AddColumn(X,1,i+1,i); if b then Q:=AddColumn(Q,1,i+1,i); end if;
  G,H,A,B,C,D:=ExtendedGcd(R!X[i,i],R!X[i+1,i]);
  A:=A`f; B:=B`f; C:=C`f; D:=D`f;
  Xi:=A*X[i]+B*X[i+1]; Xi1:=C*X[i]+D*X[i+1]; X[i]:=Xi; X[i+1]:=Xi1;
  assert R!X[i,i] eq G; assert R!X[i+1,i] eq 0;
  if b then Pi:=A*P[i]+B*P[i+1]; Pi1:=C*P[i]+D*P[i+1];
            P[i]:=Pi; P[i+1]:=Pi1; end if;
  q,r:=Quotrem(R!X[i,i+1],R!X[i,i]); assert r eq 0; q:=q`f;
  X:=AddColumn(X,-q,i,i+1); if b then Q:=AddColumn(Q,-q,i,i+1); end if;
  end for; if not b then return S!X,_,_; end if;
 return S!X,SpMatrixSpace(R,ro,ro)!P,SpMatrixSpace(R,co,co)!Q; end function;

intrinsic SmithForm(M::SpMat:Transform:=false)-> SpMat,SpMat,SpMat,RngIntElt
{The Smith form S of M, with optional transforms P,Q with S=PMQ}
 H,P:=HermiteForm(M:Transform);
 X,Q:=HermiteForm(Transpose(H):Transform); X:=Transpose(X);
 if Transform then Q:=Transpose(Q); return smith_final(M`S,X`M,P`M,Q`M,true);
 else return smith_final(M`S,X`M,0,0,false); end if; end intrinsic;

intrinsic Submatrix
(M::SpMat,i::RngIntElt,j::RngIntElt,r::RngIntElt,c::RngIntElt) -> SpMat
{Return the r-by-c submatrix of M whose first entry is the [i,j]-th entry}
 X:=New(SpMat); X`S:=SpMatrixSpace(M`S`R,r,c); X`M:=Submatrix(M`M,i,j,r,c);
 return X; end intrinsic;

intrinsic HorizontalJoin(M1::SpMat,M2::SpMat) -> SpMat
{The horizontal join of two matrices with the same number of rows}
 require M1`S`R eq M2`S`R: "Matrices must have same base ring";
 require M1`S`r eq M2`S`r: "Matrices must have same number of rows";
 X:=New(SpMat); X`S:=SpMatrixSpace(M1`S`R,Nrows(M1`M),Ncols(M1`M)+Ncols(M2`M));
 X`M:=HorizontalJoin(M1`M,M2`M); return X; end intrinsic;

intrinsic VerticalJoin(M1::SpMat,M2::SpMat) -> SpMat
{The vertical join of two matrices with the same number of columns}
 require M1`S`R eq M2`S`R: "Matrices must have same base ring";
 require M1`S`c eq M2`S`c: "Matrices must have same number of columns";
 X:=New(SpMat); X`S:=SpMatrixSpace(M1`S`R,Nrows(M1`M)+Nrows(M2`M),Ncols(M1`M));
 X`M:=VerticalJoin(M1`M,M2`M); return X; end intrinsic;

intrinsic Kernel(M::SpMat) -> SpSpc
{The kernel of a matrix over S^nu_p, given as an S^nu_p module}
 E,T:=EchelonForm(M : Transform); Z:=Integers();
 A:=[Z|i : i in [1..Nrows(E)] | IsWeaklyZero(R[i]) where R:=Rows(E)];
 K:=Rows(T)[A]; return SpSpace(K); end intrinsic;

intrinsic Image(M::SpMat : Transform:=false) -> SpSpc,SpMat
{The image of a matrix over S^nu_p, given as an S^nu_p module}
 E,T:=EchelonForm(M : Transform:=Transform); Z:=Integers();
 A:=[Z|i : i in [1..Nrows(E)] | not IsWeaklyZero(R[i])] where R:=Rows(E);
 S:=SpSpace(Rows(E)[A]);
 if Transform then return S,SpMatrix(Rows(T)[A]); else return S,_; end if;
 end intrinsic;

intrinsic Inverse(M::SpMat) -> SpMat
{The inverse of a S^nu_p matrix. An error occurs if it is not invertible}
 require Nrows(M`M) eq Ncols(M`M): "Matrix must be square";
 H,T:=HermiteForm(M : Transform);
 require H eq IdentityMatrix(Parent(M)): "Matrix is not invertible";
 return T; end intrinsic;

intrinsic IsInvertible(M::SpMat) -> BoolElt,SpMat
{Whether a square S^nu_p matrix is invertible, and if so the inverse}
 require Nrows(M`M) eq Ncols(M`M): "Matrix must be square";
 H,T:=HermiteForm(M : Transform);
 if H ne IdentityMatrix(Parent(M)) then return false,_;
 else return true,T; end if; end intrinsic;
