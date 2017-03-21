
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

declare type SuSpc[SuVec]; // R^n (RSpace) // can have Basis, Dimension

declare attributes SuSpc: R,d,M; // M is BasisMatrix (Echelon), as SuMat
declare attributes SuVec: S,v,d; // v has SuElements in it
                                 // v`S is always an Ambient

intrinsic SuSpace(R::SuRng,n::RngIntElt) -> SpSpc
{Given an S^nu_u slope ring R, construct the module space R^n}
 require n ge 0: "Dimension must be nonnegative";
 if n in Keys(R`A) then return R`A[n]; end if;
 S:=New(SuSpc); S`R:=R; S`d:=n; S`M:=IdentityMatrix(R,n); R`A[n]:=S;
 return S; end intrinsic;

intrinsic ZeroVector(S::SuSpc) -> SpVec {The zero vector of a S^nu_u space}
 v:=New(SuVec); v`S:=Ambient(S); v`d:=S`d; v`v:=[S`R | 0 : i in [1..S`d]];
 return v; end intrinsic;

intrinsic Ambient(S::SuSpc) -> SuSpc
{The ambient R^n for the S^nu_u space, where R is the slope ring}
 return SuSpace(S`R,S`d); end intrinsic;

intrinsic SuSpace(M::SuMat) -> SuSpc
{The S^nu_u space associated to the rows of the S^nu_u matrix M}
 S:=New(SuSpc); S`R:=M`S`R; S`d:=Ncols(M`M);
 S`M:=SuMatrix([SuSpace(S`R,S`d) | // handle null sequence
		r : r in Rows(HermiteForm(M)) | not IsWeaklyZero(r)]);
 assert Nrows(S`M) le Ncols(S`M); return S; end intrinsic;

intrinsic SuSpace(v::SeqEnum[SuVec]) -> SuSpc
{The S^nu_u space associated to the sequence of S^nu_u vectors v}
 U:=Universe(v); A:=ChangeUniverse(&cat[Eltseq(e) : e in v],U`R);
 return SuSpace(SuMatrix(#v,U`d,A)); end intrinsic;

intrinsic SuVector(e::SeqEnum[SuElement]) -> SuVec
{The S^nu_u vector associated to the sequence of S^nu_u elements}
 U:=Universe(e); v:=New(SuVec); v`S:=SuSpace(U,#e); v`d:=#e; v`v:=e; return v;
 end intrinsic;

intrinsic SubConstr(S::SuSpc,v::SeqEnum[SuVec]) -> SuSpc {}
 if #v eq 0 then return SuSpace(S`R,S`d,v); end if;
 require Ambient(S) eq Universe(v): "Ambient must be the same";
 require &and[e in S : e in v]: "Vectors must be in subspace";
 return SuSpace(v),_; end intrinsic;

// M is raw matrix, R is Sp-ring, v is SeqEnum of raw elements
function is_in(R,M,v) r:=Nrows(M); c:=Ncols(M); p:=1;
 // assert Type(R) eq SpRng; P:=UniformizingElement(CoefficientRing(R`R));
 s:=Vector([R`R|0 : i in [1..r]]); // assume M is in echelon form!!
 for i in [1..r] do p:=1;
  while p le c and IsWeaklyZero(R!M[i,p]) do p:=p+1; end while;
  if p gt c then continue; end if; // should not happen, row is all zero
  G,H:=Quotrem(R!v[p],R!M[i,p]);
  if not IsWeaklyZero(H) then return false,_,_; end if;
  G:=G`f; s[i]:=G; v:=v-G*M[i]; end for;
 if not &and[R!u eq 0 : u in Eltseq(v)] then return false,_,_; end if;
 return true,SuVector([R | e : e in Eltseq(s)]),0; end function;

intrinsic IsCoercible(S::SuSpc,x::.) -> . {}
 if Type(x) eq SuVec then
  if x`d ne S`d then return false,"Degrees are not compatible"; end if;
  b:=&and[IsCoercible(S`R,e) : e in x`v];
  if not b then return false,"Incompatible ring types"; end if;
  b,v:=is_in(S`R,S`M`M,Vector([e`f : e in x`v]));
  if not b then return false,"Vector not in SuSpace";
  else return true,v; end if; end if;
 if x cmpeq 0 then return true,ZeroVector(S); end if;
 if ISA(Type(x),ModTupRngElt) then return IsCoercible(S,Eltseq(x)); end if;
 if Type(x) eq SeqEnum then
  if #x ne S`d then return false,"Sequence has wrong length"; end if;
  try A:=SuVector([S`R!e : e in x]); return IsCoercible(S,A);
  catch e false,"Cannot coerce vector elements into Su-ring"; end try; end if;
 return false,"Incomptable type for coercion into SuSpace"; end intrinsic;

intrinsic '.'(S::SuSpc,n::RngIntElt) -> SuVec {The i-th basis element}
 require n ge 0 and n le Nrows(S`M`M): "n must be between 0 and dimension";
 if n eq 0 then return ZeroVector(S); else return Rows(S`M)[n]; end if;
 end intrinsic;

intrinsic Parent(v::SuVec) -> SuSpc {The parent Su space}
 return v`S; end intrinsic; // Ambient ?

intrinsic Print(S::SuSpc) {}
 if Nrows(S`M) eq S`d then
  printf "Full SuSpace of degree %o over %o\n",S`d,S`R; return; end if;
 printf "SuSpace of degree %o, dimension %o over %o\n",S`d,Nrows(S`M),S`R;
 R:=Rows(S`M); if #R eq 0 then return; end if;
 printf "Basis given by:\n";
 for i in [1..#R] do printf "%o\n",R[i]; end for; end intrinsic;

intrinsic Print(v::SuVec) {} printf "%o",v`v; end intrinsic;

intrinsic Basis(S::SuSpc) -> SeqEnum {The basis of the space (row sequence)}
 return Rows(S`M); end intrinsic;
intrinsic BasisMatrix(S::SuSpc) -> SpMat {The basis matrix of the space}
 return S`M; end intrinsic;
intrinsic Dimension(S::SuSpc) -> RngIntElt {The dimension of a S^nu_u space}
 return Nrows(S`M`M); end intrinsic;
intrinsic Degree(S::SuSpc) -> RngIntElt {The degree of a S^nu_u space}
 return Ncols(S`M`M); end intrinsic;

intrinsic Eltseq(v::SuVec) -> SeqEnum {Elements of the vector as a sequence}
 return [v`S`R!c : c in Eltseq(v`v)]; end intrinsic;

intrinsic GaussValuations(v::SuVec) -> SeqEnum
{Given an S^nu_u vector, return the sequence of GaussValuations}
 return [GaussValuation(e) : e in Eltseq(v)]; end intrinsic;
intrinsic WeierstrassDegrees(v::SuVec) -> SeqEnum
{Given an S^nu_u vector, return the sequence of WeierstrassDegrees}
 return [WeierstrassDegree(e) : e in Eltseq(v)]; end intrinsic;

intrinsic LeadingTerms(v::SuVec) -> ModTupRngElt
{The leading terms of the constituents of a S^nu_p vector, as Laurent series}
 return Vector([LeadingTerm(e) : e in Eltseq(v)]); end intrinsic;
intrinsic WeierstrassTerms(v::SuVec) -> ModTupRngElt
{The Weierstrass terms of the  S^nu_p vector constituents, as Laurent series}
 return Vector([WeierstrassTerm(e) : e in Eltseq(v)]); end intrinsic;

intrinsic '+'(v::SuVec,w::SuVec) -> SuVec {The sum of the inputs}
 require v`S`R eq w`S`R: "Vectors must have same underlying Su-ring";
 require v`S`d eq w`S`d: "Vectors must have dimension";
 x:=New(SuVec); x`S:=v`S; x`v:=[v`v[i]+w`v[i] : i in [1..v`S`d]];
 x`d:=v`S`d; return x; end intrinsic;

intrinsic '-'(v::SuVec,w::SuVec) -> SuVec {The difference of the inputs}
 require v`S`R eq w`S`R: "Vectors must have same underlying Sp-ring";
 require v`S`d eq w`S`d: "Vectors must have dimension";
 x:=New(SuVec); x`S:=v`S; x`v:=[v`v[i]-w`v[i] : i in [1..v`S`d]];
 x`d:=v`S`d; return x; end intrinsic;

intrinsic '-'(v::SuVec) -> SuVec {Negation of the input}
 x:=New(SuVec); x`S:=v`S; x`v:=[-e : e in v`v]; x`d:=v`d;
 return x; end intrinsic;

intrinsic '*'(v::SuVec,e::SuElement) -> SuVec {Scalar multiplication}
 b,e:=IsCoercible(v`S`R,e); require b: "Scalar must coerce into Su-ring";
 x:=New(SuVec); x`S:=v`S; x`v:=[e*f : f in v`v]; x`d:=v`d;
 return x; end intrinsic;
intrinsic '*'(e::SuElement,v::SuVec) -> SuVec {"} return v*e; end intrinsic;//"
intrinsic '*'(e::.,v::SuVec) -> SuVec {Generic scalar mult (tries coercion)}
 return (v`S`R!e)*v; end intrinsic;
intrinsic '*'(v::SuVec,e::.) -> SuVec {"} return (v`S`R!e)*v; end intrinsic;//"

// probably slash is not a good idea, maybe do it later

intrinsic IsWeaklyZero(v::SuVec) -> BoolElt {Whether the input is weakly zero}
 return &and[IsWeaklyZero(v`S`R!c) : c in Eltseq(v)]; end intrinsic;

intrinsic 'eq'(y::SuVec,z::SuVec) -> BoolElt {Equality of the inputs}
 return y`S`R eq z`S`R and y`d eq z`d and IsWeaklyZero(y-z); end intrinsic;
intrinsic 'ne'(y::SuVec,z::SuVec) -> BoolElt {Nonequality of the inputs}
 return not (y eq z); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '+'(M1::SuSpc,M2::SuSpc) -> SuSpc {Sum of the input spaces} // join?
 require M1`R`R eq M2`R`R: "Must be over same SuRng";
 require M1`d eq M2`d: "Must be in same dimension SuSpc";
 M:=EchelonForm(VerticalJoin(M1`M,M2`M));
 A:=[SuSpace(M1`R,M1`d) | c : c in Rows(M) | not IsWeaklyZero(c)];
 return SuSpace(SuMatrix(A)); end intrinsic;

intrinsic 'meet'(M1::SuSpc,M2::SuSpc) -> SuSpc {Intersection of the inputs}
 require M1`R`R eq M2`R`R: "Must be over same SuRng";
 require M1`d eq M2`d: "Must be in same dimension SuSpc";
 K:=BasisMatrix(Kernel(VerticalJoin(M1`M,M2`M)));
 A:=Submatrix(K,1,1,Nrows(K`M),Nrows(M1`M));
 return SuSpace(A*BasisMatrix(M1)); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(A::SuSpc,B::SuSpc) -> BoolElt,SuMat
{Equality of inputs, also returns a basis transformation if so}
 b,T:=IsSubspace(A,B); if b then b:=IsSubspace(B,A); end if;
 if b then return b,T; else return b,_; end if; end intrinsic;
intrinsic 'ne'(A::SuSpc,B::SuSpc) -> BoolElt {}
 return not (A eq B); end intrinsic;

intrinsic 'in'(v::SuVec,S::SuSpc) -> BoolElt,SuVec {Whether v is in S}
 return IsConsistent(S`M,v); end intrinsic;

intrinsic IsSubspace(A::SuSpc,B::SuSpc) -> BoolElt,SuMat
{Return whether A is a subspace of B, and if so an inclusion map}
 b,T,K,e:=IsConsistent(B`M,A`M);
 if b then return b,T,e; else return b,_,_;  end if; end intrinsic;

intrinsic IsConsistent(M::SuMat,v::SuVec) -> BoolElt,SuVec
{Return whether x*M=v is solvable, and if so a solution vector}
 require M`S`R eq v`S`R: "Arguments must have equal Su-rings";
 require M`S`c eq v`d: "Arguments must have same number of columns";
 E,T:=EchelonForm(M:Transform); b,w:=is_in(E`S`R,E`M,Vector([e`f : e in v`v]));
 if b then return b,w*T; else return false,_; end if; end intrinsic;

intrinsic IsConsistent(M::SuMat,e::SeqEnum[SuVec]) -> BoolElt,SeqEnum
{Return whether x*M=v is sovable for all v in e,
 and if so a sequence of solution vectors}
 require M`S`R eq e[1]`S`R: "Arguments must have equal Su-rings";
 if #e eq 0 then return true,e,0; end if;
 require M`S`c eq e[1]`d: "Arguments must have same number of columns";
 E,T:=EchelonForm(M:Transform); c:=0; A:=[];
 for v in e do b,w,u:=is_in(E`S`R,E`M,Vector([e`f : e in v`v]));
  if not b then return false,_,_; end if; c:=Max(c,u); Append(~A,w*T); end for;
 return true,A,c; end intrinsic;

intrinsic IsConsistent(M::SuMat,W::SuMat)-> BoolElt,SuMat,SuMat
{Return whether X*M=W is solvable, and if so a solution matrix and the kernel}
 b,V,e:=IsConsistent(M,Rows(W));
 if b then return b,V,Kernel(M),e; else return b,_,_,_; end if; end intrinsic;

intrinsic DirectSum(A::SuSpc,B::SuSpc) -> SuSpc {Direct sum of inputs}
 require Dimension(A meet B) eq 0: "Intersection is nontrivial";
 return A join B; end intrinsic;

intrinsic '*'(v::SuVec,M::SuMat) -> SuVec {Vector-times-matrix multiplication}
 require v`S`R eq M`S`R: "Arguments are not compatible";
 require v`d eq Nrows(M`M): "Degrees are not compatible";
 return
  SuVector([v`S`R | u : u in Eltseq(Vector([v`S`R`R | e`f : e in v`v])*M`M)]);
 end intrinsic;

intrinsic '*'(S::SuSpc,M::SuMat) -> SuSpc {Transformation of space by matrix}
 require S`R eq M`S`R: "Arguments are not compatible";
 require S`d eq Nrows(M`M): "Degrees are not compatible";
 return SuSpace(BasisMatrix(S)*M`M); end intrinsic;

