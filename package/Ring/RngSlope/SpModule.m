
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

declare type SpSpc[SpVec]; // R^n (RSpace) // can have Basis, Dimension

declare attributes SpSpc: R,d,M; // M is BasisMatrix (Echelon), as SpMat
declare attributes SpVec: S,v,d; // v has SpElements in it
                                 // v`S is always an Ambient

intrinsic SpSpace(R::SpRng,n::RngIntElt) -> SpSpc
{Given an S^nu_p slope ring R, construct the module space R^n}
 require n ge 0: "Dimension must be nonnegative";
 if n in Keys(R`A) then return R`A[n]; end if;
 S:=New(SpSpc); S`R:=R; S`d:=n; S`M:=IdentityMatrix(R,n); R`A[n]:=S;
 return S; end intrinsic;

intrinsic ZeroVector(S::SpSpc) -> SpVec {The zero vector of a S^nu_p space}
 v:=New(SpVec); v`S:=Ambient(S); v`d:=S`d; v`v:=[S`R | 0 : i in [1..S`d]];
 return v; end intrinsic;

intrinsic Ambient(S::SpSpc) -> SpSpc
{The ambient R^n for the S^nu_p space, where R is the slope ring}
 return SpSpace(S`R,S`d); end intrinsic;

intrinsic SpSpace(M::SpMat) -> SpSpc
{The S^nu_p space associated to the rows of the S^nu_p matrix M}
 S:=New(SpSpc); S`R:=M`S`R; S`d:=Ncols(M`M);
 S`M:=SpMatrix([SpSpace(S`R,S`d) | // handle null sequence
		r : r in Rows(HermiteForm(M)) | not IsWeaklyZero(r)]);
 assert Nrows(S`M) le Ncols(S`M); return S; end intrinsic;

intrinsic SpSpace(v::SeqEnum[SpVec]) -> SpSpc
{The S^nu_p space associated to the sequence of S^nu_p vectors v}
 U:=Universe(v); A:=ChangeUniverse(&cat[Eltseq(e) : e in v],U`R);
 return SpSpace(SpMatrix(#v,U`d,A)); end intrinsic;

intrinsic SpVector(e::SeqEnum[SpElement])  -> SpVec
{The S^nu_p vector associated to the sequence of S^nu_p elements}
 U:=Universe(e); v:=New(SpVec); v`S:=SpSpace(U,#e); v`d:=#e; v`v:=e; return v;
 end intrinsic;

intrinsic SubConstr(S::SpSpc,v::SeqEnum[SpVec]) -> SpSpc {}
 if #v eq 0 then return SpSpace(S`R,S`d,v); end if;
 require Ambient(S) eq Universe(v): "Ambient must be the same";
 require &and[e in S : e in v]: "Vectors must be in subspace";
 return SpSpace(v),_; end intrinsic;

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
 return true,SpVector([R | e : e in Eltseq(s)]),0; end function;

intrinsic IsCoercible(S::SpSpc,x::.) -> . {}
 if Type(x) eq SpVec then
  if x`d ne S`d then return false,"Degrees are not compatible"; end if;
  b:=&and[IsCoercible(S`R,e) : e in x`v];
  if not b then return false,"Incompatible ring types"; end if;
  b,v:=is_in(S`R,S`M`M,Vector([e`f : e in x`v]));
  if not b then return false,"Vector not in SpSpace";
  else return true,v; end if; end if;
 if x cmpeq 0 then return true,ZeroVector(S); end if;
 if ISA(Type(x),ModTupRngElt) then return IsCoercible(S,Eltseq(x)); end if;
 if Type(x) eq SeqEnum then
  if #x ne S`d then return false,"Sequence has wrong length"; end if;
  try A:=SpVector([S`R!e : e in x]); return IsCoercible(S,A);
  catch e false,"Cannot coerce vector elements into Sp-ring"; end try; end if;
 return false,"Incomptable type for coercion into SpSpace"; end intrinsic;

intrinsic '.'(S::SpSpc,n::RngIntElt) -> SpVec {The i-th basis element}
 require n ge 0 and n le Nrows(S`M`M): "n must be between 0 and dimension";
 if n eq 0 then return ZeroVector(S); else return Rows(S`M)[n]; end if;
 end intrinsic;

intrinsic Parent(v::SpVec) -> SpSpc {The parent Sp space}
return v`S; end intrinsic; // Ambient ?

intrinsic Print(S::SpSpc) {}
 if Nrows(S`M) eq S`d then
  printf "Full SpSpace of degree %o over %o\n",S`d,S`R; return; end if;
 printf "SpSpace of degree %o, dimension %o over %o\n",S`d,Nrows(S`M),S`R;
 R:=Rows(S`M); if #R eq 0 then return; end if;
 printf "Basis given by:\n";
 for i in [1..#R] do printf "%o\n",R[i]; end for; end intrinsic;

intrinsic Print(v::SpVec) {} printf "%o",v`v; end intrinsic;

intrinsic Basis(S::SpSpc) -> SeqEnum {The basis of the space (row sequence)}
 return Rows(S`M); end intrinsic;
intrinsic BasisMatrix(S::SpSpc) -> SpMat {The basis matrix of the space}
 return S`M; end intrinsic;
intrinsic Dimension(S::SpSpc) -> RngIntElt {The dimension of a S^nu_p space}
 return Nrows(S`M`M); end intrinsic;
intrinsic Degree(S::SpSpc) -> RngIntElt {The degree of a S^nu_p space}
 return Ncols(S`M`M); end intrinsic;

intrinsic Eltseq(v::SpVec) -> SeqEnum {Elements of the vector as a sequence}
 return [v`S`R!c : c in Eltseq(v`v)]; end intrinsic;

intrinsic GaussValuations(v::SpVec) -> SeqEnum
{Given an S^nu_p vector, return the sequence of GaussValuations}
 return [GaussValuation(e) : e in Eltseq(v)]; end intrinsic;
intrinsic WeierstrassDegrees(v::SpVec) -> SeqEnum
{Given an S^nu_p vector, return the sequence of WeierstrassDegrees}
 return [WeierstrassDegree(e) : e in Eltseq(v)]; end intrinsic;

intrinsic LeadingTerms(v::SpVec) -> ModTupRngElt
{The leading terms of the constituents of a S^nu_p vector, as power series}
 return Vector([LeadingTerm(e) : e in Eltseq(v)]); end intrinsic;
intrinsic WeierstrassTerms(v::SpVec) -> ModTupRngElt
{The Weierstrass terms of the constituents of a S^nu_p vector, as power series}
 return Vector([WeierstrassTerm(e) : e in Eltseq(v)]); end intrinsic;

intrinsic '+'(v::SpVec,w::SpVec) -> SpVec {The sum of the inputs}
 require v`S`R eq w`S`R: "Vectors must have same underlying Sp-ring";
 require v`S`d eq w`S`d: "Vectors must have dimension";
 x:=New(SpVec); x`S:=v`S; x`v:=[v`v[i]+w`v[i] : i in [1..v`S`d]];
 x`d:=v`S`d; return x; end intrinsic;

intrinsic '-'(v::SpVec,w::SpVec) -> SpVec {The difference of the inputs}
 require v`S`R eq w`S`R: "Vectors must have same underlying Sp-ring";
 require v`S`d eq w`S`d: "Vectors must have dimension";
 x:=New(SpVec); x`S:=v`S; x`v:=[v`v[i]-w`v[i] : i in [1..v`S`d]];
 x`d:=v`S`d; return x; end intrinsic;

intrinsic '-'(v::SpVec) -> SpVec {Negation of the input}
 x:=New(SpVec); x`S:=v`S; x`v:=[-e : e in v`v]; x`d:=v`d;
 return x; end intrinsic;

intrinsic '*'(v::SpVec,e::SpElement) -> SpVec {Scalar multiplication}
 b,e:=IsCoercible(v`S`R,e); require b: "Scalar must coerce into Sp-ring";
 x:=New(SpVec); x`S:=v`S; x`v:=[e*f : f in v`v]; x`d:=v`d;
 return x; end intrinsic;
intrinsic '*'(e::SpElement,v::SpVec) -> SpVec {"} return v*e; end intrinsic;//"
intrinsic '*'(e::.,v::SpVec) -> SpVec {Generic scalar mult (tries coercion)}
 return (v`S`R!e)*v; end intrinsic;
intrinsic '*'(v::SpVec,e::.) -> SpVec {"} return (v`S`R!e)*v; end intrinsic;//"

intrinsic IsWeaklyZero(v::SpVec) -> BoolElt {Whether the input is weakly zero}
 return &and[IsWeaklyZero(v`S`R!c) : c in Eltseq(v)]; end intrinsic;

intrinsic 'eq'(y::SpVec,z::SpVec) -> BoolElt {Equality of inputs}
 return y`S`R eq z`S`R and y`d eq z`d and IsWeaklyZero(y-z); end intrinsic;
intrinsic 'ne'(y::SpVec,z::SpVec) -> BoolElt {Nonequality of inputs}
 return not (y eq z); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '+'(M1::SpSpc,M2::SpSpc) -> SpSpc {Sum of the input spaces} // join?
 require M1`R`R eq M2`R`R: "Must be over same SpRng";
 require M1`d eq M2`d: "Must be in same dimension SpSpc";
 M:=EchelonForm(VerticalJoin(M1`M,M2`M));
 A:=[SpSpace(M1`R,M1`d) | c : c in Rows(M) | not IsWeaklyZero(c)];
 return SpSpace(SpMatrix(A)); end intrinsic;

intrinsic 'meet'(M1::SpSpc,M2::SpSpc) -> SpSpc {Intersection of the inputs}
 require M1`R`R eq M2`R`R: "Must be over same SpRng";
 require M1`d eq M2`d: "Must be in same dimension SpSpc";
 K:=BasisMatrix(Kernel(VerticalJoin(M1`M,M2`M)));
 A:=Submatrix(K,1,1,Nrows(K`M),Nrows(M1`M));
 return SpSpace(A*BasisMatrix(M1)); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(A::SpSpc,B::SpSpc) -> BoolElt,SpMat
{Equality of inputs, also returns a basis transformation if so}
 b,T:=IsSubspace(A,B); if b then b:=IsSubspace(B,A); end if;
 if b then return b,T; else return b,_; end if; end intrinsic;
intrinsic 'ne'(A::SpSpc,B::SpSpc) -> BoolElt {Nonequality of inputs}
 return not (A eq B); end intrinsic;

intrinsic 'in'(v::SpVec,S::SpSpc) -> BoolElt,SpVec {Whether v is in S}
 return IsConsistent(S`M,v); end intrinsic;

intrinsic IsSubspace(A::SpSpc,B::SpSpc) -> BoolElt,SpMat
{Return whether A is a subspace of B, and if so an inclusion map}
 b,T,K,e:=IsConsistent(B`M,A`M);
 if b then return b,T,e; else return b,_,_;  end if; end intrinsic;

intrinsic IsConsistent(M::SpMat,v::SpVec) -> BoolElt,SpVec
{Return whether x*M=v is solvable, and if so a solution vector}
 require M`S`R eq v`S`R: "Arguments must have equal Sp-rings";
 require M`S`c eq v`d: "Arguments must have same number of columns";
 E,T:=EchelonForm(M:Transform); b,w:=is_in(E`S`R,E`M,Vector([e`f : e in v`v]));
 if b then return b,w*T; else return false,_; end if; end intrinsic;

intrinsic IsConsistent(M::SpMat,e::SeqEnum[SpVec]) -> BoolElt,SeqEnum
{Return whether x*M=v is sovable for all v in e,
 and if so a sequence of solution vectors}
 require M`S`R eq e[1]`S`R: "Arguments must have equal Sp-rings";
 if #e eq 0 then return true,e,0; end if;
 require M`S`c eq e[1]`d: "Arguments must have same number of columns";
 E,T:=EchelonForm(M:Transform); c:=0; A:=[];
 for v in e do b,w,u:=is_in(E`S`R,E`M,Vector([e`f : e in v`v]));
  if not b then return false,_,_; end if; c:=Max(c,u); Append(~A,w*T); end for;
 return true,A,c; end intrinsic;

intrinsic IsConsistent(M::SpMat,W::SpMat)-> BoolElt,SpMat,SpMat
{Return whether X*M=W is solvable, and if so a solution matrix and the kernel}
 b,V,e:=IsConsistent(M,Rows(W));
 if b then return b,V,Kernel(M),e; else return b,_,_,_; end if; end intrinsic;

intrinsic DirectSum(A::SpSpc,B::SpSpc) -> SpSpc {Direct sum of inputs}
 require Dimension(A meet B) eq 0: "Intersection is nontrivial";
 return A join B; end intrinsic;

intrinsic '*'(v::SpVec,M::SpMat) -> SpVec {Vector-times-matrix multiplication}
 require v`S`R eq M`S`R: "Arguments are not compatible";
 require v`d eq Nrows(M`M): "Degrees are not compatible";
 return
  SpVector([v`S`R | u : u in Eltseq(Vector([v`S`R`R | e`f : e in v`v])*M`M)]);
 end intrinsic;

intrinsic '*'(S::SpSpc,M::SpMat) -> SpSpc {Transformation of space by matrix}
 require S`R eq M`S`R: "Arguments are not compatible";
 require S`d eq Nrows(M`M): "Degrees are not compatible";
 return SpSpace(BasisMatrix(S)*M`M); end intrinsic;
