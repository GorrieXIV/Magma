
freeze;

function expand_auto(M)
 d:=Degree(Parent(M)); K:=BaseRing(Parent(M)); O:=Integers(K);
 R:=MatrixAlgebra(Integers(),2*d)!0;
 for i,j in [1..d] do u:=O!M[i][j]; R[i][j]:=u[1]; R[i][j+d]:=u[2];
 u:=O!(M[i][j]*O.2); R[i+d][j]:=u[1]; R[i+d][j+d]:=u[2]; end for; return R;
 end function;

function expand_basis(G,w) cw:=Trace(w)-w; nw:=cw*w; /* much faster */
 return BlockMatrix(2,2,[G,G*cw,G*w,G*nw]); end function;

function retract_basis(G,w) /* maybe make a check also? */
 D:=Degree(Parent(G)); d:=D div 2; H:=MatrixAlgebra(Parent(w),d)!0;
 for i,j in [1..d] do H[i][j]:=G[i][j]+G[i][j+d]*w; end for;
 return H; end function;

function real_imag(G,w) D:=2*Degree(Parent(G)); H:=expand_basis(G,w);
 R:=Matrix(D,D,[Trace(e)/2 : e in Eltseq(H)]); s:=w-Trace(w)/2;
 I:=ChangeRing(Matrix(D,D,[(e-Trace(e)/2)/s : e in Eltseq(H)]),Rationals());
 return R,I; end function;

intrinsic ExpandBasis(M::Mtrx) -> Mtrx
{Expand a Hermitian Gram matrix into a rational one, taking the trace}
 K:=BaseRing(M);
 require NumberOfRows(M) eq NumberOfColumns(M): "Matrix must be square";
 M:=MatrixAlgebra(K,NumberOfRows(M))!M;
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
  "Gram matrix be over an imaginary quadratic field";
 w:=K!(Integers(K).2); D:=2*Degree(Parent(M));
 H:=expand_basis(M,w); R:=ChangeRing(H+Transpose(H),Rationals())/2;
 return R; end intrinsic;

intrinsic BlockTranspose(M::Mtrx,d::RngIntElt : Negate:=true) -> Mtrx
{Transpose dxd blocks of M, negating the off-diagonal terms of each block.
 This corresponds to Transpose with RepresentationMatrix}
 r:=NumberOfRows(M); c:=NumberOfColumns(M); r1:=r div d; c1:=c div d;
 require d ge 0 and r mod d eq 0 and c mod d eq 0: "M not the right dimension";
 R:=&cat[[Submatrix(M,1+d*(i-1),1+d*(j-1),d,d) : i in [1..r1]] : j in [1..c1]];
 return BlockMatrix(c1,r1,[2*DiagonalMatrix(Diagonal(U))-U : U in R]);
 end intrinsic;

intrinsic HermitianTranspose(M::Mtrx) -> Mtrx
{Given a matrix over an imaginary quadratic field,
 compute its Hermitian transpose} /* could make this faster */
 K:=BaseRing(M); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
  "Matrix be over an imaginary quadratic field";
 return Matrix(c,r,[Trace(e)-e : e in Eltseq(Transpose(M))]); end intrinsic;

intrinsic HermitianAutomorphismGroup(M::Mtrx : VectorsLimit:=0) -> GrpMat
{Given a Gram matrix M over an imaginary quadratic field,
 compute the Hermitian automorphism group for the maximal order}
 K:=BaseRing(M);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
  "Gram matrix be over an imaginary quadratic field";
 M:=MatrixAlgebra(K,NumberOfRows(M))!M;
 require M eq HermitianTranspose(M): "Gram matrix must be conjugate-symmetric";
 w:=K!(Integers(K).2); R,I:=real_imag(M,w);
 r:=Lcm([Denominator(x) : x in Eltseq(R)]); R:=ChangeRing(R*r,Integers());
 i:=Lcm([Denominator(x) : x in Eltseq(I)]); I:=ChangeRing(I*i,Integers());
 RR,T:=LLLGram(R : Delta:=0.999); II:=T*I*Transpose(T);
/* much faster for examples of interest with BacherDepth as 0 */
 if VectorsLimit eq 0 then AA:=AutomorphismGroup([RR,II] : BacherDepth:=0);
 else AA:=AutomorphismGroup([RR,II] : VectorsLimit:=VectorsLimit); end if;
 A:=[T^(-1)*g*T : g in Generators(AA)]; Aw:=[retract_basis(a,w): a in A];
 G:=MatrixGroup<Degree(Universe(Aw)),BaseRing(Universe(Aw))|Aw>; G`Order:=#AA;
 assert &and[a*M*HermitianTranspose(a) eq M : a in Generators(G)];
 return G; end intrinsic;

intrinsic InvariantForms(G::GrpMat[FldNum]) -> SeqEnum
{Invariant forms of a matrix group, such that gMg*=M}
 K:=BaseRing(G);
 require ISA(Type(K),FldNum) and Degree(K) eq 2 and Discriminant(K) lt 0:
 "Gram matrix be over an imaginary quadratic field";
 M:=GModule(G); D:=HermitianDual(M); B:=Basis(GHom(Expand(M),Expand(D)));
 A:=BaseRing(G); R:=[RepresentationMatrix(b) : b in Basis(A)];
 d:=Degree(G); n:=Degree(A);
 V:=VectorSpace(BaseRing(A),d*n*d*n); Z:=MatrixAlgebra(BaseRing(A),d*n)!0;
 U:=[InsertBlock(Z,r,1+(i-1)*n,1+(j-1)*n) : r in R, i,j in [1..d]];
 I:=sub<V|[Eltseq(u) : u in U]> meet sub <V|[Eltseq(b) : b in B]>;
 W:=[WriteOver(Matrix(d*n,d*n,Eltseq(b)),A) : b in Basis(I)];
 assert &and[g*w*HermitianTranspose(g) eq w : g in Generators(G), w in W];
 return W; end intrinsic;

/************************************************************************/

function expand_qbasis(M,O) B:=Basis(O);
 d:=Degree(Parent(M)); R:=MatrixAlgebra(BaseRing(M),4*d)!0;
 for a,b in [0..3] do for i,j in [1..d] do
  R[a*d+i][b*d+j]:=B[a+1]*M[i][j]*Conjugate(B[b+1]); end for; end for;
 return R; end function; /* interpreter is slow, see above */

function retract_qbasis(M,O) B:=Basis(O);
 D:=Degree(Parent(M)); d:=D div 4; R:=MatrixAlgebra(Universe(B),d)!0;
 for i,j in [1..d] do
  R[i][j]:=M[i][j]*B[1]+M[i][j+d]*B[2]+M[i][j+2*d]*B[3]+M[i][j+3*d]*B[4];
  end for; return R; end function;

function four_fold(M,O)
 N:=Eltseq(expand_qbasis(M,O)); R:=[[],[],[],[]];
 for i in [1..#N] do
  R[1][i],R[2][i],R[3][i],R[4][i]:=Explode(Eltseq(N[i])); end for;
 D:=4*Degree(Parent(M));
 return [ChangeRing(Matrix(D,D,r),Rationals()) : r in R]; end function;

intrinsic QuaternionicTranspose(M::Mtrx) -> Mtrx
{Given a matrix over a quaternion algebra, compute its conjugate transpose}
 K:=BaseRing(M); r:=NumberOfRows(M); c:=NumberOfColumns(M);
 require ISA(Type(K),AlgQuat): "Matrix be over a quaternion algebra";
 return Matrix(c,r,[Conjugate(e) : e in Eltseq(Transpose(M))]); end intrinsic;

_MaximalOrder:=MaximalOrder;
intrinsic QuaternionicAutomorphismGroup
(M::Mtrx : MaximalOrder:=false,VectorsLimit:=0) -> GrpMat
{Given a Gram matrix M over a quaternion algebra over Q,
 compute the quaternionic automorphisms, returned as a list of generators 
 A specific MaximalOrder can be passed as an additional argument.}
 K:=BaseRing(M);
 require ISA(Type(K),AlgQuat): "Matrix be over a quaternion algebra";
 require BaseRing(K) eq Rationals(): "Center of quaternions must be rationals";
 M:=MatrixAlgebra(K,NumberOfRows(M))!M;
 require M eq QuaternionicTranspose(M): "Matrix must be conjugate-symmetric";
 if Type(MaximalOrder) eq BoolElt then O:=_MaximalOrder(K);
 else O:=MaximalOrder; end if;
 require Algebra(O) eq K: "MaximalOrder must be over same quaternion algebra";
 require IsMaximal(O): "Order must be maximal";
 R:=four_fold(M,O); c:=Lcm([Denominator(x) : x in &cat[Eltseq(r) : r in R]]);
 R:=[ChangeRing(c*r,Integers()) : r in R]; assert IsSymmetric(R[1]);
 _,T:=LLLGram(R[1] : Delta:=0.999); R:=[T*r*Transpose(T) : r in R];
 if VectorsLimit eq 0 then AA:=AutomorphismGroup(R);
 else AA:=AutomorphismGroup(R : VectorsLimit:=VectorsLimit); end if;
 A:=[T^(-1)*g*T : g in Generators(AA)]; Aw:=[retract_qbasis(a,O): a in A];
 G:=MatrixGroup<Degree(Universe(Aw)),BaseRing(Universe(Aw))|Aw>; G`Order:=#AA;
 assert &and[a*M*QuaternionicTranspose(a) eq M : a in Aw];
 return G; end intrinsic;

intrinsic ExpandQuaternionicBasis(M::Mtrx : MaximalOrder:=false) -> Mtrx
{Expand a Quaternionic Gram matrix into a rational one, taking the trace}
 K:=BaseRing(M);
 require NumberOfRows(M) eq NumberOfColumns(M): "Matrix must be square";
 M:=MatrixAlgebra(K,NumberOfRows(M))!M;
 require ISA(Type(K),AlgQuat): "Matrix be over a quaternion algebra";
 require BaseRing(K) eq Rationals(): "Center of quaternions must be rationals";
 if Type(MaximalOrder) eq BoolElt then O:=_MaximalOrder(K);
 else O:=MaximalOrder; end if;
 require Algebra(O) eq K: "MaximalOrder must be over same quaternion algebra";
 require IsMaximal(O): "Order must be maximal";
 R:=four_fold(M,O); return R[1]; end intrinsic;

/************************************************************************/

function moore_determinant(M)
 d:=Degree(Parent(M)); det:=1; R:=BaseRing(BaseRing(M));
 for i in [1..d] do e:=M[i][i];                              
  if e eq 0 then return R!0;
  else v:=1/e; M[i]:=v*M[i]; det:=(R!e)*det; end if; // mult on the left
  for j in [i+1..d] do r:=-M[j][i]; M[j]:=M[j]+r*M[i]; end for; end for; 
 return det; end function;

intrinsic MooreDeterminant(M::Mtrx) -> Mtrx
{Given a conjugate-symmetric matrix over a quaternion algebra,
 compute its MooreDeterminant via echelonisation.}
 require ISA(Type(BaseRing(M)),AlgQuat): "Matrix be over a quaternion algebra";
 require M eq QuaternionicTranspose(M): "Matrix must be conjugate-symmetric";
 return moore_determinant(M); end intrinsic;

/************************************************************************/

intrinsic ConjugacyClasses(G::GrpMat[AlgAssV]) -> SeqEnum
{The conjugacy classes for the group G.}
 if assigned G`Classes then return G`Classes; end if;
 H:=Expand(G); A:=BaseRing(G); C:=ConjugacyClasses(H);
 G`Classes:=[<c[1],c[2],WriteOver(c[3],A)> : c in C];
 return G`Classes; end intrinsic;

intrinsic CharacterTable(G::GrpMat[AlgAssV]) -> AlgChtr
{Character Table of finite group G.}
 E:=Expand(G); C:=CharacterTable(E); A:=BaseRing(G);
 i:=iso<G->E|x:->RepresentationMatrixOfMatrix(x),y:->WriteOver(y,A)>;
 L:=LiftCharacters(C,i,G);
 for l in L do AssertAttribute(l, "IsIrreducible", true); end for;
 return KnownIrreducibles(G); end intrinsic;

intrinsic IsConjugate
(G::GrpMat[AlgAssV],X::GrpMatElt[AlgAssV],Y::GrpMatElt[AlgAssV]) ->
 BoolElt, Mtrx
{Whether X and Y are conjugate in G, and a conjugating matrix}
 require Parent(X) eq G and Parent(Y) eq G: "Must have same parent";
 EX:=RepresentationMatrixOfMatrix(X); EY:=RepresentationMatrixOfMatrix(Y);
 E:=Expand(G); b,ET:=IsConjugate(E,E!EX,E!EY);
 if b then T:=WriteOver(ET,BaseRing(G)); return b,T; else return b,_; end if;
 end intrinsic;

intrinsic InvariantForms(G::GrpMat[AlgAssV]) -> SeqEnum
{Invariant forms of a matrix group, such that gMg*=M}
 M:=GModule(G); D:=HermitianDual(M); B:=Basis(GHom(Expand(M),Expand(D)));
 A:=BaseRing(G); R:=[RepresentationMatrix(b) : b in Basis(A)];
 d:=Degree(G); n:=Degree(A);
 V:=VectorSpace(BaseRing(A),d*n*d*n); Z:=MatrixAlgebra(BaseRing(A),d*n)!0;
 U:=[InsertBlock(Z,r,1+(i-1)*n,1+(j-1)*n) : r in R, i,j in [1..d]];
 I:=sub<V|[Eltseq(u) : u in U]> meet sub <V|[Eltseq(b) : b in B]>;
 W:=[WriteOver(Matrix(d*n,d*n,Eltseq(b)),A) : b in Basis(I)];
 assert &and[g*w*QuaternionicTranspose(g) eq w : g in Generators(G), w in W];
 return W; end intrinsic;

intrinsic QuaternionicGModule(M::ModGrp,I::AlgMatElt,J::AlgMatElt) -> ModGrp
{Given a GModule and I and J in the endomorphism algebra such that IJ=-JI
 with I^2 and J^2 scalars, split G over the quaternions thereby induced}
 require I*J eq -J*I: "I and J must anti-commute";
 fI:=MinimalPolynomial(I); require Degree(fI) eq 2: "I must be quadratic";
 require Coefficient(fI,1) eq 0: "I must satisfy I^2 = scalar";
 fJ:=MinimalPolynomial(J); require Degree(fJ) eq 2: "J must be quadratic";
 require Coefficient(fJ,1) eq 0: "I must satisfy J^2 = scalar";
 G:=MatrixGroup(M);
 I:=Generic(Parent(I))!I; J:=Generic(Parent(J))!J; P:=Parent(I);
 require IsCoercible(P,G.0): "Group and matrix elements are not compatible";
 GENS:=[P!g : g in Generators(G)];
 require &and[g*I eq I*g : g in GENS]: "I is not an M-endomorphism";
 require &and[g*J eq J*g : g in GENS]: "J is not an M-endomorphism";
 cI:=-Coefficient(fI,0); cJ:=-Coefficient(fJ,0);
 A<i,j,k>:=QuaternionAlgebra<FieldOfFractions(BaseRing(G))|cI,cJ>;
 B:=BlockMatrix(2,1,[Transpose(I-i),Transpose(J-j)]);
 E,T:=EchelonForm(Transpose(B)); 
 R:=Rows(E); K:=[T[t] : t in [i : i in [1..#R] | R[i] eq Parent(R[i])!0]];
 assert &and[Set(Eltseq(k*(I-i))) eq {0} : k in K];
 assert &and[Set(Eltseq(k*(J-j))) eq {0} : k in K];
 E:=EchelonForm(Matrix(K)); COLS:=[]; /* why no function for this? */
 for R in Rows(E) do /* find first nonzero entry */
  U:=[t : t in [1..Ncols(E)] | R[t] ne 0]; // get column numbers for K
  if #U ne 0 then COLS cat:=[U[1]]; end if; end for;
 S:=[Submatrix(E*ChangeRing(G.i,A),[1..#K],COLS) : i in [1..Ngens(G)]];
 assert &and[S[i]*E eq E*ChangeRing(G.i,A) : i in [1..Ngens(G)]];
 RES:=MatrixGroup<#K,A|S>; return GModule(RES); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic WriteOver(M1::GrpMat[FldRat],K::AlgAssV) -> GrpMat
{Write a matrix group over an associative algebra -- inverse of Expand}
 d:=Degree(M1); e:=Degree(K);
 require d mod e eq 0: "Matrix group of wrong degree";
 G:=MatrixGroup<d div e,K | [WriteOverMatrix(g,K) : g in Generators(M1)]>;
 return G; end intrinsic;

intrinsic ElementaryAbelianSeries(M::GrpMat[AlgAssV]) -> GrpMat
{An elementary abelian series for a matrix group over an associative algebra}
 return [WriteOver(x,BaseRing(M)) :
         x in ElementaryAbelianSeries(Expand(M))]; end intrinsic;

intrinsic ElementaryAbelianSeriesCanonical(M::GrpMat[AlgAssV]) -> GrpMat
{The canonical elementary abelian series of a matrix group over an assoc alg}
 return [WriteOver(x,BaseRing(M)) :
         x in ElementaryAbelianSeriesCanonical(Expand(M))]; end intrinsic;

intrinsic ChiefFactors(M::GrpMat[AlgAssV]) -> SeqEnum
{The chief factors of a matrix group over an associative algebra}
 return ChiefFactors(Expand(M)); end intrinsic;

intrinsic ChiefSeries(M::GrpMat[AlgAssV]) -> SeqEnum, SeqEnum
{The chief factors of a matrix group over an associative algebra}
 A,B:=ChiefSeries(Expand(M));
 return [WriteOver(x,BaseRing(M)) :x in A],B; end intrinsic;

intrinsic Radical(M::GrpMat[AlgAssV]) -> GrpMat
{The radical of a matrix group over an associative algebra}
 return WriteOver(Radical(Expand(M)),BaseRing(M)); end intrinsic;

intrinsic RadicalQuotient(M::GrpMat[AlgAssV]) -> GrpPerm, Map, GrpMat
{The radical of a matrix group over an associative algebra}
 P,rho,G:=RadicalQuotient(Expand(M)); R:=WriteOver(G,BaseRing(M));
 _,iso:=IsIsomorphic(M,Expand(M)); return P,iso*rho,R; end intrinsic;

intrinsic SolubleRadical(M::GrpMat[AlgAssV]) -> GrpMat
{The soluble radical of a matrix group over an associative algebra}
 return WriteOver(SolvableRadical(Expand(M)),BaseRing(M)); end intrinsic;

intrinsic SolvableRadical(M::GrpMat[AlgAssV]) -> GrpMat
{The solvable radical of a matrix group over an associative algebra}
 return WriteOver(SolvableRadical(Expand(M)),BaseRing(M)); end intrinsic;

intrinsic Center(M::GrpMat[AlgAssV]) -> GrpMat
{The center of a matrix group over an associative algebra}
 return WriteOver(Center(Expand(M)),BaseRing(M)); end intrinsic;

intrinsic Centre(M::GrpMat[AlgAssV]) -> GrpMat
{The centre of a matrix group over an associative algebra}
 return WriteOver(Center(Expand(M)),BaseRing(M)); end intrinsic;

intrinsic Subgroups(M::GrpMat[AlgAssV]) -> SeqEnum
{Return the subgroups of a matrix group over an associative algebra}
 G:=Expand(M); S:=Subgroups(G); F:=Format(S[1]);
 E:=[rec<F|order:=s`order,length:=s`length,
	          subgroup:=WriteOver(s`subgroup,BaseRing(M))> : s in S];
 AssertAttribute(E,"Subgroups",true); return E; end intrinsic;

intrinsic NormalSubgroups(M::GrpMat[AlgAssV]) -> SeqEnum
{Return the normal subgroups of a matrix group over an associative algebra}
 G:=Expand(M); S:=NormalSubgroups(G); F:=Format(S[1]);
 E:=[rec<F|order:=s`order,length:=s`length,
	          subgroup:=WriteOver(s`subgroup,BaseRing(M))> : s in S];
 AssertAttribute(E,"Subgroups",true); return E; end intrinsic;
 
intrinsic IsNormal(M::GrpMat[AlgAssV],N::GrpMat[AlgAssV]) -> BoolElt
{Return whether N is normal in M, for matrix groups over associative algebras}
 require Generic(M) eq Generic(N): "Not over same base ring, or wrong degrees";
 return IsNormal(Expand(M),Expand(N)); end intrinsic;

/* Various isomorphisms, should they be here? */

intrinsic IsIsomorphic(M1::GrpMat,M2::GrpMat[AlgAssV]) -> BoolElt, Map
{Determine isomorphism of matrix groups, one over an associative algebra}
 E:=Expand(M2);
 h:=iso<M2->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M2))>;
 b,T:=IsIsomorphic(M1,E);
 if not b then return b,_; else return b,T*Inverse(h); end if; end intrinsic;

intrinsic IsIsomorphic(M1::GrpPC,M2::GrpMat[AlgAssV]) -> BoolElt, Map
{Determine isomorphism of matrix group over associative algebra and PC-group}
 E:=Expand(M2);
 h:=iso<M2->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M2))>;
 b,T:=IsIsomorphic(M1,E);
 if not b then return b,_; else return b,T*Inverse(h); end if; end intrinsic;

intrinsic IsIsomorphic(M1::GrpPerm,M2::GrpMat[AlgAssV]) -> BoolElt, Map
{Determine isomorphism of matrix group over associative algebra and perm group}
 E:=Expand(M2);
 h:=iso<M2->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M2))>;
 b,T:=IsIsomorphic(M1,E);
 if not b then return b,_; else return b,T*Inverse(h); end if; end intrinsic;

intrinsic IsIsomorphic(M1::GrpMat[AlgAssV],M2::GrpMat) -> BoolElt, Map
{Determine isomorphism of matrix groups, one over an associative algebra}
 E:=Expand(M1);
 h:=iso<M1->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M1))>;
 b,T:=IsIsomorphic(E,M2);
 if not b then return b,_; else return b,h*T; end if; end intrinsic;

intrinsic IsIsomorphic(M1::GrpMat[AlgAssV],M2::GrpPC) -> BoolElt, Map
{Determine isomorphism of matrix group over associative algebra and PC-group}
 E:=Expand(M1);
 h:=iso<M1->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M1))>;
 b,T:=IsIsomorphic(E,M2);
 if not b then return b,_; else return b,h*T; end if; end intrinsic;

intrinsic IsIsomorphic(M1::GrpMat[AlgAssV],M2::GrpPerm) -> BoolElt, Map
{Determine isomorphism of matrix group over associative algebra and perm group}
 E:=Expand(M1);
 h:=iso<M1->E|x:->RepresentationMatrixOfMatrix(x),
	      x:->WriteOverMatrix(x,BaseRing(M1))>;
 b,T:=IsIsomorphic(E,M2);
 if not b then return b,_; else return b,h*T; end if; end intrinsic;
