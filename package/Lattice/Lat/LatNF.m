
freeze;

/* The totally positive case is based on stuff with Gael Collinet */
/* The Lorentzian case comes from Gael Collinet more completely */

// maps between lattices ?

////////////////////////////////////////////////////////////////////////

declare type LatNF[LatNFElt];
declare attributes LatNF : BM,IP,GRAM,K,Js; // IP can be unknown
declare attributes LatNFElt : vec,coord,parent;

// convex hull

////////////////////////////////////////////////////////////////////////

intrinsic Hash(x::LatNFElt) -> RngIntElt {hash}
 return Hash(x`vec); end intrinsic;

function new_nf_lat_elt(L,cv)
 E:=Eltseq(cv); assert &and[E[j] in L`Js[j] : j in [1..#E]];
 ans:=New(LatNFElt); ans`coord:=cv; ans`vec:=cv*L`BM;
 ans`parent:=L; return ans; end function;

intrinsic Print(v::LatNFElt,level::MonStgElt) {Print number field lattice elt}
 printf "%o",v`vec; return; end intrinsic;

intrinsic Parent(v::LatNFElt) -> LatNF {parent lattice}
 return v`parent; end intrinsic;

intrinsic 'in'(v::ModTupRngElt,L::LatNF) -> BoolElt,ModTupFldElt
{Determine if a vector is in a number field lattice, and if so the coordinates}
 try v:=ChangeRing(v,L`K);
 catch err; require false: "Vector doesn't coerce into lattice field"; end try;
 require Degree(L) eq Degree(v): "Vector and lattice must have same degree";
 b,sol:=IsConsistent(L`BM,v); if not b then return b,_; end if;
 E:=Eltseq(sol); b:=&and[E[i] in L`Js[i] : i in [1..#E]];
 return b,sol; end intrinsic;

intrinsic IsIdentical(A::LatNF,B::LatNF) -> BoolElt
{Whether two number fields lattices are equal
(same basis, Gram, and ideals, and inner product if applicable)}
 return A`K eq B`K and Degree(A) eq Degree(B) and Rank(A) eq Rank(B)
        and A`BM eq B`BM and A`GRAM eq B`GRAM and A`IP eq B`IP
        and A`Js eq B`Js; end intrinsic;

intrinsic 'in'(v::LatNFElt,L::LatNF) -> BoolElt,ModTupFldElt
{Determine if a lattice element is in a number field lattice}
 if IsIdentical(Parent(v),L) then return true,v`coord; end if;
 return 'in'(v`vec,L); end intrinsic;

intrinsic IsCoercible(L::LatNF,e::.) -> BoolElt,LatNFElt {coerce}
 if Type(e) eq LatNFElt then return IsCoercible(L,Eltseq(e`vec)); end if;
 if Type(e) eq ModTupFldElt then return IsCoercible(L,Eltseq(e)); end if;
 if Type(e) eq SeqEnum then
  if #e ne Degree(L) then return false,"Illegal coercion"; end if;
  try e:=ChangeUniverse(e,L`K); e:=Vector(e);
  catch err; return false,"Illegal coercion"; end try;
  b,coord:='in'(e,L); if not b then return false,"Illegal coercion"; end if;
  return true,new_nf_lat_elt(L,coord); end if;
 return false,"Illegal coercion"; end intrinsic;

intrinsic '.'(L::LatNF,i::RngIntElt) -> LatNFElt
{The ith generator of the basis of a number field lattice}
 require i ge 0 and i le Nrows(L`BM): "Second argument not in required range";
 require i eq 0 or IsOne(L`Js[i]): "The ith ideal is not trivial";
 e:=new_nf_lat_elt // works for i eq 0 also!
    (L,Vector([L`K | j eq i select 1 else 0 : j in [1..Rank(L)]]));
 return e; end intrinsic;

intrinsic CoordinatesToLattice(L::LatNF,S::SeqEnum) -> LatNFElt
{Given suitable coordinates on the pseudobasis, construct the lattice vector}
 try S:=ChangeUniverse(S,L`K); require #S eq Rank(L): "Sequence length wrong";
 catch e; require false: "Cannot coerce sequence into number field"; end try;
 v:=Vector(S)*L`BM; require IsCoercible(L,v): "Coordinates are not in lattice";
 return L!v; end intrinsic;

intrinsic CoordinatesToLattice(L::LatNF,v::ModTupFldElt) -> LatNFElt
{Given suitable coordinates on the pseudobasis, construct the lattice vector}
 return CoordinatesToLattice(L,Eltseq(v)); end intrinsic;

intrinsic '+'(v::LatNFElt,w::LatNFElt) -> LatNFElt {add}
 require IsIdentical(Parent(v),Parent(w)): "Vectors must have same Parent";
 return new_nf_lat_elt(Parent(v),v`coord+w`coord); end intrinsic;

intrinsic '-'(v::LatNFElt,w::LatNFElt) -> LatNFElt {subtract}
 require IsIdentical(Parent(v),Parent(w)): "Vectors must have same Parent";
 return new_nf_lat_elt(Parent(v),v`coord-w`coord); end intrinsic;

intrinsic '-'(v::LatNFElt) -> LatNFElt {negate}
 return new_nf_lat_elt(Parent(v),-v`coord); end intrinsic;

intrinsic '/'(v::LatNFElt,s:RngElt) -> LatNFElt {scalar division}
 require s ne 0: "Cannot divide by zero"; return '*'(v,1/s); end intrinsic;

intrinsic '*'(s::Any,v::LatNFElt) -> LatNFElt {scalar multiply}
 require ISA(Type(s),RngElt): "Invalid type in mult"; L:=Parent(v);
 require IsCoercible(L`K,s): "Element must coerce into lattice field";
 s:=(L`K)!s; b,coord:='in'(s*v`vec,L);
 require b: "Illegal scalar multiplication (result not in lattice)";
 return new_nf_lat_elt(L,coord); end intrinsic;

intrinsic '*'(T::Mtrx,v::LatNFElt) -> LatNFElt {basis transformation}
 require Nrows(T) eq Ncols(T): "Transformation matrix must be square";
 require Determinant(T) ne 0: "Transformation must be invertible";
 L:=Parent(v); require Nrows(T) eq Nrows(L`BM): "Matrix size != basis size";
 try T:=ChangeRing(T,L`K); b,coord:='in'(v`coord*T*L`BM,L);
 catch e; require false: "Element must coerce into lattice field"; end try;
 require b: "Illegal scalar multiplication (result not in lattice)";
 return new_nf_lat_elt(L,coord); end intrinsic;

intrinsic '*'(v::LatNFElt,s::Any) -> LatNFElt {scalar multiply}
 require ISA(Type(s),RngElt): "Invalid type in mult"; L:=Parent(v);
 require IsCoercible(L`K,s): "Ring element must coerce into lattice field";
 return s*v; end intrinsic;

intrinsic '*'(v::LatNFElt,T::Mtrx) -> LatNFElt {ambient transform}
 require Nrows(T) eq Ncols(T): "Transformation matrix must be square";
 L:=Parent(v); require Degree(L) eq Nrows(T): "Vector/matrix not same degree";
 require Determinant(T) ne 0: "Transformation must be invertible"; // hackish
 try T:=ChangeRing(T,L`K);  w:=Vector(v)*T;
 catch e; require false: "Matrix must coerce into lattice field";  end try;
 require IsCoercible(L,w): "Resulting vector must be in lattice";
 return L!w; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '^'(v::LatNFElt,M::Mtrx) -> Setq[LatNFElt] {group action}
 require Nrows(M) eq Ncols(M): "Matrix must be square";
 try L:=Parent(v); M:=ChangeRing(M,L`K);
 catch err; require false: "Matrix must coerce into lattice field"; end try;
 require Rank(L) eq Nrows(M): "Rank of matrix not number of rows of matrix";
 w:=v`coord*M*L`BM; b,w:=IsCoercible(L,w);
 require b: "Matrix must map v to a lattice element"; return w; end intrinsic;

intrinsic '^'(v::LatNFElt,g::GrpMatElt) -> Setq[LatNFElt] {group action}
 return v^Matrix(g); end intrinsic;

intrinsic '^'(S::Setq[LatNFElt],g::GrpMatElt) -> Setq {orbit of group action}
 M:=Matrix(g); return {v^M : v in S}; end intrinsic; // could be more efficient

intrinsic '^'(E::SeqEnum[LatNFElt],g::GrpMatElt) -> SeqEnum {grp action orbit}
 M:=Matrix(g); return [v^M : v in E]; end intrinsic; // could be more efficient

function orbit_stab(G,v,f) // from MyStabGens package/Group/GrpMat/GLConjugate
 n:=Ngens(G); O:={@ v @}; P:=[Id(G)]; S:=[]; i:=0;
 while i lt #O do i:=i+1;
  for j in [1..n] do x:=P[i]*G.j; vx:=f(x,v); k:=Index(O,vx);
   if k eq 0 then Include(~O,vx); Append(~P,x);
   else x:=x*P[k]^(-1); assert f(x,v) eq v;
    if not IsOne(x) and x notin S and x^(-1) notin S then Append(~S,x); end if;
    end if; end for; end while; return O,S; end function;
 
intrinsic Stabilizer(G::GrpMat,S::Setq[LatNFElt]) -> GrpMat {stabilizer}
 orb,stab:=orbit_stab(G,S,func<x,v|v^x>); return sub<G|stab>; end intrinsic;

intrinsic Orbit(G::GrpMat,S::Setq[LatNFElt]) -> Setq {group action on sets}
 orb,stab:=orbit_stab(G,S,func<x,v|v^x>); return orb; end intrinsic;

intrinsic '^'(S::Setq[LatNFElt],G::GrpMat) -> Setq {group action orbit on sets}
 orb,stab:=orbit_stab(G,S,func<x,v|v^x>); return orb; end intrinsic;

intrinsic Stabilizer(G::GrpMat,E::SeqEnum[LatNFElt]) -> GrpMat {stabilizer}
 orb,stab:=orbit_stab(G,E,func<x,v|v^x>); return sub<G|stab>; end intrinsic;

intrinsic Orbit(G::GrpMat,E::SeqEnum[LatNFElt]) -> Setq {group action on sets}
 orb,stab:=orbit_stab(G,E,func<x,v|v^x>); return orb; end intrinsic;

intrinsic '^'(E::SeqEnum[LatNFElt],G::GrpMat) -> Setq {grp action on seq}
 orb,stab:=orbit_stab(G,E,func<x,v|v^x>); return orb; end intrinsic;

intrinsic Stabilizer(G::GrpMat,v::LatNFElt) -> GrpMat {stabilizer}
 orb,stab:=orbit_stab(G,v,func<x,v|v^x>); return sub<G|stab>; end intrinsic;

intrinsic Orbit(G::GrpMat,v::LatNFElt) -> Setq[LatNFElt] {orbit}
 orb,stab:=orbit_stab(G,v,func<x,v|v^x>); return orb; end intrinsic;

intrinsic '^'(v::LatNFElt,G::GrpMat) -> Setq[LatNFElt] {orbit of group action}
 orb,stab:=orbit_stab(G,v,func<x,v|v^x>); return orb; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(v::LatNFElt,w::LatNFElt) -> BoolElt
{Whether two number field lattice vectors are equal}
 require IsIdentical(Parent(v),Parent(w)): "Vectors must have same Parent";
 return v`coord eq w`coord; end intrinsic;

intrinsic 'ne'(v::LatNFElt,w::LatNFElt) -> BoolElt
{Whether two number field lattice vectors are not equal}
 require IsIdentical(Parent(v),Parent(w)): "Vectors must have same Parent";
 return v`coord ne w`coord; end intrinsic;

intrinsic IsZero(v::LatNFElt) -> BoolElt
{Whether a number field lattice vector is zero}
 return IsZero(v`coord); end intrinsic;

intrinsic InnerProduct(v::LatNFElt,w::LatNFElt) -> FldElt
{The inner product of two number field lattice vectors}
 require IsIdentical(Parent(v),Parent(w)): "Vectors must have same Parent";
 a:=Eltseq(v`coord*PseudoGramMatrix(Parent(v))); b:=Eltseq(w`coord);
 return &+[a[i]*b[i] : i in [1..#a]];  end intrinsic;

intrinsic Norm(v::LatNFElt) -> FldElt
{The inner product of two number field lattice vectors}
 return InnerProduct(v,v); end intrinsic;

intrinsic Vector(v::LatNFElt) -> ModTupFldElt
{The underlying (ambient) vector of a number field lattice vector}
 return Vector(v`vec); end intrinsic;

intrinsic Eltseq(v::LatNFElt) -> SeqEnum
{The underlying (ambient) vector of a number field lattice vector}
 return Eltseq(v`vec); end intrinsic;

intrinsic Coordinates(v::LatNFElt) -> ModTupFldElt
{The coordinates of a given number field lattice vector, in terms of the basis}
 return v`coord; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Module(L::LatNF : IP:=true) -> ModDed
{Given a number field lattice, return the corresponding Dedekind module}
 require not IP or L`IP ne 0: "The ambient inner product must be known";
 O:=Integers(L`K); F:=FieldOfFractions(O);
 if Nrows(L`BM) eq 0 then M:=Module(Rows(Matrix(O,0,Degree(L),[])));
  if IP then ChangeInnerProduct(~M,ChangeRing(L`IP,F)); end if;
  return M; end if;
 d:=LCM([d where _,d:=IsIntegral(e) : e in Eltseq(L`BM)]);
 B:=ChangeRing(L`BM*d,O); M:=Module([<L`Js[i]/d,B[i]> : i in [1..#L`Js]]);
 if IP then ChangeInnerProduct(~M,ChangeRing(L`IP,F)); end if;
 return M; end intrinsic;

function new_nf_lat(BM,GM : IP:=0,Js:=[]) BR:=BaseRing(BM);
 assert BR eq BaseRing(GM); assert ISA(Type(BR),FldNum);
 if not IsAbsoluteField(BR) then
  "WARNING: moving lattice to absolute number field extension";
  A:=AbsoluteField(BR); BM:=ChangeRing(BM,A); GM:=ChangeRing(BM,A);
  if IP ne 0 then IP:=ChangeRing(BM,A); end if;
  Js:=[ideal<Integers(A)|[A!a : a in Generators(J)]> : J in Js];
  return new_nf_lat(BM,GM : IP:=IP,Js:=Js); end if;
 L:=New(LatNF); L`K:=BaseRing(BM); O:=Integers(L`K);
 if #Js eq 0 then Js:=[Parent(1*O) | 1*O : i in [1..Nrows(BM)]]; end if;
 L`BM:=BM; L`GRAM:=GM; L`IP:=IP; L`Js:=Js;
 if IP ne 0 then assert BM*IP*Transpose(BM) eq GM; end if;
 return L; end function;

intrinsic NumberFieldLattice
(K::FldNum,d::RngIntElt : Gram:=IdentityMatrix(K,d)) -> LatNF
{The standard d-dimensional lattice over a number field,
 with the inner product matrix being given by the optional argument Gram}
 require IsCoercible(MatrixAlgebra(K,d),Gram):
 "Gram matrix must be d-by-d and coerce into K"; Gram:=ChangeRing(Gram,K);
 require IsSymmetric(Gram): "Gram matrix must be symmetric";
 require Determinant(Gram) ne 0: "Gram matrix must be invertible";
 return new_nf_lat(IdentityMatrix(K,d),Gram : IP:=Gram); end intrinsic;

intrinsic NumberFieldLattice(D::ModDed) -> LatNF
{Given a Dedekind module, return the corresponding number field lattice}
 require not InternalDedModHasDenom(D):
 "The Dedekind module has a denominator, and is likely not torsionfree";
 Q:=PseudoMatrix(D); K:=NumberField(BaseRing(D));
 BM:=ChangeRing(Matrix(Q),K); IPM:=ChangeRing(InnerProductMatrix(D),K);
 GM:=BM*IPM*Transpose(BM);
 X:=new_nf_lat(BM,GM : IP:=IPM,Js:=CoefficientIdeals(Q));
 if IsFree(X) then X:=SimpleLattice(X); end if; return X; end intrinsic;

intrinsic NumberFieldLattice
(S::SeqEnum[ModTupFldElt] :
 InnerProduct:=0,Gram:=0,Ideals:=[],Independent:=false)-> LatNF
{Determine a number field lattice from vectors over a number field}
 U:=Universe(S); K:=BaseRing(U); deg:=Degree(U); IP:=InnerProduct;
 M:=Matrix(S); r:=Rank(M); O:=Integers(K); F:=FieldOfFractions(O);
 require ISA(Type(K),FldNum): "Vectors must be over a number field";
 if #Ideals eq 0 then Ideals:=[Parent(1*O) | 1*O : i in [1..#S]]; end if;
 require #Ideals eq #S: "Number of ideals must equal nunmber of vectors";
 require &and[not IsZero(j) : j in Ideals]: "Ideals cannot be zero";
 require NumberField(Ring(Universe(Ideals))) eq K:
  "The number field for the ideals and the vectors must be same";
 if IP eq 0 and Gram eq 0 then IP:=IdentityMatrix(K,deg); end if;
 if IP ne 0 then require Nrows(IP) eq deg and Ncols(IP) eq Nrows(IP):
  "Inner product must be square with same degree as the vectors"; end if; 
 if IP ne 0 and Gram ne 0 then require Gram eq M*IP*Transpose(M):
  "Both Gram and inner product given and not coherent"; end if;
 if IP ne 0 then Gram:=M*IP*Transpose(M); end if;
 require IP eq 0 or Determinant(IP) ne 0: "Inner product must be invertible";
 require Nrows(Gram) eq #S and Ncols(Gram) eq #S:
 "Gram matrix must be square and same degree as the number of basis elements";
 try Gram:=ChangeRing(Gram,K);
  catch e; require false: "Gram matrix must coerce into number field"; end try;
 if r eq Nrows(M) then // case of independent rows
  require Determinant(Gram) ne 0: "Gram matrix must have nonzero determinant";
  return new_nf_lat(M,Gram : IP:=IP,Js:=Ideals); end if;
 require not Independent: "Vectors must be independent"; // non-independent
 d:=LCM([d where _,d:=IsIntegral(e) : e in Eltseq(M)]);
 B:=ChangeRing(M*d,O); X:=Module([<Ideals[i]/d,B[i]> : i in [1..#S]]);
 if IP ne 0 then ChangeInnerProduct(~X,ChangeRing(IP,F)); // inner prod given
  return NumberFieldLattice(X); end if;
 U:=NumberFieldLattice(X); C:=Solution(M,U`BM);
 u:=Nrows(U`BM); Z:=Gram; g:=Nrows(Z);
 G:=Matrix(u,u,[&+[E[k]*C[j][k] :k in [1..g]] where E:=C[i]*Z :i,j in [1..u]]);
 require Determinant(G) ne 0: "The pseudoGram matrix must be invertible";
 X:=new_nf_lat(U`BM,G : Js:=U`Js); S:=Solution(U`BM,M);
 b:=&and[(S[i]*G*Transpose(Matrix(S[j])))[1] eq Gram[i][j] : i,j in [1..g]];
 require b: "The Gram matrix is inconsistent on the given dependent vectors";
 return X; end intrinsic;

// allow a sequence of LatNFElt's ? no, that can use sub<>

////////////////////////////////////////////////////////////////////////

intrinsic Print(L::LatNF,level::MonStgElt) {Print number field lattice}
 printf "Number field lattice over %o",L`K;
 SB:=(Nrows(L`BM) eq Ncols(L`BM)) and L`BM eq 1;
 STR:=IsSimple(L) select "" else "pseudo";
 if Nrows(L`BM) eq Ncols(L`BM) and L`BM eq 1 then printf " in standard basis";
 else printf " with %obasis matrix\n%o",STR,L`BM; end if;
 if L`IP ne 0 and L`IP ne 1 then printf "\nand inner product matrix\n%o",L`IP;
 elif L`IP eq 0 and ((not SB) or L`GRAM ne 1) then
      printf "\nand %oGram matrix\n%o",STR,L`GRAM; end if;
 if not &and[J eq 1*Integers(L`K) : J in L`Js] then
  printf "\nand coefficient ideals\n%o",L`Js; end if; return; end intrinsic;

intrinsic SubConstr(L::LatNF,E::SeqEnum) -> LatNF, Map {sub}
 require #E eq 0: "Generic sequence must be empty in sub<> of LatNF";
 M:=Matrix(L`K,0,Degree(L),[]); G:=Matrix(L`K,0,0,[]);
 return new_nf_lat(M,G : IP:=L`IP),_; end intrinsic;

intrinsic SubConstr(L::LatNF,E::SeqEnum[ModTupFldElt]) -> LatNF, Map {sub}
 if #Set(E) ne #E then E:=[e : e in Set(E) | not IsZero(E)]; end if;
 try E:=[ChangeRing(e,L`K) : e in E]; M:=Matrix(E); r:=Nrows(M);
 catch err; require false: "Vectors must coerce into lattice field"; end try;
 if Nrows(L`BM) eq 0 then return L; end if;
 if #E eq 0 then return SubConstr(L,E); end if;
 require &and[e in L : e in E]: "The vectors must be in the lattice";
 if Rank(M) eq r then // given vectors are independent, up to 0 and repeats
  G:=Matrix(r,r,[InnerProduct(L!E[i],L!E[j]) : i,j in [1..r]]);
  X:=new_nf_lat(M,G : IP:=L`IP); return X,_; end if;
 if L`IP ne 0 then // inner product given
  M:=Module(L); S:=sub<M|[M!e : e in E]>; X:=NumberFieldLattice(S);
  if not IsSimple(X) and IsFree(X) then X:=SimpleLattice(X); end if;
  return X,_; end if;
 M:=Module(L : IP:=false); S:=sub<M|[M!e : e in E]>; // create GRAM from data
 Y:=NumberFieldLattice(S); u:=Nrows(Y`BM); g:=Nrows(L`GRAM);
 C:=[c where _,c:='in'(Y`BM[i],L) : i in [1..u]]; // Solution
 G:=[&+[E[k]*C[j][k] : k in [1..g]] where E:=C[i]*L`GRAM : i,j in [1..u]];
 G:=Matrix(u,u,G); X:=new_nf_lat(Y`BM,G : Js:=Y`Js);
 if IsFree(X) then X:=SimpleLattice(X); end if; return X,_; end intrinsic;

intrinsic SubConstr(L::LatNF,E::SeqEnum[LatNFElt]) -> LatNF, Map {sub}
 return SubConstr(L,[e`vec : e in E]); end intrinsic;

intrinsic 'eq'(A::LatNF,B::LatNF) -> BoolElt
{Whether two number fields lattices are equal, namely subsets of each other
 respecting the inner product and/or Gram matrix}
 require Degree(A) eq Degree(B): "Lattices must be same degree";
 return A subset B and B subset A; end intrinsic;

intrinsic 'ne'(A::LatNF,B::LatNF) -> BoolElt
{Whether two number fields lattices are equal
 (same basis, and Gram, and ideals, and inner product if applicable)}
 return not (A eq B); end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic '+'(A::LatNF,B::LatNF) -> LatNF
{The addition (join) of two number field lattices}
 require Degree(A) eq Degree(B): "Lattices must have same degree";
 require A`K eq B`K: "Lattices must be over the same number field";
 require A`IP eq B`IP: "Lattices must have same ambient inner product matrix";
 if Rank(A) eq 0 then return B; end if; if Rank(B) eq 0 then return A; end if;
 M:=VerticalJoin(A`BM,B`BM); R:=0; S:=0;
 if A`IP ne 0 then // inner product is known
  if Rank(M) eq Nrows(M) then J:=A`Js cat B`Js; // independent case
   return new_nf_lat(M,M*A`IP*Transpose(M) : IP:=A`IP, Js:=J); end if;
  return NumberFieldLattice(Module(A)+Module(B)); end if;
 if Rank(M) eq Rank(A) then R:=A; S:=B; end if;
 if Rank(M) eq Rank(B) then R:=B; S:=A; end if;
 require R cmpne 0: "Ambient inner product unknown";
 Y:=NumberFieldLattice(Module(A : IP:=false)+Module(B : IP:=false));
 C:=Solution(R`BM,Y`BM); g:=Nrows(R`GRAM); u:=Nrows(C);
 G:=[&+[E[k]*C[j][k] : k in [1..g]] where E:=C[i]*R`GRAM : i,j in [1..u]];
 X:=new_nf_lat(Y`BM,Matrix(u,u,G) : Js:=Y`Js);
 b:=&and[InnerProduct(X!g,X!h) eq InnerProduct(g,h) : g,h in Generators(S)];
 require b: "Given Gram matrices are not consistent"; return X; end intrinsic;

intrinsic 'meet'(A::LatNF,B::LatNF) -> LatNF
{The intersection of two number field lattices}
 require Degree(A) eq Degree(B): "Lattices must have same degree";
 require A`K eq B`K: "Lattices must be over the same number field";
 require A`IP eq B`IP: "Lattices must have same ambient inner product matrix";
 if Rank(A) eq 0 then return A; end if; if Rank(B) eq 0 then return B; end if;
 if IsSublattice(A,B) then return B; end if;
 if IsSublattice(B,A) then return A; end if;
 if A`IP ne 0 then return NumberFieldLattice(Module(A) meet Module(B)); end if;
 M:=Module(A : IP:=false); N:=Module(B : IP:=false);
 X:=NumberFieldLattice(M meet N); u:=Nrows(X`BM);
 sA:=Solution(A`BM,X`BM); gA:=Nrows(A`GRAM);
 sB:=Solution(B`BM,X`BM); gB:=Nrows(B`GRAM);
 GA:=[&+[E[k]*sA[j][k] : k in [1..gA]] where E:=sA[i]*A`GRAM : i,j in [1..u]];
 GB:=[&+[E[k]*sB[j][k] : k in [1..gB]] where E:=sB[i]*B`GRAM : i,j in [1..u]];
 require GA eq GB: "The lattices do not have consistent Gram matrices";
 return new_nf_lat(X`BM,Matrix(u,u,GA) : Js:=X`Js); end intrinsic;

intrinsic DirectSum(A::LatNF,B::LatNF) -> LatNF
{The direct sum of two number field lattices}
 require BaseRing(A) eq BaseRing(B): "Lattices must have same base ring";
 if A`IP ne 0 and B`IP ne 0 then I:=DiagonalJoin(A`IP,B`IP); else I:=0; end if;
 BM:=DiagonalJoin(A`BM,B`BM); G:=DiagonalJoin(A`GRAM,B`GRAM);
 return new_nf_lat(BM,G : IP:=I,Js:=A`Js cat B`Js); end intrinsic;

intrinsic DirectSum(S::SeqEnum[LatNF]) -> LatNF
{The direct sum of a sequence of number field lattices}
 require #S ne 0: "The sequence of number field lattice cannot be empty";
 if #S eq 1 then return S[1]; end if; A:=S[1];
 for i in [2..#S] do A:=DirectSum(A,S[i]); end for; return A; end intrinsic;

intrinsic '*'(T::Mtrx,L::LatNF) -> LatNF
{Transform the coordinates of a number field lattice by the given matrix}
 try T:=ChangeRing(T,BaseRing(L));
 catch e; error "Transformation matrix must coerce into lattice field";end try;
 require Ncols(T) eq Nrows(T): "Transformation matrix must be square";
 require Nrows(T) eq Dimension(L): "Basis must be same size of transform";
 require Determinant(T) ne 0: "Transformation must be invertible";
 if IsSimple(L) then R:=Rows(T*L`BM); G:=T*GramMatrix(L)*Transpose(T);
 else C:=[(v`coord)*T : v in Generators(L)]; r:=Rank(L); g:=#C;
      M:=[&+[W[k]*C[j][k] where W:=C[i]*L`GRAM : k in [1..r]] : i,j in [1..g]];
      G:=Matrix(g,g,M); R:=[c*(L`BM) : c in C]; end if;
 return NumberFieldLattice(R : InnerProduct:=L`IP, Gram:=G); end intrinsic;

intrinsic '*'(TJ::PMat,L::LatNF) -> LatNF
{Multiply the pseudobasis by T and the coefficient ideals by the J sequence}
 K:=NumberField(Order(TJ)); T:=Matrix(TJ); J:=CoefficientIdeals(TJ);
 require K eq L`K: "Fields of pseudomatrix and number field lattice not same";
 require Determinant(T) ne 0: "Transformation must be invertible";
 require Nrows(T) eq Dimension(L): "Basis must be same size of transform";
 if Rank(L) eq 0 then return L; end if; G:=T*PseudoGramMatrix(L)*Transpose(T);
 return new_nf_lat(T*L`BM,G : IP:=L`IP,Js:=[L`Js[i]*J[i] : i in [1..#J]]);
 end intrinsic;

intrinsic '*'(L::LatNF,T::Mtrx) -> LatNF
{Transformation on the ambient vectors of a number field lattice}
 try T:=ChangeRing(T,BaseRing(L));
 catch e; error "Transformation matrix must coerce into lattice field";end try;
 require Ncols(T) eq Nrows(T): "Transformation matrix must be square";
 require Ncols(T) eq Degree(L): "Basis must be same size of transform";
 require Determinant(T) ne 0: "Transformation must be invertible";
 if L`IP ne 0 then R:=GeneratorMatrix(L)*T; // TT:=Transpose(T);
  return NumberFieldLattice(Rows(R) : InnerProduct:=L`IP); end if;
 R:=GeneratorMatrix(L)*T; u:=Nrows(R); g:=Rank(L); b,S:=IsConsistent(L`BM,R);
 require b: "Transformation must retain basis span when inner product unknown";
 G:=[&+[E[k]*S[j][k] : k in [1..g]] where E:=S[i]*L`GRAM : i,j in [1..u]];
 return NumberFieldLattice(Rows(R) : Gram:=Matrix(u,u,G)); end intrinsic;
 // should transform the inner product also?! // don't think so

intrinsic '*'(J::RngOrdFracIdl,L::LatNF) -> LatNF
{Multiply all the fractional ideals of a number field lattice by given ideal}
 require NumberField(Ring(Parent(J))) eq L`K:
 "Ideal and lattice must be over the same number field";
 require not IsZero(J): "The ideal must be nonzero";
 return new_nf_lat(L`BM,L`GRAM : IP:=L`IP,Js:=[J*X : X in L`Js]);
 end intrinsic;

intrinsic '*'(L::LatNF,J::RngOrdFracIdl) -> LatNF
{Multiply all the fractional ideals of a number field lattice by given ideal}
 return J*L; end intrinsic;

intrinsic '*'(s::Any,L::LatNF) -> LatNF
{Given a lattice and a nonzero field element, scale the basis vectors}
 require ISA(Type(s),RngElt): "Invalid type in mult";
 require IsCoercible(L`K,s): "Ring element must coerce into lattice field";
 return BasisScaling(L,s); end intrinsic;

intrinsic '*'(L::LatNF,s::Any) -> LatNF
{Given a lattice and a nonzero field element, scale the basis vectors}
 require ISA(Type(s),RngElt): "Invalid type in mult";
 require IsCoercible(L`K,s): "Ring element must coerce into lattice field";
 return BasisScaling(L,s); end intrinsic;

intrinsic '/'(L::LatNF,s::RngElt) -> LatNF
{Given a lattice and a nonzero field element, scale the basis vectors}
 require IsCoercible(L`K,s): "Ring element must coerce into lattice field";
 require s ne 0: "s cannot be 0"; return BasisScaling(L,1/s); end intrinsic;

intrinsic '/'(L::LatNF,J::RngOrdFracIdl) -> LatNF
{Divide all the fractional ideals of a number field lattice by given ideal}
 require not IsZero(J): "The ideal must be nonzero";
 return (1/J)*L; end intrinsic;

intrinsic BasisScaling(L::LatNF,s::RngElt) -> LatNF
{Given a lattice and a nonzero field element, scale the basis vectors}
 try s:=(L`K)!s; require s ne 0: "s cannot be 0";
 catch e; require false: "Element must coerce into lattice field"; end try;
 return new_nf_lat(s*L`BM,s^2*L`GRAM : IP:=L`IP,Js:=L`Js); end intrinsic;

intrinsic InnerProductScaling(L::LatNF,s::RngElt) -> LatNF
{Given a lattice and a nonzero field element, scale the inner product}
 try s:=(L`K)!s; require s ne 0: "s cannot be 0";
 catch e; require false: "Element must coerce into lattice field"; end try;
 return new_nf_lat(L`BM,s*L`GRAM : IP:=s*L`IP,Js:=L`Js); end intrinsic;

intrinsic MakeAmbientInnerProduct(~L::LatNF,IP::Mtrx)
{Attach the given inner product matrix to a number field lattice}
 require L`IP eq 0: "The lattice already has an ambient inner product";
 try IP:=ChangeRing(IP,L`K); r:=Nrows(IP);
 catch e; require false: "The matrix does not coerce in the field"; end try;
 require r eq Ncols(IP): "Inner product matrix must be square";
 require r eq Degree(L): "Degree of inner product must be same as lattice";
 require L`BM*IP*Transpose(L`BM) eq L`GRAM:
 "The inner product does not induce the known pseudoGram matrix";
 L`IP:=IP; end intrinsic;

////////////////////////////////////////////////////////////////////////

intrinsic Basis(L::LatNF) -> SeqEnum[ModTupFldElt]
{The basis (given as rows) of a simple number field lattice}
 require IsSimple(L): "The number field lattice must be simple";
 return Rows(L`BM); end intrinsic;

intrinsic BasisMatrix(L::LatNF) -> Mtrx
{The matrix of the basis of a simple number field lattice}
 require IsSimple(L): "The number field lattice must be simple";
 return L`BM; end intrinsic;

intrinsic PseudoBasis(L::LatNF) -> SeqEnum[ModTupFldElt]
{The pseudobasis (given as rows) of a number field lattice}
 return Rows(L`BM); end intrinsic;

intrinsic PseudoBasisMatrix(L::LatNF) -> Mtrx
{The matrix of the pseudobasis of a number field lattice}
 return L`BM; end intrinsic;

intrinsic PseudoMatrix(L::LatNF) -> PMat
{The pseudomatrix of a number field lattice}
 return PseudoMatrix(L`Js,L`BM); end intrinsic;

intrinsic CoefficientIdeals(L::LatNF) -> SeqEnum
{The coefficient ideals of a number field lattice}
 return L`Js; end intrinsic;

intrinsic Generators(L::LatNF) -> SeqEnum
{A sequence of generators for a number field lattice}
 if IsSimple(L) then return [L.i : i in [1..Rank(L)]]; end if;
 return ChangeUniverse(Rows(GeneratorMatrix(L)),L); end intrinsic;

intrinsic GeneratorMatrix(L::LatNF) -> SeqEnum
{A matrix whose rows are generators a number field lattice}
 if IsSimple(L) then return Matrix([Vector(L.i) : i in [1..Rank(L)]]); end if;
 return ChangeRing(GeneratorMatrix(Module(L : IP:=false)),L`K); end intrinsic;

intrinsic InnerProductMatrix(L::LatNF) -> Mtrx
{The inner product matrix of a number field lattice (if given)}
 require L`IP ne 0: "Inner product matrix is not known";
 return L`IP; end intrinsic;

intrinsic GramMatrix(L::LatNF) -> Mtrx
{The Gram matrix of a simple number field lattice}
 require IsSimple(L): "The lattice must be given a simple lattice";
 return L`GRAM; end intrinsic;

intrinsic PseudoGramMatrix(L::LatNF) -> Mtrx
{The Gram matrix of the pseudobasis of a number field lattice}
 return L`GRAM; end intrinsic;

intrinsic Rank(L::LatNF) -> RngIntElt
{The rank (dimension) of a number field lattice}
 return Nrows(L`BM); end intrinsic;

intrinsic Dimension(L::LatNF) -> RngIntElt
{The dimension (rank) of a number field lattice}
 return Nrows(L`BM); end intrinsic;

intrinsic Degree(L::LatNF) -> RngIntElt
{The degree of a number field lattice (that is, of its ambient)}
 return Ncols(L`BM); end intrinsic;

intrinsic BaseRing(L::LatNF) -> Rng
{The base ring of a number field lattice}
 return L`K; end intrinsic;

intrinsic Determinant(L::LatNF) -> FldNumElt
{The determinant of a number field lattice, defined up to squares of units}
 if #L`Js eq 0 then return L`K!1; end if;
 require IsFree(L): "The number field lattice must be free";
 return Determinant(GramMatrix(SimpleLattice(L))); end intrinsic;

intrinsic Discriminant(L::LatNF) -> RngOrdFracIdl
{The discriminant ideal of a number field lattice}
 return Determinant(L`GRAM)*(&*[J : J in L`Js])^2; end intrinsic;

intrinsic Volume(L::LatNF) -> RngOrdFracIdl
{The volume of a number field lattice, which is the ideal
 generated by the determinants of all free sublattices}
 return Determinant(L`GRAM)*(&*[J : J in L`Js])^2; end intrinsic;

intrinsic Norm(L::LatNF) -> RngOrdFracIdl // from Markus and David Lorch
{The norm of the lattice L}
 if Rank(L) eq 0 then return ideal<L`K|>; end if;
 D:=Diagonal(PseudoGramMatrix(L)); J:=L`Js;
 return &+{D[i]*J[i]^2 : i in [1..#D]} + 2*Scale(L); end intrinsic;

intrinsic Scale(L::LatNF) -> RngOrdFracIdl // from Markus and David Lorch
{The scale of the lattice L}
 if Rank(L) eq 0 then return ideal<L`K|>; end if; G:=L`GRAM; J:=L`Js;
 return &+{G[i,j]*J[i]*J[j] : i in [1..j],j in [1..#J] | G[i,j] ne 0};
 end intrinsic;

intrinsic Zero(L::LatNF) -> LatNFElt
{The zero vector of a number field lattice}
 return L.0; end intrinsic;

intrinsic IsSimple(L::LatNF) -> BoolElt
{Whether all the fractional ideals of a number field lattice are trivial}
 return &and[IsOne(j) : j in L`Js]; end intrinsic;

intrinsic IsFree(L::LatNF) -> BoolElt
{Whether a number field lattice is free}
 return IsFree(Module(L : IP:=false)); end intrinsic;

intrinsic IsFree(M::ModDed) -> BoolElt // from Markus and David Lorch
{Tests if M is a free module}
 return ok where ok:= IsPrincipal(SteinitzClass(M)); end intrinsic;

intrinsic SimpleLattice(L::LatNF) -> LatNF
{Given a free number field lattice, return an equivalent lattice
 with all of its coefficients ideals trivial}
 if &and[IsPrincipal(j) : j in L`Js] then // easy case
  E:=[L`K | e where _,e:=IsPrincipal(j) : j in L`Js]; D:=DiagonalMatrix(E);
  return new_nf_lat(D*L`BM,D*L`GRAM*D : IP:=L`IP); end if;
 require IsFree(L): "Lattice is not free";
 M:=Module(L : IP:=false); P:=SteinitzForm(PseudoMatrix(M));
 B:=ChangeRing(Matrix(P),L`K); J:=CoefficientIdeals(P);
 // assert &and[IsPrincipal(j) : j in J];
 E:=[L`K | e where _,e:=IsPrincipal(j) : j in J];
 D:=DiagonalMatrix(E); B:=D*B; r:=Nrows(B);
 G:=Matrix(r,r,[InnerProduct(L!(B[i]),L!(B[j])) : i,j in [1..r]]);
 R:=new_nf_lat(B,G : IP:=L`IP);
 // assert IsSublattice(L,R) and IsSublattice(R,L);
 return R; end intrinsic;
// SteinitzForm on the module seems insufficient, need on the PMat ...
// ok, the point is that SteinitzForm on the PseudoMatrix
// calls PseudoMatrix on the SteinitzForm(M) *but* with vararg Generators
// I was not using Generators when calling PseudoMatrix

intrinsic Dual(L::LatNF) -> LatNF
{The dual lattice to L}
 if Rank(L) eq 0 then return L; end if;
 GI:=L`GRAM^(-1); R:=GI*L`BM; J:=[J^(-1) : J in L`Js];
return new_nf_lat(R,GI : Js:=J,IP:=L`IP); end intrinsic; // GI^t in general

intrinsic IsModular(L::LatNF) -> BoolElt, RngOrdFracIdl
{Return if L is modular, and if so an ideal such that J*Dual(L) equals L}
 if Rank(L) eq 0 then return true,ideal<L`K|1>; end if; s:=Scale(L);
 if Volume(L) eq s^Rank(L) then return true,s; else return false,_; end if;
 end intrinsic;

////////////////////////////////////////////////////////////////////////

function gram_is_totally_positive_definite(G) OrthoGram:=OrthogonalizeGram;
 return &and[IsTotallyPositive(d) : d in Diagonal(OrthoGram(G))]; end function;

intrinsic IsTotallyPositiveDefinite(L::LatNF) -> BoolElt
{Whether a number field lattice is totally positive definite}
 require IsTotallyReal(L`K): "Number field of lattice must be totally real";
 return gram_is_totally_positive_definite(L`GRAM); end intrinsic;

////////////////////////////////////////////////////////////////////////

function gram_ideals_over_Z(G,J) K:=NumberField(Ring(Universe(J)));
 B:=ChangeRing(Matrix([AbsoluteBasis(j) : j in J]),K);
 d:=AbsoluteDegree(K); r:=Nrows(G); assert #J eq r; Y:=[[] : j in [1..d]];
 A:=[B[i][a]*B[j][b]*G[i][j]:j in [1..r],b in [1..d], i in [1..r],a in [1..d]];
 M:=[Matrix(d*r,[Rationals()|Trace(b*x) : x in Eltseq(A)]) : b in Basis(K)];
 return M; end function;
/*
 for i in [1..(d*r)^2] do E:=Eltseq(A[i]);
  for j in [1..d] do Y[j][i]:=E[j]; end for; end for;
 return [ChangeRing(Matrix(d*r,d*r,y),Rationals()) : y in Y];
*/

function retract_to_K(T,J1,J2) K:=NumberField(Ring(Universe(J1)));
 B:=ChangeRing(Matrix([AbsoluteBasis(j) : j in J1]),K);
 C:=ChangeRing(Matrix([AbsoluteBasis(j) : j in J2]),K);
 d:=AbsoluteDegree(K); nd:=Ncols(T); assert nd mod d eq 0; n:=nd div d;
 R:=MatrixAlgebra(K,n)!0; // undo "jbia" of above
 for i,j in [1..n] do
  R[i][j]:=&+[T[i][j+(k-1)*n]*C[j][k] : k in [1..d]]/B[i][1]; end for;
 return R; end function;

function auto_group(G,J) // G is pseudoGram matrix
 R:=gram_ideals_over_Z(G,J);
 c:=Lcm([Denominator(x) : x in &cat[Eltseq(r) : r in R]]);
 R:=[ChangeRing(c*r,Integers()) : r in R]; assert IsSymmetric(R[1]);
  _,T:=LLLGram(R[1] : Delta:=0.999); TT:=Transpose(T); R:=[T*r*TT : r in R];
 AA:=AutomorphismGroup(R); TI:=T^(-1);
 A:=[TI*g*T : g in Generators(AA)]; Aw:=[retract_to_K(a,J,J) : a in A];
 ANS:=MatrixGroup<Degree(Universe(Aw)),BaseRing(Universe(Aw))|Aw>;
 ANS:=ChangeRing(ANS,BaseRing(G)); ANS`Order:=#AA; return ANS; end function;

function extend_pseudobasis(M) R:=Random; I:=[-1,1]; u:=0; // Smith can reorder
 c:=Ncols(M); s:=c-Nrows(M); K:=BaseRing(M); d:=AbsoluteDegree(K);
 while true do u:=u+1; if u gt 10 then u:=0; I cat:=[R(2*#I)]; end if;
  A:=Matrix(s,c,[K|&+[R(I)*K.1^i : i in [1..d]] : j in [1..c],k in [1..s]]);
  V:=VerticalJoin(M,A); if Rank(V) eq c then return V; end if; end while;
 end function;

intrinsic AutomorphismGroup
(L::LatNF : NaturalAction:=false,Check:=true) -> GrpMat
{The automorphism group of a totally positive definite number field lattice}
 require IsTotallyPositiveDefinite(L): "Lattice must be totally pos definite";
 if Rank(L) eq 0 then
  if NaturalAction then require Degree(L) ne 0: "Lattice degree cannot be 0";
   return MatrixGroup<Degree(L),L`K|>; end if;
  require false: "Lattice must be positive rank"; end if;
 // if Rank(L) eq 0 then return MatrixGroup<0,L`K|>; end if;
 if not NaturalAction then A:=auto_group(PseudoGramMatrix(L),L`Js);
  if Check then assert &and[a*L eq L : a in Generators(A)]; end if;
  return A; end if;
 // not working in quartic case, none of extended Gram matrices are pos def?
 A:=auto_group(PseudoGramMatrix(L),L`Js);
 B:=extend_pseudobasis(L`BM); BI:=B^(-1); d:=Degree(L); r:=Rank(L);
 GENS:=[BI*DiagonalJoin(g,IdentityMatrix(L`K,d-r))*B: g in Generators(A)];
 if Check then assert &and[L*T eq L : T in GENS]; end if;
 M:=MatrixGroup<d,L`K|GENS>; M`Order:=#A; return M; end intrinsic;

function is_isom_basis_act(A,B)
 Y:=PseudoGramMatrix(A); Z:=PseudoGramMatrix(B);
 E:=gram_ideals_over_Z(Y,A`Js); F:=gram_ideals_over_Z(Z,B`Js);
 c:=Lcm([Denominator(x) : x in &cat[Eltseq(r) : r in E cat F]]);
 E:=[ChangeRing(c*r,Integers()) : r in E];
 F:=[ChangeRing(c*r,Integers()) : r in F];
 _,T:=LLLGram(E[1] : Delta:=0.999); TT:=Transpose(T); TI:=T^(-1);
 _,U:=LLLGram(F[1] : Delta:=0.999); UU:=Transpose(U); UI:=U^(-1);
 E:=[T*e*TT : e in E]; F:=[U*f*UU : f in F];
 b,X:=IsIsometric(E,F); if not b then return b,_; end if;
 R:=ChangeRing(retract_to_K(UI*X*T,A`Js,B`Js),A`K); return true,R;
 end function;

intrinsic IsIsometric
(A::LatNF,B::LatNF : NaturalAction:=false) -> BoolElt, Mtrx
{Whether two totally positive definite number field lattices are isometric}
 require BaseRing(A) eq BaseRing(B): "Lattices must be over same field";
 require IsTotallyPositiveDefinite(A) and IsTotallyPositiveDefinite(B):
  "Lattices must be totally positive definite";
 if Rank(A) ne Rank(B) then return false,_; end if;
 if NaturalAction then
  require A`IP eq B`IP: "Ambients must have the same inner product (if known)";
  require Degree(A) eq Degree(B): "Lattices must be of same degree";
 elif Rank(A) eq 0 then return true,Matrix(0,[A`K|]); end if;
 b,T:=is_isom_basis_act(A,B); if not b then return b,_; end if;
 if not NaturalAction then return b,T; end if; d:=Degree(A); r:=Rank(A);
 U:=extend_pseudobasis(A`BM); UI:=U^(-1); V:=extend_pseudobasis(B`BM);
 return b,UI*DiagonalJoin(T,IdentityMatrix(A`K,d-r))*V; end intrinsic;

////////////////////////////////////////////////////////////////////////

function vec_retract_to_K(v,J) K:=NumberField(Ring(Universe(J)));
 d:=AbsoluteDegree(K); nd:=Degree(v); assert nd mod d eq 0; n:=nd div d;
 R:=VectorSpace(K,n)!0; // undo "jbia" of above
 B:=ChangeRing(Matrix([AbsoluteBasis(j) : j in J]),K);
 for j in [1..n] do // R[j]:=&+[v[j+(k-1)*n]*B[k] : k in [1..d]];
  R[j]:=&+[v[j+(k-1)*n]*B[j][k] : k in [1..d]]/B[1][1]; end for;
 return R; end function;

intrinsic Sphere(L::LatNF,e::RngElt : Negatives:=true) -> Setq[LatNFElt]
{Given a number field lattice and a norm, return the vectors on that sphere}
 require IsCoercible(L`K,e): "Field elements must coerce into number field";
 require IsTotallyPositiveDefinite(L): "Lattice must be totally pos definite";
 if e eq 0 then return {L.0}; end if; e:=L`K!e; deg:=AbsoluteDegree(L`K);
 require IsTotallyPositive(e): "The given norm must be totally positive";
 if e notin Norm(L) then return {L|}; end if; // from Markus + David Lorch
 G:=gram_ideals_over_Z(L`GRAM/e,L`Js); // Is G[1] always trace?
 LAT:=LatticeWithGram(G[1]); SV:=ShortVectors(LAT,deg,deg);
 X:=[L | vec_retract_to_K(v[1],L`Js)*L`BM : v in SV ];
 X:=[v : v in X | Norm(v) eq e];
 if Negatives then X cat:=[-x : x in X]; end if; return Set(X); end intrinsic;
 /*
 B:=[AbsoluteBasis(J) : J in L`Js]; r:=Rank(L); deg:=AbsoluteDegree(L`K);
 V:=VectorSpace(L`K,r); ZB:= [b*V.i : b in B[i], i in [1..r]];
 M:=[&+[E[k]*y[k] : k in [1..r]] where E:=x*L`GRAM/e : x,y in ZB];
 M:=Matrix(r*deg,[AbsoluteTrace(x) : x in M]);
 LAT:=LatticeWithGram(M); SV:=ShortVectors(LAT,deg,deg);
 X:=[L | &+[sv[1,i]*ZB[i] : i in [1..#ZB]]*L`BM : sv in SV];
 X:=[x : x in X | Norm(x) eq e];
 if Negatives then X cat:=[-x : x in X]; end if;
 return Set(X); end intrinsic;
 */

////////////////////////////////////////////////////////////////////////

intrinsic IsSublattice(S::LatNF,L::LatNF) -> BoolElt
{Return if S is a sublattice of L}
 require Degree(S) eq Degree(L): "Lattices must be same degree";
 require S`K eq L`K: "Lattices must be over the same number field";
 require S`IP eq L`IP: "Lattices must have the same ambient inner product";
 G:=Generators(S);
 for g in G do if not g in L then return false; end if; end for;
 for g,h in G do // other 'subset's in Magma give error on nonconsistent IPs
  if InnerProduct(g,h) ne InnerProduct(L!g,L!h) then return false; end if;
  end for; return true; end intrinsic; // would rather allow it this way

intrinsic 'subset'(S::LatNF,L::LatNF) -> BoolElt, Mtrx {"}//"
 return IsSublattice(S,L); end intrinsic;

intrinsic OrthogonalComplement(L::LatNF,v::LatNFElt) -> LatNF
{Given a lattice L and a vector v, return the orthogonal complement}
 require v in L: "The vector must be in the lattice";
 return OrthogonalComplement(L,sub<L|[v]>); end intrinsic;

intrinsic OrthogonalComplement(L::LatNF,S::LatNF) -> LatNF
{Given a lattice L and a sublattice S, return the orthogonal complement}
 require IsSublattice(S,L): "S must be a sublattice of L";
 if Rank(S) eq 0 then return L; end if; r:=Rank(L); A:=[]; K:=L`K;
 if Rank(S) eq Rank(L) then return SubConstr(L,[]); end if; // hackish, IP
 GRAM:=PseudoGramMatrix(L); M:=Matrix([(L!g)`coord*GRAM : g in Generators(S)]);
 O:=MaximalOrder(L`K); d:=LCM([d where _,d:=IsIntegral(e) : e in Eltseq(M)]);
 T:=ChangeRing(Transpose(M)*d,O); R:=RSpace(O,r); Jd:=Denominator(&+L`Js);
 B:=[b*R.i : b in AbsoluteBasis(Jd*L`Js[i]), i in [1..r]]; Z:=Integers();
 KER:=KernelMatrix(Matrix(Z,[&cat[Eltseq(O!x) : x in Eltseq(b*T)] : b in B]));
 // AbsoluteBasis OK with Eltseq(O!x) here, as all K are absolute
 C:=ChangeRing(GeneratorMatrix(Module(Rows(Matrix(O,KER)*Matrix(B)))),K);
 R:=Rows(C*L`BM/Jd); // above is from Markus, though I added Jd myself
 if L`IP eq 0 then // this should be OK now
  G:=Matrix(#R,#R,[InnerProduct(L!R[i],L!R[j]) : i,j in [1..#R]]);
  return NumberFieldLattice(R : Gram:=G); end if; // could assert...
 return NumberFieldLattice(R : InnerProduct:=L`IP); end intrinsic;

////////////////////////////////////////////////////////////////////////

function nflat_is_lorentzian(L) IP:=InfinitePlaces(L`K); ok:=false;
 O,T:=OrthogonalizeGram(L`GRAM); D:=Diagonal(O);
 for i in [1..#D],j in [1..#IP] do
  if Real(Evaluate(D[i],IP[j])) gt 0 then continue; end if;
  if ok then return false,_,_; end if; ok:=true; w:=i; e:=j; end for;  
 if not ok then return false,_,_; end if;
 v:=Vector([i eq w select L`K!1 else 0 : i in [1..Nrows(L`GRAM)]]);
 return ok,v*(T^(-1)),e; end function;

intrinsic IsLorentzian(L::LatNF) -> BoolElt, ModTupFldElt, RngIntElt
{Whether a number field lattice is lorentzian}
 require IsTotallyReal(L`K): "Number field of lattice must be totally real";
 r:=Rank(L); if r eq 0 then return false,_,_; end if;
 b,coord,e:=nflat_is_lorentzian(L); if not b then return b,_,_; end if;
 S:=&+[coord[j]*(L`Js[j]^(-1)) : j in [1..r]];
 d:=Denominator(S); c:=Content(S); w:=(d/c)*coord;
 return true,new_nf_lat_elt(L,w),e; end intrinsic;

intrinsic IsTimelike(v::LatNFElt) -> BoolElt
{Whether a vector in a Lorentzian lattice is timelike}
 L:=v`parent; b,_,e:=IsLorentzian(L); require b: "Lattice must be Lorentzian";
 return Real(Evaluate(Norm(v),InfinitePlaces(L`K)[e])) lt 0; end intrinsic;

intrinsic IsSpacelike(v::LatNFElt) -> BoolElt
{Whether a vector in a Lorentzian lattice is timelike}
 L:=v`parent; b,_,e:=IsLorentzian(L); require b: "Lattice must be Lorentzian";
 return Real(Evaluate(Norm(v),InfinitePlaces(L`K)[e])) gt 0; end intrinsic;

intrinsic IsIsometric
(L::LatNF,v::LatNFElt,w::LatNFElt : NaturalAction:=false) -> BoolElt, Mtrx
{Given a Lorentzian lattice and two timelike vectors,
 determine if there is an automorphism T of L with v=Tw}
 require IsIdentical(L,v`parent): "Lattice must be parent of the first vector";
 require IsIdentical(L,w`parent): "Lattice must be parent of second vector";
 require IsLorentzian(L): "The lattice must be Lorentzian";
 require IsTimelike(v): "The first vector must be timelike";
 require IsTimelike(w): "The second vector must be timelike";
 if Norm(v) ne Norm(w) then return false,_; end if; K:=L`K;
 Ov:=OrthogonalComplement(L,v); Ow:=OrthogonalComplement(L,w);
 b,T:=IsIsometric(Ov,Ow); if not b then return false,_; end if;
 R:=Matrix(Rows(Ov`BM) cat [v`vec]); Rs:=Solution(L`BM,R);
 S:=Matrix(Rows(Ow`BM) cat [w`vec]); Ss:=Solution(L`BM,S);
 U:=Ss^(-1)*DiagonalJoin(T,DiagonalMatrix([K|1]))*Rs; assert U*w eq v;
 if U*L eq L then if not NaturalAction then return true,U; end if;
  E:=extend_pseudobasis(L`BM); EI:=E^(-1); d:=Degree(L); r:=Rank(L);
  return true,EI*DiagonalJoin(U,IdentityMatrix(K,d-r))*E; end if;
 // this all needs to be tested...
 G,M:=AutomorphismGroup(L,v); C:=RightTransversal(M,G);
 for c in C do if IsOne(c) then continue; end if; // c*v eq v;
  ci:=c^(-1); assert (U*ci)*w eq v; // this is the right way around...
  if (U*ci)*L eq L then if not NaturalAction then return true,U*ci; end if;
   E:=extend_pseudobasis(L`BM); EI:=E^(-1); d:=Degree(L); r:=Rank(L);
   return true,EI*DiagonalJoin(U*ci,IdentityMatrix(K,d-r))*E; end if; end for;
 return false,_; end intrinsic;

intrinsic AutomorphismGroup
(L::LatNF,v::LatNFElt : NaturalAction:=false) -> GrpMat, GrpMat
{Given a Lorentzian lattice and a timelike vector, determine the stabilizer}
 require IsIdentical(L,v`parent): "Lattice must be parent of the vector";
 require IsTimelike(v): "The vector must be timelike";
 O:=OrthogonalComplement(L,v); A:=AutomorphismGroup(O); K:=L`K;
 Gs:=[DiagonalJoin(g,DiagonalMatrix([K|1])) : g in Generators(A)];
 R:=Matrix(Rows(O`BM) cat [v`vec]); S:=Solution(L`BM,R);
 Gs:=[S^(-1)*g*S : g in Gs]; M:=MatrixGroup<Rank(L),K|Gs>; M`Order:=#A;
 orb,stab:=orbit_stab(M,L,func<g,L|g*L>);
 if not NaturalAction then return sub<M|stab>,M; end if;
 E:=extend_pseudobasis(L`BM); EI:=E^(-1); d:=Degree(L); r:=Rank(L);
 MG:=MatrixGroup<d,K|[EI*DiagonalJoin(g,IdentityMatrix(K,d-r))*E : g in Gs]>;
 ST:=sub<MG|[EI*DiagonalJoin(g,IdentityMatrix(K,d-r))*E : g in stab]>;
 return ST,MG; end intrinsic;

