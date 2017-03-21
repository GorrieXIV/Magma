freeze;

ZZ:=Integers(); QQ:=Rationals();

intrinsic WittInvariant(M::AlgMatElt,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by rational symmetric matrix M}
 require IsSymmetric(M): "Matrix must be symmetric";
 BR:=BaseRing(M); n:=Degree(Parent(M));
 require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring must be Integers or Rationals";
 require p eq -1 or IsPrime(p): "Second argument must be prime or -1";
 D:=Diagonalization(M); D:=[Rationals()!D[i][i] : i in [1..n] | D[i][i] ne 0];
 d:=#D; if d le 1 then return 1; end if;
 r:=&*[&*[HilbertSymbol(D[i],D[j],p) : j in [i+1..d]] : i in [1..d-1]];
 return r; end intrinsic;

intrinsic WittInvariant(f::RngMPolElt,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by f}
 return WittInvariant(SymmetricMatrix(f),p); end intrinsic;

intrinsic WittInvariant(L::Lat,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by the lattice L}
 return WittInvariant(GramMatrix(L),p); end intrinsic;

intrinsic WittInvariants(M::AlgMatElt : Minimize:=false) -> SeqEnum
{Returns the Witt (Hasse-Minkowski) invariants at all bad primes of
 the quadratic form given by the symmetric matrix M}
 require IsSymmetric(M): "Matrix must be symmetric"; BR:=BaseRing(M);
 require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring must be Integers or Rationals";
 D:=Determinant(M*Denominator(M));
 P:=[-1] cat PrimeFactors(4*Numerator(D)*Denominator(D)*Denominator(M));
 DIAG:=Diagonalization(M); E:=[<p,WittInvariant(DIAG,p)> : p in P];
 if Minimize then
  E:=[e : e in E | e[1] le 2 or e[2] eq -1 or IsOdd(Valuation(D,e[1]))];
  end if; return E; end intrinsic;

intrinsic WittInvariants(L::Lat : Minimize:=false) -> SeqEnum
{Returns the Witt (Hasse-Minkowski) invariants
 at all bad primes of the quadratic form given by the lattice L}
 return WittInvariants(GramMatrix(L) : Minimize:=Minimize); end intrinsic;

intrinsic WittInvariants(f::RngMPolElt : Minimize:=false) -> SeqEnum
{Computes the Witt (or Hasse-Minkowski) invariants
 at all bad primes of the quadratic form given by f}
 return WittInvariants(SymmetricMatrix(f) : Minimize:=Minimize); end intrinsic;

intrinsic HasseMinkowskiInvariant(M::AlgMatElt,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by rational symmetric matrix M}
 return WittInvariant(M,p); end intrinsic;

intrinsic HasseMinkowskiInvariant(f::RngMPolElt,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by f}
 return WittInvariant(f,p); end intrinsic;

intrinsic HasseMinkowskiInvariant(L::Lat,p::RngIntElt) -> RngIntElt
{Computes the Witt (or Hasse-Minkowski) invariant over Q_p
 of the quadratic form given by the lattice L}
 return WittInvariant(L,p); end intrinsic;

intrinsic HasseMinkowskiInvariants(M::AlgMatElt : Minimize:=false) -> SeqEnum
{Returns the Witt (Hasse-Minkowski) invariants at all bad primes of
 the quadratic form given by the symmetric matrix M}
 return WittInvariants(M : Minimize:=Minimize); end intrinsic;

intrinsic HasseMinkowskiInvariants(L::Lat : Minimize:=false) -> SeqEnum
{Returns the Witt (Hasse-Minkowski) invariants
 at all bad primes of the quadratic form given by the lattice L}
 return WittInvariants(L : Minimize:=Minimize); end intrinsic;

intrinsic HasseMinkowskiInvariants(f::RngMPolElt : Minimize:=false) -> SeqEnum
{Computes the Witt (or Hasse-Minkowski) invariants
 at all bad primes of the quadratic form given by f}
 return WittInvariants(f : Minimize:=Minimize); end intrinsic;

intrinsic IsRationallyEquivalent(X::AlgMatElt,Y::AlgMatElt)
 -> BoolElt, AlgMatElt
{Given two rational symmetric matrices X and Y, determine if they
 are rationally equivalent, and if so, return T with Y=TXT^t.}
 require IsSymmetric(X) and IsSymmetric(Y): "Matrices must be symmetric";
 BR:=BaseRing(X); require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring of X must be Integers or Rationals";
 BR:=BaseRing(Y); require BR cmpeq Integers() or BR cmpeq Rationals():
  "Base Ring of Ymust be Integers or Rationals";
 detxy:=Determinant(X)*Determinant(Y);
 require detxy ne 0: "Matrices must be nonsingular";
 if WittInvariants(X : Minimize) ne WittInvariants(Y : Minimize)
  then return false,_; end if;
 if pSignature(X,-1) ne pSignature(Y,-1) then return false,_; end if;
 if not IsSquare(detxy) then return false,_; end if;
 X:=ChangeRing(X,Rationals()); Y:=ChangeRing(Y,Rationals());
 S:=DirectSum(-Y,X); n:=Degree(Parent(X));
 B:=Basis(IsotropicSubspace(S)); assert #B eq n; // Simon's algorithm
 E:=EchelonForm(ChangeRing(Matrix(B),Rationals()));
 T:=Submatrix(E,1,n+1,n,n); assert2 T*X*Transpose(T) eq Y;
 return true,T; end intrinsic;

intrinsic IsRationallyEquivalent(f::RngMPolElt,g::RngMPolElt)
 -> BoolElt,AlgMatElt
{Given two quadratic forms f and g over Q, determine whether they are
 rationally equivalent, and if so, return a transform.}
 return IsRationallyEquivalent(SymmetricMatrix(f),SymmetricMatrix(g));
 end intrinsic;

intrinsic IsRationallyEquivalent(L::Lat,M::Lat) -> BoolElt,AlgMatElt
{Given two lattices L and M over Q determine whether they are
 rationally equivalent, and if so, return a transform.}
 return IsRationallyEquivalent(GramMatrix(L),GramMatrix(M)); end intrinsic;
