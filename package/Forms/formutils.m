freeze;
/*****************************************************
  Utilities for reflexive forms defined on finite dimensional vector spaces 
  over finite fields, including fields of characteristic two.

  August 2010 Don Taylor

  $Id: formutils.m 52483 2016-05-03 04:48:38Z don $

  Classical geometries
  --------------------
  If V is a vector space, there are three types of geometry based on V whose
  group of isometries is a classical group.
  
  (a) symplectic: (V,J) where J is an alternating form.
  (b) unitary:    (V,J,sigma) where sigma is a field automorphism of order 2
                  and J is hermitian or skew-hermitian with respect to sigma.
  (c) quadratic: (V,J,Q) where Q is a quadratic form and J is the polar form
                  of Q.  If the characteristic of the base field is not 2,
                  then J determines Q.

  There are two other possibilities:
 
  (d) orthogonal: (V,J) where the characteristic of the base field is not 2,
                  J is a symmetric bilinear form but no quadratic form is 
                  attached to the space. This is equivalent to (c).
  (e) pseudo-symplectic: (V,J) where the characteristic of the base field is 2
                  and J is symmetric but not alternating.
  

  This file contains code relevant to all types of forms. Additional code
  specific to quadratic spaces is in quadform.m.

  Intrinsics defined in this file:

    CommonComplement
    ConjugateTranspose
    Discriminant
    DotProduct
    DotProductMatrix
    ExtendIsometry (Witt's theorem)
    GeneralisedWallForm
    HasIsotropicVector
    HyperbolicPair
    HyperbolicSplitting
    IsIsometric
    IsIsometry
    IsNondegenerate
    IsometryGroup
    IsPolarSpace
    IsPseudoSymplecticSpace
    IsSimilar
    IsSimilarity
    IsSymplecticSpace
    IsTotallyIsotropic
    IsUnitarySpace
    MaximalTotallyIsotropicSubspace
    OrthogonalComplement
    PolarSpaceType
    Radical
    SimilarityGroup
    SymplecticBasis
    SymplecticSpace
    UnitarySpace
    WallForm
    WallIsometry
    WittDecomposition
    WittIndex

******************************************************/
declare verbose ExtendIsometry, 3;
declare verbose PolarSpace, 3;

declare attributes ModTupFld: Involution, hSplit;

/*
   Involution: a field automorphism sigma (usually of order 2) 
     needed for sigma-sesquilinear forms.
   
   hSplit: a maximal decomposition of the space into an orthogonal
     sum of m hyperbolic planes and their orthogonal complement,
     where m is the Witt index.
*/

// Messages

OnlyFldFin := "only available for spaces over finite fields";
notpolar := "cannot identify the space";

/*****************************************************
   General utilities
   -----------------
*/

intrinsic DotProduct(u:: ModTupFldElt, v::ModTupFldElt) -> FldElt
{The inner product of u and v}
  V := Generic(Parent(u));
  require v in V : "vectors must be in the same space";
//  require V eq Generic(Parent(v)): "vectors must be in the same space";
  if assigned V`Involution then
    sigma := V`Involution;
    vbar := Matrix(Ncols(v),1, [sigma(e) : e in Eltseq(v)]);
  else
    vbar := Transpose(Matrix(v));
  end if;
  return (u*InnerProductMatrix(V)*vbar)[1];
end intrinsic;

intrinsic ConjugateTranspose( M::Mtrx, sigma::Map ) -> Mtrx
{ The transpose of sigma(M)  }
  R := BaseRing(M);
  m := Nrows(M);
  n := Ncols(M);
  return Transpose(Matrix(R,m,n, [sigma(e) : e in Eltseq(M) ]));
end intrinsic;

intrinsic DotProductMatrix(S::SeqEnum[ModTupFldElt]) -> AlgMatElt
{ The matrix of inner products of the vectors in S,
 taking into account any attached field automorphism}
  U := Universe(S);
  V := Generic(U);
  J := InnerProductMatrix(U);
  B := Matrix(BaseRing(U),#S,OverDimension(U), S);
  C :=  assigned V`Involution select B*J*ConjugateTranspose(B,V`Involution)
       else B*J*Transpose(B);
  return Matrix(C);
end intrinsic;

intrinsic Discriminant(V::ModTupFld) -> RngIntElt
{ The discriminant of the inner product space V; 0 if 
  the determinant of the form is a square, 1 if a non-square}
//  require ISA( Type(BaseField(V)), FldFin ) : OnlyFldFin;
  d := Determinant(DotProductMatrix(Basis(V)));
  require d ne 0 : "the form is degenerate";
  flag, _ := IsSquare(d);
  return flag select 0 else 1;
end intrinsic;

/* A subspace of a vector space with an assigned inner product,
   inherits the inner product.

   By default, the orthogonal complement is the *left* orthogonal
   complement.  The right orthogonal complement is returned when
   Right is true.  If the form is reflexive, these coincide.
*/
intrinsic OrthogonalComplement(V::ModTupFld,X::ModTupFld : Right := false) -> ModTupFld
{ The (left) orthogonal complement of X in V.}
  A := Generic(V);
  J := InnerProductMatrix(A);
  B := BasisMatrix(X);
  if assigned A`Involution then
    sigma := A`Involution;
    B := Matrix(BaseRing(B),Nrows(B),Ncols(B), [sigma(e) : e in Eltseq(B)]);
  end if;
  M := Right select Transpose(B*J) else J*Transpose(B);
  N := NullSpace(M);
  // Magma does not recognise N as a subspace of A, therefore:
  return V meet sub<A|Basis(N)>;
end intrinsic;

intrinsic Radical(V::ModTupFld : Right := false) -> ModTupFld
{ The (left) radical of the inner product space V }
  return OrthogonalComplement(V,V : Right := Right);
end intrinsic;

intrinsic IsNondegenerate(V::ModTupFld) -> BoolElt
{True iff the matrix of inner products of V is nonsingular}
  return Determinant(DotProductMatrix(Basis(V))) ne 0;
end intrinsic;


/*****************************************************
   Polar spaces
   ------------

   1) The set of totally isotropic subspaces with respect to a reflexive
   bilinear or sesquilinear form on a vector space is a polar space
   2) The set of totally singular subspaces with respect to a quadratic form 
   on a vector space is a polar space.
   
   (There are other types of polar space are related to non-commutative fields
   and non-Desarguesian projective planes but they will not be accommodated
   here.)
   
   To test whether a vector space V is a polar space, let sigma either be the 
   involution attached to V or the identity if the Involution attribute is
   not assigned.  If V is a quadratic space or if the Gram matrix of V is
   hermitian or skew-hermitian with respect to sigma, then V is a polar
   space.
   
   A vector space with a symmetric inner product matrix but no quadratic 
   form attached is a polar space. If the characteristic is 2 and the form 
   is not alternating it is a pseudo-symplectic space, otherwise it is called
   an orthogonal space (to distinguish it from quadratic spaces).
*/

intrinsic IsPolarSpace(W::ModTupFld) -> BoolElt
{Check if V is a quadratic space or the Gram matrix of V is a reflexive form}
  V := Generic(W);
  if IsQuadraticSpace(W) then return true; end if;
  J := DotProductMatrix(Basis(W));
  Jct := assigned V`Involution select ConjugateTranspose(J, V`Involution)
         else Transpose(J);
  return J eq -Jct or J eq Jct;
end intrinsic;

quadratic_space := 1;
symplectic_space := 2;
unitary_space := 3;
pseudo_symplectic_space := 4;
orthogonal_space := 5;
unknown_space := 6;

PolarType := [
  "quadratic", 
  "symplectic", 
  "unitary", 
  "pseudo-symplectic", 
  "orthogonal",
  "unknown"
  ];

polar_type := function(V)
  if IsQuadraticSpace(V) then
    type := quadratic_space;
  elif IsSymplecticSpace(V) then
    type := symplectic_space;
  elif IsUnitarySpace(V) then
    type := unitary_space;
  elif IsPseudoSymplecticSpace(V) then
    type := pseudo_symplectic_space;
  elif GramMatrix(V) eq Transpose(GramMatrix(V)) then
    type := orthogonal_space;
  else 
    type := unknown_space;
  end if;
  return type;
end function;

is_nondegenerate := func< V | IsQuadraticSpace(V) select IsNonsingular(V) else 
    Determinant(DotProductMatrix(Basis(V))) ne 0 >;

intrinsic PolarSpaceType(V::ModTupFld) -> BoolElt
{The type of the polar space V}
  return PolarType[polar_type(V)] cat " space";
end intrinsic;

/*****************************************************
   Unitary geometry
   ----------------
   A unitary space is characterised as a vector space V
   whose ambient space, Generic(V), has the attribute Involution
   and whose inner product matrix is either hermitian or skew hermitian.
   
   Involution:  an automorphism of order 2 of the coefficient
     ring of the vector space.
*/
intrinsic UnitarySpace(J::AlgMatElt, sigma::Map) -> ModTupFld
{The n-dimensional unitary space over the base ring F of J, where
 sigma is an automorphism of F of order 2 and where J is an n by n 
 hermitian or skew-hermitian matrix with respect to sigma}
  F := BaseRing(J);
  require ISA( Type(F), Fld ) : "must be defined over a field";
  require Domain(sigma) cmpeq F : "sigma must be defined on the base field of J";
  V := VectorSpace( F, Nrows(J), J );
  V`Involution := sigma;
  return V;
end intrinsic;

intrinsic IsUnitarySpace( W::ModTupFld ) -> BoolElt, RngIntElt
{ Test if the ambient space carries a form which is
 hermitian or skew-hermitian when restricted to W }
  V := Generic(W);
  if assigned V`Involution then
    J := DotProductMatrix(Basis(W));
    Jct := ConjugateTranspose( J, V`Involution );
    if J eq Jct then
        m := 1;
    elif J eq -Jct then
        m := -1;
    else
        m := 0;
    end if;
    return m ne 0, m;
  else 
    return false, 0;
  end if;
end intrinsic;

isSkewUnitarySpace := function( W )
    V := Generic(W);
    if assigned V`Involution then
        J := DotProductMatrix(Basis(W));
        Jct := ConjugateTranspose( J, V`Involution );
        return J eq -Jct;
    else 
        return false;
    end if;
end function;

/*****************************************************
   Symplectic geometry
   -------------------
   A symplectic space is characterised as a vector space V whose ambient
   space, Generic(V), does *not* have the attribute Involution and whose
   inner product matrix is alternating.  Note this criterion implies
   that in characteristic 2 a quadratic space is also a symplectic space.
*/
intrinsic SymplecticSpace(J::AlgMatElt) -> ModTupRng
{The n-dimensional symplectic space over the base ring F of J;
 J must be alternating}
  n := Nrows(J);
  require J eq -Transpose(J) and 
    forall{ i : i in [1..n] | J[i,i] eq 0 } : "form is not alternating";
  return RSpace( BaseRing(J), n, J );
end intrinsic;

intrinsic IsSymplecticSpace( W::ModTupFld ) -> BoolElt
{ Test if the space carries an alternating form }
  V := Generic(W);
  if assigned V`Involution then
    return false;
  else
    return J eq -Transpose(J) and forall{ i : i in [1..n] | J[i,i] eq 0 }
    where n is Nrows(J) where J is GramMatrix(W);
  end if;
end intrinsic;

/*****************************************************
   Pseudo-symplectic geometry
   -------------------
   A pseudo-symplectic space is characterised as a vector space V over a 
   perfect field of characteristic two whose ambient space, Generic(V), 
   does *not* have the attribute Involution and whose inner product matrix 
   is symmetric but not alternating.  
*/

intrinsic IsPseudoSymplecticSpace( W::ModTupFld ) -> BoolElt
{ Test if the space carries a pseudo-alternating form }
  if assigned Generic(W)`Involution or Characteristic(BaseField(W)) ne 2 then
    return false;
  else
    return J eq Transpose(J) and exists{ i : i in [1..n] | J[i,i] ne 0 }
    where n is Nrows(J) where J is GramMatrix(W);
  end if;
end intrinsic;


/*****************************************************
   Isometries
   ----------

   The following versions of IsIsometry are designed to work correctly for
   maps/matrices defined on *subspaces* of inner product and quadratic spaces.
*/
intrinsic IsIsometry(U::ModTupFld, V::ModTupFld, f::Map) -> BoolElt
{True if the map f is an isometry from U to V with respect to the attached forms}
  require U subset Domain(f) : "subspace is not in the domain of the map";
  B := Basis(U);
  isom := forall{ <u,v> : u, v in B | DotProduct(f(u),f(v)) eq DotProduct(u,v) };
  if IsQuadraticSpace(U) and IsQuadraticSpace(V) then
    isom and:= forall{ u : u in B | QuadraticNorm(f(u)) eq QuadraticNorm(u) };
  end if;
  return isom;
end intrinsic;

intrinsic IsIsometry(f::Map) -> BoolElt
{True if the map f is an isometry from its domain to its codomain}
  return IsIsometry(Domain(f),Codomain(f),f);
end intrinsic;

intrinsic IsIsometry(V::ModTupFld, g::Mtrx) -> BoolElt
{True if g is an isometry of V with respect to the attached form}
  B := Basis(V);
  isom := forall{ <u,v> : u, v in B | DotProduct(u*g,v*g) eq DotProduct(u,v) };
  if IsQuadraticSpace(V) then
    isom and:= forall{ u : u in B | QuadraticNorm(V!(u*g)) eq QuadraticNorm(u) };
  end if;
  return isom;
end intrinsic;

/*****************************************************
   Similarities
   ------------

  Test whether a map or matrix preserves the form up to a scalar multiple.
  If so, the multiplier is the second return value.

*/
multiplier := function(V,f)
  n := Dimension(V);
  if not exists(t){ <i,j> : i,j in [1..n] | DotProduct(V.i,V.j) ne 0 } then
    return BaseRing(V)!1;
  end if;
  i := t[1];  j := t[2];
  dp := ISA(Type(f),Mtrx) select DotProduct((V.i)*f,(V.j)*f) else DotProduct(f(V.i),f(V.j));
  return dp*DotProduct(V.i,V.j)^-1; 
end function;

intrinsic IsSimilarity(U::ModTupFld, V::ModTupFld, f::Map) -> BoolElt, FldElt
{True if the map f is a similarity from U to V with respect to the attached forms}
  require U subset Domain(f) : "subspace is not in the domain of the map";
  lambda := multiplier(U,f);
  B := Basis(U);
  simil := forall{ <u,v> : u, v in B | DotProduct(f(u),f(v)) eq lambda*DotProduct(u,v) };
  if IsQuadraticSpace(U) and IsQuadraticSpace(V) then
    simil and:= forall{ u : u in B | QuadraticNorm(f(u)) eq lambda*QuadraticNorm(u) };
  end if;
  return simil, lambda;
end intrinsic;

intrinsic IsSimilarity(f::Map) -> BoolElt, FldElt
{True if the map f is a similarity from its domain to its codomain}
  return IsSimilarity(Domain(f),Codomain(f),f);
end intrinsic;

intrinsic IsSimilarity(V::ModTupFld, g::Mtrx) -> BoolElt, FldElt
{True if g is a similarity of V with respect to the attached form}
  lambda := multiplier(V,g);
  B := Basis(V);
  simil := forall{ <u,v> : u, v in B | DotProduct(u*g,v*g) eq lambda*DotProduct(u,v) };
  if IsQuadraticSpace(V) then
    simil and:= forall{ u : u in B | QuadraticNorm(V!(u*g)) eq lambda*QuadraticNorm(u) };
  end if;
  return simil, lambda;
end intrinsic;



/*****************************************************
   Isotropic and singular vectors
   ------------------------------
*/
quadrep_ := function(a,b,c)
// Given non-zero elements a and b and any element c in a
// finite field, find x and y such that c = a*x^2 + b*y^2.
  q := c*a^-1;
  F := Parent(a);
  sq, x := IsSquare(q);
  if sq then
    return x,F!0;
  else
    r := b*a^-1;
    for w in F do
      sq, x := IsSquare(q - r*w^2);
      if sq then y := w; break; end if;
    end for;
    return x,y;
  end if;
end function;

intrinsic IsTotallyIsotropic(U::ModTupFld) -> BoolElt
{ True if the polar space V is totally isotropic }
  require IsPolarSpace(U) : "not a polar space";
  J := DotProductMatrix(Basis(U));
  return J eq Parent(J)!0;
end intrinsic;

symIsotropicVector_ := function(V)
// Assumes that V has a symmetric form and the characteristic is *not* 2.
  if Dimension(V) eq 0 then return false, _;  end if;
  B := Basis(V);
  if exists(u){ u : u in B | DotProduct(u,u) eq 0 } then
    return true, u;
  end if;
  if #B eq 1 then return false, _; end if;
  u := B[1];
  qu := DotProduct(u,u);
  F := BaseField(V);
  if #B eq 2 then
    x := PolynomialRing(F).1;
    v := B[2];
    b := DotProduct(u,v);
    qv := DotProduct(v,v);
    roots := Roots(qu*x^2 + 2*b*x + qv);
    if IsEmpty(roots) then
      return false, _;
    else
      return true, (roots[1][1])*u+v;
    end if;
  else
    U := sub< V | u >;
    Uperp := OrthogonalComplement(V,U);
    B := Basis(Uperp);
    if exists(up){ z : z in B | DotProduct(z,z) eq 0 } then
      return true, up;
    end if;
    v := B[1];
    qv := DotProduct(v,v);
    W := OrthogonalComplement(V,sub< V | u,v >);
    w := Basis(W)[1];
    qw := DotProduct(w,w);
    if qw eq 0 then return true, w; end if;
    r,s := quadrep_(qu,qv,-qw);
    return true, r*u+s*v+w;
  end if;
end function;

paltIsotropicVector_ := function(V)
// Assumes that V has a pseudo-alternating form.
// Only look for isotropic vectors in the "alternating" part,
// that is, the kernel of V -> F : v :-> vJv^t
  n := Dimension(V);
  if n eq 0 then return false, _;  end if;
  F := BaseRing(V);
  B := BasisMatrix(V);
  J := DotProductMatrix(Basis(V));
  M := Matrix(F,n,1,[ SquareRoot(J[i,i]) : i in [1..n]]);
  N := NullSpace(M);
  H := sub< V | [v*B : v in Basis(N) ] >;
  R := Radical(H);
  if R eq H then return false, _; end if;
  u := rep{ u : u in Basis(H) | u notin R };
  return true, u;
end function;

hermIsotropicVector_ := function(V,q)
// Assumes that V has an hermitian or skew-hermitian form and the base field
// of V is GF(q^2)
  B := Basis(V);
  if exists(u){ u : u in B | DotProduct(u,u) eq 0 } then return true, u; end if;
  if #B eq 1 then return false, _; end if;
  u := B[1];
  uu := DotProduct(u,u);
  W := OrthogonalComplement(V,sub<V|u>);
  v := Basis(W)[1];
  vv := DotProduct(v,v);
  if vv eq 0 then return true, v; end if;
  F := BaseField(V);
  b := -uu*vv^-1;
  flag, a := NormEquation(F,GF(q)!b);
  error if not flag, "hermIsotropicVector internal error, cannot solve the norm equation";
  return true, u + a*v;
end function;

intrinsic HasIsotropicVector(V::ModTupFld) -> BoolElt, ModTupFldElt
{ Determine whether the polar space V contains an isotropic vector; 
  if it does, assign a representative as the second return value }
  require IsPolarSpace(V) : "not a polar space";
  if Dimension(V) eq 0 then return false, _; end if;
  if IsSymplecticSpace(V) then return true, V.1; end if;
  F := BaseField(V);
  require ISA( Type(F), FldFin ) : OnlyFldFin;
  case polar_type(V):
    when quadratic_space :
    // In characteristic 2 a quadratic space is also a symplectic space
    // and has been dealt with above.
      return HasSingularVector(V);
    when unitary_space:
      flag, q := IsSquare(#F);
      assert flag;
      return hermIsotropicVector_(V,q);
    when pseudo_symplectic_space :
      return paltIsotropicVector_(V);
    when orthogonal_space :
      return symIsotropicVector_(V);
    when unknown_space :
      error "internal error " cat notpolar;
    else
      error "internal error, type identifier out of range";
  end case;
end intrinsic;

/*****************************************************
  Hyperbolic pairs
  ----------------
  A hyperbolic pair (u,v) for a bilinear or sesquilinear form B is a pair 
  of isotropic vectors such that B(u,v) = 1.  If V is a quadratic space we 
  require u and v to be singular.
*/
quadHyperbolicPair_ := function(V,u)
// Extends a singular vector u to a hyperbolic pair for a quadratic form
// provided u is not in the radical 
  error if u eq V!0, "(hyperbolicPair) zero vector";
  error if QuadraticNorm(u) ne 0, "(hyperbolicPair) non-singular vector";
  error if not exists(w){ w : w in Basis(V) | DotProduct(u,w) ne 0 },
    "(hyperbolicPair) vector is in the radical";
  a := DotProduct(u,w);
  return -QuadraticNorm(w)*a^-2*u+a^-1*w;
end function;

altHyperbolicPair_ := function(V,u)
// Extends an isotropic vector u to a hyperbolic pair for an alternating form
// provided u is not in the radical 
  error if u eq V!0, "(hyperbolicPair) zero vector";
  error if not exists(w){ w : w in Basis(V) | DotProduct(u,w) ne 0 },
    "(hyperbolicPair) vector is in the radical";
  return DotProduct(u,w)^-1 * w;
end function;

symHyperbolicPair_ := function(V,u)
// Extends an isotropic vector u to a hyperbolic pair for a symmetric form
// provided u is not in the radical 
  error if u eq V!0, "(hyperbolicPair) zero vector";
  error if DotProduct(u,u) ne 0, "(hyperbolicPair) non-isotropic vector";
  error if not exists(w){ w : w in Basis(V) | DotProduct(u,w) ne 0 },
    "(hyperbolicPair) vector is in the radical";
  a := DotProduct(u,w);
  return -(DotProduct(w,w)/2)*a^-2*u+a^-1*w;
end function;

paltHyperbolicPair_ := function(V,u)
// Extends an isotropic vector u to a hyperbolic pair for a pseudo-alternating
// form provided u is not in the radical of the symplectic part
  error if DotProduct(u,u) ne 0, "(hyperbolicPair) non-isotropic vector";
  n := Dimension(V);
  J := DotProductMatrix(Basis(V));
  M := Matrix(BaseRing(V),n,1,[ SquareRoot(J[i,i]) : i in [1..n]]);
  N := NullSpace(M);
  B := BasisMatrix(V);
  H := [V| v*B : v in Basis(N) ];
  error if not exists(w){ w : w in H | DotProduct(u,w) ne 0 },
    "(hyperbolicPair) vector is in the pseudo radical";
  return DotProduct(u,w)^-1 * w;
end function;

hermHyperbolicPair_ := function(V,u)
// Extends an isotropic vector u to a hyperbolic pair for an hermitian form
// or skew-hermitian form provided u is not in the radical 
  error if u eq V!0, "(hyperbolicPair) zero vector";
  error if DotProduct(u,u) ne 0, "(hyperbolicPair) non-isotropic vector";
  error if not exists(w){ w : w in Basis(V) | DotProduct(u,w) ne 0 },
    "(hyperbolicPair) vector is in the radical";
  
  c := DotProduct(u,w);
  d := DotProduct(w,w);
  K := BaseRing(V);
  sigma := Generic(V)`Involution;
  if d eq 0 then
    v := w;
  elif Characteristic(K) eq 2 then
    xi := PrimitiveElement(K);
    b := (1+sigma(xi)/xi)*c/d;
    v := u + b*w;
  else
    b := -2*c/d;
    v := u + b*w;
  end if;
  a := DotProduct(u,v)^-1;
  return sigma(a) * v;
end function;

intrinsic HyperbolicPair(V::ModTupFld,u::ModTupFldElt) -> ModTupFldElt
{Extends a singular or isotropic vector u to a hyperbolic pair provided u is 
not in the radical}
  require u ne V!0 : "vector is the zero vector";
  require DotProduct(u,u) eq 0 : "vector is not isotropic";
  require u in V : "vector is not in the space";
  case polar_type(V) :
    when quadratic_space :
      return quadHyperbolicPair_(V,u);
    when symplectic_space :
      return altHyperbolicPair_(V,u);
    when unitary_space:
      return hermHyperbolicPair_(V,u);
    when pseudo_symplectic_space :
      return paltHyperbolicPair_(V,u);
    when orthogonal_space :
      return symHyperbolicPair_(V,u);
    else
      error notpolar;
  end case;
end intrinsic;

/*****************************************************
  Hyperbolic splitting
  --------------------
*/

specialQuadBasis_ := function(V)
// It is assumed that V is an asingular quadratic space of
// dimension 2 over a finite field with quadratic form Q and
// polar form J.  The function returns a basis e, f for V
// such that Q(e) = J(e,f) = 1.
  B := Basis(V);
//  error if #B ne 2, "Dimension should be 2";
  a := QuadraticNorm(B[1]);
  squ_a, sqrt_a := IsSquare(a);
  if squ_a then
    e := sqrt_a^-1*B[1];
    v := B[2];
  else // odd characteristic
    d := DotProduct(B[1],B[2])/(2*a);
    x,y := quadrep_(a,QuadraticNorm(B[2])-a*d^2,1);
    e := (x-d*y)*B[1]+y*B[2];
    v := B[1];
  end if;
  b := DotProduct(e,v); // non-zero if characteristic eq 2
  f := b eq 0 select (e+v)/2 else v/b;
  return [e,f];
end function;

quadSplit_ := procedure(V)
  hpairs := [];
  W := V;
  singular, u := HasSingularVector(W);
  while singular do
    v := quadHyperbolicPair_(W,u);
    Append(~hpairs,[u,v]);
    W := OrthogonalComplement(W,sub<W|u,v>);
    singular, u := HasSingularVector(W);
  end while;
  B := Dimension(W) eq 2 select specialQuadBasis_(W) else Basis(W);
  V`hSplit := <hpairs, B>;
end procedure;

altSplit_ := procedure(V)
  hpairs := [];
  W := V;
  while Dimension(W) gt 0 do
    u := W.1;
    v := altHyperbolicPair_(W,u);
    Append(~hpairs,[u,v]);
    W := OrthogonalComplement(W,sub<W|u,v>);
  end while;
  V`hSplit := <hpairs, Basis(W)>;
end procedure;

specialSymBasis_ := function(V)
// It is assumed that V is an anisotropic polar space of dimension 2 over a 
// finite field of odd characteristic defined by a symmetric bilinear form J.
// The function returns a basis e,f for V such that J(e,e) = 1 and J(e,f) = 0.
  B := Basis(V);
  a := DotProduct(B[1],B[1]);
  squ_a, sqrt_a := IsSquare(a);
  if squ_a then
    e := sqrt_a^-1*B[1];
    v := B[2];
  else
    d := -DotProduct(B[1],B[2])/a;
    x,y := quadrep_(a,DotProduct(B[2],B[2])-a*d^2,1);
    e := (x+d*y)*B[1]+y*B[2];
    v := B[1];
  end if;
  return [e, v - DotProduct(e,v)*e];
end function;

symSplit_ := procedure(V)
  hpairs := [];
  W := V;
  isotropic, u := HasIsotropicVector(W);
  while isotropic do
    v := symHyperbolicPair_(W,u);
    Append(~hpairs,[u,v]);
    W := OrthogonalComplement(W,sub<W|u,v>);
    isotropic, u := HasIsotropicVector(W);
  end while;
  B := Dimension(W) eq 2 select specialSymBasis_(W) else Basis(W);
  V`hSplit := <hpairs,B>;
end procedure;


paltSplit_ := procedure(V)
  hpairs := [];
  W := V;
  isotropic, u := HasIsotropicVector(W);
  while isotropic do
    v := paltHyperbolicPair_(W,u);
    Append(~hpairs,[u,v]);
    W := OrthogonalComplement(W,sub<W|u,v>);
    isotropic, u := HasIsotropicVector(W);
  end while;
  if Dimension(W) eq 1 then
    w := W.1;
    _, a := IsSquare(DotProduct(w,w));
    B := [a^-1*w];
  else
    w1 := W.1; w2 := W.2;
    a1 := DotProduct(w1,w1);
    a2 := DotProduct(w2,w2);
    if a1 eq 0 then
      w := w1;
      v := w2;
    elif a2 eq 0 then
      w := w2;
      v := w1;
    else
      _, x := IsSquare(a1^-1*a2);
      w := x*w1+w2;
      v := w2;
    end if;
    _, b := IsSquare(DotProduct(v,v));
    v := b^-1*v;
    w := DotProduct(w,v)^-1*w;
    B := [w,v];
  end if;
  V`hSplit := <hpairs,B>;
end procedure;

hermSplit_ := procedure(V)
  hpairs := [];
  W := V;
  isotropic, u := HasIsotropicVector(W);
  while isotropic do
    v := hermHyperbolicPair_(W,u);
    Append(~hpairs,[u,v]);
    W := OrthogonalComplement(W,sub<W|u,v>);
    isotropic, u := HasIsotropicVector(W);
  end while;
  V`hSplit := <hpairs,Basis(W)>;
end procedure;

intrinsic HyperbolicSplitting(V::ModTupFld) -> SeqEnum, SeqEnum
{ A maximal list of pairwise orthogonal hyperbolic pairs and
  a basis for the orthogonal complement of the subspace they span }
  if not assigned V`hSplit then
    F := BaseRing(V);
    require ISA(Type(F), Fld) : "base ring should be a field";
    require is_nondegenerate(V) : "space must be nondegenerate";
    tp := polar_type(V);
    if tp ne symplectic_space then
      require ISA(Type(F), FldFin) : OnlyFldFin;
    end if;
    case tp :
      when symplectic_space:
        vprint PolarSpace, 2 : "-- symplectic space";
        split := altSplit_;
      when quadratic_space:
        vprint PolarSpace, 2 : "-- quadratic space";
        require IsNonsingular(V) : "space must be non-singular";
        Q := QuadraticFormMatrix(V);
        require InnerProductMatrix(V) eq Q + Transpose(Q) : 
                "Inner product matrix does not match quadratic form";
        split := quadSplit_;
      when unitary_space:
        vprint PolarSpace, 2 : "-- unitary space";
        require Dimension(Radical(V)) eq 0 : "non-zero radical";
        split := hermSplit_;
      when pseudo_symplectic_space:
        vprint PolarSpace, 2 : "-- pseudo-symplectic space";
        split := paltSplit_;
      when orthogonal_space:
        vprint PolarSpace, 2 : "-- orthogonal geometry";
        split := symSplit_;
      else
        error notpolar;
    end case;
    split(V); 
  end if;
  return V`hSplit;
end intrinsic;

intrinsic SymplecticBasis(V::ModTupFld,U::ModTupFld,W::ModTupFld) -> SeqEnum
{Given a polar space V, which is the direct sum of totally isotropic 
 subspaces U and W, each of dimension m, return a symplectic basis 
 e1, f1, e2, f2, ... for V such that e1, e2, ... is a basis for U and
 f1, f2, ... is a basis for W}

  require IsPolarSpace(V) : "first argument is not a polar space";
  require IsTotallyIsotropic(U) : "second argument is not totally isotropic";
  require IsTotallyIsotropic(W) : "third argument is not totally isotropic";
  require V eq sub< V | Basis(U) cat Basis(W) > : 
      "V is not the direct sum of U and W";
  sympbasis := [];
  X := U;
  Y := W;
  for i := 1 to Dimension(U) do
    u := X.1;
    assert exists(v){ v : v in Basis(Y) | DotProduct(u,v) ne 0 };
    Append(~sympbasis,DotProduct(u,v)^-1*V!u);
    Append(~sympbasis,V!v);
    X := OrthogonalComplement(X,sub<V|v>);
    Y := OrthogonalComplement(Y,sub<V|u>);
  end for;
  return sympbasis;
end intrinsic;

intrinsic IsIsometric(V1::ModTupFld,V2::ModTupFld) -> BoolElt, Map
{ Determine whether the polar spaces V1 and V2 are isometric; if they
  are, return an isometry (as a map)}
  F1 := BaseRing(V1);
  require ISA(Type(F1), Fld) : "base ring of first argument should be a field";
  F2 := BaseRing(V2);
  require ISA(Type(F2), Fld) : "base ring of second argument should be a field";
  tp1 := polar_type(V1);
  require tp1 ne unknown_space : "first argument is not a polar space";
  tp2 := polar_type(V2);
  require tp2 ne unknown_space : "second argument is not a polar space";
  require is_nondegenerate(V1) : "first argument is degenerate";
  require is_nondegenerate(V2) : "second argument is degenerate";
  require F1 cmpeq F2 : "the base fields should be equal";
  if tp1 ne tp2 then return false, _; end if;
  if Dimension(V1) ne Dimension(V2) then return false, _; end if;
  if (tp1 eq unitary_space) and 
        (isSkewUnitarySpace(V1) ne isSkewUnitarySpace(V2)) then
    return false, _;
  end if;
  if tp1 ne symplectic_space then
    require ISA(Type(F1), FldFin) : OnlyFldFin;
  end if;
  hs1 := HyperbolicSplitting(V1);
  hs2 := HyperbolicSplitting(V2);
  if (#hs1[1] ne #hs2[1]) then return false, _; end if;
  M1 := Matrix(&cat hs1[1] cat hs1[2]);
  frame := &cat hs2[1];
  anisodim := #hs1[2];
  if anisodim eq 0 then
    M2 := Matrix(frame);
  else
    w1 := hs1[2][1];
    w2 := hs2[2][1];
    case tp1 :
      when quadratic_space:
        if anisodim eq 1 then
          flag, a := IsSquare(QuadraticNorm(w1)/QuadraticNorm(w2));
          if flag then
            M2 := Matrix(Append(frame, a*w2));
          else
            return false, _;
          end if;
        else // anisotropic part has dimension 2
          x1 := hs1[2][2];
          x2 := hs2[2][2];
          a1 := QuadraticNorm(x1);
          a2 := QuadraticNorm(x2);
          if Characteristic(F1) eq 2 then
            x := PolynomialRing(F1).1;
            // The Artin-Schreier set {a^2+a : a in F1} is a subgroup of
            // index 2 in the additive group of F1.  Therefore the following
            // polynomial splits in F1.
            rts := Roots(x^2 + x + a1+a2);
            assert not IsEmpty(rts);
            B := [w2, rts[1][1]*w2 + x2];
          else
            flag, b := IsSquare((4*a1-1)/(4*a2-1));
            assert flag;
            B := [w2,(1-b)/2*w2+b*x2];
          end if;
          M2 := Matrix(frame cat B);
        end if;

      when unitary_space:
        flag, q := IsSquare(#F1);
        assert flag;
        b := DotProduct(w1,w1)/DotProduct(w2,w2);
        flag, a := NormEquation(F1,GF(q)!b);
        error if not flag, "IsIsometric internal error, cannot solve the norm equation";
        M2 := Matrix(Append(frame,a*w2));

      when orthogonal_space: // this never occurs in characteristic 2
        if anisodim eq 1 then
          flag, a := IsSquare(DotProduct(w1,w1)/DotProduct(w2,w2));
          if flag then
            M2 := Matrix(Append(frame, a*w2));
          else
            return false, _;
          end if;
        else // anisotropic part has dimension 2
          x1 := hs1[2][2];
          x2 := hs2[2][2];
          flag, b := IsSquare(DotProduct(x1,x1)/DotProduct(x2,x2));
          assert flag;
          M2 := Matrix(frame cat [w2,b*x2]);
        end if;

      when pseudo_symplectic_space:
        M2 := Matrix(frame cat hs2[2]);

      else
        error "Internal error in IsIsometric";
    end case;
  end if;
  // If V1 or V2 is a proper subspace of its generic space, then M1 or M2
  // may not be square and so we cannot use the "obvious" code:
  // M := M1^-1*M2;
  // isom := hom< V1 -> V2 | v :-> V2!(v*M), w :-> V1!(w*M^-1) >;
  f := function(v,A,B)
    u, N := Solution(A,v);
    assert Dimension(N) eq 0;
    return u*B;
  end function;
  isom := hom< V1 -> V2 | v :-> f(v,M1,M2), w :-> f(w,M2,M1) >;
  return true, isom; 

end intrinsic;

/*
Tform := function(A,tp)
  F := BaseRing(A);
  n := Nrows(A);
  case tp:
    when "symplectic" :
      V := SymplecticSpace(A);
      J := StandardAlternatingForm(n,F);
      W := SymplecticSpace(J);
    when "unitary" :
      flag, q := IsSquare(#F);
      assert flag;
      J, mu := StandardHermitianForm(n,F);
      V := UnitarySpace(A,mu);
      W := UnitarySpace(J,mu);
    when "orth", "orthogonal", "orthogonalcircle", "orth+", "orthogonalplus", "oplus" :
      V := QuadraticSpace(A);
      Q := StandardQuadraticForm(n,F);
      W := QuadraticSpace(Q);
    when "orth-", "orthogonalminus", "ominus" :
      V := QuadraticSpace(A);
      Q := StandardQuadraticForm(n,F : Minus, Variant := "Revised");
      W := QuadraticSpace(Q);
    else
      error "bad form type";
  end case;
  
  flag, f := IsIsometric(V,W);
  assert flag;
  return Matrix(F,n,n,[f(V.i) : i in [1..n]]);

end function;
*/

// Similar non-degenerate polar spaces over a finite field are isometric 
// except possibly for:
// (1) unitary and skew-unitary spaces and 
// (2) quadratic spaces in odd dimension and odd characteristic.
intrinsic IsSimilar(V1::ModTupFld,V2::ModTupFld) -> BoolElt, Map
{ Determine whether the polar spaces V1 and V2 are similar; if they
  are, return a similarity (as a map)}
  F1 := BaseRing(V1);
  require ISA(Type(F1),Fld) : "base ring of first argument should be a field";
  F2 := BaseRing(V2);
  require ISA(Type(F2),Fld) : "base ring of second argument should be a field";
  tp1 := polar_type(V1);
  tp2 := polar_type(V2);
  if tp1 ne tp2 then return false, _; end if;
  if Dimension(V1) ne Dimension(V2) then return false, _; end if;
  if (tp1 ne unitary_space) and (tp1 ne quadratic_space) then
      return IsIsometric(V1,V2);
  end if;
  if Characteristic(F1) eq 2 then return IsIsometric(V1,V2); end if;
  require is_nondegenerate(V1) : "first argument is degenerate";
  require is_nondegenerate(V2) : "second argument is degenerate";
  require F1 cmpeq F2 : "the base fields should be equal";
  require ISA(Type(F1), FldFin) : OnlyFldFin;

  if tp1 eq unitary_space then
      if isSkewUnitarySpace(V1) ne isSkewUnitarySpace(V2) then
          sigma := V2`Involution;
          a := F2.1 - sigma(F2.1);
          V3 := UnitarySpace(a*V2`ip_form,sigma);
          flag, phi := IsIsometric(V1,V3);
      else
          flag, phi := IsIsometric(V1,V2);
      end if;
  else // quadratic space
      hs1 := HyperbolicSplitting(V1);
      hs2 := HyperbolicSplitting(V2);
      if (#hs1[1] ne #hs2[1]) then return false, _; end if;
      if #hs1[2] ne 1 then return IsIsometric(V1,V2); end if;
      // quadratic space of odd dimension
      flag, phi := IsIsometric(V1,V2);
      if not flag then
        Q := Nonsquare(F2)*QuadraticFormMatrix(V2);
        V3 := QuadraticSpace(Q);
        flag, phi := IsIsometric(V1,V3);
      end if;
  end if;
  if not flag then return false, _; end if;
  M := Matrix([ phi(b) : b in Basis(V1) ]);
  return true, hom< V1 -> V2 | v :-> V2!(v*M), w :-> V1!(w*M^-1) >;

end intrinsic;

polar_group_ := function(F,V,tp,isom_grp_flag)
  R := (tp eq quadratic_space) select SingularRadical(V) else Radical(V);
  n := Dimension(V);
  r := Dimension(R);
  if r eq n then return GL(V); end if;
  if r eq 0 then
    W := V;
  else
//  if there is a non-trivial radical R, the isometry (resp. similarity)
//  group contains all groups of the form H x GL(R), where H is the group 
//  of isometries (resp. similarities) of a complement to R.

//  W is a complement to R in V.  Cannot use Complement(V,R) because
//  the return value is not always recognised as a subspace of V.
    W := sub<V|[e : e in ExtendBasis(B,V) | e notin B] where B is Basis(R)>;
  end if;
  n0 := n - r;
  q := #F;
  
// ...........................
    polar_grp := function(W,T,H)
    // W is a non-degenerate polar space, 
    // T is the standard version, and
    // H is the group of isometries or similarities of T.
      flag, f := IsIsometric(W,T);
      assert flag;
      M := Matrix(F,n0,n0,[f(W.i) : i in [1..n0]]);
      wgens := [ M*H.i*M^-1 : i in [1..Ngens(H)] ];
      ord := FactoredOrder(H);
      if r eq 0 then
        gens := wgens;
      else
        I0 := IdentityMatrix(F,n0);
        I1 := IdentityMatrix(F,r);
        Y := GL(r,F);
        gens := [ DiagonalJoin(g,I1) : g in wgens ] cat
                [ DiagonalJoin(I0,g) : g in Generators(Y) ];
        u := IdentityMatrix(F,n);
        u[1,n0+1] := F!1;
        // u is a transvection
        Append(~gens, u);
        C := Matrix( Basis(W) cat Basis(R) );
        gens := [C^-1*g*C : g in gens];
        ord *:= FactoredOrder(Y)*Factorisation(q^(n0*r));
      end if;
      A := sub<GL(V) | gens>;
      if n gt 1 then
        A`Order := ord;
      end if;
      return A;
    end function;
// ...........................

  case tp :
    when quadratic_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      Q := StandardQuadraticForm(n0,F : Minus := minus, Variant := "Revised" );
      T := QuadraticSpace(Q);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if IsOdd(q) and not IsIsometric(W,T) then
          T := QuadraticSpace(PrimitiveElement(F)*Q);
        end if;
        H := (isom_grp_flag) select GeneralOrthogonalGroup(n0,F)
             else ConformalOrthogonalGroup(n0,F);
      elif minus then
        H := (isom_grp_flag) select GeneralOrthogonalGroupMinus(n0,F)
             else ConformalOrthogonalGroupMinus(n0,F);
      else
        H := (isom_grp_flag) select GeneralOrthogonalGroupPlus(n0,F)
             else ConformalOrthogonalGroupPlus(n0,F);
      end if;
      A := polar_grp(W,T,H);

    when symplectic_space:
      J := StandardAlternatingForm(n0,F);
      T := SymplecticSpace(J);
      H := (isom_grp_flag) select SymplecticGroup(n0,F)
           else ConformalSymplecticGroup(n0,F);
      A := polar_grp(W,T,H);

    when unitary_space:
      J, sigma := StandardHermitianForm(n0,F);
      T := UnitarySpace(J,sigma);
      H := (isom_grp_flag) select GeneralUnitaryGroup(n0,F)
           else ConformalUnitaryGroup(n0,F);
      A := polar_grp(W,T,H);

    when orthogonal_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      J := StandardSymmetricForm(n0,F : Minus := minus, Variant := "Revised" );
      T := VectorSpace(F,n0,J);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if not IsIsometric(W,T) then
          T := VectorSpace(F,n0,PrimitiveElement(F)*J);
        end if;
        H := (isom_grp_flag) select GeneralOrthogonalGroup(n0,F)
             else ConformalOrthogonalGroup(n0,F);
      elif minus then
        H := (isom_grp_flag) select GeneralOrthogonalGroupMinus(n0,F)
             else ConformalOrthogonalGroupMinus(n0,F);
      else
        H := (isom_grp_flag) select GeneralOrthogonalGroupPlus(n0,F)
             else ConformalOrthogonalGroupPlus(n0,F);
      end if;
      A := polar_grp(W,T,H);

    when pseudo_symplectic_space:
      error if not isom_grp_flag, "not implemented for pseudo-symplectic spaces";
      J := StandardPseudoAlternatingForm(n0,F);
      T := VectorSpace(F,n0,J);
      H := PseudoSymplecticGroup(n0,F);
      A := polar_grp(W,T,H);

  else
    error "Internal error in polar_group_";
  end case;

  return A;  

end function;

intrinsic IsometryGroup(V::ModTupFld) -> GrpMat
{The group of isometries of the polar space V}
  F := BaseRing(V);
  require ISA(Type(F), Fld) : "base ring should be a field";
  tp := polar_type(V);
  require tp ne unknown_space : "argument is not a polar space";
  // if the form is skew hermitian, find a multiple which is hermitian.
  if tp eq unitary_space and isSkewUnitarySpace(V) then
    sigma := V`Involution;
    a := F.1 - sigma(F.1);
    W := UnitarySpace(a*V`ip_form,sigma);
  else
    W := V;
  end if;
  return polar_group_(F,W,tp,true);
end intrinsic;

intrinsic SimilarityGroup(V::ModTupFld) -> GrpMat
{The group of similarities of the polar space V}
  F := BaseRing(V);
  require ISA(Type(F), Fld) : "base ring should be a field";
  tp := polar_type(V);
  require tp ne unknown_space : "argument is not a polar space";
  if tp eq unitary_space and isSkewUnitarySpace(V) then
    sigma := V`Involution;
    a := F.1 - sigma(F.1);
    W := UnitarySpace(a*V`ip_form,sigma);
  else
    W := V;
  end if;
  return polar_group_(F,W,tp,false);
end intrinsic;

/*
intrinsic IsometryGroupAlt(V::ModTupFld) -> GrpMat
{The group of isometries of the polar space V}
  F := BaseRing(V);
  require ISA(Type(F), Fld) : "base ring should be a field";
  tp := polar_type(V);
  require tp ne unknown_space : "argument is not a polar space";

  R := (tp eq quadratic_space) select SingularRadical(V) else Radical(V);
  n := Dimension(V);
  r := Dimension(R);
  n0 := n - r;
  if r eq n then return GL(V); end if;
  if r eq 0 then
    W := V;
  else
//  if there is a non-trivial radical R, the isometry group contains all
//  groups of the form H x GL(R), where H is the group of isometries of a
//  complement to R.

//  W is a complement to R in V.  Cannot use Complement(V,R) because
//  the return value is not always recognised as a subspace of V.
    W := sub<V|[e : e in ExtendBasis(B,V) | e notin B] where B is Basis(R)>;
  end if;
  q := #F;
  
// ...........................
    isom_grp := function(W,T,H)
    // W is a non-degenerate polar space, 
    // T is the standard version, and
    // H is the group of isometries of T.
      flag, f := IsIsometric(W,T);
      assert flag;
      M := Matrix(F,n0,n0,[f(W.i) : i in [1..n0]]);
      wgens := [ M*H.i*M^-1 : i in [1..Ngens(H)] ];
      ord := FactoredOrder(H);
      if r eq 0 then
        gens := wgens;
      else
        I0 := IdentityMatrix(F,n0);
        I1 := IdentityMatrix(F,r);
        Y := GL(r,F);
        gens := [ DiagonalJoin(g,I1) : g in wgens ] cat
                [ DiagonalJoin(I0,g) : g in Generators(Y) ];
        u := IdentityMatrix(F,n);
        u[1,n0+1] := F!1;
        // u is a transvection
        Append(~gens, u);
        C := Matrix( Basis(W) cat Basis(R) );
        gens := [C^-1*g*C : g in gens];
        ord *:= FactoredOrder(Y)*Factorisation(q^(n0*r));
      end if;
      A := sub<GL(V) | gens>;
      if n gt 1 then
        A`Order := ord;
      end if;
      return A;
    end function;
// ...........................

  case tp :
    when quadratic_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      Q := StandardQuadraticForm(n0,F : Minus := minus, Variant := "Revised" );
      T := QuadraticSpace(Q);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if IsOdd(q) and not IsIsometric(W,T) then
          T := QuadraticSpace(PrimitiveElement(F)*Q);
        end if;
        H := GeneralOrthogonalGroup(n0,F);
      elif minus then
        H := GeneralOrthogonalGroupMinus(n0,F);
      else
        H := GeneralOrthogonalGroupPlus(n0,F);
      end if;
      A := isom_grp(W,T,H);

    when symplectic_space:
      J := StandardAlternatingForm(n0,F);
      T := SymplecticSpace(J);
      H := SymplecticGroup(n0,F);
      A := isom_grp(W,T,H);

    when unitary_space:
      J, sigma := StandardHermitianForm(n0,F);
      T := UnitarySpace(J,sigma);
      H := GeneralUnitaryGroup(n0,F);
      A := isom_grp(W,T,H);

    when orthogonal_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      J := StandardSymmetricForm(n0,F : Minus := minus, Variant := "Revised" );
      T := VectorSpace(F,n0,J);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if not IsIsometric(W,T) then
          T := VectorSpace(F,n0,PrimitiveElement(F)*J);
        end if;
        H := GeneralOrthogonalGroup(n0,F);
      elif minus then
        H := GeneralOrthogonalGroupMinus(n0,F);
      else
        H := GeneralOrthogonalGroupPlus(n0,F);
      end if;
      A := isom_grp(W,T,H);

    when pseudo_symplectic_space:
      J := StandardPseudoAlternatingForm(n0,F);
      T := VectorSpace(F,n0,J);
      H := PseudoSymplecticGroup(n0,F);
      A := isom_grp(W,T,H);

  else
    error "Internal error in IsometryGroup";
  end case;

  return A;  

end intrinsic;

intrinsic SimilarityGroupAlt(V::ModTupFld) -> GrpMat
{The group of similarities of the polar space V}
  F := BaseRing(V);
  require ISA(Type(F), Fld) : "base ring should be a field";
  tp := polar_type(V);
  require tp ne unknown_space : "argument is not a polar space";

  R := (tp eq quadratic_space) select SingularRadical(V) else Radical(V);
  n := Dimension(V);
  r := Dimension(R);
  n0 := n - r;
  if r eq n then return GL(V); end if;
  if r eq 0 then
    W := V;
  else
//  if there is a non-trivial radical R, the similarity group contains all
//  groups of the form H x GL(R), where H is the group of similariies of a
//  complement to R.

//  W is a complement to R in V.  Cannot use Complement(V,R) because
//  the return value is not always recognised as a subspace of V.
    W := sub<V|[e : e in ExtendBasis(B,V) | e notin B] where B is Basis(R)>;
  end if;
  q := #F;
  
// ...........................
    sim_grp := function(W,T,H)
    // W is a non-degenerate polar space, 
    // T is the standard version, and
    // H is the group of similarities of T.
      flag, f := IsIsometric(W,T);
      assert flag;
      M := Matrix(F,n0,n0,[f(W.i) : i in [1..n0]]);
      wgens := [ M*H.i*M^-1 : i in [1..Ngens(H)] ];
      ord := FactoredOrder(H);
      if r eq 0 then
        gens := wgens;
      else
        I0 := IdentityMatrix(F,n0);
        I1 := IdentityMatrix(F,r);
        Y := GL(r,F);
        gens := [ DiagonalJoin(g,I1) : g in wgens ] cat
                [ DiagonalJoin(I0,g) : g in Generators(Y) ];
        u := IdentityMatrix(F,n);
        u[1,n0+1] := F!1;
        // u is a transvection
        Append(~gens, u);
        C := Matrix( Basis(W) cat Basis(R) );
        gens := [C^-1*g*C : g in gens];
        ord *:= FactoredOrder(Y)*Factorisation(q^(n0*r));
      end if;
      A := sub<GL(V) | gens>;
      if n gt 1 then
        A`Order := ord;
      end if;
      return A;
    end function;
// ...........................

  case tp :
    when quadratic_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      Q := StandardQuadraticForm(n0,F : Minus := minus, Variant := "Revised" );
      T := QuadraticSpace(Q);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if IsOdd(q) and not IsIsometric(W,T) then
          T := QuadraticSpace(PrimitiveElement(F)*Q);
        end if;
        H := ConformalOrthogonalGroup(n0,F);
      elif minus then
        H := ConformalOrthogonalGroupMinus(n0,F);
      else
        H := ConformalOrthogonalGroupPlus(n0,F);
      end if;
      A := sim_grp(W,T,H);

    when symplectic_space:
      J := StandardAlternatingForm(n0,F);
      T := SymplecticSpace(J);
      H := ConformalSymplecticGroup(n0,F);
      A := sim_grp(W,T,H);

    when unitary_space:
      J, sigma := StandardHermitianForm(n0,F);
      T := UnitarySpace(J,sigma);
      H := ConformalUnitaryGroup(n0,F);
      A := sim_grp(W,T,H);

    when orthogonal_space:
      m := WittIndex(W);
      minus := n0 eq 2*m+2;
      J := StandardSymmetricForm(n0,F : Minus := minus, Variant := "Revised" );
      T := VectorSpace(F,n0,J);
      if n0 eq 1 then
        H := sub<GL(1,F)| Matrix(F,1,1,[-1]) >;
      elif IsOdd(n0) then
        if not IsIsometric(W,T) then
          T := VectorSpace(F,n0,PrimitiveElement(F)*J);
        end if;
        H := ConformalOrthogonalGroup(n0,F);
      elif minus then
        H := ConformalOrthogonalGroupMinus(n0,F);
      else
        H := ConformalOrthogonalGroupPlus(n0,F);
      end if;
      A := sim_grp(W,T,H);

    when pseudo_symplectic_space:
      error "Not implemented for pseudo-alternating spaces";
//      J := StandardPseudoAlternatingForm(n0,F);
//      T := VectorSpace(F,n0,J);
//      H := PseudoSymplecticGroup(n0,F);
//      A := sim_grp(W,T,H);

  else
    error "Internal error in SimilarityGroup";
  end case;

  return A;  

end intrinsic;
*/

intrinsic WittDecomposition(V::ModTupFld) -> SeqEnum[ModTupFld]
{ The Witt decomposition [R,P,N,D] of the space V such that V is the 
  orthogonal sum of R, P+N and D where R is the radical, P+N is hyperbolic
  and D is anisotropic }
  if IsQuadraticSpace(V) and Characteristic(BaseField(V)) eq 2 then
    R := SingularRadical(V);
  else 
    R := Radical(V);
  end if;
  W := (Dimension(R) eq 0) select V
       else sub<V|[e : e in ExtendBasis(B,V) | e notin B] where B is Basis(R)>;
  hs := HyperbolicSplitting(W);
  P := sub<V| [ e[1] : e in hs[1] ] >;
  N := sub<V| [ e[2] : e in hs[1] ] >;
  D := sub<V| hs[2] >;
  return [R,P,N,D];
end intrinsic;

/* 
  According to Lam (The Algebraic Theory of Quadratic Forms), the
  Witt index is half the dimension of a maximal hyperbolic subspace
*/
intrinsic WittIndex(V::ModTupFld) -> RngIntElt
{ The Witt index of the space V }
  return Dimension(wd[2]) where wd is WittDecomposition(V);
end intrinsic;

intrinsic MaximalTotallyIsotropicSubspace(V::ModTupFld) -> ModTupFld
{ A representative maximal totally isotropic subspace of the polar space V }
  wd := WittDecomposition(V);
  return sub<V| wd[1],wd[2] >;
end intrinsic;


/*****************************************************
  The following intrinsic is required for Witt's theorem
*/
intrinsic CommonComplement(V::ModTupFld, U1::ModTupFld, U2::ModTupFld) -> ModTupFld
{A common complement to the subspaces U1 and U2 in the vector space V.
 The subspaces must have the same dimension.}
  require Dimension(U1) eq Dimension(U2): "U1 and U2 must have the same dimension";
  E := [e : e in ExtendBasis(C,V) | e notin C] where C is Basis(U1+U2);
  if U1 ne U2 then
    B := Basis(U1 meet U2);
    B1 := ExtendBasis(B,U1);
    B2 := ExtendBasis(B,U2);
    F := E cat [B1[ndx] + B2[ndx] : ndx in [#B+1..#B1]];
  else
    F := E;
  end if;
  return sub<V |  F >;
end intrinsic;

/*****************************************************
  Witts theorem
  -------------
  An implementation of Witt's theorem on the extension
  of an isometry defined on a subspace of a symplectic, 
  unitary or quadratic space.
  
  Input:
    U,V,f
    V: a space with a reflexive form J
    U: a subspace of V
    f : U -> V is an isometry such that 
    f(U\cap rad V) = f(U)\cap rad V 
    
  Conditions:
    If the characteristic is 2 and J is symmetric,
    then J should be alternating

  Return: 
    An extension of f to an isometry V -> V
*/
intrinsic ExtendIsometry(V::ModTupFld,U::ModTupFld,f::Map) -> Map
{An extension of the isometry f : U -> V to an isometry V -> V, 
 where V carries a symplectic, unitary or quadratic form}
   require not IsPseudoSymplecticSpace(V) : "space is pseudo-symplectic";
 
  if Dimension(U) eq 0 then return IdentityHomomorphism(V); end if;

  R := Radical(V);
  require (f(U) meet R) eq (f(U meet R)): "cannot extend the map";
  require IsIsometry(U,V,f): "the map is not an isometry";

  BU := Basis(U);
  if BU subset R then
    vprint ExtendIsometry, 2 : "U is contained in the radical";
    E := [ e : e in ExtendBasis(BU,V) | e notin BU ];
    return hom< V -> V | [u -> f(u) : u in BU] cat [e -> e : e in E] >;
  end if;

  if R notsubset U then // Extend f along the radical
    vprint ExtendIsometry, 2 : "extending along radical";
    W := CommonComplement(R,U meet R, f(U) meet R );
    U_ := U + W;
    // replace f by f + 1_W
    f := hom< U_ -> V | [v -> f(v) : v in BU ] cat [e -> e : e in Basis(W)] >;
    U := U_;
    BU := Basis(U);
  end if;

  // At this point rad V is a proper subset of U
  E := (Dimension(R) eq 0) select BU else ExtendBasis(R,U);
  v := E[#E];
  BH := Prune(E);
  H := sub< U | BH >; // H is a hyperplane containing the radical
  // Recursion
  g1 := ExtendIsometry(V,H,hom< H -> V | [h -> f(h) : h in BH]>);
  if g1(v) eq f(v) then return g1; end if;
  f2 := hom< U -> V | [ u -> f(u) @@ g1 : u in BU] >;
  // f2 fixes every element of H
  p := f2(v) - v;
  Pperp := OrthogonalComplement(V,sub<V|p>);
  assert Dimension(Pperp) eq Dimension(V) - 1;

  if U notsubset Pperp then
    vprint ExtendIsometry, 2 :  "U is not a subset of P perp";
    W := [e : e in ExtendBasis(BH,Pperp) | e notin BH];
    return hom< V -> V | [u -> f(u) : u in BU] cat [w -> g1(w) : w in W] >;
  end if;
  // U and f2(U) are contained in Pperp
  assert p in Pperp;
  assert DotProduct(p,p) eq 0;
  // Extend f2 to h : Pperp -> V
  X := U + f2(U);
  S := [e : e in ExtendBasis(BX,Pperp) | e notin BX] where BX is Basis(X);
  if X notsubset U then Append(~S,p); end if;
  h := hom< Pperp -> V | [u -> f2(u) : u in BU] cat [w -> w : w in S] >;

  assert forall{ e : e in BH cat S | h(e) eq e };
  
  w := HyperbolicPair(V,p);
  Q := OrthogonalComplement(V,sub<V|w>) meet Pperp;
  Z := OrthogonalComplement(V,h(Q) + sub<V|w>);
  assert exists(y){ y : y in Basis(Z) | y notin Pperp };
  z := HyperbolicPair(sub<V|h(p),Z.1>,h(p));
  
  return hom< V -> V | [u -> g1(h(u)) : u in Basis(Pperp)] cat [w -> g1(z)] >;
end intrinsic;

/*****************************************************
  The Wall form
  -------------
  Given an isometry f of a quadratic, symplectic or unitary space V with
  bilinear form B, the Wall form of f is the form chi defined on the image I 
  of 1-f by chi(u,v) := B(w,v), where u = w(1-f).
  
  In general, the Wall form is not reflexive.
*/
intrinsic WallForm(V::ModTupFld, f::Mtrx) -> ModTupFld, Map
{The space of the Wall form of the isometry f and its embedding in V}
  tp := polar_type(V);
  require tp le unitary_space : "not a quadratic, symplectic or unitary space";
  require IsIsometry(V,f) : "not an isometry";
  F := BaseRing(V);
// Get the kernel of 1 - f
  K := sub<V | Basis(Eigenspace(f,1))>;
  if K eq V then
    I := VectorSpace(F,0);
    mu := hom< I -> V | >;
  else
    MI := Matrix([ e : e in ExtendBasis(K,V) | e notin K ]);
    MIf_ := MI*(Parent(Matrix(f))!1 - f);
    MIft := (tp eq unitary_space) select ConjugateTranspose(MIf_,V`Involution)
      else Transpose(MIf_);
    chi := MI*InnerProductMatrix(V)*MIft;
    I := VectorSpace(F,Nrows(MI),chi);
    mu := hom< I -> V | MIf_ >;
  end if;
  // Return an inner-product space and an embedding into V
  if tp eq unitary_space then I`Involution := V`Involution; end if;
  return I, mu;
end intrinsic;

intrinsic GeneralisedWallForm(V::ModTupFld, f::Mtrx) -> ModTupFld, Map
{The space of the generalised Wall form of the similarity f and its embedding in V}
  tp := polar_type(V);
  require tp le 2 : "not a quadratic or symplectic space";
  flag, lambda := IsSimilarity(V,f);
  require flag : "not a similarity";
  if lambda eq 1 then return WallForm(V,f); end if;
  isq, a := IsSquare(lambda);
  F := BaseRing(V);
  J := InnerProductMatrix(V);
  if not isq then
    P := PolynomialRing(F); x := P.1;
    F<a> := ext<F | x^2-lambda >;
    J := ChangeRing(J,F);
    f := ChangeRing(f,F);
    V := ChangeRing(V,F);
  end if;
  A := Parent(Matrix(f));
  f_ := A!a - f;
  K := sub<V | Basis(Eigenspace(f,1))>;
  if K eq V then
    I := VectorSpace(F,0);
    mu := hom< I -> V | >;
  else
    MI := Matrix([ e : e in ExtendBasis(K,V) | e notin K ]);
    chi := MI*J*Transpose(f_)*Transpose(MI);
    I := VectorSpace(F,Nrows(MI),chi);
    mu := hom< I -> V | MI*f_ >;
  end if;
  // Return an inner-product space and an embedding into V
  return I, mu;
end intrinsic;

intrinsic WallIsometry(V::ModTupFld,I::ModTupFld,mu::Map) -> Mtrx
{ The inverse of WallForm: an isometry corresponding to the embedding 
  mu : I -> V, where V is a quadratic, symplectic or unitary space}
// First some checks
  tp := polar_type(V);
  require tp le unitary_space : "not a quadratic, symplectic or unitary space";
  if Dimension(I) eq 0 then return IdentityMatrix(BaseRing(V),Dimension(V)); end if;
  require Image(mu) subset V : "the image of mu must be a subspace of V";
  B0 := Basis(I);
  chi := DotProductMatrix(B0);
  require Dimension(NullSpace(chi)) eq 0 : "degenerate form";
  require Dimension(Image(mu) meet Radical(V)) eq 0 : "subspace meets the radical";
  J0 := Matrix([[DotProduct(mu(u),mu(v)) : v in B0] : u in B0]);
  J := InnerProductMatrix(V);
  B := Matrix([mu(u) : u in B0]);
  if tp eq quadratic_space then
    require chi + Transpose(chi) eq J0 : "symmetric bilinear form not compatible";
    require forall{ u : u in B0 | DotProduct(u,u) eq QuadraticNorm(mu(u)) } :
      "quadratic form not compatible";
    BT := Transpose(B);
  elif tp eq symplectic_space then
    require chi - Transpose(chi) eq J0 : "alternating form not compatible";
    BT := Transpose(B);
  else // tp eq unitary_space
    sigma := I`Involution;
    require chi + ConjugateTranspose(chi,sigma) eq J0 : "hermitian form not compatible";
    BT := ConjugateTranspose(B,sigma);
  end if;

  return One(Parent(J)) - J*BT*chi^-1*B;
end intrinsic;

