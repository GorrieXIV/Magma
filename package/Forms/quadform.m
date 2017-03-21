freeze;
/*****************************************************
  Functions for quadratic forms defined on finite 
  dimensional vector spaces over finite fields,
  including fields of characteristic two.
  
  See formutils.m for code common to all types of geometries.

  August 2010 Don Taylor

  $Id: quadform.m 48512 2014-09-30 07:24:54Z don $

  Intrinsics defined in this file:

    ArfInvariant
    DicksonInvariant
    HasSingularVector
    HyperbolicBasis
    IsNonsingular
    IsTotallySingular
    MaximalTotallySingularSubspace
    MetabolicSpace
    OrthogonalReflection
    OrthogonalSum
    QuadraticFormPolynomial
    QuadraticNorm
    QuadraticSpace
    ReflectionFactors
    RootSequence
    SemiOrthogonalBasis
    SemiOrthogonalBasis2
    SiegelTransformation
    SingularRadical
    SpinorNorm
    SymmetricToQuadraticForm
    TotallySingularComplement
    WallDecomposition
  
******************************************************/

/* Given a vector space V of dimension n over a field K, a
   *quadratic form* on V is a function Q : V -> K such that 
   -  Q(av) = a^2 Q(v) for all a in K and all v in V;
   -  B(u,v) = Q(u+v) - Q(u) - Q(v) is bilinear.
   The bilinear form B is called the *polar form* of Q.
   (Chevalley calls this the form *associated* with Q.) 

   If b is a bilinear form (not necessarily symmetric), then
   the function Q(v) = b(v,v) is a quadratic form whose polar 
   form is B(u,v) = b(u,v) + b(v,u).  Moreover, every quadratic
   form may be represented in this way. Consequently we shall
   represent *every* quadratic form by an upper triangular 
   n x n matrix.

   In this version several functions are only available over
   finite fields.

   A lot of the code requires the quadratic space V to be non-degenerate; 
   that is, the radical of V should not contain singular vectors.
   
   Radical() and OrthogonalComplement() are in formutils.m
*/

import "formutils.m" : quadrep_;

// Messages
OnlyFldFin := "only available for quadratic spaces over finite fields";
notquad := "not a quadratic space";

/*
   A *quadratic space* is characterised as a vector space V with an
   attached quadratic form, represented by a matrix Q, which is inherited 
   by subspaces. The inner product matrix of V is Q + Transpose(Q).
  
   The following functions are defined at the C level
     IsQuadraticSpace
     QuadraticFormMatrix
     QuadraticSpace

   If Q is a matrix, then V := QuadraticSpace(Q) creates the quadratic space.
   IsQuadraticSpace(V) returns true if V has a quadratic form.
   QuadraticFormMatrix(V) returns the matrix Q.
*/

intrinsic QuadraticSpace(f::RngMPolElt) -> ModTupRng
{The quadratic space of the homogeneous polynomial f of degree 2}
  require IsHomogeneous(f) and TotalDegree(f) eq 2: "must be a quadratic form";
  P := Parent(f);
  K := BaseRing(P);
  n := Rank(P);
  Q := Matrix(K,n,n,
    [ case< Sign(i-j) | -1 : MonomialCoefficient(f,P.i*P.j),
                         0 : MonomialCoefficient(f,P.i^2),
                         default : 0 > : i,j in [1..n]]);
  return QuadraticSpace(Q);
end intrinsic;

intrinsic OrthogonalSum(V1::ModTupFld, V2::ModTupFld) -> ModTupFld, Map, Map
{The orthogonal direct sum V of quadratic spaces V1 and V2, together
 with the canonical isometric embeddings of V1 and V2 into V}
  require IsQuadraticSpace(V1) : notquad;
  require IsQuadraticSpace(V2) : notquad;
  F := BaseRing(V1);
  require F cmpeq BaseRing(V2) :
    "Arguments 1 and 2 have incompatible coefficient rings";
  V := QuadraticSpace(
    DiagonalJoin(QuadraticFormMatrix(V1),QuadraticFormMatrix(V2)));
  n1 := Dimension(V1);
  n2 := Dimension(V2);
  M1 := HorizontalJoin(IdentityMatrix(F,n1),ZeroMatrix(F,n1,n2));
  M2 := HorizontalJoin(IdentityMatrix(F,n2),ZeroMatrix(F,n2,n1));
  f1 := hom< V1 -> V | v :-> V!(v*M1) >;
  f2 := hom< V2 -> V | v :-> V!(v*M2) >;
  return V,f1,f2;
end intrinsic;

intrinsic OrthogonalTensorProduct(V1::ModTupFld, V2::ModTupFld) -> ModTupFld
{The tensor product of the quadratic spaces V1 and V2}
  require IsQuadraticSpace(V1) : notquad;
  require IsQuadraticSpace(V2) : notquad;
  F := BaseRing(V1);
  require F cmpeq BaseRing(V2) :
    "Arguments 1 and 2 have incompatible coefficient rings";
  B := KroneckerProduct(GramMatrix(V1), GramMatrix(V2));
  m := Dimension(V1) * Dimension(V2);
  for i := 2 to m do
      for j := 1 to i-1 do B[i,j] := 0; end for;
  end for;
  if Characteristic(F) eq 2 then
      for i := 1 to m do B[i,i] := 0; end for;
  else
      for i := 1 to m do B[i,i] := B[i,i]/2; end for;
  end if;
  return QuadraticSpace(B);
end intrinsic;

intrinsic QuadraticFormPolynomial(Q::AlgMatElt) -> RngMPolElt
{The quadratic form associated to the upper triangular matrix Q}
  require IsUpperTriangular(Q) : "matrix is not upper triangular";
  n := Nrows(Q);
  P := PolynomialRing(BaseRing(Q),n);
  AssignNames(~P, ["x" cat IntegerToString(i): i in [1..n]]);
  return &+[ Q[i][j]*P.i*P.j : i in [1..j], j in [1..n] ]; 
end intrinsic;

intrinsic QuadraticFormPolynomial(V::ModTupFld) -> RngMPolElt
{The quadratic form associated to the quadratic space V}
  require IsQuadraticSpace(V) : notquad;
  return QuadraticFormPolynomial(QuadraticFormMatrix(V));
end intrinsic;

/* In order to evaluate the quadratic form on an element of
   the vector space we must be careful to use the original
   matrix, not its polar form.
*/
intrinsic QuadraticNorm(v::ModTupFldElt) -> FldElt
{ The value of the quadratic form of a quadratic space on the vector v }
  V := Parent(v);
  require IsQuadraticSpace(V) : "vector must be in a quadratic space";
  Q := QuadraticFormMatrix(V);
  return (v*Q*Transpose(Matrix(v)))[1];
end intrinsic;


intrinsic SymmetricToQuadraticForm(J::AlgMatElt ) -> AlgMatElt
{The upper triangular matrix which represents the same quadratic 
 form as the symmetric matrix J. The characteristic of the field 
 must not be 2}
  require IsSymmetric(J) : "argument must be symmetric";
  require Characteristic(BaseRing(J)) ne 2 : "characteristic should not be 2";
  Q := Zero(Parent(J));
  m := Nrows(J);
  for i := 1 to m do
    Q[i,i] := J[i,i]/2;
    for j := i+1 to m do Q[i,j] := J[i,j]; end for;
  end for;
  return Q;
end intrinsic;


intrinsic HasSingularVector(V::ModTupFld) -> BoolElt, ModTupFldElt
{ Determine whether the quadratic space V contains a singular vector; 
  if it does, assign a representative as the second return value }
  require IsQuadraticSpace(V) : notquad;
  F := BaseField(V);
  require ISA( Type(F), FldFin ) : OnlyFldFin;
  if Dimension(V) eq 0 then
    return false, _; 
  end if;
  B := Basis(V);
  if exists(u){ u : u in B | QuadraticNorm(u) eq 0 } then
    return true, u;
  end if;
  if #B eq 1 then return false, _; end if;
  u := B[1];
  qu := QuadraticNorm(u);
  if #B eq 2 then
    x := PolynomialRing(F).1;
    v := B[2];
    b := DotProduct(u,v);
    qv := QuadraticNorm(v);
    roots := Roots(qu*x^2 + b*x + qv);
    if IsEmpty(roots) then
      return false, _;
    else
      return true, (roots[1][1])*u+v;
    end if;
  else
    U := sub< V | u >;
    Uperp := OrthogonalComplement(V,U);
    error if not exists(v){ v : v in Basis(Uperp) | v notin U },
      "Internal error in HasSingularVector";
    qv := QuadraticNorm(v);
    if qv eq 0 then return true, v; end if;
    if Characteristic(F) eq 2 then
      a := SquareRoot(qu^-1*qv);
      return true, a*u+v;
    else
      W := OrthogonalComplement(V,sub< V | u,v >);
      w := Basis(W)[1];
      qw := QuadraticNorm(w);
      if qw eq 0 then return true, w; end if;
      r,s := quadrep_(qu,qv,-qw);
      return true, r*u+s*v+w;
    end if;
  end if;
end intrinsic;

/*
intrinsic IsSingular(V::ModTupFld) -> BoolElt, ModTupFldElt
{}
  require IsQuadraticSpace(V) : notquad;
  return HasSingularVector(V);
end intrinsic;
*/

/*****************************************************
  If V is a quadratic space over a perfect field of  characteristic 2,
  the restriction of the quadratic form Q to the radical is a semilinear
  functional (with respect to x :-> x^2) whose kernel is the *singular
  radical* of V.  A quadratic space is nonsingular if its singular radical
  is zero.
*/
intrinsic SingularRadical(V::ModTupFld) -> ModTupFld
{ The kernel of the restriction of the quadratic form
  of the quadratic space V to the radical of V }
  require IsQuadraticSpace(V) : notquad;
  F := BaseField(V);
  require IsPerfect(F) : "only available for perfect fields";
  R := Radical(V);
  r := Dimension(R);
  if r eq 0 or Characteristic(F) ne 2 then
    return R;
  end if;
  B := Basis(R);
  if forall{ u : u in B | QuadraticNorm(u) eq 0 } then
    return R;
  end if;
  M := Matrix(F,r,1,[SquareRoot(QuadraticNorm(u)) : u in B]);
  return sub<V | Rows(BasisMatrix(NullSpace(M))*BasisMatrix(R))>;
end intrinsic;

intrinsic IsNonsingular(V::ModTupFld) -> BoolElt
{ True iff V is a non-singular quadratic space }
  require IsQuadraticSpace(V) : notquad;
  R := Radical(V);
  if Dimension(R) eq 0 then return true; end if;
  if Characteristic(BaseField(V)) ne 2 then return false; end if;
  require ISA( Type(BaseField(V)), FldFin ) : OnlyFldFin;
  return Dimension(R) eq 1 select
    QuadraticNorm(R.1) ne 0 else Dimension(R) eq 0;
end intrinsic;


intrinsic MaximalTotallySingularSubspace(V::ModTupFld) -> ModTupFld
{ A representative maximal totally singular subspace of the quadratic space V }
  require IsQuadraticSpace(V) : notquad;
  hs := HyperbolicSplitting(V);
  return sub<V| [ e[1] : e in hs[1] ] >;
end intrinsic;


/* For finite fields there is not much happening here because there
   are only two possibilities for spaces of dimension 2m over finite
   fields of characteristic two: either the form is of Witt m or
   of Witt index m-1 and this determines the Arf invariant (modulo
   { a + a^2 : a in BaseField(V) }).
*/
intrinsic ArfInvariant(V::ModTupFld) -> RngIntElt
{ The Arf invariant of the characteristic 2 quadratic space V }
  require IsQuadraticSpace(V) : notquad;
  require ISA( Type(BaseField(V)), FldFin ) : OnlyFldFin;
  require Characteristic(BaseField(V)) eq 2 : 
     "only defined in characteristic 2";
  require IsEven(Dimension(V)) : "only defined in even dimensions";
  H := HyperbolicSplitting(V);
  return IsEmpty(H[2]) select 0 else 1;
//    else QuadraticNorm(H[2][1])*QuadraticNorm(H[2][2]);
end intrinsic;

intrinsic OrthogonalReflection(a::ModTupFldElt) -> AlgMatElt
{ The reflection determined by a non-singular vector of a 
  quadratic space }
  na := QuadraticNorm(a);
  require na ne 0 : "the vector must be nonsingular";
  V := Parent(a);
  n := Dimension(V);
  return Matrix(n,n,[v - na^-1*DotProduct(v,a)*a : v in Basis(V)]);
end intrinsic;

// Siegel transformations are also known as Eichler transformations
intrinsic SiegelTransformation(u::ModTupFldElt,v::ModTupFldElt) -> AlgMatElt
{ The Siegel transformation defined by a singular vector u and a
  vector v orthogonal to u in a quadratic space }
  require QuadraticNorm(u) eq 0 : "the first vector must be singular";
  require DotProduct(u,v) eq 0 : "the vectors must be orthogonal";
  V := Parent(u);
  n := Dimension(V);
  return Matrix(n,n,
    [x + DotProduct(x,v)*u - DotProduct(x,u)*(v + QuadraticNorm(v)*u) : x in Basis(V)]);
end intrinsic;

nonIsotropicVector := function(V)
  B := Basis(V);
  n := #B;
  for i := 1 to n do
    u := B[i];
    if DotProduct(u,u) ne 0 then return true, u; end if;
    for j := i+1 to n do
      v := u + B[j];
      if DotProduct(v,v) ne 0 then return true, v; end if;
    end for;
  end for;
  return false, _;
end function;

// Find a non-singular vector in the subspace W of V
nonSingularVector := function(V,W)
  B := Basis(W);
  n := #B;
  rad := Radical(V);  // assumes Dimension(rad) le 1
  for i := 1 to n do
    u := B[i];
    if u notin rad and QuadraticNorm(u) ne 0 then return true, u; end if;
    for j := i+1 to n do
      v := u + B[j];
      if QuadraticNorm(v) ne 0 then return true, v; end if;
    end for;
  end for;
  return false, _;
end function;

// Use this only when it is known that the space does not carry an involution
isSymplecticSpace := func< W |
  J eq -Transpose(J) and forall{ i : i in [1..n] | J[i,i] eq 0 }
  where n is Nrows(J) where J is GramMatrix(W)>;

intrinsic SemiOrthogonalBasis(V::ModTupFld) -> SeqEnum
{A semi-orthogonal basis with respect to the non-degenerate, non-alternating 
 form attached to V. If the base field is GF(2), the form should be symmetric.}
  J := GramMatrix(V);
  require Determinant(J) ne 0 : "the form is degenerate";
  B := [V|];
  if Dimension(V) eq 0 then return B; end if;
  require not isSymplecticSpace(V) : "the form is alternating";
  F := BaseRing(V);
  if ISA(Type(F),FldFin) and (#F eq 2) then
    require J eq Transpose(J) : "for GF(2) the form must be symmetric";
  end if;

  W := V;
  while Dimension(W) gt 0 do
    while not isSymplecticSpace(W) do
      found, v := nonIsotropicVector(W);
      error if not found, "(SemiOrthogonalBasis) internal error 1";
      Append(~B,v);
      W := OrthogonalComplement(V,sub<V|B> : Right);
    end while;
    assert IsEven(Dimension(W));
    if Dimension(W) gt 0 then
      u := B[#B];
      Prune(~B);
      BW := Basis(W);
      v := rep{ v : v in [BW[1],BW[2],BW[1]+BW[2]] | DotProduct(u+v,u+v) ne 0};
      c := DotProduct(u+v,u+v);
      w := c*HyperbolicPair(W,v);
      if exists(b){ b : b in [F|0,1] | DotProduct(u+b*v-w,u+b*v-w) ne 0} then
        Append(~B,u+v);
        Append(~B,u+b*v-w);
      else
        // if the form is symmetric we never take this branch
        assert DotProduct(v,u) eq 0;
        assert DotProduct(w,u) eq c;
        // for some infinite fields, F.1 is 1
        d := Characteristic(F) eq 2 select F.1 else F!1;  // this is where GF(2) fails
        Append(~B,u+d*w);
        Append(~B,d*u+(1+d)*v);
      end if;
      W := OrthogonalComplement(V,sub<V|B> : Right);
    end if;
  end while;
  return B;
end intrinsic;

intrinsic SemiOrthogonalBasis2(V::ModTupFld) -> BoolElt, SeqEnum
{A maximal semi-orthogonal sequence with respect to the non-degenerate,
 non-alterating form attached to the vector space V over the field of two elements.}
 /* NOTE
 This does not always find a complete semi-orthogonal basis even when
 one exists.  The best it can do is find n-2 vectors, where n = dim(V). 
 */
  F := BaseRing(V);
  require ISA(Type(F),FldFin) and (#F eq 2) : "available only for the field of two elements";
  J := GramMatrix(V);
  require Determinant(J) ne 0 : "the form is degenerate";
  B := [V|];
  if Dimension(V) eq 0 then return true, B; end if;
  if isSymplecticSpace(V) then return false, B; end if;

  W := V;
  while Dimension(W) gt 0 do
    while not isSymplecticSpace(W) do
      found, v := nonIsotropicVector(W);
      error if not found, "(SemiOrthogonalBasis2) internal error 1";
      W := OrthogonalComplement(W,sub<W|v> : Right );
      Append(~B,v);
    end while;
    assert IsEven(Dimension(W));
    if Dimension(W) gt 0 then
      u := B[#B];
      Prune(~B);
      BW := Basis(W);
      v := rep{ v : v in [BW[1],BW[2],BW[1]+BW[2]] | DotProduct(v,u) eq 0};
      w := HyperbolicPair(W,v);
      if DotProduct(w,u) eq 0 then
        Append(~B,u+v);
        Append(~B,u+w);
      else // DotProduct(v,u) eq 0; DotProduct(w,u) eq 1;
        if Dimension(W) gt 2 then
          X := OrthogonalComplement(W,sub<W| v,w >);
          BX := Basis(X);
          v1 := rep{ v : v in [BX[1],BX[2],BX[1]+BX[2]] | DotProduct(v,u) eq 0};
          w1 := HyperbolicPair(X,v1);
          if DotProduct(w1,u) eq 0 then
            Append(~B,u+v1);
            Append(~B,u+w1);
          else 
            Append(~B,u+v);
            Append(~B,u+w+w1);
          end if;
        else // Dimension(W) eq 2
          if #B gt 0 then
            u0 := B[#B];
            a := DotProduct(u,u0);
            b := DotProduct(v,u0);
            c := DotProduct(w,u0);
            if a eq 0 and b eq 0 and c eq 0 then
              Prune(~B);
              Append(~B,u);
              Append(~B,u0+v+w);
              Append(~B,u0+w);
            elif a eq 1 and b eq 0 then
              Prune(~B);
              if c eq 0 then
                Append(~B,u+u0);
                Append(~B,u0+v);
                Append(~B,u0+w);
              else
                Append(~B,u);
                Append(~B,u+u0+v);
                Append(~B,u+u0+w);
              end if;
            else
              Append(~B,u); // put back u
              break;
            end if;
          else
            Append(~B,u); // put back u
            break;
          end if;
        end if;
      end if;
      W := OrthogonalComplement(V,sub<V|B> : Right);
    end if;
  end while;
  return (#B eq Dimension(V)), B;
end intrinsic;

 
intrinsic DicksonInvariant(V::ModTupFld,f::Mtrx) -> RngIntElt
{The Dickson invariant of the isometry f of the quadratic space V}
  require IsQuadraticSpace(V) : notquad;
  I,_ := WallForm(V,f);
  return Dimension(I) mod 2;
end intrinsic;

intrinsic SpinorNorm(V::ModTupFld,f::Mtrx) -> RngIntElt
{The spinor norm of the isometry f of the quadratic space V}
  I,_ := WallForm(V,f);
  return Discriminant(I);
end intrinsic;

intrinsic TotallySingularComplement(V::ModTupFld, U::ModTupFld, W::ModTupFld) -> ModTupFld
{A totally singular complement, containing W, to the orthogonal complement of 
 the totally singular subspace U}
  require IsTotallySingular(U) : "first space is not totally singular";
  require IsTotallySingular(W) : "second space is not totally singular";
  Uperp := OrthogonalComplement(V,U);
  require Dimension(Uperp meet W) eq 0 : "second space meets the orthogonal complement of first space";
  Z := OrthogonalComplement(V,W);
  UZ := U meet Z;
  while Dimension(UZ) gt 0 do
    p := rep{<u,w> : u in Basis(UZ), w in Basis(Z) | DotProduct(u,w) ne 0};
    u := p[1]; w := p[2];
    v := -QuadraticNorm(w)*a^-2*u+a^-1*w where a is DotProduct(u,w);
    W := sub<V| W, v>;
    Z := OrthogonalComplement(V,W);
    UZ := U meet Z;
  end while;
  return W;
end intrinsic;

// assumes that I is symplectic and hence mu(I) is totally singular
rootSeq := function(V,f,I,mu)
  VI := sub< V | [mu(b) : b in Basis(I)] >;
  rad := Radical(V);
  if Dimension(rad) gt 0 then
    w := VI.1 + rad.1;
  else
    W := OrthogonalComplement(V,VI);
    found, w := nonSingularVector(V,W);
    error if not found, "(refSeq) internal error";
  end if;
  t := OrthogonalReflection(V!w);
  I,mu := WallForm(V,f*t);
  B := SemiOrthogonalBasis(I); // we know that the form is symmetric
  R := [V!w];
  for b in B do
    Append(~R,mu(b));
  end for;
  return R;
end function;

// assumes that I is symplectic and hence mu(I) is totally singular
refSeq := function(V,f,I,mu)
  VI := sub< V | [mu(b) : b in Basis(I)] >;
  rad := Radical(V);
  if Dimension(rad) gt 0 then
    w := VI.1 + rad.1;
  else
    W := OrthogonalComplement(V,VI);
    found, w := nonSingularVector(V,W);
    error if not found, "(refSeq) internal error";
  end if;
  t := OrthogonalReflection(V!w);
  I,mu := WallForm(V,f*t);
  B := SemiOrthogonalBasis(I); // we know that the form is symmetric
  T := [t];
  for a in B do
    Append(~T,OrthogonalReflection(mu(a)));
  end for;
  return T;
end function;

//  The next function is the intrinsic (in formutils.m) stripped of error checking
WallIsometry_ := function(V,I,mu)
  if Dimension(I) eq 0 then return IdentityMatrix(BaseRing(V),Dimension(V)); end if;
  B0 := Basis(I);
  chi := DotProductMatrix(B0);
  J := InnerProductMatrix(V);
  B := Matrix([mu(u) : u in B0]);
  return One(Parent(J)) - J*Transpose(B)*chi^-1*B;
end function;

// A sequence of roots such that f is the product of the corresponding reflections (over GF(2))
rootSequence2 := function(V, f)
  F := BaseRing(V);
  I, mu := WallForm(V,f);
  complete, B := SemiOrthogonalBasis2(I);
  R := [V| mu(b) : b in B];
  T := [OrthogonalReflection(a) : a in R];
  if not complete then
    if #B gt 0 then
      g := Parent(f)!&*T;
      f *:= g;
      I, mu := WallForm(V,f);
    end if;
    // mu(I) is totally singular and I is alternating
    if 2*Dimension(I) lt Dimension(V) then
      R cat:= rootSeq(V,f,I,mu);
    else
      v := I.1;
      w := HyperbolicPair(I,v);
      I1 := sub<I|v,w>;
      I2 := OrthogonalComplement(I,I1 : Right);
      f1 := WallIsometry_(V,I1,mu);
      f2 := WallIsometry_(V,I2,mu);  // f eq f2*f1
      R1 := rootSeq(V,f1,I1,mu);
      R2 := rootSeq(V,f2,I2,mu);
      R := R1 cat R2;
    end if;
  end if;
  return Reverse(R);
end function;

// A sequence of reflections whose product is f (over GF(2))
/*
reflectionFactors2 := function(V, f)
  F := BaseRing(V);
  I, mu := WallForm(V,f);
  complete, B := SemiOrthogonalBasis2(I);
  T := [OrthogonalReflection(mu(a)) : a in B];
  if not complete then
    if #B gt 0 then
      g := Parent(f)!&*T;
      f *:= g;
      I, mu := WallForm(V,f);
    end if;
    // mu(I) is totally singular and I is alternating
    if 2*Dimension(I) lt Dimension(V) then
      T cat:= refSeq(V,f,I,mu);
    else
      v := I.1;
      w := HyperbolicPair(I,v);
      I1 := sub<I|v,w>;
      I2 := OrthogonalComplement(I,I1 : Right);
      f1 := WallIsometry_(V,I1,mu);
      f2 := WallIsometry_(V,I2,mu);  // f eq f2*f1
      T1 := refSeq(V,f1,I1,mu);
      T2 := refSeq(V,f2,I2,mu);
      T := T1 cat T2;
    end if;
  end if;
  return Reverse(T);
end function;
*/
intrinsic RootSequence(V::ModTupFld, f::Mtrx) -> SeqEnum
{A sequence of vectors such that the product of the corresponding 
 orthogonal reflections is f. The empty sequence is returned if
 f is the identity matrix}
  F := BaseRing(V);
  if f eq IdentityMatrix(F,Dimension(V)) then return [V|]; end if;
  require IsQuadraticSpace(V) : notquad;
  require IsIsometry(V,f) : "not an isometry";
  if IsFinite(F) and #F eq 2 then
    R := rootSequence2(V,f);
  else
    I, mu := WallForm(V,f);
    alt := isSymplecticSpace(I);
    if alt then // Image(mu) is totally singular
      rad := Radical(V);
      if Dimension(rad) gt 0 then
        a := mu(I.1)+rad.1;
      else
//        found := exists(a){a : a in V | QuadraticNorm(a) ne 0 and a notin Image(mu)};
        found, a := nonSingularVector(V,V);
        error if not found, "(RootSequence) internal error";
      end if;
      t := OrthogonalReflection(V!a);
      I,mu := WallForm(V,f*t);
    end if;
    B := SemiOrthogonalBasis(I);
    R := [mu(b) : b in Reverse(B) ];
    if alt then Append(~R,a); end if;
  end if;
  return R;
end intrinsic;

intrinsic ReflectionFactors(V::ModTupFld, f::Mtrx) -> SeqEnum
{A sequence of reflections whose product is f. The empty sequence 
 corresponds to the identity matrix}
  return [OrthogonalReflection(a) : a in RootSequence(V,f)];
end intrinsic;

/*
intrinsic ReflectionFactors(V::ModTupFld, f::Mtrx) -> SeqEnum
{A sequence of reflections whose product is f. The empty sequence 
 corresponds to the identity matrix}
  F := BaseRing(V);
  if f eq IdentityMatrix(F,Ncols(f)) then return [Parent(f)|]; end if;
  if IsFinite(F) and #F eq 2 then
    T := reflectionFactors2(V,f);
  else
    I, mu := WallForm(V,f);
    alt := isSymplecticSpace(I);
    if alt then
      rad := Radical(V);
      if Dimension(rad) gt 0 then
        a := mu(I.1)+rad.1;
      else
//        found := exists(a){a : a in V | QuadraticNorm(a) ne 0 and a notin Image(mu)};
        found, a := nonSingularVector(V,V);
        error if not found, "(ReflectionFactors) internal error";
      end if;
      t := OrthogonalReflection(a);
      I,mu := WallForm(V,f*t);
    end if;
    B := SemiOrthogonalBasis(I);
    T := [OrthogonalReflection(mu(a)) : a in Reverse(B) ];
    if alt then Append(~T,t); end if;
  end if;
  return T;
end intrinsic;
*/

intrinsic IsTotallySingular(U::ModTupFld) -> BoolElt
{ True if the quadratic space U is totally singular }
  require IsQuadraticSpace(U) : notquad;
  J := GramMatrix(U);
  return J eq Parent(J)!0 and forall{b : b in Basis(U) | QuadraticNorm(b) eq 0};
end intrinsic;

intrinsic HyperbolicBasis(U::ModTupFld, B::SeqEnum, W::ModTupFld) -> SeqEnum
{Given complementary totally singular subspaces U and W and a basis B for U,
return a sequence of pairwise orthogonal hyperbolic pairs whose second components
form a basis for W}
  require IsTotallySingular(U) : "first space is not totally singular";
  require IsTotallySingular(W) : "second space is not totally singular";
  V := Generic(U);
  Uperp := OrthogonalComplement(V,U);
  require Dimension(Uperp meet W) eq 0 : "second space meets the orthogonal complement of first space";
  k := #B;
  require U eq sub<V|B> and k eq Dimension(U): "not a basis";
  L := [];
  for i := 1 to k do
    u := B[i];
    H := sub<U|Remove(B,i)>;
    v := W!(OrthogonalComplement(W,H).1); // omitting W! caused a crash (in Magma 2.16)
    Append(~L,<u,DotProduct(u,v)^-1*v>);
  end for;
  return L;
end intrinsic;

intrinsic WallDecomposition(V::ModTupFld, f::Mtrx) -> Mtrx, Mtrx
{ Return a (Wall) regular element fr and a unipotent element fu
  such that f = fr * fu = fu * fr }
  f_ := Parent(Matrix(f))!1 - f;
  prev := f_;
  next := prev*f_;
  while Rank(prev) gt Rank(next) do
    prev := next;
    next := prev*f_;
  end while;
  I, mu := WallForm(V,f);
  Ir := sub< I | [b@@mu : b in Basis(Image(prev))] >;
  fr := WallIsometry(V,Ir,mu);
  return fr, f*fr^-1;
end intrinsic;

intrinsic MetabolicSpace(V::ModTupFld) -> ModTupFld
{The metabolic space based on the quadratic space V}
  require IsQuadraticSpace(V) : notquad;
  q := QuadraticFormMatrix(V);
  n := Dimension(V);
  M := DiagonalJoin(q,ZeroMatrix(BaseRing(V),n,n));
  for i := 1 to n do M[i,2*n+1-i] := 1; end for;
  return QuadraticSpace(M);
end intrinsic;
