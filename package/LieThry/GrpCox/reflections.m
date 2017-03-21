freeze;
/*=========================================================
  Don Taylor

  3 September 2010 

  $Id: reflections.m 45908 2014-01-21 06:20:02Z don $

==========================================================
  Basic code for pseudo-reflections and general reflection
  groups.
  
  Pseudo-reflections include projections and transvections.

  The following intrinsics defined in the old FIURG package 
  have been replaced:
  
   - ComplexReflectionGroup
   - ImprimitiveReflectionGroup
   - ShephardTodd

  The "abstract" Cartan matrices used in this package include:
   - the ordinary (integral) Cartan matrices for Weyl groups and 
     Lie algebras
   - complex Cartan matrices for the complex reflection groups
     (see CartanData.m for the actual matrices)
   - the generalised Cartan matrices for Kac-Moody algebras
   
  A square matrix C is an abstract Cartan matrix if
   - C[i,j] = 0 if and only if C[j,i] = 0
   - the diagonal elements of I - C are roots of unity ne 1

  The following intrinsics have been removed from GrpCox and replaced 
  by code in this file:
  
    - IsReflection
    - IsReflectionGroup
    
  Intrinsics defined in this file:

    BasicRootMatrices
    ComplexReflectionGroup
    ImprimitiveReflectionGroup
    IsAbstractCartanMatrix
    IsPseudoReflection
    IsReflection
    IsReflectionGroup
    IsTransvection
    PseudoReflection
    PseudoReflectionGroup
    Reflection
    ShephardTodd
    SymplecticTransvection
    Transvection
    TransvectionFactors
    UnitaryReflection
    UnitaryTransvection

==========================================================*/
declare verbose Transvection, 4;

/*
 There is a ScalarProduct intrinsic (with two signatures) in Nice.m
 which does something similar to the following. (See also, DotProduct)
*/

// Regard v as an element of the dual space and return <u,v> 
pairing := func< u, v | (u*Transpose(Matrix(v)))[1] >;


// ==========================================================
// PART I  Pseudo-reflections
// ==========================================================
pseudo_ref_type := function( a, c )
  /* Return codes for p:
      0 transvection
      1 projection
     >1 reflection (dilatation)
  */
  V := Generic(Parent(a));
  flag := (c in V);
  if flag then
    p := pairing(a,c);
    msg := (p eq 0) select "the root and coroot define a transvection"
           else (p eq 1) select "the root and coroot define a projection"
           else "the root and coroot define a reflection";
    return flag, msg, p, V;
  else
    msg := "the root and coroot are not in the same space";
    return flag, msg, _, _;
  end if;
end function;


// Constructions
// -------------
pseudoReflection_ := function(V,a,c)
  // Assumes that a and c are the root and coroot of a pseudo-reflection
  // in the space V
  return MatrixAlgebra(BaseRing(V),Dimension(V))!1 - Transpose(Matrix(c))*Matrix(a);
end function;


intrinsic PseudoReflection(root::ModTupRngElt, coroot::ModTupRngElt ) -> AlgMatElt
{ The pseudo-reflection with the given root and coroot }
  flag, msg, reftype, V := pseudo_ref_type(root,coroot);
  require flag : msg;
  return pseudoReflection_(V, root, coroot);
end intrinsic;


intrinsic Transvection( root::ModTupRngElt, coroot::ModTupRngElt ) -> AlgMatElt
{ The transvection with the given root and coroot }
  flag, msg, reftype, V := pseudo_ref_type(root,coroot);
  require flag : msg;
  require reftype ne 1  : msg;
  require reftype eq 0  : msg;
  return pseudoReflection_(V, root, coroot);
end intrinsic;


intrinsic Reflection( root::ModTupRngElt, coroot::ModTupRngElt ) -> AlgMatElt
{ The reflection with the given root and coroot }
  flag, msg, reftype, V := pseudo_ref_type(root,coroot);
  require flag : msg;
  require reftype ne 1  : msg;
  require reftype ne 0  : msg;
  return pseudoReflection_(V, root, coroot);
end intrinsic;

// The following intrinsic has been moved from GrpCox.m
intrinsic Reflection( root::LatElt, coroot::LatElt ) -> AlgMatElt
{The reflection with the given root and coroot}
  V := RSpace( Integers(), Ncols(root) );
  return Reflection( V!root, V!coroot );
end intrinsic;

// Factorisation into a product of transvections
// ---------------------------------------------

/* Check whether g is a scalar transformation modulo W.
   If so, return the scalar.
   If not, find a vector 'a' in V such that a*g is not a 
   multiple of 'a' modulo W.  
*/
isHomothety := function(V,W,g)
  BW := Basis(W);
  EW := [ e : e in ExtendBasis(W,V) | e notin W ];
  m := #EW;

  for i := 1 to m do
    a := EW[i];
    c := a*g;
    if c notin sub<V | W, a > then return false, a, c; end if;
    for j := i+1 to m do
      b := a + EW[j];
      c := b*g;
      if c notin sub<V | W, b > then return false, b, c; end if;
    end for;
  end for;
  BM := Matrix(BW cat EW);
  a := EW[1];
  flag, v, K := IsConsistent(BM,a*g);
  error if not flag, "Inconsistent data in isHomothety";
  return true, v[#BW+1], _;
end function;

// return a basis for the space of linear functionals
// which vanish on a subspace W of V.
reldual := func< W | Basis(NullSpace(Transpose(BasisMatrix(W)))) >;


intrinsic TransvectionFactors(V::ModTupFld, f::GrpMatElt) -> SeqEnum
{A sequence of transvections and at most one dilatation whose product is f. If the
 determinant of f is not 1, the first element of the sequence will be a dilatation.}
  id := IdentityMatrix(BaseRing(V),Dimension(V));
  G := Parent(f);
  T := [G|];
  
  while f ne id do
    f_ := id - f;
    r := Rank(f_);
    if r eq 1 then
      Append(~T,f);
      break;
    end if;
  
    W := NullSpace(f_);
    ishom, alpha, gamma := isHomothety(V,W,f_);
    if ishom then  // alpha is a scalar
       a := rep{ a : a in Basis(V) | a notin W };
      if alpha eq 0 then
        vprint Transvection, 2 : "1) homothety 0";
        phi := rep{ psi : psi in reldual(W) | pairing(a,psi) ne 0 };
        phi := - phi/pairing(a,phi);
        t := G!Transvection(a*f_,phi);
      else
        vprint Transvection, 2 : "2) homothety",alpha;
        phi := reldual(sub<V|W,a>)[1];
        t := G!Transvection(a,phi);
      end if;
    else // alpha in V, gamma = alpha*f_
      vprint Transvection, 2 : "3) not homothety";
      phi := rep{ p : p in reldual(sub<V|W,gamma>) | pairing(alpha,p) ne 0 };
      phi := - phi/pairing(alpha,phi);
      t := G!Transvection(gamma,phi);
      if r ne 2 then
        vprint Transvection, 2 : "rank > 2";
        g_ := id - f*t;
        W1 := NullSpace(g_); // W1 eq sub<V|W,alpha>;
        flag, x, y := isHomothety(V,W1,g_);
        if flag then
          vprint Transvection, 2 : "replace";
          psi := rep{ p : p in reldual(sub<V|W,alpha,gamma>) };
          t := G!Transvection(gamma,phi + psi);
        end if;
      end if;
    end if;
    f := f*t;
    Append(~T,t^-1);
  end while;
    
  return Reverse(T);
end intrinsic;

// Predicates
// ----------
isPseudoReflection_ := function( rr )
  R := BaseRing(rr);
  F := FieldOfFractions(R);
  r := ChangeRing(rr,F);
  n := Nrows( r );
  H := Eigenspace(r,1);
  // Check that we have a pseudo-reflection
  if Dimension(H) ne n-1 then
    return false, _, _, _;
  end if;
  // Now determine the type of the pseudo-reflection
  V := VectorSpace(F,n);
  a := ExtendBasis(H,V)[n];
  root := a - a*r;
  coroot := Image(IdentityMatrix(BaseRing(r),n)-Transpose(r)).1;
  // Scale the coroot, being careful not to use the built-in
  // inner product, which may be hermitian
  pval := pairing(root,coroot);
  if pval eq 0 then
    reftype := 0;                             // 0=transvection
    coroot *:= 1/pairing(a,coroot);
  else
    reftype := IsSingular(r) select 1 else 2; // 1=projection, 2=reflection
    coroot *:= (n - Trace(r))/pval;
  end if;
  return true, reftype, root, coroot;
end function;


intrinsic IsPseudoReflection( r::AlgMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a pseudo-reflection, return a root and a coroot }
  flag, reftype, root, coroot := isPseudoReflection_(r);
  if flag then
    return true, root, coroot;
  end if;
  return false, _, _;
end intrinsic;


intrinsic IsPseudoReflection( r::GrpMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a pseudo-reflection, return a root and a coroot }
  return IsPseudoReflection( Matrix(r) );
end intrinsic;


intrinsic IsReflection( r::AlgMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a reflection, return a root and a coroot }
  flag, reftype, root, coroot := isPseudoReflection_(r);
  if flag and reftype gt 1 then return true, root, coroot; end if;
  return false, _, _;
end intrinsic;


intrinsic IsReflection( M::GrpMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a reflection, return a root and a coroot }
  return IsReflection( Matrix( M ) );
end intrinsic;


intrinsic IsTransvection( r::AlgMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a transvection, return a root and a coroot }
  flag, reftype, root, coroot := isPseudoReflection_(r);
  if flag and reftype eq 0 then
    return true, root, coroot;
  end if;
  return false, _, _;
end intrinsic;


intrinsic IsTransvection( r::GrpMatElt ) -> BoolElt, ModTupFldElt, ModTupFldElt
{ If r is a transvection, return a root and a coroot }
  return IsTransvection( Matrix(r) );
end intrinsic;


// Pseudo-reflections preserving reflexive forms
// ---------------------------------------------
intrinsic SymplecticTransvection( a::ModTupRngElt, alpha::FldElt ) -> AlgMatElt
{ The symplectic transvection with root a and multiplier alpha with respect to 
  the attached form }
  require alpha ne 0 : "zero multiplier";
  V := Parent(a);
  n := Dimension(V);
  J := GramMatrix(V);
  require J eq -Transpose(J) and 
    forall{ i : i in [1..n] | J[i,i] eq 0 } : "form is not alternating";
  return Matrix([v - alpha*DotProduct(v,a)*a : v in Basis(V)]);
end intrinsic;


/* 
The next two intrinsics require the base ring to carry an involution such
that the inner product is hermitian with respect to this involution.
*/

intrinsic UnitaryTransvection( a::ModTupRngElt, alpha::FldElt ) -> AlgMatElt
{ The unitary transvection with root a and multiplier alpha with respect to the 
  attached form, which must be alternating. alpha must have trace 0. }
  require alpha ne 0 : "zero multiplier";
  V := Generic(Parent(a));
  require IsUnitarySpace(V) : "vector is not in a unitary space";
  require DotProduct(a,a) eq 0 : "root is not isotropic";
  sigma := V`Involution;
  require alpha + sigma(alpha) eq 0 : "alpha must have trace 0";
  return Matrix([v - alpha*DotProduct(v,a)*a : v in Basis(V)]);
end intrinsic;


intrinsic UnitaryReflection( a::ModTupRngElt, zeta::FldElt ) -> AlgMatElt
{ The unitary reflection in the root a with respect to the attached hermitian form.
  The reflection sends a to zeta*a, where zeta is a root of unity }
  V := Generic(Parent(a));
  require IsUnitarySpace(V) : "vector is not in a unitary space";
  require DotProduct(a,a) ne 0 : "root is isotropic";
  require IsRootOfUnity(zeta) : "zeta must be a root of unity";
  lambda := (1-zeta)/DotProduct(a,a);
  require lambda ne 0 : "zeta cannot be 1";
  return Matrix([v - lambda*DotProduct(v,a)*a : v in Basis(V)]);
end intrinsic;


/*
Abstract Cartan matrices
========================
*/

intrinsic IsAbstractCartanMatrix( C::AlgMatElt ) -> BoolElt
{ Check if C is the (abstract) Cartan matrix of a collection of reflections }
  m := Ncols(C);
  require m eq Nrows(C) : "a Cartan matrix must be square";

  return forall{ <i,j> : i in [j+1..m], j in [1..m] | (C[i,j] eq 0) eq (C[j,i] eq 0)}
     and forall{i : i in [1..m] | (C[i,i] ne 0) and IsRootOfUnity(1-C[i,i])};
end intrinsic;


/*
  The following intrinsic does no checking on the type of roots returned.
  Therefore, the pseudo-reflection of a given root pair could be a
  projection, a transvection or a reflection.
  
  In any case, this is only needed when the abstract Cartan matrix has a 
  non-trivial null space.
*/
intrinsic BasicRootMatrices( C::Mtrx : Reduced := true ) -> AlgMatElt, AlgMatElt
{ A matrix A of roots and a matrix B of coroots of the matrix C
  such that C is A*Transpose(B). The default (Reduced is true) is 
  to compute the roots and coroots modulo the null space of C}
  m := Ncols(C);
  require m eq Nrows(C) : "a Cartan matrix must be square";
  // ensure that C is in the AlgMat category
  C := MatrixAlgebra(BaseRing(C),m)!C;
  C_ := Transpose(C);
  n := Rank(C);
  if m eq n then
    Reduced := false;
  end if;
  if Reduced then
    N := NullSpace(C);
    V := Generic(N);
    W, mu := quo< V | N >;
    A := Matrix([mu(b) : b in Basis(V)]);
    B := C_*Transpose(Matrix([w@@mu : w in Basis(W)]));
//    B := Matrix([W![pairing(C_[i],w@@mu) : w in Basis(W)] : i in [1..m]]);
  else
    A := One(Parent(C));
    B := C_;
  end if;
  return A,B;
end intrinsic;

// ==========================================================
// PART II  Reflection groups
// ==========================================================

// Complex reflection groups
// -------------------------
intrinsic PseudoReflectionGroup( A::Mtrx, B::Mtrx ) -> GrpMat, Map
{ The pseudo-reflection group with the given basic root and coroot matrices }
  require Nrows( A ) eq Nrows( B ) : 
    "the number of roots and coroots must be equal";
  require Ncols( A ) eq Ncols( B ) : 
    "the roots and coroots must have the same dimension";
  require BaseRing( A ) cmpeq BaseRing( B ) : 
    "the roots and coroots must have the same base ring";
  refs := [ PseudoReflection(A[i],B[i]) : i in [1..Nrows(A)] ];
  require forall{ r : r in refs | IsInvertible(r) } : "reflections must be invertible";
  return MatrixGroup< Ncols(A), BaseRing(A) | refs >;
end intrinsic;

/* Not really needed

intrinsic PseudoReflectionGroup( C::Mtrx : Reduced := true ) -> GrpMat, Map
{ The reflection group with the given (abstract) Cartan matrix }
  A, B := BasicRootMatrices(C : Reduced := Reduced);
  return PseudoReflectionGroup(A,B);
end intrinsic;
*/

STOrders := 
[ 24, 72, 48, 144, 96, 192, 288, 576, 48, 96, 144, 288, 600, 1200, 1800, 3600, 
  360, 720, 240, 120, 336, 648, 1296, 2160, 1152, 7680, 14400, 46080, 155520, 
  51840, 39191040, 51840, 2903040, 696729600 ];

intrinsic ShephardTodd( n::RngIntElt : NumFld := false ) -> GrpMat, Map
{ The primitive complex reflection group G_n using the Shephard-Todd numbering }
  A, B, _, _, _ := ComplexRootMatrices( n : NumFld := NumFld );
  G, m := PseudoReflectionGroup(A,B);
  // G`Order := STOrders[n-3];
  return G, m;
end intrinsic;

intrinsic ShephardTodd( m::RngIntElt, p::RngIntElt, n::RngIntElt : Minimal := false) 
  -> GrpMat, Map
{The imprimitive complex reflection (Shephard-Todd) group G(m,p,n)}
  A, B, _, _, _ := ComplexRootMatrices(m,p,n : Minimal := Minimal);
  return PseudoReflectionGroup(A,B);
end intrinsic;


/* 
  The following intrinsics are included to maintain compatibility with the old
  FIURG package.

  - ImprimitiveReflectionGroup(m,p,n) is identical to ShephardTodd(m,p,n).
  - ComplexReflectionGroup(C) is identical to PseudoReflectionGroup(A,B)
      where A and B are the root and coroot matrices derived from C.
*/
intrinsic ImprimitiveReflectionGroup( m::RngIntElt, p::RngIntElt, n::RngIntElt ) 
  -> GrpMat, Map
{The imprimitive complex reflection (Shephard-Todd) group G(m,p,n)}
  A, B, _, _, _ := ComplexRootMatrices(m,p,n);
  return PseudoReflectionGroup(A,B);
end intrinsic;

intrinsic ComplexReflectionGroup( C::Mtrx : Reduced := true ) -> GrpMat, Map
{ The reflection group with the given (abstract) Cartan matrix }
  A, B := BasicRootMatrices(C : Reduced := Reduced );
  return PseudoReflectionGroup(A,B);
end intrinsic;

intrinsic ComplexReflectionGroup( X::MonStgElt, n::RngIntElt : NumFld := false ) -> GrpMat, Map
{ The primitive complex reflection group of type X_n}
  if X in "ABCDG" then
    C := CartanMatrix(X*IntegerToString(n));
    return ReflectionGroup(C);
  else
    return ShephardTodd( ShephardToddNumber( X, n ) : NumFld := NumFld );
  end if;
end intrinsic;


// Predicates
// ----------
intrinsic IsReflectionGroup(G::GrpMat : Strict := true) -> BoolElt
{ Test if the generators of G are reflections.  Set Strict to false
  to test if G is generated by its reflections }
  // First a quick check of the generators
  if forall{ g : g in Generators(G) | IsReflection(g) } then
    return true;
  end if;
  if Strict then return false; end if;
  refcl := [cl : cl in Classes(G) | IsReflection(cl[3])];
  return G eq ncl< G | [ cl[3] : cl in refcl ] >;
end intrinsic;


