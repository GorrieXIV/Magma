freeze;
/**********************************************************************
  The "standard" alternating, hermitian, quadratic, symmetric and
  pseudo-alternating forms defined on a finite dimensional vector space
  over a field. We take these to be the non-degenerateforms of maximal 
  Witt index together with the quadratic forms of non-maximal Witt index
  over finite fields.

  If J is the matrix of the form, then X preserves the form (acting on 
  the right) if X*J*Transpose(X) eq J.

  When the field is finite the forms preserved by the Magma implementation 
  of the orthogonal groups are not always standard.  To obtain the 
  forms currently preserved by these groups, set the "Variant" parameter
  to "Revised".  To obtain the form orginally used for orthogonal groups of 
  non-maximal Witt index set "Variant" to "Original".
  
  January 2012 Don Taylor

  $Id: standard.m 52114 2016-02-26 05:56:54Z don $

  Intrinsics defined in this file:

    StandardAlternatingForm
    StandardHermitianForm
    StandardPseudoAlternatingForm
    StandardQuadraticForm
    StandardSymmetricForm
*/

// ------------------------------------------------------------------
// Alternating forms
// ------------------------------------------------------------------
// The following code is equivalent to SymplecticForm in 
// Group/GrpMat/Classical/standard.m
intrinsic StandardAlternatingForm( n::RngIntElt, R::Rng) -> AlgMatElt
{The matrix of the standard alternating form of degree n over the ring R}
  require n ge 0 and IsEven(n) : "the degree should be non-negative and even";
  J := ZeroMatrix(R,n,n);
  m := n div 2;
  for i := 1 to m do
    k := n-i+1;
    J[i,k] := 1;
    J[k,i] := -1;
  end for;
  return J;
end intrinsic;

intrinsic StandardAlternatingForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard alternating form of degree n over GF(q)}
  require IsPrimePower(q) : "argument 2 is not a prime power";
  return StandardAlternatingForm(n,GF(q));
end intrinsic;

// ------------------------------------------------------------------
// Hermitian forms
// ------------------------------------------------------------------
intrinsic StandardHermitianForm( n::RngIntElt, F::Fld ) -> AlgMatElt, Map
{The matrix of the standard hermitian form of degree n, and the involution
 of the field F}
  require n gt 0 : Sprintf("the degree (%o) must be non-negative",n);
  J := ZeroMatrix(F,n,n);
  for i := 1 to n do J[i,n-i+1] := 1; end for;
  tp := Type(F);
  if tp eq FldFin then
    flag, q := IsSquare(#F);
    require flag : "the order of the field must be a square";
    sigma := hom< F -> F | x :-> x^q >; 
  elif ISA(tp,FldAlg) then
    r, cx := Signature(F);
    flag, f := HasComplexConjugate(F);
    if flag and cx gt 0 then
      sigma := hom< F -> F | x :-> f(x) >;
    else
      error "Hermitian forms not available for this field";
    end if;
  end if;
  return J, sigma;
end intrinsic;

intrinsic StandardHermitianForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt, Map
{The matrix of the standard hermitian form of degree n, over GF(q^2) and 
 the involution x -> x^q of the field}
  require q gt 1 : Sprintf("the order of the field (%o) must be at least 2",q);
  require IsPrimePower(q) : Sprintf("argument 2 (%o) is not a prime power",q);
  return StandardHermitianForm(n,GF(q^2));
end intrinsic;

// ------------------------------------------------------------------
// Quadratic forms
// ------------------------------------------------------------------
/* The Artin-Schreier subgroup of a field F of characteristic p is
   the set AS(F) := { x^p + x : x in F }.

   In order to find an element not in AS(F), where F is a finite field of
   characteristic two, we work up through the chain of quadratic extensions
   GF(2) < GF(4) < GF(16) ... < F.
*/
NonQuadAS_elt := function( F ) 
  x := PolynomialRing(F).1;
  k := Valuation(Valuation(#F,2),2); // the characteristic of F must be 2.
  a := F!1;
  for n := 2 to 2^k do
    f := x^2 + x + a;
    a := Roots(f)[1][1];
  end for;
  return a;
end function;

intrinsic StandardQuadraticForm( n::RngIntElt, F::Fld : Minus := false, Variant := "Default") -> AlgMatElt
{The matrix of the standard quadratic form of degree n over the field F.
  If Minus is false (the default), the form has maximal Witt index.
  If Minus is true and the field is finite the Witt index is non-maximal
  if n is even; if n is odd the form is similar but not congruent to the
  default.  Variant is "Original", "Revised", "Default"}
  require n gt 0 : "the degree should be a positive integer";
  require Type(Variant) eq MonStgElt : "Variant must be a string";
  require Variant in ["Original","Revised","Default"] : "unsupported variant -> " cat Variant;
  require not Minus or IsFinite(F) : "Minus type available only for finite fields";
  Q := ZeroMatrix(F,n,n);
  m := (n+1) div 2;
  for i := 1 to m-1 do Q[i,n-i+1] := F!1; end for;
  p := Characteristic(F);
  if IsOdd(n) then
/*
   For historical reasons, over finite fields of odd characteristic,
   the (m,m) element in the quadratic form used by the orthogonal groups 
   of odd degree is 1/4.
     Originally, the generators were written down with respect to a
   quadratic form all of whose non-zero entries were 1 (on the upper
   secondary diagonal) but the matrix action was on the left. When 
   regarded as matrices acting on the right this changes the bilinear 
   form to its inverse hence changing its (m,m) entry from 2 to 1/2,
   thereby changing the (m,m) entry of the quadratic form from 1 to 1/4.
*/
    if Variant ne "Default" and IsFinite(F) and p ne 2 then
      Q[m,m] := (F!4)^-1;
    else
      Q[m,m] := F!1;
    end if;
    if Minus then
      error if p eq 2, "Minus type is not available in even characteristic";
      a := Nonsquare(F);
      Q[m,m] := a*Q[m,m];
    end if;
  elif Minus then
    if Variant eq "Original" then
/*
   The C code which constructs the generators for the original variant of
   GOMinus(n,q) and friends uses custom field extension code via the function
   ff_create_ext__n_primitive().  This produces a primitive element for 
   GF(q^2) not generally available via package code. Therefore, we extract the 
   necessary elements (norm and trace) from the first generator returned by 
   OldOmegaMinus.
*/
      h := OldOmegaMinus(4,#F).1;
//      F := BaseRing(G);
//      Q := ZeroMatrix(F,n,n);
//      for i := 1 to m-1 do Q[i,n-i+1] := F!1; end for;
//      xi := PrimitiveElement(GF(q^2));
      Q[m,m] := -F!1;
      Q[m,m+1] := h[3,2];      // -F!(xi+xi^q);
      Q[m+1,m+1] := -h[1,1];   // -F!(xi^(q+1));
    elif Variant eq "Revised" then
    // When p is odd, the revised variant uses a diagonal matrix for
    // the central 2 x 2 block.
      if p ne 2 then
        Q[m,m] := F!1/2;
        Q[m+1,m+1] := -Nonsquare(F)/2;
      else
    // The revised variant scales the basis vectors so that the central
    // block is Matrix(2,2,[1,1,0,a], where a is not in {x^2 + x | x in F}.
        Q[m,m] := F!1;
        Q[m,m+1] := F!1;
        Q[m+1,m+1] := NonQuadAS_elt(F);
      end if;
    else // Default
      if p ne 2 then
        a := (F!1 - PrimitiveElement(F))/4; // x^2 + x + a is irreducible
//        Q[m,m] := F!1;
//        Q[m+1,m+1] := -Nonsquare(F);
      else
//        xi := PrimitiveElement( GF(q^2) )^(q-1);
//        a := F!(xi/(1+xi)^2);
//        Q[m,m] := F!1;
//        Q[m,m+1] := F!1;
//        Q[m+1,m+1] := NonQuadAS_elt(F);
        a := NonQuadAS_elt(F);
      end if;
      Q[m,m] := F!1; Q[m,m+1] := F!1; Q[m+1,m+1] := a;
    end if;
  else
    Q[m,m+1] := F!1;
  end if;
  return Q;
end intrinsic;

intrinsic StandardQuadraticForm( n::RngIntElt, q::RngIntElt : Minus := false, Variant := "Default") -> AlgMatElt
{The matrix of the standard quadratic form of degree n over the field GF(q).
  If Minus is false (the default), the form has maximal Witt index.
  If Minus is true, the Witt index is non-maximal if n is even; 
  if n is odd the form is similar but not isometric to the default.
  Variant is "Original", "Revised", "Default"}
  require n gt 0 : "the degree should be a positive integer";
  require q gt 1 : Sprintf("the order of the field (%o) must be at least 2",q);
  require IsPrimePower(q) : "argument 2 is not a prime power";
  return StandardQuadraticForm(n,GF(q) : Minus := Minus, Variant := Variant);
end intrinsic;


// ------------------------------------------------------------------
// Symmetric forms
// ------------------------------------------------------------------
intrinsic StandardSymmetricForm( n::RngIntElt, F::Fld : Minus := false, Variant := "Default") -> AlgMatElt
{The matrix of the standard symmetric form of degree n and maximal 
  Witt index over the field F.  Use Minus:=true to obtain a form
  of non-maximal Witt index. Variant is "Original", "Revised", "Default"}
  require n gt 0 : "the degree should be a positive integer";
  require Type(Variant) eq MonStgElt : "Variant must be a string";
  require Variant in ["Original","Revised","Default"] : "unsupported variant -> " cat Variant;
  Q := StandardQuadraticForm(n,F : Minus := Minus, Variant := Variant);
  return Q + Transpose(Q);
end intrinsic;


intrinsic StandardSymmetricForm( n::RngIntElt, q::RngIntElt : Minus := false, Variant := "Default") -> AlgMatElt
{The matrix of the standard symmetric form of degree n over GF(q)}
  require n gt 0 : "the degree should be a positive integer";
  require q gt 1 : Sprintf("the order of the field (%o) must be at least 2",q);
  require IsPrimePower(q) : "argument 2 is not a prime power";
  Q := StandardQuadraticForm(n,GF(q) : Minus := Minus, Variant := Variant);
  return Q + Transpose(Q);
end intrinsic;


// ------------------------------------------------------------------
// Pseudo-alternating forms
// ------------------------------------------------------------------
// A pseudo-alternating form is a symmetric form (over a field of
// characteristic two) which is not alternating.

// The following code returns a matrix which makes the alternating form 
// evident. In all cases this matrix is congruent to the identity matrix.
intrinsic StandardPseudoAlternatingForm( n::RngIntElt, F::Fld ) -> AlgMatElt
{The matrix of the standard pseudo-alternating form of degree n over the
field F, which must have characteristic 2 }
  require Characteristic(F) eq 2 : "the characteristic of the field must be 2";
  if IsOdd(n) then
    m := n - 1;
    Z := IdentityMatrix(F,1);
  else 
    m := n - 2;
    Z := Matrix(F,2,2,[0,1,1,1]);
  end if;
  J := StandardAlternatingForm(m,F);
  return DiagonalJoin(J,Z);
end intrinsic;
  
intrinsic StandardPseudoAlternatingForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard pseudo-alternating form of degree n over the 
field GF(q), where q is a power of 2 }
  require IsEven(q) and IsPrimePower(q) : "second argument must be a power of 2";
  return StandardPseudoAlternatingForm( n, GF(q) );
end intrinsic;

