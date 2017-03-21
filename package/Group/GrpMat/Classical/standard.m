freeze;

//
// Constructing the standard classical forms
//
// None of the intrinsics in this file are documented (at v.2-19)
// .........................................................
//
// Symplectic and unitary forms
//
// Use StandardAlternatingForm and StandardHermitianForm instead
//
/*
intrinsic SymplecticForm( n::RngIntElt, F::Fld ) -> AlgMatElt
{The matrix of the standard symplectic form of degree n over F}
  require n ge 0 and IsEven(n) : "the degree should be non-negative and even";
  J := ZeroMatrix(F,n,n);
  m := n div 2;
  for i in [1..m] do
    J[i,n-i+1] := 1;
    J[n-i+1,i] := -1;
  end for;
  return J;
end intrinsic;

intrinsic SymplecticForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard symplectic form of degree n over GF(q)}
//  require q gt 1 : "Not a prime power";
  require IsPrimePower(q) : "Not a prime power";
  return SymplecticForm(n,GF(q));
end intrinsic;

intrinsic UnitaryForm( n::RngIntElt, F::Fld ) -> AlgMatElt, Map
{The matrix of the standard unitary form of degree n over F}
  require n ge 0 : "argument 1 should be non-negative";
  require IsFinite(F) : "the field must be finite";
  flag, q := IsSquare(#F);
  require flag : "the order of the field must be a square";
  J := ZeroMatrix(F,n,n);
  m := (n+1) div 2;
  for i in [1..m] do
    J[i,n-i+1] := 1;
    J[n-i+1,i] := 1;
  end for;
  return J, hom< F -> F | x :-> x^q >;
end intrinsic;

intrinsic UnitaryForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt, Map
{The matrix of the standard unitary form of degree n over GF(q^2)}
//  require q gt 1 : "Not a prime power";
  require IsPrimePower(q) : "not a prime power";
  return UnitaryForm(n,GF(q^2));
end intrinsic;
*/

// .........................................................
//
// Orthogonal forms
//
function quad_form(n, F)
    J := ZeroMatrix(F,n,n);
    m := n div 2;
    for i in [1..m] do
	J[i,n-i+1] := 1;
    end for;
    J[m+1,m+1] := Characteristic(F) eq 2 select 1 else (F!4)^-1;
    return J;
end function;

// This is StandardQuadaticForm(n,F : Variant := "Revised")
intrinsic QuadraticForm( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard quadratic form of odd degree n over F}
  require n gt 0 and IsOdd(n) : "the degree should be an odd positive integer";
//  require Characteristic(F) ne 2 : "characteristic 2 not allowed";
  return quad_form(n, F);
end intrinsic;

intrinsic QuadraticForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard quadratic form of degree n over GF(q)}
  require n gt 0 and IsOdd(n) : "the degree should be an odd positive integer";
  require IsPrimePower(q) : "Not a prime power";
//  require IsOdd(q) : "characteristic 2 not allowed";
  return quad_form(n,GF(q));
end intrinsic;

// This is StandardQuadaticForm(n,F : Variant := "Revised")
intrinsic QuadraticFormPlus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard quadratic plus type form of even degree n over F}
  require n ge 0 and IsEven(n) : "the degree should be an even non-negative integer";
  J := ZeroMatrix(F,n,n);
  m := n div 2;
  for i in [1..m] do
    J[i,n-i+1] := 1;
  end for;
  return J;
end intrinsic;

intrinsic QuadraticFormPlus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard quadratic plus type form of degree n over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return QuadraticFormPlus(n,GF(q));
end intrinsic;

intrinsic Nonsquare( F::FldFin ) -> FldFinElt
{A nonsquare in F}
  q := #F;
  require IsOdd(q) : "The field must have odd characteristic";
  r := Valuation( q-1, 2 );
  delta := F!-1;
  for i in [2..r] do
    delta := SquareRoot(delta);
  end for;
  return delta;
end intrinsic;

/* test
pps := [ q : q in [2..100] | IsOdd(q) and IsPrimePower(q) ];
forall(q){ q : q in pps | not IsSquare(Nonsquare(GF(q))) };
*/

// F finite of even char, returns an element outside of
// F^[2] := { a^2+a : a in F }
IsSquarish := function( x )
  P := PolynomialRing( Parent(x) ); X := P.1;
  f := X^2+X+x;
  if IsIrreducible( f ) then
    return false, _;
  else
    return true, Roots( f )[1][1];
  end if;
end function;
Nonsquarish := function( F )
  new := F!1;
  repeat
    delta := new;
    sqr, new := IsSquarish( delta );
  until not sqr;
  return delta;
end function;

/* test
pps := [ 2^i : i in [1..100] ];
forall(q){ q : q in pps | not IsSquarish(Nonsquarish(GF(q))) };
*/

// This is StandardQuadaticForm(n,F : Minus, Variant := "Revised")
intrinsic QuadraticFormMinus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal minus type form of even degree n over F}
  require n gt 0 and IsEven(n) : "the degree should be an even positive integer";
  require IsFinite(F) : "The field must be finite";
  J := ZeroMatrix(F,n,n);
  m := n div 2;
  for i in [1..m-1] do
    J[i,n-i+1] := 1;
  end for;
  if Characteristic( F ) ne 2 then
    J[m,m] := 1/2;
    J[m+1,m+1] := -Nonsquare(F)/2;
  else
    J[m,m] := 1;
    J[m+1,m+1] := Nonsquarish(F);
    J[m,m+1] := 1;
  end if;
  return J;
end intrinsic;

intrinsic QuadraticFormMinus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard quadratic minus type form of degree n over GF(q)}
  require IsPrimePower(q) : "Not a prime power";
  return QuadraticFormMinus(n,GF(q));
end intrinsic;

intrinsic QuadraticForm( t::RngIntElt, n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal form of degree n and sign t over F}
  require IsFinite(F) : "the field must be finite";
  if IsEven(n) then
    require t in [+1,-1] : "sign should be 1 or -1";
    return (t eq +1) select QuadraticFormPlus(n,F) else
      QuadraticFormMinus(n,F);
  else
     require t in [+1,0,-1] : "sign should be 1, 0 or -1";
     Q := QuadraticForm(n,F);
     if t ne 0 then  
       require Characteristic(F) ne 2: "invalid odd degree with characteristic 2";
       m := n div 2;
       Q[m+1,m+1] := (t eq 1) select F!1/2 else Nonsquare(F)/2;
     end if;
     return Q;
  end if;
end intrinsic;

intrinsic QuadraticForm( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard quadratic form of degree n and sign t over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return QuadraticForm(t,n,GF(q));
end intrinsic;


intrinsic SymmetricBilinearForm( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard symmetric bilinear form of odd degree n over F}
  return (Q+Transpose(Q)) where Q is QuadraticForm(n,F);
end intrinsic;
intrinsic SymmetricBilinearForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard symmetric bilinear form of degree n over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return SymmetricBilinearForm(n,GF(q));
end intrinsic;

intrinsic SymmetricBilinearFormPlus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard symmetric bilinear plus type form of even degree n over F}
  return (Q+Transpose(Q)) where Q is QuadraticFormPlus(n,F);
end intrinsic;
intrinsic SymmetricBilinearFormPlus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard symmetric bilinear plus type form of degree n over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return SymmetricBilinearFormPlus(n,GF(q));
end intrinsic;

intrinsic SymmetricBilinearFormMinus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard symmetric bilinear minus type form of even degree n over F}
  return (Q+Transpose(Q)) where Q is QuadraticFormMinus(n,F);
end intrinsic;
intrinsic SymmetricBilinearFormMinus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard symmetric bilinear minus type form of degree n over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return SymmetricBilinearFormMinus(n,GF(q));
end intrinsic;
intrinsic SymmetricBilinearForm( t::RngIntElt, n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard symmetric bilinear form of degree n and sign t over F}
  return (Q+Transpose(Q)) where Q is QuadraticForm(t,n,F);
end intrinsic;
intrinsic SymmetricBilinearForm( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard symmetric bilinear form of degree n and sign t over GF(q)}
  require IsPrimePower(q) : "not a prime power";
  return SymmetricBilinearForm(t,n,GF(q));
end intrinsic;

/* 
 * Not used, not documented and contains errors DET 2016-03-24
 *

intrinsic OrthogonalForm( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal form of odd degree n over F}
  return IsOdd(Characteristic(F)) select 
    SymmetricBilinearForm(n,F) else QuadraticForm(n,F);
end intrinsic;

intrinsic OrthogonalForm( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard orthogonal form of degree n over GF(q)}
  return IsOdd(q) select 
    SymmetricBilinearForm(n,q) else QuadraticForm(n,q);
end intrinsic;

intrinsic OrthogonalFormPlus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal plus type form of even degree n over F}
  return IsOdd(Characteristic(F)) select 
    SymmetricBilinearFormPlus(n,F) else QuadraticFormPlus(n,F);
end intrinsic;
intrinsic OrthogonalFormPlus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard orthogonal plus type form of degree n over GF(q)}
  return IsOdd(q) select 
    SymmetricBilinearFormPlus(n,q) else QuadraticFormPlus(n,q);
end intrinsic;

intrinsic OrthogonalFormMinus( n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal minus type form of even degree n over F}
  return IsOdd(Characteristic(F)) select 
    SymmetricBilinearFormMinus(n,F) else QuadraticFormMinus(n,F);
end intrinsic;

intrinsic OrthogonalFormMinus( n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard orthogonal minus type form of degree n over GF(q)}
  return IsOdd(q) select 
    SymmetricBilinearFormPlus(n,q) else QuadraticFormPlus(n,q);
end intrinsic;

intrinsic OrthogonalForm( t::RngIntElt, n::RngIntElt, F::FldFin ) -> AlgMatElt
{The matrix of the standard orthogonal form of degree n and sign t over F}
  return IsOdd(Characteristic(F)) select 
    SymmetricBilinearForm(t,n,F) else QuadraticForm(t,n,F);
end intrinsic;

intrinsic OrthogonalForm( t::RngIntElt, n::RngIntElt, q::RngIntElt ) -> AlgMatElt
{The matrix of the standard orthogonal form of degree n and sign t over GF(q)}
  return IsOdd(q) select 
    SymmetricBilinearForm(t,n,q) else QuadraticForm(t,n,q);
end intrinsic;
*/
