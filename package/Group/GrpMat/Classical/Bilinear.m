freeze;

/*
  Bilinear.m

  Scott H. Murray

  Basic functions for bilinear and quadratic spaces.
 
  We need sesqui forms (bilinear forms over C).
  Need to redefine Norm for char 2 quadratic forms.
  
  Char two problems:
    The nonsymplectic bilin forms do not come from quad forms.
    the quad form x^2+y^2+xy does not come from a symm bilin form.
*/

//import "/home/murray/magma/Prog/package/LieThry/Repn.m" : isPara;

// SEE ORTHOGONALISE IN LATTICES

// quadratic forms are represented by sequences of length (n-1)n/2
declare attributes ModTupFld : QuadraticForm;

normQ := function( Q, x )
  n := Dimension(Generic(Parent(x)));
  ret := 0;  pos := 1;
  for i in [1..n] do  
    for j in [1..i] do
      ret +:= Q[pos]*x[i]*x[j];
      pos +:= 1;
    end for;
  end for;
  return ret;
end function;

  
    

form := function( x, y, X : sigma:=false )
  return (Category(sigma) eq BoolElt) select (x*X*Transpose(Matrix(y)))[1] else
    (x*X*Transpose(Matrix([sigma(a):a in Eltseq(y)])))[1];
end function;

norm := function( x, X : sigma:=false )
  return evaluate(x,x,X:sigma:=sigma);
end function;


// -------------------------------------------------------
//
// Construction
//
// Currently we can only make bilinear forms, unless the field is C,
// when we can only make sesquilinear forms.
//

intrinsic BilinearSpace( F::AlgMatElt ) -> ModTupFld
{The R-space with bilinear form given by the Gram matrix F}
  return RSpace( BaseRing(F), Nrows(F), F );
end intrinsic;

/*
intrinsic SesquilinearSpace( F::AlgMatElt, sigma::Map[Rng,Rng] ) -> ModTupFld
{The R-space with sesquilinear form given by the Gram matrix F and the field
automorphism sigma}
  return ??
end intrinsic;
*/

/*
intrinsic QuadraticSpace( F::AlgMatElt ) -> ModTupFld
{The space with quadratic form given by the matrix F}
  
end intrinsic;
*/

intrinsic QuadraticSpace( Q::[RngElt] ) -> ModTupFld
{The space with quadratic form given by the sequence Q}
  F := SymmetricMatrix( Q );
  V := RSpace( BaseRing(F), Nrows(F), F );
  V`QuadraticForm := Q;
  return V;
end intrinsic;


// -------------------------------------------------------
//
// Ring functions
//
// -------------------------------------------------------

intrinsic IsSumOfSquares( a::FldFinElt ) -> FldFinElt
{Returns true, together with an expression for a as a sum of squares}
  ok, x := IsSquare( a );
  if ok then
    return true, [ x ];
  else
    // there should be a better way
    k := Parent( a );
    for x in k do
      for y in k do
        if x ne 0 and y ne 0 and not IsSquare( x^2+y^2 ) then
          _, z := IsSquare( (x^2+y^2)/a );
          return true, [ x/z, y/z ];
        end if;
      end for;
    end for;
    error "Error:  This should not happen";
  end if;
end intrinsic;




// -------------------------------------------------------
//
// Basic functions for bilinear forms
//
// -------------------------------------------------------

intrinsic IsAntisymmetric( X::Mtrx ) -> BoolElt
{True iff X is an antisymmetric matrix}
    return X eq -Transpose(X);
end intrinsic;

intrinsic IsAlternate( X::Mtrx ) -> BoolElt
{True iff X is an alternate matrix}
  return IsAntisymmetric(X) and 
    forall{ i : i in [1..Nrows(X)] | X[i,i] eq 0 };
end intrinsic;

intrinsic IsReflexive( X::Mtrx ) -> BoolElt
{True iff X is the matrix of a reflexive bilinear form}
  return IsSymmetric(X) or IsAntisymmetric(X);
end intrinsic;

intrinsic IsNondegenerate( X::Mtrx ) -> BoolElt
{True iff X is the matrix of a nondegenerate bilinear form}
  return Determinant( X ) ne 0;
end intrinsic;

intrinsic IsDegenerate( X::Mtrx ) -> BoolElt
{True iff X is the matrix of a degenerate bilinear form}
  return Determinant( X ) eq 0;
end intrinsic;

perp := function( M, X : Right:=false )
  return Right select Nullspace( Transpose(M*X) ) 
    else Nullspace( X*Transpose(M) );
end function;

intrinsic Perpendicular( S::{ModTupRngElt}, X::Mtrx :
  Right:=false ) -> ModTupRng
{The space of elements perpendicular to S under the bilinear form with matrix X}
  require Nrows(X) eq Ncols(X) : "The matrix is not square";
  return perp( Matrix( Setseq( S ) ), X : Right:=Right );
end intrinsic;

intrinsic Perpendicular( U::ModTupRng, X::Mtrx : 
  Right:=false ) -> ModTupRng
{The space of elements perpendicular to U under the bilinear form with matrix X}
  require Nrows(X) eq Ncols(X) : "The matrix is not square";
  return perp( Matrix( Basis( U ) ), X : Right:=Right );
end intrinsic;
 
intrinsic Radical( X::Mtrx : Right:=false ) -> ModTupRng
{The radical of the bilinear form with matrix X}
  V := RSpace( BaseRing(X), Nrows(X) );
  return Perpendicular( V, X : Right:=Right );
end intrinsic;



// -------------------------------------------------------
//
// Bases
//
// -------------------------------------------------------

// The functions that take X and B assume that X is 
// nondegenerate on the subspace spanned by B, and
// compute the appropriate thing on that subspace.

// Q^perp wrt gram matrix X in the space spanned by B
subperp := function( Q, X, B )
  return perp( Matrix(Q), X ) meet sub< Universe(B) | B >;
end function;

hasAnisotropicVector := function( X, B )
  n := #B;
  if n eq 0 then  return false, _;  end if;
  if IsAlternate( X ) then
    return false, _;
  elif exists(b){ b : b in B | evaluate(b,b,X) ne 0 } then
    return true, b;
  elif exists(t){ <i,j> : i in [j+1..n], j in [1..n] | 
  evaluate(B[i],B[j],X) ne 0 } then
    return true, B[t[1]] + B[t[2]];
  else
    error "Error: This should not happen";
  end if;
end function;

// orthogonalBasis and symplecticBasis call each other in exceptional
// circumstances, but are not actually recursive.
forward symplecticBasis;

orthogonalBasis := function( X, B )
  if #B eq 0 then  return B;  end if;

  // find the anisotropic vectors
  newB := [];
  ok, u := hasAnisotropicVector( X, B );
  while ok do
    Append( ~newB, u );
    B := Basis( subperp( [u], X, B ) );
    ok, u := hasAnisotropicVector( X, B );
  end while;

  // return an symplectic basis for the rest
  // NB: this only happens if X symplectic or characteristic is two
  return newB cat symplecticBasis( X, B : OrthOrder );
  
end function;

//
// The orthonormal basis functions assume X is symmetric
//

// functions for fields which are closed under taking square roots
orthonormalBasis_SqrtClosed := function( X, B )
  B := orthogonalBasis( X, B );
  for i in [1..#B] do
    _, a := IsSquare( evaluate(B[i],B[i],X) );
    B[i] := B[i]/a;
  end for;
  return B;
end function;

hasIsotropicVector_SqrtClosed := function( X, B )
  if #B lt 2 then
    return false, _;
  else
    B := orthonormalBasis_SqrtClosed( X, B[[1,2]] );
    _, i := IsSquare( BaseRing( X )!(-1) );
    return B[1] + i*B[2];
  end if;
end function;

// functions for finite fields
// We actually use:
//  (i) the product of two nonsquares is a square, and
// (ii) every element is the sum of two squares.
orthonormalBasis_FldFin := function( X, B )
  B := orthogonalBasis( X, B );
  n := #B;  sqrts := [];
  for i in [1..n] do
    ok, a := IsSquare( norm(B[i],X) );
    sqrts[i] := ok select a else 0;
  end for;
  for i in [1..n] do
    if sqrts[i] ne 0 then
      B[i] := B[i]/sqrts[i];
    else
      if exists(j){ j : j in [i+1..n] | sqrts[j] eq 0 } then
        bi := B[i];  bj := B[j];
        ni := norm(bi,X);  nj := norm(bj,X);
        _, a := IsSquare( ni/nj );
        bj *:= a;  B[j] := bj;
        _, Q := IsSumOfSquares( 1/ni );
        B[i] := Q[1]*bi+Q[2]*bj;
        B[j] := Q[1]*bi-Q[2]*bj;
        sqrts[j] := 1;
      elif i ne n then
        tmp := B[i];  B[i] := B[n];  B[n] := tmp;
      end if;
    end if;
  end for;
  return B;
end function; 
        
hasIsotropicVector_FldFin := function( X, B )
  if #B eq 1 then
    return false, _;
  elif #B eq 2 then
    B := orthonormalBasis_FldFin( X, B );
    u := B[1];  v := B[2];
    ok, a := IsSquare( -1/evaluate(v,v,X) );
    if ok then
      return true, u+a*v;
    else
      return false, _;
    end if;
  else
    B := orthonormalBasis_FldFin( X, B[[1,2,3]] );
    ns := [ norm(b,X) : b in B ];
    sqs := [ IsSquare( n ) : n in ns ];
    i := 0;
    repeat  i +:= 1;
    until exists(j){ j : j in [i+1..3] | j ne i and sqs[i] eq sqs[j] };
    k := Rep( {1..3} diff {i,j} );
    _, a := IsSquare( ns[i]/ns[j] );
    _, Q := IsSumOfSquares( -ns[k]/ns[j] );
    if #Q eq 1 then  Q[2] := 0;  end if;
    return true, Q[1]*a*B[i] + Q[2]*B[j] + B[k];
  end if;
end function;      


hasIsotropicVector := function( X, B )
  if #B eq 0 then  return false, _;  end if;
  k := BaseRing( X );
  if exists(b){ b : b in B | evaluate(b,b,X) eq 0 } then
    return true, b;
  else
    // X is now symmetric
    case Category( k ) :
    when FldAC, FldCom :   
      return hasIsotropicVector_SqrtClosed( X, B );
    when FldFin :  
      return hasIsotropicVector_FldFin( X, B );
    else
      error "Error:  Not implemented over the given ring";
    end case;
  end if;
end function;

orthonormalBasisSesqui_FldFin := function( X, B )
  return B;
end function;

hasIsotropicVectorSesqui_FldFin := function( X, B, sigma )
  if #B eq 1 then
    return false;
  else
    B := orthonormalBasisSesqui_FldFin( X, B[[1,2]] );
    K := BaseRing( X );
    _, p, a := IsPrimePower( #K );
    k := sub< K | a div 2 >;
    i := NormEquation( K, k!(-1) );
    return B[1] + i*B[2];
  end if;
end function;

hasIsotropicVectorSesqui := function( X, B, sigma )
  if #B le 1 then  return false, _;  end if;
  k := BaseRing( X );
  if exists(b){ b : b in B | evaluate(b,b,X) eq 0 } then
    return true, b;
  else
    case Category( k ) :
    when FldFin :  
      return hasIsotropicVectorSesqui_FldFin( X, B );
    else
      error "Error:  Not implemented over the given ring";
    end case;
  end if;
end function;
    
  

intrinsic IsIsotropic( X::Mtrx ) -> BoolElt, ModTupRng
{True iff X is the matrix of an isotropic bilinear form}
  require IsReflexive( X ) : "Not a reflexive matrix";
  return hasIsotropicVector( X );  
end intrinsic;

intrinsic IsAnisotropic( X::Mtrx ) -> BoolElt, ModTupRng
{True iff X is the matrix of an isotropic bilinear form}
  isot, v := IsIsotropic( X );
  return not isot, v;
end intrinsic;


// ODD CHARACTERISTIC!
symplecticBasis := function( X, B : OrthOrder:=false )
  if #B eq 0 then  return B;  end if;

  // find the symplectic pairs
  us := [];  vs := [];
  ok, u := hasIsotropicVector( X, B );
  while ok do
//    print us, vs, B, "\n";
    j := 0;  
    repeat  
      j +:= 1;  
      b := evaluate(u,B[j],X);
    until b ne 0 and not isPara(u,B[j]);
    u := u/b;  v := B[j] - norm(B[j],X)*u/2;
    Append( ~us, u );  Append( ~vs, v );
    B := Basis( subperp( [u,v], X, B ) );
    ok, u := hasIsotropicVector( X, B );  
  end while;
  
  // reorder the symplectic pairs
  if OrthOrder then
    S1 := [];  S2 := [];
    for i in [1..#us] do
      Append( ~S1, us[i] );  Append( ~S1, vs[i] );
    end for;
  else
    S1 := us;  S2 := Reverse( vs );
  end if;
  
  // return an orthogonal basis for the anisotropic subspace
  return S1 cat orthogonalBasis( X, B ) cat S2;
end function;





intrinsic OrthogonalBasis( X::Mtrx ) -> SeqEnum
{An orthogonal basis for the reflexive bilinear form with matrix X}
  require IsReflexive( X ) : "Not a reflexive matrix";
  require ISA( BaseRing(X), Fld ) : "Not defined over a field";
  n := Nrows( X );  V := VectorSpace( BaseRing(X), n );
  R := Radical( X );  r := Dimension( R );
  B := ExtendBasis( R, V );
  return B[[1..r]] cat orthogonalBasis( X, B[[r+1..n]] );
end intrinsic;

intrinsic SymplecticBasis( X::Mtrx ) -> SeqEnum
{An symplectic basis for the reflexive bilinear form with matrix X}
  require IsReflexive( X ) : "Not a reflexive matrix";
  require ISA( Category(BaseRing(X)), Fld ) : "Not defined over a field";
  n := Nrows( X );  V := VectorSpace( BaseRing(X), n );
  R := Radical( X );  r := Dimension( R );
  B := ExtendBasis( R, V );
  return B[[1..r]] cat symplecticBasis( X, B[[r+1..n]] );
end intrinsic;


// THIS IS NOT UNIQUE
intrinsic WittRepresentative( X::Mtrx ) -> Mtrx, SeqEnum
{}
  B := SymplecticBasis( X );
  B := [ b : b in B | norm(b,X) ne 0 ];
  return Matrix( #B, #B, [ BaseRing(X) | evaluate(a,b,X) : b in B, a in B ] );
end intrinsic;

intrinsic WittClass( X::Mtrx ) -> .
{}
  if Determinant(X) eq 0 then
    return "-";
  end if;
  d := Nrows(X);
  n := d div 2;
  disc := Determinant(X);
  if d mod 2 eq 0 then 
    if IsSquare( (-1)^n*disc ) then return 0;
    else return "omega";
    end if;
  else
    if IsSquare( (-1)^n*disc ) then return 1;
    else return "delta";
    end if;
  end if;
end intrinsic;


