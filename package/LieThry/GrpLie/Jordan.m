freeze;

/*

  Jordan.m

  The Jordan decomposition and related functions.

*/

// This function returns a polynomial f such that
// f=X mod p and p(f)=0 mod p^d
findf := function( p, d )
  P<X> := Parent(p);
  if d eq 1 then
    return X;
  else
    F := BaseRing(P);
    PP<Y,Z> := PolynomialRing( F, 2 );
    g := $$( p, d-1 );
    b := ExactQuotient( Evaluate(p,g), p^(d-1) );
    pp := Coefficient( Evaluate(p,Y+Z), Z, 1 );  pp := Evaluate( pp, <X,P!1> );
    _,_,u := Xgcd(p,Evaluate(pp,g));  u := -b*u mod p^d;
    return g+u*p^(d-1) mod p^d;
  end if;
end function;


intrinsic JordanDecomposition( x::AlgMatElt ) -> AlgMatElt, AlgMatElt, RngUPolElt, RngUPolElt
{The (additive) Jordan decomposition of x}
  F := FactoredMinimalPolynomial( x );
  P<X> := Parent( F[1][1] );
  p := &*[ t[1] : t in F ];
  d := Maximum( [ t[2] : t in F ] );
  f := findf( p, d );
  As := Evaluate(f,x);
  return As, x-As, f, X-f;
end intrinsic;

intrinsic MultiplicativeJordanDecomposition( x::AlgMatElt ) -> AlgMatElt, AlgMatElt
{The multiplicative Jordan decomposition of x}
  As, An := JordanDecomposition( x );
  return As, 1+As^-1*An;
end intrinsic;

intrinsic MultiplicativeJordanDecomposition( x::GrpMatElt ) -> GrpMatElt, GrpMatElt
{The multiplicative Jordan decomposition of x}
  G := Parent( x );
  As, Au := MultiplicativeJordanDecomposition( Matrix( x ) );
  gl := Generic( G );
  return gl!As, gl!Au;
end intrinsic;

intrinsic IsSemisimple( x::AlgMatElt ) -> BoolElt
{True if x is semisimple over the base field}
  return forall{ t : t in FactoredMinimalPolynomial(x) | t[2] eq 1 };
end intrinsic;

intrinsic IsAbsolutelySemisimple( x::AlgMatElt ) -> BoolElt
{True if x is semisimple over the algebraic closure of the base field}

  F := FactoredMinimalPolynomial(x);
  return forall{ t : t in F | t[2] eq 1 and IsSeparable( t[1] ) };
end intrinsic;

intrinsic IsSemisimple( x::GrpMatElt ) -> BoolElt
{True iff x is semisimple}
  return IsSemisimple( Matrix( x ) );
end intrinsic;

intrinsic IsSemisimple( x::AlgMatLieElt ) -> BoolElt
{True iff x is semisimple}
  return IsSemisimple( Matrix( x ) );
end intrinsic;

// IsNilpotent already implemented for AlgMatElt aad AlgMatLieElt

// IsUnipotent  alread implemented for AlgMatElt

intrinsic IsUnipotent( x::GrpMatElt  ) -> BoolElt
{True iff x is unipotent}
  return IsUnipotent( Matrix( x ) );
end intrinsic;

repn2 := function( L )
  if assigned L`RootSystem then
    rho := StandardRepresentation( L : NoCharacteristicError );
  end if;
  if not assigned rho or Category(rho) eq BoolElt then
    rho := AdjointRepresentation( L );
  end if;
  inv := Inverse( rho );
  return rho, inv;
end function;
  
intrinsic IsNilpotent( x::AlgLieElt ) -> BoolElt
{True iff x is semisimple}
  rho := repn2( Parent( x ) );
  return IsNilpotent( rho( x ) );
end intrinsic;
  
intrinsic IsSemisimple( x::AlgLieElt ) -> BoolElt
{True iff x is semisimple}
  L := Parent( x );  k := BaseRing( L );
  require ISA( Category(k), Fld ) : 
    "The Lie algebra must be defined over a field";
    
  if Characteristic( k ) eq 0 then
    rho := repn2( Parent( x ) );
    return IsSemisimple( rho( x ) );
  else  // use the Seligman definition in char p
    ok, pmap := IsRestrictable( L );
    require ok : "The element must be in a restrictable Lie algebra";
    return x in pSubalgebra( {x} );
  end if;
   
end intrinsic;

intrinsic JordanDecomposition( x::AlgMatLieElt ) -> AlgMatLieElt, AlgMatLieElt
{The (additive) Jordan decomposition of x}
  L := Parent( x );
  s, n := JordanDecomposition( Matrix( x ) );
  return L!s, L!n;
end intrinsic;


intrinsic JordanDecomposition( x::AlgLieElt ) -> AlgLieElt, AlgLieElt
{The (additive) Jordan decomposition of x}
  rho, inv := repn2( Parent( x ) );
  S, N := JordanDecomposition( rho( x ) );
  return inv( S ), inv( N );
end intrinsic;

