freeze;

/*
  Solving the Hilbert 90 equation.
  
  Hilbert Theorem 90:
    a in GF(q^r) satisfies N_{q^r,q}(a)=1
    iff x^q x^-1 = a has a solution in GF(q^r).
    
  Additive Hilbert Theorem 90: 
    a in GF(q^r) satisfies T_{q^r,q}(a)=0
    iff x^q - x = a has a solution in GF(q^r).
    
  Suppose a is in a finite field k of characteristic p and
  q is a power of p.  Then N_{q^r,q}(a)=1 for r sufficiently 
  large, so the Hilbert 90 equation has a solution is a
  sufficiently large finite extension of k.
  Similarly for additive Hilbert 90
*/

intrinsic FrobeniusMap( K::FldFin ) -> Map
{The Frobenius map of K w.r.t. its base field}
  return iso< K -> K | x :-> Frobenius(x) >;
end intrinsic;

intrinsic FrobeniusMap( K::FldFin, S::FldFin ) -> Map
{The Frobenius map of K w.r.t. the subfield S}
  require S subset K : "Not a subfield";
  return iso< K -> K | x :-> Frobenius(x, S) >;
end intrinsic;
  
intrinsic FrobeniusMap( K::FldFin, r::RngIntElt ) -> Map
{The r-th Frobenius map of K w.r.t. its base field}
  return iso< K -> K | x :-> Frobenius(x,r) >;
end intrinsic;

intrinsic FrobeniusMap( K::FldFin, S::FldFin, r::RngIntElt ) -> Map
{The r-th Frobenius map of K w.r.t. the subfield S}
  require S subset K : "Not a subfield";
  return iso< K -> K | x :-> Frobenius(x, S, r) >;
end intrinsic;
  
/* This has now been superceded by C-code
intrinsic Hilbert90( a::FldFinElt, q::RngIntElt ) -> FldFinElt
{Returns b such that a = b^q * b^-1}
  ok, p := IsPrimePower( q );
  require ok : "Not a prime power";
  require p eq Characteristic(Parent(a)) : "Incorrect prime power";
  if a eq 0 or a eq 1 then  return a;  end if;
  k := GF( q );  K := CommonOverfield( k, Parent(a) );
  a := K!a;  t := Order( Norm( a, k ) );
  P := PolynomialRing( ext<K|t> ); x := P.1;
  has, rt :=  HasRoot( x^(q-1) - a );
  assert has;
  return rt;
end intrinsic;
*/

intrinsic AdditiveHilbert90( a::FldFinElt, q::RngIntElt ) -> FldFinElt
{Returns b such that a = b^q - b}
  ok, p := IsPrimePower( q );
  require ok : "Not a prime power";
  require p eq Characteristic(Parent(a)) : "Incorrect prime power";
  if a eq 0 then  return a;  end if;
  k := GF( q );  K := CommonOverfield( k, Parent(a) );
  a := K!a;  
  tr := Trace( a, k );
  if tr ne 0 then
    K := ext< K | Characteristic(K) >;  a := K!a;
  end if;
  d := Degree( K, k );  x := Generator( K, k );
  a := Vector( Eltseq( a, k ) );
  A := Matrix( [ Vector( Eltseq( (x^i)^q, k ) ) : i in [0..d-1] ] );
  b := Solution( A-1, a );
  return &+[ b[i+1]*x^i : i in [0..d-1] ];
end intrinsic;  
