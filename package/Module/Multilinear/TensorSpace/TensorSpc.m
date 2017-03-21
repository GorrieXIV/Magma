freeze;

/*
  This file contains all the constructors for tensor spaces (TenSpc).
*/


import "../GlobalVars.m" : __LIST, __SANITY_CHECK;
import "../Tensor/TensorBasic.m" : __HasBasis;

__GetTensorSpace := function( R, L, C )
  T := New(TenSpc);
  T`Cat := C;
  T`Valence := C`Valence;
  T`Ring := R;
  if Type(L) eq SeqEnum then
    T`Frame := [* X : X in L *];
  else // should be list
    assert Type(L) eq List;
    T`Frame := L;
  end if;
  T`Mod := RSpace(R,&*[Dimension(M) : M in L]); // builds a universal copy.
  T`UniMap := hom< T`Mod -> T`Mod | x:->x, y:->y >;
  return T;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// General universal tensor spaces
intrinsic TensorSpace( S::SeqEnum, C::TenCat ) -> TenSpc
{The universal tensor space with given modules and specified tensor category.}
  require #S eq (C`Valence+1) : "Number of modules does not match tensor category valence.";
  try
    require forall{ M : M in S | BaseRing(M) cmpeq BaseRing(S[1]) } : "All modules must have a common base ring.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;
  require forall{ M : M in S | __HasBasis(M) } : "All entries in frame must be free modules.";
  R := BaseRing(S[1]);
  return __GetTensorSpace(R,S,C);
end intrinsic;

intrinsic TensorSpace( S::SeqEnum ) -> TenSpc
{The universal tensor space with given modules and homotopism category.}
  return TensorSpace(S,HomotopismCategory(#S-1));
end intrinsic;

intrinsic TensorSpace( S::List, C::TenCat ) -> TenSpc
{The universal tensor space with given modules and specified tensor category.}
  require #S eq (C`Valence+1) : "Number of modules does not match tensor category valence.";
  try
    require forall{ M : M in S | BaseRing(M) cmpeq BaseRing(S[1]) } : "All modules must have a common base ring.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;
  require forall{ M : M in S | __HasBasis(M) } : "All entries in frame must be free modules.";
  R := BaseRing(S[1]);
  return __GetTensorSpace(R,S,C);
end intrinsic;

intrinsic TensorSpace( S::List ) -> TenSpc
{The universal tensor space with given modules and homotopism category.}
  return TensorSpace(S,HomotopismCategory(#S-1));
end intrinsic;

// General universal cotensor spaces
intrinsic CotensorSpace( S::SeqEnum, C::TenCat ) -> TenSpc
{The universal cotensor space with given modules and specified tensor category.}
  require #S eq (C`Valence) : "Number of modules does not match tensor category valence.";
  try
    require forall{ M : M in S | BaseRing(M) cmpeq BaseRing(S[1]) } : "All modules must have a common base ring.";
    require ISA(Type(BaseRing(S[1])),Fld) : "Base ring must be a field.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;
  require C`Contra : "Category is not contravariant.";
  require forall{ M : M in S | __HasBasis(M) } : "All entries in frame must be vector spaces.";
  R := BaseRing(S[1]);
  S := SequenceToList(S) cat [*RSpace(R,1)*];
  return __GetTensorSpace(R,S,C);
end intrinsic;

intrinsic CotensorSpace( S::SeqEnum ) -> TenSpc
{The universal cotensor space with given modules and homotopism category.}
  return CotensorSpace(S,HomotopismCategory(#S : Contravariant := true));
end intrinsic;

intrinsic CotensorSpace( S::List, C::TenCat ) -> TenSpc
{The universal cotensor space with given modules and specified tensor category.}
  require #S eq (C`Valence) : "Number of modules does not match tensor category valence.";
  try
    require forall{ M : M in S | BaseRing(M) cmpeq BaseRing(S[1]) } : "All modules must have a common base ring.";
    require ISA(Type(BaseRing(S[1])),Fld) : "Base ring must be a field.";
  catch err
    error "Entries in frame must have a module structure.";
  end try;
  require C`Contra : "Category is not contravariant.";
  require forall{ M : M in S | __HasBasis(M) } : "All entries in frame must be vector spaces.";
  R := BaseRing(S[1]);
  S cat:= [*RSpace(R,1)*];
  return __GetTensorSpace(R,S,C);
end intrinsic;

intrinsic CotensorSpace( S::List ) -> TenSpc
{The universal cotensor space with given modules and homotopism category.}
  return CotensorSpace(S,HomotopismCategory(#S : Contravariant := true));
end intrinsic;

//Coordinatized universal tensor spaces.
intrinsic RTensorSpace( R::Rng, S::SeqEnum[RngIntElt], C::TenCat ) -> TenSpc
{Universal tensor space with free R-modules of given ranks and specified category.}
  require #S eq (C`Valence+1) : "Number of modules does not match tensor category valence.";
  require forall{ s : s in S | s gt 0 } : "Integers in argument 2 must be positive.";
  return __GetTensorSpace( R, [* RSpace( R, s ) : s in S *], C );
end intrinsic;

intrinsic RTensorSpace( R::Rng, S::SeqEnum[RngIntElt] ) -> TenSpc
{Universal tensor space with free R-modules of given ranks and homotopism category.}
  return RTensorSpace( R, S, HomotopismCategory(#S-1) );
end intrinsic;

intrinsic KTensorSpace( K::Fld, S::SeqEnum[RngIntElt], C::TenCat ) -> TenSpc
{Universal tensor space with K-vector spaces of given dimenisions and specified category.}
  require #S eq (C`Valence+1) : "Number of modules does not match tensor category valence.";
  require forall{ s : s in S | s gt 0 } : "Integers in argument 2 must be positive.";
  return __GetTensorSpace( K, [* KSpace( K, s ) : s in S *], C );
end intrinsic;

intrinsic KTensorSpace( K::Fld, S::SeqEnum[RngIntElt] ) -> TenSpc
{Universal tensor space with free R-modules of given ranks and homotopism category.}
  return KTensorSpace( K, S, HomotopismCategory(#S-1) );
end intrinsic;

//Coordinatized universal cotensor spaces.
intrinsic KCotensorSpace( K::Fld, S::SeqEnum[RngIntElt], C::TenCat ) -> TenSpc
{Universal cotensor space with K-vector spaces of given dimenisions and specified category.}
  require #S eq C`Valence : "Number of modules does not match tensor category valence.";
  require forall{ s : s in S | s gt 0 } : "Integers in argument 2 must be positive.";
  require C`Contra : "Category is not contravariant.";
  S cat:= [1];
  return __GetTensorSpace( K, [* KSpace( K, s ) : s in S *], C );
end intrinsic;

intrinsic KCotensorSpace( K::Fld, S::SeqEnum[RngIntElt] ) -> TenSpc
{Universal cotensor space with free R-modules of given ranks and homotopism category.}
  return KCotensorSpace( K, S, HomotopismCategory(#S : Contravariant := true) );
end intrinsic;

//Signatured tensor spaces.
intrinsic TensorSpace( K::Fld, d::RngIntElt, p::RngIntElt, q::RngIntElt ) -> TenSpc
{Returns the signatured (p,q)-tensor space over K^d.}
  require d gt 0 : "Argument 2 must be positive.";
  require p ge 0 : "Argument 3 must be nonnegative.";
  require q ge 0 : "Arugment 4 must be nonnegative.";
  require p+q gt 0 : "Must have more than one index.";
  A := [-1 : i in [1..p]] cat [1 : i in [1..q]] cat [0];
  P := {{q+1..q+p}, {1..q},{0}};
  C := TensorCategory( A, P );
  return __GetTensorSpace( K, [* KSpace( K, d ) : i in [1..p+q] *] cat [*KSpace(K,1)*], C);
end intrinsic;

intrinsic TensorSpace( V::ModTupFld, p::RngIntElt, q::RngIntElt ) -> TenSpc
{Returns the signatured (p,q)-tensor space over V.}
  require p ge 0 : "Argument 3 must be nonnegative.";
  require q ge 0 : "Arugment 4 must be nonnegative.";
  require p+q gt 0 : "Must have more than one index.";
  A := [-1 : i in [1..p]] cat [1 : i in [1..q]] cat [0];
  P := {{q+1..q+p}, {1..q},{0}};
  C := TensorCategory( A, P );
  return __GetTensorSpace( BaseRing(V), [* V : i in [1..p+q] *] cat [*KSpace(BaseRing(V),1)*], C );
end intrinsic;

// Standard examples
intrinsic ExteriorCotensorSpace( V::ModTupFld, n::RngIntElt ) -> TenSpc
{Returns the nth exterior power of V as a cotensor space.}
  d := Dimension(V); 
  require d ge n : "Vector space dimension too small."; 
  K := BaseRing(V);
  T := __GetTensorSpace( K, [* V : i in [1..n] *] cat [* VectorSpace(K,1) *], CotensorCategory([ 1 : i in [1..n] ], {{1..n}}) );
  U := T`Mod;
  Ex := KSpace(K,Binomial(d,n));
  subs := [ Sort([ x : x in s ]) : s in Subsets({1..d},n) ];
  G := Sym( {1..n} );
  CP := CartesianProduct( < [1..d] : i in [1..n] > );

  IntoUniversal := function(x)
    temp := [ K!0 : i in [1..d^n] ];
    for g in G do
      perm := Eltseq(g);
      k := Sign(g);
      for i in [1..Binomial(d,n)] do
        s := Eltseq(x)[i];
        if s ne K!0 then
          ind := 1 + (&+[d^(j-1)*(((subs[i])[perm])[j]-1): j in [1..n]]);
          temp[ind] := k*s;
        end if;
      end for;
    end for;
    return U!temp;    
  end function;

  IntoExterior := function(y)
    temp := Eltseq(y);
    x := [ K!0 : i in [1..Binomial(d,n)] ];
    for i in [1..Binomial(d,n)] do
      ind := 1 + (&+[d^(j-1)*(subs[i][j]-1): j in [1..n]]);
      x[i] := temp[ind];
    end for;
    return Ex!x;
  end function;

  pi := map< Ex -> U | x :-> IntoUniversal(x), y :-> IntoExterior(y) >;
  T`Mod := Ex;
  T`UniMap := pi*T`UniMap;
  return T;
end intrinsic;

intrinsic SymmetricCotensorSpace( V::ModTupFld, n::RngIntElt ) -> TenSpc
{Returns the nth exterior power of V as a cotensor space.}
  d := Dimension(V); 
  K := BaseRing(V);
  T := __GetTensorSpace( K, [* V : i in [1..n] *] cat [* VectorSpace(K,1) *], CotensorCategory([ 1 : i in [1..n] ], {{1..n}}) );
  U := T`Mod;
  Sy := KSpace(K,Binomial(d+n-1,n));
  subs := [ Sort([ x : x in s ]) : s in Multisets({1..d},n) ];
  G := Sym( {1..n} );
  CP := CartesianProduct( < [1..d] : i in [1..n] > );

  IntoUniversal := function(x)
    temp := [ K!0 : i in [1..d^n] ];
    for g in G do
      perm := Eltseq(g);
      for i in [1..#subs] do
        s := Eltseq(x)[i];
        if s ne K!0 then
          ind := 1 + (&+[d^(j-1)*(((subs[i])[perm])[j]-1): j in [1..n]]);
          temp[ind] := s;
        end if;
      end for;
    end for;
    return U!temp;    
  end function;

  IntoSymmetric := function(y)
    temp := Eltseq(y);
    x := [ K!0 : i in [1..#subs] ];
    for i in [1..#subs] do
      ind := 1 + (&+[d^(j-1)*(subs[i][j]-1): j in [1..n]]);
      x[i] := temp[ind];
    end for;
    return Sy!x;
  end function;

  pi := map< Sy -> U | x :-> IntoUniversal(x), y :-> IntoSymmetric(y) >;
  T`Mod := Sy;
  T`UniMap := pi*T`UniMap;
  return T;
end intrinsic;
