freeze;

/*
  This file contains all the constructors for tensors (TenSpcElt).
*/ 


import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __GLUE;
import "TensorBasic.m" : __HasBasis;
import "../TensorCategory/Hom.m" : __GetHomotopism;

__GetBimapRecord := function( B )
  D := B`Domain;
  C := B`Codomain;
  rf := recformat< U : BmpU, V : BmpV, Reflexive : Rec >;
  B`Bimap := rec< rf | U := New(BmpU), V := New(BmpV) >;
  B`Bimap`U`Parent := B;
  B`Bimap`V`Parent := B;
  B`Bimap`U`Space := D[1];
  B`Bimap`V`Space := D[2];
  return B;
end function;

// Given a list of domain D, codomain C, and a user defined function F,
// write the necessary information into t to make it a functional TenSpcElt.
__GetTensor := function( D, C, F : Par := false, Co := false, Cat := HomotopismCategory(#D) )
  t := New(TenSpcElt);
  dom := CartesianProduct( < X : X in D > );
  m := map< dom -> C | x :-> F(x) >;
  t`Map := m;
  t`Valence := #D;  
  if Type(D) eq SeqEnum then
    t`Domain := [* X : X in D *];
  else // must be list
    assert Type(D) eq List;
    t`Domain := D;
  end if;
  t`Codomain := C;
  t`Radicals := [* 0 : i in [1..t`Valence+1] *]; // radical and coradical
  t`Nuclei := [* [* S : S in Subsets( {0..t`Valence},2 ) *], [* 0 : i in [1..#Subsets( {0..t`Valence},2 )] *] *];
  t`Centroids := [* [* S : S in Subsets( {1..t`Valence},i ), i in Reverse([2..t`Valence]) *], [* 0 : i in [1..2^(t`Valence)-t`Valence-1] *] *];
  rf := recformat< Alternating : BoolElt, Antisymmetric : BoolElt, Symmetric : BoolElt >;
  t`Reflexive := rec< rf | >;
  t`Cat := Cat;
  t`Permutation := Sym({0..#D})!1;
  if Type(Par) ne BoolElt then
    t`Parent := Par;
  end if;
  if Type(Co) ne BoolElt then
    t`Coerce := Co;
  end if;
  if t`Valence eq 2 and not t`Cat`Contra then
    t := __GetBimapRecord(t);
  end if;
  return t;
end function;

__GetPolarisation := function( f )
  P := Parent(f);
  n := Ngens(P);
  gens := [ P.i : i in [1..n] ];
  d := Degree(f);
  R := PolynomialRing( BaseRing(P), n*d );
  p := R!0;
  T := Terms(f);

  // polar = f( x1 + ... + xn ) - f( x1 + ... + xn-1 ) - f( x1 + ... + xn-2 + xn ) - ... f( x2 + ... + xn ) + ... + (-1)^n-1 * f( x1 ) + ... + (-1)^n-1 * f( xn ) 
  // we go from left to right starting with f( x1 + ... + xn ).

  for i in [0..d-1] do // i = number of variables to remove.
    subs := [ SetToSequence(t) : t in Subsets({0..d-1}) | d-#t eq i ];
    for s in subs do // subs is the sequence of increasing sequences of { 0, ..., d-1 } with length d-i.
      sum := R!0;
      for t in T do
        c := Coefficients(t)[1];
        vars := Factorization( c^-1 * t );
        vars := &cat[ [ Index(gens,v[1]) : j in [1..v[2]] ] : v in vars ];
        m := c;
        for v in vars do
          m *:= &+[ R.(v+j*n) : j in s ];
        end for;
        sum +:= m;
      end for;
      p +:= (-1)^i * sum;
    end for;
  end for;

  return p;
end function;

//__sl2Module := function( d, K )
//  e := InsertBlock( ZeroMatrix(K,d,d), DiagonalMatrix(K,[i : i in [1..d-1]]), 1,2 );
//  f := InsertBlock( ZeroMatrix(K,d,d), DiagonalMatrix(K,[d-i : i in [1..d-1]]), 2,1 );
//  h := DiagonalMatrix(K,[d-1-2*i : i in [0..d-1]]);
//  sl2 := sub< MatrixLieAlgebra(K,d) | h,f,e >;
//  return sl2, RModule( sl2 );
//end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ==============================================================================
//                                  Black-box
// ==============================================================================
intrinsic Tensor( D::SeqEnum, C::., F::UserProgram, Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the Cartesian product of the sequence D into C given by F with tensor category Cat. 
The UserProgram F must take as input a tuple in D.}
  require #D eq Cat`Valence : "Given modules do not match category valence.";
  return __GetTensor( D, C, F : Cat := Cat );
end intrinsic;

intrinsic Tensor( D::SeqEnum, C::., F::UserProgram ) -> TenSpcElt
{Returns the tensor from the Cartesian product of the sequence D into C given by F. 
The UserProgram F must take as input a tuple in D.}
  return __GetTensor( D, C, F );
end intrinsic;

intrinsic Tensor( S::SeqEnum, F::UserProgram, Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the sequence S evaluated by F with tensor category Cat. 
The UserProgram F must take as input a tuple in the domain.}
  require #S-1 eq Cat`Valence : "Given modules do not match category valence.";
  return __GetTensor( S[1..#S-1], S[#S], F : Cat := Cat );
end intrinsic;

intrinsic Tensor( S::SeqEnum, F::UserProgram ) -> TenSpcElt
{Returns the tensor from the sequence S evaluated by F. 
The UserProgram F must take as input a tuple in the domain.}
  return __GetTensor( S[1..#S-1], S[#S], F );
end intrinsic;

intrinsic Tensor( D::List, C::., F::UserProgram, Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the Cartesian product of the list D into C given by F with tensor category Cat. 
The UserProgram F must take as input a tuple in D.}
  require #D eq Cat`Valence : "Given modules do not match category valence.";
  return __GetTensor( D, C, F : Cat := Cat );
end intrinsic;

intrinsic Tensor( D::List, C::., F::UserProgram ) -> TenSpcElt
{Returns the tensor from the Cartesian product of the list D into C given by F. 
The UserProgram F must take as input a tuple in D.}
  return __GetTensor( D, C, F );
end intrinsic;

intrinsic Tensor( S::List, F::UserProgram, Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the list S evaluated by F with tensor category Cat. 
The UserProgram F must take as input a tuple in the domain.}
  require #S-1 eq Cat`Valence : "Given modules do not match category valence.";
  return __GetTensor( S[1..#S-1], S[#S], F : Cat := Cat );
end intrinsic;

intrinsic Tensor( S::List, F::UserProgram ) -> TenSpcElt
{Returns the tensor from the list S evaluated by F. 
The UserProgram F must take as input a tuple in the domain.}
  return __GetTensor( S[1..#S-1], S[#S], F );
end intrinsic;

// ==============================================================================
//                                    Sequences
// ==============================================================================
intrinsic Tensor( R::Rng, D::[RngIntElt], S::[RngElt], Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the sequence S over the free R-modules with dimensions given by D in the tensor category Cat.}
  if Cat`Contra then
    Append(~D,1);
  end if;
  require #D eq Cat`Valence+1 : "Number of implied modules does not match category valence.";
  require &*(D) eq #S : "Dimensions do not match.";
  require IsCoercible( R, S[1] ) : "Entries cannot be coerced into the ring.";
  offsets := [ &*D[i+1..#D] : i in [1..#D-1] ] cat [1];
  F := function(x)
    coords := [* Eltseq(x[i]) : i in [1..#x] *];
    B := CartesianProduct( < [0..D[i]-1] : i in [1..#D-1] > );
    vec := [ R!0 : i in [1..D[#D]] ];
    for i in [0..D[#D]-1] do
      for b in B do
        ind := [ b[j] : j in [1..#b] ] cat [i];
        entry := &+[ ind[j] * offsets[j] : j in [1..#D] ] + 1;
        vec[i+1] +:= &*[ coords[j][b[j]+1] : j in [1..#D-1] ] * S[entry];
      end for;
    end for;
    return RSpace(R,D[#D])!vec;
  end function;
  t := __GetTensor( [* RSpace( R, D[i] ) : i in [1..#D-1] *], RSpace( R, D[#D] ), F : Cat := Cat );
  if CanChangeUniverse(S,R) then
    sc := ChangeUniverse(S,R);
  else
    sc := [ R!x : x in S ];
  end if;
  t`CoordImages := sc;
  return t;
end intrinsic;

intrinsic Tensor( D::[RngIntElt], S::[RngElt], Cat::TenCat ) -> TenSpcElt
{Returns the tensor from the sequence S over the free R-modules with dimensions given by D in the tensor category Cat.}
  return Tensor(Universe(S),D,S,Cat);
end intrinsic;

intrinsic Tensor( R::Rng, D::[RngIntElt], S::[RngElt] ) -> TenSpcElt
{Returns the tensor from the sequence S over the free R-modules with dimensions given by D in the tensor category Cat.}
  return Tensor(R,D,S,HomotopismCategory(#D-1));
end intrinsic;

intrinsic Tensor( D::[RngIntElt], S::[RngElt] ) -> TenSpcElt
{Returns the tensor from the sequence S over the free R-modules with dimensions given by D in the tensor category Cat.}
  return Tensor(Universe(D),D,S,HomotopismCategory(#D-1));
end intrinsic;

// ==============================================================================
//                             From algebraic objects
// ==============================================================================
intrinsic AssociatorTensor( A::Alg ) -> TenSpcElt
{Returns the tensor given by the associator in A.}
  F := function(x)
    return (x[1]*x[2])*x[3] - x[1]*(x[2]*x[3]);
  end function;
  return __GetTensor( [* A, A, A *], A, F : Co := [* map< A->A | x :-> x, y:->y > : i in [1..4] *], Cat := TensorCategory( [1,1,1,1], {{0..3}}) );
end intrinsic;

intrinsic Polarization( f::MPolElt ) -> TenSpcElt, MPolElt
{Returns the tensor, given by the polarization of the homogeneous polynomial f, along with the polarization of f.}
  require IsHomogeneous(f) : "Polynomial is not homogeneous.";
  P := Parent( f );
  R := BaseRing( P );
  n := Ngens( P );
  d := Degree( f );
  V := RSpace( R, n );
  p := __GetPolarisation( f );
  W := RSpace(R,1);

  F := function(x)
    return W![Evaluate( p, &cat[ Eltseq(i) : i in x ] )];
  end function;
  
  return __GetTensor( [* V : i in [1..d] *], W, F : Cat := TensorCategory([1 : i in [0..d]],{{1..d},{0}}) ), p;
end intrinsic;

intrinsic CommutatorTensor( A::Alg ) -> TenSpcElt
{Returns the tensor given by commutator in A.}
  F := function(x)
    return x[1]*x[2] - x[2]*x[1];
  end function;
  return __GetTensor( [* A, A *], A, F : Co := [* map< A->A | x :-> x, y:->y > : i in [1..3] *], Cat := TensorCategory( [1,1,1], {{0,1,2}} ) );
end intrinsic;

intrinsic Tensor( A::Alg ) -> TenSpcElt 
{Returns the tensor from A x A to A given by the product.}
  F := function(x)
    return x[1]*x[2];
  end function;
  return __GetTensor( [*A, A*], A, F : Co := [* map< A->A | x :-> x, y:->y > : i in [1..3] *], Cat := TensorCategory([1,1,1],{{0,1,2}}) );
end intrinsic;

intrinsic pCentralTensor( G::Grp, p::RngIntElt, s::RngIntElt, t::RngIntElt ) -> TenSpcElt
{Returns the tensor Ls x Lt >-> Ls+t from the associated Lie algebra from the p-central series of G.}
  require s gt 0 : "First index must be positive.";
  require t gt 0 : "Second index must be positive.";
  pcs := pCentralSeries(G,p);
  require s+t le #pcs : "The sum of the given indices is larger than the p-class.";
  U1,f1 := GModule( G, pcs[s], pcs[s+1] );
  U2,f2 := GModule( G, pcs[t], pcs[t+1] );
  U3,f3 := GModule( G, pcs[s+t], pcs[s+t+1] );
  V1 := VectorSpace( GF(p), Dimension(U1) );
  V2 := VectorSpace( GF(p), Dimension(U2) );
  V3 := VectorSpace( GF(p), Dimension(U3) );
  g1 := hom< U1 -> V1 | [ < U1.i, V1.i > : i in [1..Dimension(U1)] ] >;
  g2 := hom< U2 -> V2 | [ < U2.i, V2.i > : i in [1..Dimension(U2)] ] >;
  g3 := hom< U3 -> V3 | [ < U3.i, V3.i > : i in [1..Dimension(U3)] ] >;
  F := function(x)
    return ( x[1] @@ g1 @@ f1, x[2] @@ g2 @@ f2 ) @ f3 @ g3;
  end function;
  if s eq t then
    C := TensorCategory([1,1,1],{{0},{1,2}});
  else 
    C := HomotopismCategory(2);
  end if;
  return __GetTensor( [*V1, V2*], V3, F : Co := [* f1*g1, f2*g2, f3*g3 *], Cat := C );
end intrinsic;

intrinsic pCentralTensor( G::GrpPC, s::RngIntElt, t::RngIntElt ) -> TenSpcElt
{Returns the tensor Ls x Lt >-> Ls+t from the associated Lie algebra from the p-central series of G.}
  order := Factorization(#G);
  require #order eq 1 : "Group must be a p-group.";
  p := order[1][1];
  return pCentralTensor(G,p,s,t);
end intrinsic;

// ==============================================================================
//                                  New from old
// ==============================================================================
intrinsic Shuffle( M::TenSpcElt, g::GrpPermElt ) -> TenSpcElt 
{Returns the Knuth-Liebler shuffle of M, with valence v, by the permutation g on the set [0..v].}
  v := M`Valence;
  K := BaseRing(M);
  require IsField(K) : "Base ring must be a field.";
  if M`Cat`Contra then
    require Labelling(Parent(g)) in {{1..v},{0..v}} : "Permutation must act on {1..v}.";
    if Labelling(Parent(g)) eq {1..v} then
      g := Parent(M`Permutation)!([0] cat Eltseq(g));
    else
      require 0^g eq 0 : "Permutation must fix 0 for cotensors.";
    end if;
  else
    require Labelling(Parent(g)) eq {0..v} : "Permuation must act on {0..v}.";
  end if;
  try
    _ := Eltseq(M);
  catch err
    error "Cannot compute structure constants.";
  end try;
  g_elt := Reverse([ v-i+1 : i in Eltseq(g) ]);
  ginv_elt := Reverse([ v-i+1 : i in Eltseq(g^-1) ]);
  spaces := __GLUE(M);
  N_spaces := spaces[g_elt];
  D := N_spaces[1..v]; 
  C := N_spaces[v+1];
  AF := AssociatedForm( M );
  F := function( x )
    seq := [];
    for c in Basis(C) do
      temp := [* v : v in x *] cat [* c *];
      y := < z : z in temp[ginv_elt] >; 
      Append(~seq,Coordinates(AF`Codomain,y@AF));
    end for;
    return C!seq;
  end function; 

  // Construct new tensor from the old one.
  t := New(TenSpcElt);
  dom := CartesianProduct( < X : X in D > );
  m := map< dom -> C | x :-> F(x) >;
  t`Map := m;
  t`Valence := #D;
  t`Domain := D;
  t`Codomain := C;
  t`Radicals := [* 0 : i in [1..t`Valence+1] *]; // radical and coradical
  t`Nuclei := [* [* S : S in Subsets( {0..t`Valence},2 ) *], [* 0 : i in [1..#Subsets( {0..t`Valence},2 )] *] *];
  t`Centroids := [* [* S : S in Subsets( {1..t`Valence},i ), i in Reverse([2..t`Valence]) *], [* 0 : i in [1..2^(t`Valence)-t`Valence-1] *] *];
  rf := recformat< Alternating : BoolElt, Antisymmetric : BoolElt, Symmetric : BoolElt >;
  t`Reflexive := rec< rf | >;
  if assigned M`Coerce then
    t`Coerce := M`Coerce[g_elt];
  end if;
  if t`Valence eq 2 then
    t := __GetBimapRecord(t);
  end if;
  if assigned M`CoordImages then
    t`CoordImages := M`CoordImages;
  end if;
  t`Permutation := M`Permutation*g; 
  t`Cat := New(TenCat);
  t`Cat`Valence := v;
  t`Cat`Arrows := map< {0..v} -> {-1,0,1} | x:->(x^g) @ M`Cat`Arrows >;
  t`Cat`Repeats := { { x^(g^-1) : x in f } : f in M`Cat`Repeats };
  t`Cat`Contra := M`Cat`Contra;
  return t;
end intrinsic;

intrinsic Shuffle( M::TenSpcElt, g::SeqEnum ) -> TenSpcElt
{Returns the Knuth-Liebler shuffle of M, with valence v, by the permutation given by g on the set [0..v].}
  if M`Cat`Contra then
    isit, perm := IsCoercible(Sym({1..M`Valence}),g);
    if not isit then
      isit, perm := IsCoercible(Sym({0..M`Valence}),g);
      require isit : "Permutation must act on {1..v}.";
      require Index(g,0) eq 1 : "Permutation must fix 0.";
    end if;
  else
    isit, perm := IsCoercible(Sym({0..M`Valence}),g);
    require isit : "Permutation must act on {0..v}.";
  end if;
  return Shuffle(M,perm);
end intrinsic;

intrinsic TensorOnVectorSpaces( M::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the tensor on vector spaces (forgets all other structure of the domain and codomain) along with a homotopism.}
  if forall{ X : X in Frame(M) | Type(X) eq ModTupFld } then
    Maps := [* map< X -> X | x:->x, y:->y > : X in __GLUE(M) *];
    return M, __GetHomotopism(M,M,Maps : Cat := HomotopismCategory(M`Valence : Contravariant := M`Cat`Contra));
  end if;
  D := M`Domain;
  v := M`Valence;
  require forall{ X : X in D | __HasBasis(X) } : "Domain does not contain vector space structure.";
  require __HasBasis(M`Codomain) : "Codomain does not have vector space structure.";
  try
    R := BaseRing(M);
  catch err
    error err`Object;
  end try;
  require IsField(R) : "Base ring is not a field.";
  B := [* Basis(D[i]) : i in [1..v] *];
  V := [* VectorSpace( R, #B[i] ) : i in [1..v] *];
  C := M`Codomain;
  W := VectorSpace( R, #Basis(C) );
  maps := [* map< D[i] -> V[i] | x:-> &+[ Coordinates( D[i], x )[j]*V[i].j : j in [1..#B[i]] ],
                                 y:-> &+[ Coordinates( V[i], y )[j]*B[i][j] : j in [1..#B[i]] ] > : i in [1..v] *];
  Append(~maps, map< C -> W | x:-> &+[ Coordinates( C, x )[j]*W.j : j in [1..Dimension(W)] ],
                              y:-> &+[ Coordinates( W, y )[j]*Basis(C)[j] : j in [1..Dimension(W)] ] >);

  F := function(x)
    return < x[i] @@ maps[i] : i in [1..#x] > @ M @ maps[v+1];
  end function;

  N := __GetTensor( V, W, F : Cat := M`Cat );    
  if assigned M`CoordImages then
    N`CoordImages := M`CoordImages;
  end if;
  N`Nuclei := M`Nuclei;
  N`Centroids := M`Centroids;
  if assigned M`Coerce then
    N`Coerce := [* M`Coerce[i] * maps[i] : i in [1..#maps] *];
  end if;
  if assigned M`Derivations then
    N`Derivations := M`Derivations;
  end if;
  N`Permutation := M`Permutation;
  H := __GetHomotopism( M, N, maps : Cat := HomotopismCategory(M`Valence : Contravariant := M`Cat`Contra) );
  return N,H;
end intrinsic;

intrinsic AntisymmetricTensor( t::TenSpcElt ) -> TenSpcElt
{Returns an antisymmetric tensor induced from the given tensor.}
  if assigned t`Reflexive`Antisymmetric and t`Reflexive`Antisymmetric then
    return t;
  end if;
  try 
    sc := Eltseq(t);
  catch err
    error err`Object;
  end try;
  require forall{ X : X in t`Domain | Dimension(X) eq Dimension(t`Domain[1]) } : "Modules in domain are not all isomorphic.";
  K := BaseRing(t);
  if IsAntisymmetric(t) then
    return t;
  end if;
  G := Sym( {0..t`Valence} );
  Stab := Stabilizer( G, GSet(G), GSet(G)!0 );
  temp := [ K!0 : i in [1..#sc] ];
  for g in Stab do
    s := Shuffle(t,g);
    seq := Eltseq(s);
    k := Sign(g);
    temp := [ temp[i] + k*seq[i] : i in [1..#seq] ];
  end for;
  spaces := Frame(t);
  s := Tensor( K, [Dimension(X) : X in spaces], temp, t`Cat );
  if assigned t`Parent then
    s`Parent := t`Parent;
  end if;
  s`Reflexive`Alternating := true;
  s`Reflexive`Antisymmetric := true;
  if Characteristic(K) eq 2 then
    s`Reflexive`Symmetric := true;
  end if;
  return s;
end intrinsic;

intrinsic AlternatingTensor( t::TenSpcElt ) -> TenSpcElt
{Returns an alternating tensor induced from the given tensor.}
  if assigned t`Reflexive`Alternating and t`Reflexive`Alternating then
    return t;
  end if;
  return AntisymmetricTensor(t);
end intrinsic;

intrinsic SymmetricTensor( t::TenSpcElt ) -> TenSpcElt
{Returns a symmetric tensor induced from the given tensor.}
  if assigned t`Reflexive`Symmetric and t`Reflexive`Symmetric then
    return t;
  end if;
  try 
    sc := Eltseq(t);
  catch err
    error err`Object;
  end try;
  require forall{ X : X in t`Domain | Dimension(X) eq Dimension(t`Domain[1]) } : "Modules in domain are not all isomorphic.";
  K := BaseRing(t);
  if IsSymmetric(t) then
    return t;
  end if;
  G := Sym( {0..t`Valence} );
  Stab := Stabilizer( G, GSet(G), GSet(G)!0 );
  temp := [ K!0 : i in [1..#sc] ];
  for g in Stab do
    s := Shuffle(t,g);
    seq := Eltseq(s);
    temp := [ temp[i] + seq[i] : i in [1..#seq] ];
  end for;
  spaces := Frame(t);
  s := Tensor( K, [Dimension(X) : X in spaces], temp, t`Cat );
  if assigned t`Parent then
    s`Parent := t`Parent;
  end if;
  s`Reflexive`Symmetric := true;
  if Characteristic(K) eq 2 then
    s`Reflexive`Antisymmetric := false;
  end if;
  return s;
end intrinsic;

// ==============================================================================
//                                      Forms
// ==============================================================================
intrinsic Tensor( M::[Mtrx], s::RngIntElt, t::RngIntElt, Cat::TenCat ) -> TenSpcElt
{Returns the tensor given by the st-system of forms with the given tensor category.}  
  require s ne t : "Integers must be distinct.";
  require {s,t} subset {0..2} : "Integers must be contained in [0..2].";
  require Valence(Cat) eq 2 : "Tensor category incompatible.";
  if Cat`Contra then
    require {s,t} subset {1,2} : "Integers must be contained in [1..2].";
    require #M eq 1 : "Does not represent a cotensor.";
  end if;
  if s lt t then
    M := [ Transpose(X) : X in M ];
  end if;
  if {s,t} eq {1,2} then
    S := &cat[ &cat[ [ M[k][i][j] : k in [1..#M] ] : j in [1..Ncols(M[1])] ] : i in [1..Nrows(M[1])] ];
    dims := [ Nrows(M[1]), Ncols(M[1]), #M ];
  elif {s,t} eq {0,2} then
    S := &cat[ &cat[ Eltseq(M[k][i]) : k in [1..#M] ] : i in [1..Nrows(M[1])] ];
    dims := [ Nrows(M[1]), #M, Ncols(M[1]) ];
  elif {s,t} eq {0,1} then
    S := &cat[ &cat[ Eltseq(M[k][i]) : i in [1..Nrows(M[1])] ] : k in [1..#M] ];
    dims := [ #M, Nrows(M[1]), Ncols(M[1]) ];
  end if;
  return Tensor( dims, S, Cat );
end intrinsic;

intrinsic Tensor( M::[Mtrx], s::RngIntElt, t::RngIntElt ) -> TenSpcElt
{Returns the tensor given by the st-system of forms.}
  return Tensor( M, s, t, HomotopismCategory(2) );
end intrinsic;

intrinsic Tensor( M::Mtrx, s::RngIntElt, t::RngIntElt, Cat::TenCat ) -> TenSpcElt
{Returns the tensor given by the st-system of forms with the given tensor category.}
  return Tensor( [M], s, t, Cat );
end intrinsic;

intrinsic Tensor( M::Mtrx, s::RngIntElt, t::RngIntElt ) -> TenSpcElt
{Returns the tensor given by the st-system of forms.}
  return Tensor( [M], s, t );
end intrinsic;
