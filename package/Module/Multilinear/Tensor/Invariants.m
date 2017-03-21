freeze;

/*
  This file contains invariants for tensors. They come in two flavors: linear
  algebra and polynomial-based invariants. Most of the invariants have been 
  optimized for bimaps (2-tensors).
*/


import "Tensor.m" : __GetTensor;
import "../TensorCategory/Hom.m" : __GetHomotopism;
import "../GlobalVars.m" : __LIST, __SANITY_CHECK, __GLUE;
import "../Util/ConjugateCyclic.m" : __IsCyclic;

// Given vectors return blocks
__VectorToBlocks := function( v, d )
  F := BaseRing( v );
  v := Eltseq( v );
  return < MatrixAlgebra( F, d[i] )![ v[ &+([0] cat [ d[j]^2 : j in [1..i-1] ]) + k] : k in [1..d[i]^2] ] : i in [1..#d] >;
end function;

__SCentroid := function( M, S )
  S := Sort([ s : s in S ]);
  C := Basis( M`Codomain );
  d := #C;
  R := BaseRing( M`Codomain );
  B := CartesianProduct( < [1..Dimension(X)] : X in M`Domain > );
  dims := [ Dimension( M`Domain[s] ) : s in S ];
  V := RSpace( R, &+[ d^2 : d in dims ] + d^2 );
  mat := [];

  for x in B do
    for k in [1..d] do
      r := V!0; 
      for i in [1..d] do
        temp := [ x[l] : l in [1..#x] ] cat [i];
        r[ &+[ d^2 : d in dims ] + k + (i-1)*d ] -:= Slice(M,[{t} : t in temp])[1];
      end for;
      rows := [ r : i in [1..#S] ];
      for i in [1..#S] do
        for j in [1..dims[i]] do
          temp := [ x[l] : l in [1..#x] ] cat [k];
          temp[S[i]] := j;
          rows[i][ &+([ dims[x]^2 : x in [1..i-1] ] cat [0]) + (x[S[i]]-1)*dims[i] + j ] +:= Slice(M,[{t} : t in temp])[1];
        end for;
      end for;
      mat cat:= rows;
    end for;
  end for;

  T := NullspaceOfTranspose( Matrix(mat) );
  MA := MatrixAlgebra( R, &+(dims) + d );
  C := sub< MA | [ MA!DiagonalJoin( __VectorToBlocks( T.i, dims cat [d] ) ) : i in [1..Dimension(T)] ] >;
  return C;
end function;

__Derivations := function( M )
  B := CartesianProduct( < [1..Dimension(X)] : X in M`Domain > );
  C := Basis( M`Codomain );
  d := #C;
  R := BaseRing( M`Codomain );
  dims := [ Dimension( X ) : X in M`Domain ];
  V := RSpace( R, &+[ d^2 : d in dims ] + d^2 );
  mat := [];

  for x in B do
    for k in [1..d] do
      r := V!0; 
      for i in [1..d] do
        temp := [ x[l] : l in [1..#x] ] cat [i];
        r[ &+[ d^2 : d in dims ] + k + (i-1)*d ] -:= Slice(M,[{t} : t in temp])[1]; 
      end for;
      for i in [1..M`Valence] do
        for j in [1..dims[i]] do
          temp := [ x[l] : l in [1..#x] ] cat [k];
          temp[i] := j; // represents the endomorphism from x[i] to e_j (jth basis element)
          r[ &+([ dims[t]^2 : t in [1..i-1] ] cat [0]) + (x[i]-1)*dims[i] + j ] +:= Slice(M,[{t} : t in temp])[1];
        end for;
      end for;
      Append(~mat,r);
    end for;
  end for;

  S := NullspaceOfTranspose( Matrix(mat) );
  MA := MatrixLieAlgebra( R, &+(dims) + d );
  T := sub< MA | [ MA!DiagonalJoin( __VectorToBlocks( S.i, dims cat [d] ) ) : i in [1..Dimension(S)] ] >;
  return T;
end function;

// Computes the nucleus of the first two terms. Therefore, it is n,(n-1) nucleus.
__12Nucleus := function( M )
  I := CartesianProduct( < [1..Dimension(X)] : X in M`Domain > );
  M1 := M`Domain[1];
  M2 := M`Domain[2];
  R := BaseRing( M1 );
  d1 := Dimension( M1 );
  d2 := Dimension( M2 );
  V := RSpace( R, d1^2 + d2^2 );
  mat := [];

  for x in I do
    for k in [1..Dimension(M`Codomain)] do
      r := V!0;
      temp := [ x[l] : l in [1..#x] ];
      for i in [1..d1] do
        temp[1] := i;
        r[ (x[1]-1)*d1 + i ] +:= Slice(M,[{t} : t in temp] cat [{k}])[1]; 
      end for;
      temp := [ x[l] : l in [1..#x] ];
      for j in [1..d2] do
        temp[2] := j;
        r[ d1^2 + (x[2]-1)*d2 + j ] -:= Slice(M,[{t} : t in temp] cat [{k}])[1];
      end for;
      Append(~mat,r);
    end for;
  end for;

  T := NullspaceOfTranspose( Matrix(mat) );
  blocks := [ __VectorToBlocks( T.i, [d1,d2] ) : i in [1..Dimension(T)] ];
  MA := MatrixAlgebra( R, d1 + d2 );
  N := sub< MA | [ MA!DiagonalJoin( b[1], Transpose(b[2]) ) : b in blocks ] >;  

  return N;
end function;

// Kantor's Lemma
__GetFieldHom := function( E, F )
  f := DefiningPolynomial(E);
  R := PolynomialRing(F);
  factors := Factorization(R!f);
  assert exists(p){ g[1] : g in factors | Degree(g[1]) eq 1 };
  p := LeadingCoefficient(p)^-1 * p;
  phi := hom< E -> F | R.1-p >;
  g := DefiningPolynomial(F);
  R := PolynomialRing(E);
  factors := Factorization(R!g);
  i := 1;
  repeat 
    q := LeadingCoefficient(factors[i][1])^-1 * factors[i][1];
    phi_inv := hom< F -> E | R.1-q >;
    i +:= 1;
  until (E.1 @ phi) @ phi_inv eq E.1 and (F.1 @ phi_inv) @ phi eq F.1;
  return phi,phi_inv;
end function;

// Below are functions optimized for bimaps.
__AdjointOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  M := ZeroMatrix(K,a^2+b^2,a*b*c);

  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ -Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  if exists(S){ S : S in t`Cat`Repeats | {1,2} subset S } then
    S := { 1,2 };
    inds := [a,b,c];
    assert a eq b;
    offset := [ 1,a^2+1,a^2+1 ];
    s := Maximum(S);
    Exclude(~S,s);
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      X := ZeroMatrix(K,a^2+b^2,inds[s]^2);
      InsertBlock(~X,-IdentityMatrix(K,inds[s]^2),offset[s],1);
      InsertBlock(~X,IdentityMatrix(K,inds[m]^2),offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  N := NullspaceMatrix(M);
  MA := MatrixAlgebra(K,a+b);
  A := sub< MA | [ DiagonalJoin( Matrix(a,a,Eltseq(N[i])[b^2+1..a^2+b^2]), Transpose(Matrix(b,b,Eltseq(N[i])[1..b^2])) ) : i in [1..Nrows(N)] ] >;
  return A;
end function;

__LeftScalarsOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  M := ZeroMatrix(K,a^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := HorizontalJoin( AsMatrices( t,2,1 ) );
  ipos := c^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := AsMatrices(t,0,1);
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    block := -Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= b;
    end for;
  end for;
  delete Fb;

  if exists(S){ S : S in t`Cat`Repeats | {0,2} subset S } then
    S := { 1,3 };
    inds := [a,b,c];
    assert a eq c;
    offset := [ 1,a^2+1,a^2+1 ];
    s := Maximum(S);
    Exclude(~S,s);
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      X := ZeroMatrix(K,a^2+c^2,inds[s]^2);
      perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
      InsertBlock(~X,-PermutationMatrix(K,perm),offset[s],1);
      InsertBlock(~X,IdentityMatrix(K,inds[m]^2),offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  N := NullspaceMatrix(M);
  MA := MatrixAlgebra(K,a+c);
  A := sub< MA | [ DiagonalJoin( Transpose(Matrix(a,a,Eltseq(N[i])[c^2+1..a^2+c^2])), Matrix(c,c,Eltseq(N[i])[1..c^2]) ) : i in [1..Nrows(N)] ] >;
  return A;
end function;

__RightScalarsOfBimap := function( t )
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  M := ZeroMatrix(K,b^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := -HorizontalJoin( AsMatrices( t,1,2 ) );
  ipos := c^2+1;
  jpos := 1;
  for i in [1..b] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= b;
    jpos +:= a*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := AsMatrices(t,0,2);
  jpos := 1;
  for i in [1..b] do
    ipos := 1;
    block := Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= a;
    end for;
  end for;
  delete Fb;

  if exists(S){ S : S in t`Cat`Repeats | {0,1} subset S } then
    S := { 2,3 };
    inds := [a,b,c];
    assert b eq c;
    offset := [ 1,c^2+1,1 ];
    s := Maximum(S);
    Exclude(~S,s);
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      X := ZeroMatrix(K,b^2+c^2,inds[s]^2);
      perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
      InsertBlock(~X,PermutationMatrix(K,perm),offset[s],1);
      InsertBlock(~X,-IdentityMatrix(K,inds[m]^2),offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  N := NullspaceMatrix(M);
  MA := MatrixAlgebra(K,b+c);
  A := sub< MA | [ DiagonalJoin( Matrix(b,b,Eltseq(N[i])[c^2+1..b^2+c^2]), Transpose(Matrix(c,c,Eltseq(N[i])[1..c^2])) ) : i in [1..Nrows(N)] ] >;
  return A;
end function;

__CentroidOfBimap := function(t)
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  M := ZeroMatrix(K,a^2+b^2+c^2,2*a*b*c);

  // Adjoint blocks:
  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  // Left Scalars:
  // Put the A blocks in
  Fa := HorizontalJoin( AsMatrices( t,2,1 ) );
  ipos := b^2+1;
  jpos := a*b*c+1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := AsMatrices(t,0,1);
  jpos := a*b*c+1;
  for i in [1..a] do
    ipos := a^2+b^2+1;
    block := Fb[i];
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      ipos +:= c;
      jpos +:= b;
    end for;
  end for;
  delete Fb;

  // add block for the fuse
  w := [b^2,0,a^2+b^2];
  if exists(S){ S : S in t`Cat`Repeats | #S ge 2 } then
    S := { 3-x : x in S };
    if S eq {2,3} then k := -1; else k := 1; end if;
    inds := [a,b,c];
    assert forall{ s : s in S | inds[s] eq inds[Maximum(S)] };
    offset := [ b^2+1,1,a^2+b^2+1 ];
    s := Minimum(S);
    Exclude(~S,s);
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      if m eq 3 then
        perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
        N := PermutationMatrix(K,perm);
      else
        N := IdentityMatrix(K,inds[m]^2);
      end if;
      X := ZeroMatrix(K,a^2+b^2+c^2,inds[s]^2);
      InsertBlock(~X,k*IdentityMatrix(K,inds[s]^2),offset[s],1);
      InsertBlock(~X,N,offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  /* Eventually fix this to not have to multiply matrices. */
  D := DiagonalMatrix(K,[1 : i in [1..b^2]] cat [-1 : i in [1..a^2]] cat [1 : i in [1..c^2]]);
  N := NullspaceMatrix(D*M);
  MA := MatrixAlgebra(K,a+b+c);
  A := sub< MA | [ DiagonalJoin( < Matrix(a,a,Eltseq(N[i])[w[1]+1..w[1]+a^2]), Matrix(b,b,Eltseq(N[i])[w[2]+1..w[2]+b^2]), Transpose(Matrix(c,c,Eltseq(N[i])[w[3]+1..w[3]+c^2])) > ) : i in [1..Nrows(N)] ] >;
  return A;
end function;

__DerivationsOfBimap := function(t)
  a := Dimension(t`Domain[1]);
  b := Dimension(t`Domain[2]);
  c := Dimension(t`Codomain);
  S := StructureConstants(t);
  K := BaseRing(t);
  // t : K^a x K^b >-> K^c given by S

  M := ZeroMatrix(K,a^2+b^2+c^2,a*b*c);

  // Put the A blocks in
  Fa := Foliation(t, 2);
  ipos := b^2+1;
  jpos := 1;
  for i in [1..a] do
    InsertBlock( ~M, Fa, ipos, jpos );
    ipos +:= a;
    jpos +:= b*c;
  end for;
  delete Fa;

  // Put the B blocks in
  Fb := Transpose(Foliation(t, 1));
  Fb_blocks := [ Transpose(Matrix(Fb[(i-1)*c+1..i*c])) : i in [1..a] ];
  delete Fb;
  jpos := 1;
  for i in [1..a] do
    ipos := 1;
    for j in [1..b] do
      InsertBlock( ~M, Fb_blocks[1], ipos, jpos );
      ipos +:= b;
      jpos +:= c;
    end for;
    Remove(~Fb_blocks,1);
  end for;

  // Put the C blocks in
  Fc := Transpose(Foliation(t, 0));
  jpos := 1;
  for i in [1..a*b] do
    ipos := a^2+b^2+1;
    block := Transpose(Matrix( Fc[i] ));
    for j in [1..c] do
      InsertBlock( ~M, block, ipos, jpos );
      jpos +:= 1;
      ipos +:= c;
    end for;
  end for;
  delete Fc;

  // add block for the fuse
  if exists(S){ S : S in t`Cat`Repeats | #S ge 2 } then
    S := { 3-x : x in S };
    inds := [a,b,c];
    assert forall{ s : s in S | inds[s] eq inds[Maximum(S)] };
    offset := [ b^2+1,1,a^2+b^2+1 ];
    s := Maximum(S);
    Exclude(~S,s);
    if s eq 3 then 
      perm := Eltseq(Transpose(Matrix(IntegerRing(),c,c,[1..c^2])));
      N := PermutationMatrix(K,perm);
    else 
      N := -IdentityMatrix(K,inds[s]^2); 
    end if;
    while #S gt 0 do
      m := Maximum(S);
      Exclude(~S,m);
      X := ZeroMatrix(K,a^2+b^2+c^2,inds[s]^2);
      InsertBlock(~X,N,offset[s],1);
      InsertBlock(~X,IdentityMatrix(K,inds[m]^2),offset[m],1);
      M := HorizontalJoin(X,M);
    end while;
  end if;

  /* Eventually fix this to not have to multiply matrices. */
  D := DiagonalMatrix(K,[1 : i in [1..a^2+b^2]] cat [-1 : i in [1..c^2]]);
  N := NullspaceMatrix(D*M);
  MA := MatrixLieAlgebra(K,a+b+c);
  A := sub< MA | [ DiagonalJoin( < Matrix(a,a,Eltseq(N[i])[b^2+1..a^2+b^2]), Matrix(b,b,Eltseq(N[i])[1..b^2]), Transpose(Matrix(c,c,Eltseq(N[i])[a^2+b^2+1..a^2+b^2+c^2])) > ) : i in [1..Nrows(N)] ] >;
  return A;
end function;

__GetSmallerRandomGenerators := function( X ) 
  if not IsFinite(BaseRing(X)) then
    return X;
  end if;
  gens := Generators(X);
  if #gens le 3 then
    return X;
  end if;
  small := {};
  repeat
    Include(~small,Random(X));
    S := sub< X | small>;
  until Dimension(X) eq Dimension(S);
  return S;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                   Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
// ==============================================================================
//                             Linear algebra methods
// ==============================================================================
intrinsic Radical( t::TenSpcElt, i::RngIntElt ) -> ModTupRng, Map
{Returns the ith radical of t contained in Vi.}
  v := t`Valence;
  require i ge 1 : "Argument must be a positive integer.";
  require i le v : "Argument exceeds valence of tensor.";
  if Type(t`Radicals[v-i+1]) ne RngIntElt then
    return t`Radicals[v-i+1][1],t`Radicals[v-i+1][2];
  end if;

  try 
    F := Foliation(t,i);
  catch err
    error "Cannot compute structure constants.";
  end try;

  D := t`Domain[v-i+1];
  B := Basis(D);
  V := VectorSpace(BaseRing(t),#B);
  phi := map< D -> V | x:-> &+[ Coordinates( D, x )[j]*V.j : j in [1..#B] ], y:-> &+[ Coordinates( V, y )[j]*B[j] : j in [1..#B] ] >;
  R := Nullspace(F);
  
  if __SANITY_CHECK then
    printf "Sanity check turned on... (Radical)";
    tvs := TensorOnVectorSpaces(t);
    for j in [1..10] do
      x := < Random(X) : X in tvs`Domain >;
      x[v-i+1] := Random(R);
      assert x @ tvs eq tvs`Codomain!0;
    end for;
    printf "  DONE!\n";
  end if;
  t`Radicals[v-i+1] := <R,phi>;
  return R,phi;
end intrinsic;

intrinsic Coradical( M::TenSpcElt ) -> ModTupRng, Map
{Returns the coradical of M.}
  if Type(M`Radicals[M`Valence+1]) ne RngIntElt then
    return M`Radicals[M`Valence+1][1],M`Radicals[M`Valence+1][2];
  end if;
  require Type(M`Codomain) in __LIST : "Codomain not a vector space.";
  I := Image(M);
  C,pi := M`Codomain/I;
  M`Radicals[M`Valence+1] := <C,pi>;
  return C,pi;
end intrinsic;

intrinsic Radical( M::TenSpcElt ) -> Tup
{Returns the radical of M.}
  return < Radical(M,i) : i in Reverse([1..M`Valence]) >;
end intrinsic;

intrinsic Centroid( t::TenSpcElt ) -> AlgMat
{Returns the centroid of the tensor t.}
  if Type(t`Centroids[2][1]) ne RngIntElt then
    return t`Centroids[2][1];
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  if t`Valence eq 2 then
    C := __CentroidOfBimap( t );
  else
    C := __SCentroid( t, {1..t`Valence} );
  end if;
  C := __GetSmallerRandomGenerators(C);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (Centroid)";
    tvs := TensorOnVectorSpaces(t);
    spaces := __GLUE(tvs);
    dims := [ Dimension(X) : X in spaces ];
    MultiplyByBlock := function(x,B,i)
      x[i] := x[i]*B;
      return x;
    end function;
    for c in Generators(C) do
      blocks := [* ExtractBlock( c, &+(dims[1..i-1] cat [0])+1, &+(dims[1..i-1] cat [0])+1, dims[i], dims[i] ) : i in [1..#dims] *];
      assert forall{ x : x in CartesianProduct( < Basis(spaces[i]) : i in [1..#spaces-1] > ) |
              (&and[ (MultiplyByBlock(x,blocks[i],i) @ tvs) eq (MultiplyByBlock(x,blocks[1],1) @ tvs) : i in [2..tvs`Valence] ]) and
              ( ((x @ tvs)*blocks[#blocks]) eq (MultiplyByBlock(x,blocks[1],1) @ tvs) ) };
    end for;
    printf "  DONE!\n";
  end if;
  C`DerivedFrom := < t, [1..t`Valence+1] >;
  t`Centroids[2][1] := C;
  return C;
end intrinsic;

intrinsic DerivationAlgebra( t::TenSpcElt ) -> AlgMatLie
{Returns the derivation algebra of the tensor t.}
  if assigned t`Derivations then
    return t`Derivations;
  end if;
  try
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  if t`Valence eq 2 then
    D := __DerivationsOfBimap( t );
  else
    D := __Derivations( t );
  end if;
  D := __GetSmallerRandomGenerators(D);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (DerivationAlgebra)";
    tvs := TensorOnVectorSpaces(t);
    spaces := __GLUE(tvs);
    dims := [ Dimension(X) : X in spaces ];
    MultiplyByBlock := function(x,B,i)
      x[i] := x[i]*B;
      return x;
    end function;
    for d in Generators(D) do
      blocks := [* ExtractBlock( d, &+(dims[1..i-1] cat [0])+1, &+(dims[1..i-1] cat [0])+1, dims[i], dims[i] ) : i in [1..#dims] *];
      assert forall{ x : x in CartesianProduct( < Basis(X) : X in tvs`Domain > ) |
              &+[ MultiplyByBlock(x,blocks[i],i) @ tvs : i in [1..#dims-1] ] eq (x @ tvs)*blocks[#blocks] };
    end for;
    printf "  DONE!\n";
  end if;

  D`DerivedFrom := < t, [1..t`Valence+1] >;
  t`Derivations := D;
  return D;
end intrinsic;

intrinsic Nucleus( t::TenSpcElt, i::RngIntElt, j::RngIntElt ) -> AlgMat
{Returns the ij-nucleus of the tensor t.}
  require i ne j : "Integers must be distinct.";
  v := t`Valence;
  require {i,j} subset {0..v} : "Integers must correspond to Cartesian factors.";
  if t`Cat`Contra then
    require 0 notin {i,j} : "Integers must be positive for cotensors.";
  end if;

  // has it been computed before?
  ind := Index(t`Nuclei[1],{i,j});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;

  a := Maximum([i,j]);
  b := Minimum([i,j]);
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;

  if t`Valence eq 2 then
    if {i,j} eq {0,1} then
      Nij := __RightScalarsOfBimap(t);
    elif {i,j} eq {0,2} then
      Nij := __LeftScalarsOfBimap(t);
    elif {i,j} eq {1,2} then
      Nij := __AdjointOfBimap(t);
    end if;
  else
    // shuffle a,b to v,v-1.
    perm := [0..v];
    if #{a,b,v,v-1} eq 2 then
      perm := [ k : k in [0..v] ];
    elif #{a,b,v,v-1} ne 3 then
      perm[v+1] := a;
      perm[v] := b;
      perm[i+1] := v;
      perm[j+1] := v-1;
    else
      k := Random(Exclude(Exclude({a,b,v-1,v},v-1),v));
      l := Random(Exclude(Exclude({a,b,v-1,v},a),b));
      perm[v+1] := a;
      perm[v] := b;
      perm[k+1] := l;
    end if;
    s := Shuffle( t, perm ); 
    Nij := __12Nucleus(s);
  end if;
  
  if __SANITY_CHECK then
    printf "Sanity check turned on... (Nucleus)";
    tvs := TensorOnVectorSpaces(t);
    spaces := Reverse(__GLUE(tvs));
    MultiplyByBlock := function(x,B,k)
      x[k] := x[k]*B;
      return x;
    end function;
    for x in [Random(Nij) : r in [1..20]] do
      X := ExtractBlock( x, 1, 1, Dimension(spaces[a+1]), Dimension(spaces[a+1]) );
      Y := ExtractBlock( x, Dimension(spaces[a+1])+1, Dimension(spaces[a+1])+1, Dimension(spaces[b+1]), Dimension(spaces[b+1]) );
      if a eq 0 then
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          (B @ tvs) * X eq MultiplyByBlock(B,Y,v-b+1) @ tvs };
      elif b eq 0 then
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          MultiplyByBlock(B,X,v-a+1) @ tvs eq (B @ tvs) * Y };
      else
        assert forall{ B : B in CartesianProduct( < Basis(X) : X in tvs`Domain > ) | 
          MultiplyByBlock(B,X,v-a+1) @ tvs eq MultiplyByBlock(B,Transpose(Y),v-b+1) @ tvs };
      end if;
    end for;
    printf "  DONE!\n";
  end if;
  Nij`DerivedFrom := < t, [v-a+1,v-b+1] >;
  t`Nuclei[2][ind] := Nij;
  return Nij;
end intrinsic;

intrinsic TensorOverCentroid( t::TenSpcElt ) -> TenSpcElt, Hmtp
{Returns the tensor of t as a tensor over its centroid.}
  if t`Cat`Contra then
    return t;
  end if;
  C := Centroid(t);
  K := BaseRing(C);
  require IsFinite(K) : "Base ring must be finite.";
  n := Nrows(C.1);
  J,S := WedderburnDecomposition(C);
  require IsCommutative(S) : "Centroid is not a commutative ring.";
  if Generators(S) eq { Generic(S)!1 } then
    return t,_;
  end if;
  isit,X := __IsCyclic(S);
  require isit : "Centroid is not a commutative local ring.";
  
  t,H2 := TensorOnVectorSpaces(t);
  D := t`Domain;
  C := t`Codomain;
  dims := [ Dimension(X) : X in D ] cat [ Dimension(C) ];
  blocks := [* ExtractBlock( X, &+(dims[1..i-1] cat [0]) + 1, &+(dims[1..i-1] cat [0]) + 1, dims[i], dims[i] ) : i in [1..#dims] *];
  Exts := [* ext< K | MinimalPolynomial(blocks[i]) > : i in [1..#dims] *];
  E := GF( #Exts[1] );
  phi := [* *]; 
  phi_inv := [* *];
  for i in [1..#Exts] do
    f,g := __GetFieldHom( Exts[i], E );
    Append(~phi,f);
    Append(~phi_inv,g);
  end for;
  e := Degree( E, K );
  
  Spaces := __GLUE(t);
  InvSubs := [* [ sub< Spaces[i] | [ Spaces[i].1*blocks[i]^j : j in [0..e-1] ] > ] : i in [1..#Spaces] *]; // invariant subspaces
  // loop through the spaces and get the rest of the invariant subspaces
  for i in [1..#Spaces] do
    notdone := true;
    while notdone do
      U := &+(InvSubs[i]);
      Q,pi := Spaces[i]/U;
      if Dimension(Q) eq 0 then
        notdone := false;
      else
        S := sub< Spaces[i] | [ (Q.1@@pi)*blocks[i]^j : j in [0..e-1] ] >;
        Append(~InvSubs[i],S);
      end if;
    end while;
  end for;
  Bases := [* &cat[ Basis(S) : S in InvSubs[i] ] : i in [1..#Spaces] *];
  VS := [* VectorSpaceWithBasis( B ) : B in Bases *];

  dom := [* VectorSpace( E, dims[i] div e ) : i in [1..#dims-1] *];
  cod := VectorSpace( E, dims[#dims] div e );

  ToNewSpace := function(x,i)
    c := Coordinates(VS[i],VS[i]!x);
    vec := [ Exts[i]!(c[(j-1)*e+1..j*e]) : j in [1..dims[i] div e] ];
    vec := [ v @ phi[i] : v in vec ];
    return vec;
  end function;

  ToOldSpace := function(y,i)
    c := Eltseq(y);
    c := [ x @ phi_inv[i] : x in c ];
    vec := &cat[ Eltseq(c[j]) : j in [1..#c] ];
    vec := &+[ vec[j]*Bases[i][j] : j in [1..#Bases[i]] ];
    return vec;
  end function;

  Maps := [* map< D[i] -> dom[i] | x :-> dom[i]!ToNewSpace(x,i), y :-> D[i]!ToOldSpace(y,i) > : i in [1..#D] *];
  Maps cat:= [* map< C -> cod | x :-> cod!ToNewSpace(x,#VS), y :-> C!ToOldSpace(y,#VS) > *];

  F := function(x)
    return (< x[i] @@ Maps[i] : i in [1..#x] > @ t) @ Maps[#Maps];
  end function;

  s := __GetTensor( dom, cod, F );
  H := __GetHomotopism( t, s, Maps : Cat := HomotopismCategory(t`Valence) );
  if assigned t`Coerce then
    s`Coerce := [* t`Coerce[i] * Maps[i] : i in [1..#t`Coerce] *];
  end if;
  if assigned H2 then
    H := H2*H;
  end if;

  if __SANITY_CHECK then
    printf "Sanity check turned on... (MultimapOverCentroid)";
    assert forall{ x : x in CartesianProduct( < Basis( X ) : X in t`Domain > ) |
           (< x[i] @ Maps[i] : i in [1..#x] > @ s) eq (x @ t @ Maps[#Maps]) };
    printf "  DONE!\n";
  end if;

  return s,H;
end intrinsic;

// ==============================================================================
//                              Optimized for bimaps
// ==============================================================================
intrinsic AdjointAlgebra( t::TenSpcElt ) -> AlgMat
{Returns the adjoint *-algebra of the 2-tensor t.}
  require t`Valence eq 2 : "Must be a 2-tensor.";
  if assigned t`Adjoint then
    return t`Adjoint;
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  
  S := SystemOfForms(t);
  A := AdjointAlgebra(S);
  try
    _ := RecognizeStarAlgebra(A);
  catch err 
    error "Cannot recognize the star algebra.";
  end try;
  A`DerivedFrom := < t, [1,2] >;
  t`Adjoint := A;
  return A;
end intrinsic;

intrinsic LeftNucleus( t::TenSpcElt ) -> AlgMat
{Returns the left nucleus of the 2-tensor t.}
  require t`Valence eq 2 : "Tensor must have valence 2.";
  ind := Index(t`Nuclei[1], {0,2});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  L := __LeftScalarsOfBimap(t);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (LeftScalars)";
    S := SystemOfForms(t);
    for l in Generators(L) do
      X := ExtractBlock(l,1,1,Nrows(S[1]),Nrows(S[1]));
      Z := ExtractBlock(l,Nrows(S[1])+1,Nrows(S[1])+1,#S,#S);
      assert [ Transpose(X)*S[i] : i in [1..#S] ] eq [ &+[ Z[i][j]*S[j] : j in [1..#S] ] : i in [1..#S] ];
    end for;
    printf "  DONE!\n";
  end if;
  L`DerivedFrom := < t, [1,3] >;
  t`Nuclei[2][ind] := L;
  return L;
end intrinsic;

intrinsic MidNucleus( t::TenSpcElt ) -> AlgMat
{Returns the mid nucleus of the 2-tensor t.}
  require t`Valence eq 2 : "Tensor must have valence 2.";
  return Nucleus(t,2,1);
end intrinsic;

intrinsic RightNucleus( t::TenSpcElt ) -> AlgMat
{Returns the right nucleus of the 2-tensor t.}
  require t`Valence eq 2 : "Tensor must have valence 2.";
  ind := Index(t`Nuclei[1], {0,1});
  if Type(t`Nuclei[2][ind]) ne RngIntElt then
    return t`Nuclei[2][ind];
  end if;
  try 
    _ := Eltseq(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  R := __RightScalarsOfBimap(t);

  if __SANITY_CHECK then
    printf "Sanity check turned on... (RightScalars)";
    S := SystemOfForms(t);
    for r in Generators(R) do
      Y := ExtractBlock(r,1,1,Ncols(S[1]),Ncols(S[1]));
      Z := ExtractBlock(r,Ncols(S[1])+1,Ncols(S[1])+1,#S,#S);
      assert [ S[i]*Transpose(Y) : i in [1..#S] ] eq [ &+[ S[j]*Z[j][i] : j in [1..#S] ] : i in [1..#S] ];
    end for;
    printf "  DONE!\n";
  end if;
  R`DerivedFrom := < t, [2,3] >;
  t`Nuclei[2][ind] := R;
  return R;
end intrinsic;

// ==============================================================================
//                           Polynomial-based invariants
// ==============================================================================
intrinsic Discriminant( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) discriminant of the 2-tensor t.}
  require t`Valence eq 2 : "Only defined for tensors of valence 2.";
  K := BaseRing(t);
  require Type(K) ne BoolElt : "Tensor must have a base ring.";
  require Dimension(t`Domain[1]) eq Dimension(t`Domain[2]) : "Discriminant not defined for this tensor.";
  C := t`Codomain;
  n := Dimension(C);
  R := PolynomialRing(K,n);
  try
    S := SystemOfForms(t);
  catch err
    error "Cannot compute structure constants.";
  end try;
  MA := MatrixAlgebra(K,Nrows(S[1]));
  return Determinant( &+[ (MA!S[i])*R.i : i in [1..n] ] );
end intrinsic;

intrinsic Pfaffian( t::TenSpcElt ) -> RngMPolElt
{Returns the (generalized) Pfaffian of the alternating bimap.}
  require t`Valence eq 2 : "Only defined for tensors of valence 2.";
  require IsAlternating(t) : "Tensor must be alternating.";
  try
    disc := Discriminant(t);
  catch err
    error "Cannot compute the discriminant of the bimap."; 
  end try;
  if disc ne Parent(disc)!0 then
    factors := Factorisation(disc);
    assert forall{ f : f in factors | IsEven(f[2]) };
    return &*[ f[1]^(f[2] div 2) : f in factors ];
  end if;
  return Parent(disc)!0;
end intrinsic;
