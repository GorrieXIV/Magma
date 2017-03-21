freeze;

/*
  This file contains utilities for the user and functions to construct algebraic
  objects from tensors.
*/


__GetInduction := function( X, i )
  t := X`DerivedFrom[1];
  v := t`Valence;
  j := v-i+1;
  gens := [ g : g in Generators(X) ];
  grp := Type(X) eq GrpMat;
  lie := Type(X) eq AlgMatLie;
  K := BaseRing(t);
  spaces := Frame(t);
  d := Dimension(spaces[j]);
  s := &+([Dimension(spaces[k]) : k in [ x : x in X`DerivedFrom[2] | x lt j ]] cat [1]);
  blocks := { ExtractBlock(g,s,s,d,d) : g in gens };
  if grp then
    if GL(d,K)!1 in blocks then
      Exclude(~blocks,GL(d,K)!1);
    end if;
    Y := sub< Generic(GL(d,K)) | blocks >;
  else
    if lie then
      if MatrixLieAlgebra(K,d)!0 in blocks then
        Exclude(~blocks,MatrixLieAlgebra(K,d)!0);
      end if;
      Y := sub< MatrixLieAlgebra(K,d) | blocks >;
    else
      if MatrixAlgebra(K,d)!0 in blocks then
        Exclude(~blocks,MatrixAlgebra(K,d)!0);
      end if;
      Y := sub< MatrixAlgebra(K,d) | blocks >;
    end if;
  end if;
  proj := map< X -> Y | x :-> Y!ExtractBlock(x,s,s,d,d) >;
  return Y, proj;
end function;

__WriteOverPrimeField := function( Forms )
  M := Tensor(Forms,2,1);
  K := BaseRing(M);
  k := GF(Characteristic(K));
  e := Round(Log(#k, #K));
  D_old := M`Domain;
  D_new := [*KSpace( k, Dimension(D)*e ) : D in D_old*];
  C_old := M`Codomain;
  C_new := KSpace( k, Dimension(M`Codomain)*e );
  maps_D := [ map< D_new[i] -> D_old[i] | 
    x :-> D_old[i]![ K![ Coordinates(D_new[i],x)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(D_old[i])] ],
    y :-> D_new[i]!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(D_old[i],y) ] ]) > : i in [1..#D_old] ];
  map_C := map< C_old -> C_new | 
    x :-> C_new!(&cat[ &cat[ Eltseq( s ) : s in Coordinates(C_old,x) ] ]),
    y :-> C_old![ K![ Coordinates(C_new,y)[j] : j in [(k-1)*e+1..k*e] ] : k in [1..Dimension(C_old)] ] >;
  F := function(x)
    return (< x[i] @ maps_D[i] : i in [1..#x] > @ M) @ map_C;
  end function;
  N := Tensor( D_new, C_new, F );
  assert forall{ b : b in CartesianProduct( < [ c*K.1^i : i in [0..e-1], c in Basis(D) ] : D in D_old > ) | 
    (b @ M) @ map_C eq < b[i] @@ maps_D[i] : i in [1..#b] > @ N };
  return SystemOfForms(N);
end function;

intrinsic HeisenbergGroup( B::TenSpcElt ) -> GrpPC
{Returns the group of class 2 and exponent p from the given Zp tensor B.}
  require B`Valence eq 2 : "Tensor must have valence 2.";
  try
    t := AlternatingTensor(B);
    Forms := SystemOfForms(t);
  catch err
    error err`Object;
  end try;
  K := BaseRing(Forms[1]);
  p := Characteristic(K);
  require p gt 0 : "Field must have nonzero characteristic.";
  if #K gt p then
    Forms := __WriteOverPrimeField(Forms);
  end if;
  require Nrows(Forms[1]) + #Forms le 256 : "Cannot handle groups larger than p^256.";
  d := Nrows(Forms[1]);
  e := #Forms;
  F := FreeGroup( d+e );
  powers := [ F.i^p = 1 : i in [1..d] ];
  commutators := [];
  for i in [1..d] do
    for j in [i+1..d] do
      commutators cat:= [ F.j^F.i = F.j * &*[ F.(d+k)^(Integers()!(Forms[k][i][j])) : k in [1..e] ] ];
    end for;
  end for;
  Q := quo< F | powers cat commutators >;
  P := pQuotient( Q, p, 2 : Exponent := p );
  return P;
end intrinsic;

intrinsic HeisenbergAlgebra( B::TenSpcElt ) -> AlgGen
{Returns the algebra whose product is given by the tensor.}
  require B`Valence eq 2 : "Tensor must have valence 2.";
  try
    _ := Eltseq(B);
  catch err
    error err`Object;
  end try;
  K := BaseRing(B);
  if Dimension(B`Domain[1]) ne Dimension(B`Domain[2]) then
    Forms := SystemOfForms(B);
    c := Dimension(B`Domain[1]);
    d := Dimension(B`Domain[2]);
    Forms := [ InsertBlock(ZeroMatrix(K,c+d,c+d),f,1,c+1) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  if Dimension(B`Domain[1]) ne Dimension(B`Codomain) then
    Forms := SystemOfForms(B);
    d := Dimension(B`Domain[1]);
    e := Dimension(B`Codomain);
    Forms := [ ZeroMatrix(K,d+e,d+e) : i in [1..d] ] cat [ DiagonalJoin(f,ZeroMatrix(K,e,e)) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  A := Algebra< K, Dimension(B`Domain[1]) | Eltseq(B) >;
  return A;
end intrinsic;

intrinsic HeisenbergLieAlgebra( B::TenSpcElt ) -> AlgLie
{Returns the Lie algebra whose Lie bracket is given by the tensor.}
  require B`Valence eq 2 : "Tensor must have valence 2.";
  try
    _ := Eltseq(B);
  catch err
    error err`Object;
  end try;
  K := BaseRing(B);
  B := AlternatingTensor(B);
  Forms := SystemOfForms(B);
  if Dimension(B`Domain[1]) ne Dimension(B`Codomain) then
    d := Dimension(B`Domain[1]);
    e := Dimension(B`Codomain);
    Forms := [ ZeroMatrix(K,d+e,d+e) : i in [1..d] ] cat [ DiagonalJoin(f,ZeroMatrix(K,e,e)) : f in Forms ];
    B := Tensor(Forms,2,1);
  end if;
  L := LieAlgebra< K, d+e | Eltseq(B) >;
  return L;
end intrinsic;

intrinsic Induce( X::GrpMat, i::RngIntElt ) -> GrpMat, Map
{Given a group of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i+1 in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic Induce( X::AlgMat, i::RngIntElt ) -> AlgMat, Map
{Given an algebra of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i+1 in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic Induce( X::AlgMatLie, i::RngIntElt ) -> AlgMatLie, Map
{Given a Lie algebra of matrices associated to a tensor, returns the restriction of the object onto the ith space and a projection.}
  require assigned X`DerivedFrom : "Cannot find the associated tensor.";
  require Type(X`DerivedFrom[1]) eq TenSpcElt : "Cannot recognize associated tensor.";
  require X`DerivedFrom[1]`Valence-i+1 in X`DerivedFrom[2] : "No restriction found.";
  return __GetInduction(X,i);
end intrinsic;

intrinsic DerivationAlgebra( A::Alg ) -> AlgMatLie
{Returns the derivation algebra of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := Tensor(A);
  D := DerivationAlgebra(B);
  Der := Induce(D,2);
  return Der;
end intrinsic;

intrinsic Centroid( A::Alg ) -> AlgMat
{Returns the centroid of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := Tensor(A);
  C := Centroid(B);
  Cent := Induce(C,2);
  return Cent;
end intrinsic;

intrinsic LeftNucleus( A::Alg ) -> AlgMat
{Returns the left nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,2,0),2);
  bas := Basis(sub<KMatrixSpace(K,d,d)|[ Transpose(X) : X in Basis(N) ]> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  L := sub< MatrixAlgebra(K,d) | bas >;
  return L;
end intrinsic;

intrinsic RightNucleus( A::Alg ) -> AlgMat
{Returns the right nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,1,0),1);
  bas := Basis(sub<KMatrixSpace(K,d,d)|Basis(N)> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  R := sub< MatrixAlgebra(K,d) | bas >;
  return R;
end intrinsic;

intrinsic MidNucleus( A::Alg ) -> AlgMat
{Returns the mid nucleus of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  K := BaseRing(A);
  d := Dimension(A);
  B := Tensor(A);
  N := Induce(Nucleus(B,2,1),2);
  bas := Basis(sub<KMatrixSpace(K,d,d)|Basis(N)> meet sub<KMatrixSpace(K,d,d)|AsMatrices(B,2,0)>);
  M := sub< MatrixAlgebra(K,d) | bas >;
  return M;
end intrinsic;

intrinsic Center( A::Alg ) -> Alg
{Returns the center of A.}
  if Type(BaseRing(A)) in {FldRe,FldCom} then 
    "Warning: answers known to be incorrect for the Real and Complex fields.";
  end if;
  B := CommutatorTensor(A);
  R := Radical(B);
  C := R[1] meet R[2];
  S := sub< A | [ c @@ B`Coerce[1] : c in Basis(C) ] >;
  return S;
end intrinsic;
