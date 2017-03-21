freeze;

/*
  This file contains the constructor for the densor subspace of a tensor.
*/


import "TensorSpc.m" : __GetTensorSpace;
import "../GlobalVars.m" : __SANITY_CHECK;

// Given operators O and dims a,b,c compute the tensors t (flat arrays) such that O is a subset of Der(t).
__GetDensorTensors := function( O, a, b, c )
  /* Assumption: 
   *   T : K^a x K^b >-> K^c
   *   #O = d
   * Solves abc linear equations with abcd variables. 
   */

  K := BaseRing(O[1]);
  d := #O;
  dims := [a,b,c];
  offset := [1,a+1,a+b+1];
  blocks := [* [ ExtractBlock(X,offset[i],offset[i],dims[i],dims[i]) : X in O ] : i in [1..3] *];
  //blocks[2] := [ Transpose(X) : X in blocks[2] ];
  Z := ZeroMatrix(K,a*b*c,a*b*c*d);
  Y := ZeroMatrix(K,a*b*c*d,a*b*c);
  X := ZeroMatrix(K,a*b*c*d,a*b*c);
  
  // Z Block
  jpos := 1;
  for i in [1..d] do
    ipos := 1;
    for j in [1..a*b] do
      InsertBlock(~Z,blocks[3][i],ipos,jpos);
      ipos +:= c;
      jpos +:= c;
    end for;
  end for;

  // Y Block
  ipos := 1;
  for i in [1..d] do
    jpos := 1;
    for j in [1..a] do
      Yblock := [];
      for k in [1..b] do
        vec := &cat[ [x] cat [0 : i in [1..c-1]] : x in Eltseq(blocks[2][i][k]) ];
        for l in [1..c] do
          Append(~Yblock,vec);
          Remove(~vec,#vec);  
          vec := [0] cat vec;
        end for;      
      end for;
      InsertBlock(~Y,Matrix(K,Yblock),ipos,jpos);
      ipos +:= b*c;
      jpos +:= b*c;
    end for;
  end for;

  // X Block
  ipos := 1;
  for i in [1..d] do
    for j in [1..a] do
      vec := &cat[[x] cat [0 : i in [1..b*c-1]] : x in Eltseq(blocks[1][i][j])];
      for k in [1..b*c] do
        InsertBlock(~X,Matrix(K,1,a*b*c,vec),ipos,1);
        Remove(~vec,#vec);
        vec := [0] cat vec;
        ipos +:= 1;
      end for;
    end for;
  end for;

  M := Transpose(X+Y)-Z;
  N := NullspaceMatrix(M);
  return N;
end function;

// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//                                  Intrinsics
// ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
intrinsic DerivationClosure( TS::TenSpc, O::[Mtrx] ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators O.}
  require TS`Valence eq 2 : "Tensor space must have valence 2.";
  dims := [ Dimension(X) : X in TS`Frame ];
  require Nrows(O[1]) eq &+dims and Ncols(O[1]) eq &+dims : "Incompatible operators.";
  require BaseRing(TS) eq BaseRing(O[1]) : "Base rings are incompatible.";
  N := __GetDensorTensors(O,dims[1],dims[2],dims[3]);
  S := __GetTensorSpace( TS`Ring, TS`Frame, TS`Cat );
  S`Mod := sub< TS`Mod | [ TS`Mod!N[i] : i in [1..Nrows(N)] ] >;
  if __SANITY_CHECK and Dimension(S) gt 0 then
    printf "Sanity check turned on... (DerivationClosure)";
    assert forall{ i : i in [1..10] | O subset DerivationAlgebra(Random(S)) };
    printf "  DONE!\n";
  end if;
  return S;
end intrinsic;

intrinsic DerivationClosure( TS::TenSpc, O::[AlgMatLie] ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators O.}
  return DerivationClosure(TS,[ Matrix(X) : X in O ]);
end intrinsic;

intrinsic DerivationClosure( TS::TenSpc, O::AlgMatLie ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators O.}
  return DerivationClosure(TS,Basis(O));
end intrinsic;

intrinsic DerivationClosure( TS::TenSpc, O::AlgMat ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators O.}
  return DerivationClosure(TS,Basis(O));
end intrinsic;

intrinsic DerivationClosure( TS::TenSpc, O::ModMatFld ) -> TenSpc
{Returns the derivation closure of the tensor space with the given operators O.}
  return DerivationClosure(TS,Basis(O));
end intrinsic;

intrinsic DerivationClosure( TS::TenSpc, T::TenSpcElt ) -> TenSpc
{Returns the derivation closure of the tensor space with the derivation algebra of the given tensor.}
  return DerivationClosure(TS,Basis(DerivationAlgebra(T)));
end intrinsic;

intrinsic NucleusClosure( TS::TenSpc, O::[Mtrx], s::RngIntElt, t::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators O acting on Us and Ut.}
  require TS`Valence eq 2 : "Tensor space must have valence 2.";
  K := BaseRing(TS);
  require K eq BaseRing(O[1]) : "Base rings are incompatible.";
  dims := [ Dimension(X) : X in TS`Frame ];
  a := 3-s;
  b := 3-t;
  c := Random({1,2,3} diff {a,b});
  require (&+(dims[[a,b]]) eq Nrows(O[1])) and (Nrows(O[1]) eq Ncols(O[1])) : "Incompatible operators.";
  blocks := [* [ ExtractBlock( X, 1, 1, dims[a], dims[a] ) : X in O ], [ ExtractBlock( -Transpose(X), dims[a]+1, dims[a]+1, dims[b], dims[b] ) : X in O ], [ ZeroMatrix(K,dims[c],dims[c]) : i in [1..#O] ] *];
  perm := [1,2,3];
  temp := [a,b,c];
  ParallelSort(~temp,~perm);
  M := [ DiagonalJoin( < blocks[perm[i]][j] : i in [1..3] > ) : j in [1..#O] ];
  N := __GetDensorTensors(M,dims[1],dims[2],dims[3]);
  S := __GetTensorSpace( TS`Ring, TS`Frame, TS`Cat );
  S`Mod := sub< TS`Mod | [ TS`Mod!N[i] : i in [1..Nrows(N)] ] >;
  if __SANITY_CHECK and Dimension(S) gt 0 then
    printf "Sanity check turned on... (NucleusClosure)";
    assert forall{ i : i in [1..10] | O subset Nucleus(Random(S),s,t) };
    printf "  DONE!\n";
  end if;
  return S;
end intrinsic;

intrinsic NucleusClosure( TS::TenSpc, O::AlgMat, s::RngIntElt, t::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators O acting on Us and Ut.}
  return NucleusClosure(TS,Basis(O),s,t);
end intrinsic;

intrinsic NucleusClosure( TS::TenSpc, O::ModMatFld, s::RngIntElt, t::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the given operators O acting on Us and Ut.}
  return NucleusClosure(TS,Basis(O),s,t);
end intrinsic;

intrinsic NucleusClosure( TS::TenSpc, T::TenSpcElt, s::RngIntElt, t::RngIntElt ) -> TenSpc
{Returns the nucleus closure of the tensor space with the st-nucleus of the given tensor.}
  return NucleusClosure(TS,Basis(Nucleus(T,s,t)),s,t);
end intrinsic;
