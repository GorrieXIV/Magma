freeze;
/*****************************************************
  Construction of a Lie algebra from a bilinear form

  August 2012 Don Taylor

  $Id: LieAlgebra.m 43943 2013-07-19 04:36:20Z don $

******************************************************/

/*
  The elements of the Lie algebra are the matrices X such that
  X*J + J*Transpose(X) eq 0.  This is equivalent to n^2 equations
  in n^2 unknowns.  The following function returns the matrix for
  these equations.
*/

createMatrix := function(J)
  n := Ncols(J);
  pairs := [<i,j> : i,j in [1..n]];
  NumPairs := n*n;
  M := KMatrixSpace(BaseRing(J),NumPairs,NumPairs);
  S := M!0;
  for col := 1 to NumPairs do
    ik := pairs[col];  i := ik[1];  k := ik[2];
    for row := 1 to NumPairs do
      pj := pairs[row]; p := pj[1]; j := pj[2];
      if p eq i then S[row,col] := J[j,k]; end if;
      if p eq k then S[row,col] +:= J[i,j]; end if;
    end for;
  end for;
  return S;
end function;


intrinsic DerivationAlgebra(J::AlgMatElt : Rep := "Sparse", Check := false) -> AlgLie
{The Lie algebra of derivations of the bilinear form with matrix J}
  K := KernelMatrix(createMatrix(J));
  n := Ncols(J);
  m := Nrows(K);
  F := BaseRing(J);
  V := VectorSpace(F,n*n);
  A := MatrixAlgebra(F,n);
  comm := func< a, b | a*b - b*a >;
  mat := func< v | A!Eltseq(v) >;
  struct := [Eltseq(Solution(K,V!Eltseq(comm(mat(K[i]),mat(K[j]))))) :
       i,j in [1..m]];

  return LieAlgebra< F, m | struct : Rep := Rep, Check := Check >;
end intrinsic;

intrinsic HeisenbergAlgebra(J::AlgMatElt : Rep := "Sparse", Check := false) -> AlgLie
{The Heisenberg (Lie) algebra defined by the alternating form with matrix J}
    require J eq -Transpose(J) : "form is not alternating";
    m := Nrows(J);
    T := [ <i,j,m+1,J[i,j]> : i,j in [1..m] | J[i,j] ne 0 ];
    return LieAlgebra< BaseRing(J), m+1 | T : Rep := Rep, Check := Check >;
end intrinsic;


