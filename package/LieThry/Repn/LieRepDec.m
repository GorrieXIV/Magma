freeze;

import "RootDatumDan.m":myComponents;

intrinsic InternalLieRepDecROK(R::RootDtm) -> BoolElt
{Internal. Check whether root datum R is compatible with LieRepDec code}

	corts := SimpleCoroots(R);
	if Nrows(corts) eq Ncols(corts) and IsIdentity(corts) then return true; end if;
	
	//Check that myComponents can handle it, and that all components are identity matrices.
	try
		comps := myComponents( R : IncludeToralPart := false );
		i := 0; for comp in comps do
			c := comp[2];
			subrws := [i+1..i+#c]; 
			subcls := c; 
			if not IsIdentity(Submatrix(corts, subrws, subcls)) then 
				vprintf LieRepDec, 1 : "LieRepDecROK: component of R (%o) does not have the identity matrix for its coroots.\n", comp[1];
				return false; 
			end if;
			i +:= #c;
		end for;
		return true;
	catch err
		vprintf LieRepDec, 1 : "Problem in LieRepDecROK: \n%o\n", err;
		return false;
	end try;
end intrinsic;


intrinsic LieRepresentationDecomposition(N::MonStgElt, v::Any) -> LieRepDec
{ The decomposition of the irreducible representation with highest weight v.}
	R := RootDatum(N : Isogeny := "SC");
	return LieRepresentationDecomposition(R, v);
end intrinsic;

intrinsic LieRepresentationDecomposition(N::MonStgElt) -> LieRepDec
{ The decomposition of the trivial representation}
	R := RootDatum(N : Isogeny := "SC");
	print R;
	return LieRepresentationDecomposition(R);
end intrinsic;

intrinsic TrivialLieRepresentationDecomposition(N::MonStgElt) -> LieRepDec
{ The decomposition of the trivial representation}
	R := RootDatum(N : Isogeny := "SC");
	print R;
	return LieRepresentationDecomposition(R);
end intrinsic;

intrinsic LieRepresentationDecomposition(N::MonStgElt, Wt::SeqEnum, Mp::SeqEnum) -> LieRepDec
{The decomposition of the representation which decomposes into the direct
 sum of the irreducible representations with highest weights in Wt, where
 the representation with highest weight Wt[i] occurs Mp[i] times.}
	R := RootDatum(N : Isogeny := "SC");
	return LieRepresentationDecomposition(R, Wt, Mp);
end intrinsic;



// Synonyms

intrinsic TensorProduct(D::LieRepDec, E::LieRepDec : Goal:= false) -> LieRepDec
{Tensor product of Lie representation decompositions D and E}
  return Tensor(D,E:Goal:=Goal);
end intrinsic;

intrinsic TensorProduct(R::RootDtm, v::ModTupRngElt, w::ModTupRngElt : Goal:= false) -> LieRepDec
{Tensor product of Lie representations with highest weights v and w}
  return Tensor(R,v,w:Goal:=Goal);
end intrinsic;

intrinsic TensorProduct(Q::[LieRepDec] : Goal:= false) -> LieRepDec
{Tensor product of Lie representations decompositions in Q}
  T := Q[1];
  for i in [2..#Q] do
    T := TensorProduct(T,Q[i]);
  end for;
  return T;
end intrinsic;

intrinsic Weights( V::ModAlg ) -> SeqEnum, SeqEnum
{Weights and corresponding vectors of a module over a split semisimple 
Lie algebra or quantum group}
  return WeightsAndVectors(V);
end intrinsic;

intrinsic HighestWeights( V::ModAlg ) -> SeqEnum, SeqEnum
{Highest weights and corresponding vectors of a module over a split semisimple 
Lie algebra or quantum group}
  return HighestWeightsAndVectors(V);
end intrinsic;

intrinsic HighestWeightsAndVectors( rho::Map[AlgLie, AlgMat] ) -> SeqEnum, SeqEnum
{Highest weights and corresponding vectors of a module over a split semisimple 
Lie algebra or quantum group}
  return HighestWeights(rho);
end intrinsic;


/* 
//Overwritten by WeightsAndVectors in Repn.m, so useless here.
intrinsic WeightsAndVectors( rho::Map[GrpLie, GrpMat] ) -> SeqEnum, SeqEnum
{Weights and corresponding vectors of a module over a split semisimple 
Lie algebra or quantum group}
  return Weights(rho);
end intrinsic;
*/

intrinsic HighestWeightsAndVectors( rho::Map[GrpLie, GrpMat] ) -> SeqEnum,
SeqEnum
{Highest weights and corresponding vectors of a module over a split semisimple 
Lie algebra or quantum group}
  return HighestWeights(rho);
end intrinsic;



intrinsic CharacterMultiset( V::ModAlg ) -> LieRepDec
{Weight character of a module over a split semisimple 
Lie algebra or quantum group}
   wts := Weights( V );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Algebra(V)), wts, mls );
end intrinsic;

intrinsic CharacterMultiset( rho::Map[GrpLie,GrpMat] ) -> LieRepDec
{Weight character of a representation of a split semisimple 
Lie algebra or quantum group}
   wts := Weights( rho );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Codomain(rho)), wts, mls );
end intrinsic;

intrinsic CharacterMultiset( rho::Map[AlgLie,AlgMat] ) -> LieRepDec
{Weight character of a representation of a group of Lie type}
   wts := Weights( rho );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Codomain(rho)), wts, mls );
end intrinsic;



intrinsic DecompositionMultiset( V::ModAlg ) -> LieRepDec
{Weight decomposition of a module over a split semisimple 
Lie algebra or quantum group}
   wts := HighestWeights( V );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Algebra(V)), wts, mls );
end intrinsic;

intrinsic DecompositionMultiset( rho::Map[GrpLie,GrpMat] ) -> LieRepDec
{Weight decomposition of a representation of a split semisimple 
Lie algebra or quantum group}
   wts := HighestWeights( rho );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Codomain(rho)), wts, mls );
end intrinsic;

intrinsic DecompositionMultiset( rho::Map[AlgLie,AlgMat] ) -> LieRepDec
{Weight decomposition of a representation of a group of Lie type}
   wts := HighestWeights( rho );
   wts := IndexedSetToSequence( {@ wt : wt in wts @} );
   mls := [ #[w : w in wts | w eq wt ] : wt in wts ];
   return LieRepresentationDecomposition( RootDatum(Codomain(rho)), wts, mls );
end intrinsic;


