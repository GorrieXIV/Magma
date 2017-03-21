freeze;


////////////////////////////////////////////////////////////////////
//
//  Basic functionality for modules and representations
//
//  Scott H. Murray
//  (Using a lot of code by Willem de Graaf)
//
////////////////////////////////////////////////////////////////////


// =================================================================
//
// Converting between modules and representations
//

intrinsic Module( rho::Map[AlgLie,AlgMatLie] : LeftAction:=false ) -> ModAlg
{The module of the representation rho}
  L := Domain( rho );
  V := RModule( BaseRing( L ), Degree(Codomain(rho)) );
  return LeftAction select
    Module( L, hom< CartesianProduct(L,V)->V | x:->Matrix(rho(x[1]))*x[2] > )
    else
    Module( L, hom< CartesianProduct(V,L)->V | x:->x[1]*Matrix(rho(x[2])) > );
end intrinsic; 



// =================================================================
//
// Adjoint modules/representations
//
// should we store these.
// need to assign weights for Adjoint modules
// implement for matrix lie algebras
//

intrinsic AdjointModule( L::AlgLie : LeftAction:=false ) -> ModAlg
{The adjoint module of L}
  V := RModule( BaseRing(L), Dimension(L) );
  if LeftAction then
    act := hom< CartesianProduct( L, V ) -> V | 
      x :-> V!Eltseq( x[1] * L!Eltseq(x[2]) ) >;
  else
    act := hom< CartesianProduct( V, L ) -> V | 
      x :-> V!Eltseq( L!Eltseq(x[1]) * x[2] ) >;
  end if;
  return Module( L, act );
end intrinsic;

intrinsic AdjointRepresentation( L::AlgLie : LeftAction := false, ComputePreImage := true) -> Map
{The adjoint representation of L}
  M := MatrixLieAlgebra( BaseRing(L), Dimension(L) );
  if LeftAction then
	ad := map< L -> M | x :-> AdjointMatrix(L,x) >;
  else
    ad := map< L -> M | x :-> RightAdjointMatrix(L, x) >;
  end if;
  ad`IsInjective := true;
  if assigned L`StandardBasis then
    V := Module( L );  R := RootDatum( L );  N := NumPosRoots( R );
    ad`Weights := [ Root( R, r ) : r in [N..1 by -1] ] cat 
      [ RootSpace( R )!0 ] cat 
      [ Root( R, r ) : r in [N+1..2*N] ];
    pos, neg, cart := StandardBasis( L );
    ad`WeightSpaces := [ sub< V | pos[r] > : r in [N..1 by -1] ] cat
      [ sub< V | [ V!c : c in cart ] > ] cat 
      [ sub< V | neg[r] > : r in [1..N] ];
    ad`HighestWeights := [ (ad`Weights)[1] ];
    ad`HighestWeightSpaces := [ (ad`WeightSpaces)[1] ];
  end if;
  if ComputePreImage then ComputePreImageRule(ad); end if;
  return ad;
end intrinsic;

// =================================================================
//
// Standard modules/representations
//
// should we store these.
// need to assign weights for Adjoint modules
//

// =================================================================
//
// Highest weight modules/representations
//
// should we store these.
// need to assign weights for Adjoint modules
//

