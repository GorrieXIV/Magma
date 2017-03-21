
freeze;

//
//  Abelian algebras
//
//  Constructing abelian Lie algebras.
//


//////////////////////////////////////////////////////////////////////////////
intrinsic AbelianLieAlgebra( k::Rng, n::RngIntElt : Rep:="Sparse" ) -> AlgLie
{The abelian Lie algebra of dimension n over k}

    Z := Integers();
    return LieAlgebra< k, n | [car<Z,Z,Z,k>|] : Rep:=Rep >;

end intrinsic;



//////////////////////////////////////////////////////////////////////////////
intrinsic IsAbelian( L::AlgLie ) -> BoolElt
{Test whether the Lie algebra L is abelian}

  d := Dimension( L );
  return forall{ <i,j> : j in [i+1..d], i in [1..d] | L.i * L.j eq L!0 };

end intrinsic;






