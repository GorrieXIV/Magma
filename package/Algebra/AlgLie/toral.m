freeze;

/*
   toral.m
   
   Intrinsics involving toral subalgebras.
   
   Scott H. Murray

   Dan Roozemond, 2010, code for small char (see also stsa*.m)
*/

declare attributes AlgLie : SplitMaximalToralSubalgebra;

intrinsic IsToralSubalgebra( L::AlgLie, H::AlgLie ) -> BoolElt
{True iff L is a toral Lie algebra}
  return IsAbelian( H ) and 
    forall{ b : b in Basis(H) | IsSemisimple( L!b ) };
end intrinsic;

// How should this be defined for infinite fields?
intrinsic IsSplitToralSubalgebra( L::AlgLie, H::AlgLie ) -> BoolElt
{True iff H is a toral subalgebra of L}
  k := BaseRing( L );  e := Degree( k );
  require ISA( Category(k), FldFin ) : 
    "The Lie algebra must be defined over a finite field";
  ok, pmap := IsRestrictable( L );
  require ok : "The Lie algebra must be restrictable";
  qmap := pmap^e;
  
  return IsToralSubalgebra( L, H ) and 
    forall{ b : b in Basis(H) | qmap(L!b) eq L!b };
end intrinsic;

/*
MTSRecurse := function( L )
  repeat
    repeat
      x := Random( L );
    until IsSemisimple( x );
    M := Centraliser( L, x );
    M2 := pSubalgebra( { L!b : b in Basis(M) } );
  until M eq M2;
  if IsAbelian( M ) then
    return M;
  else
    return $$(M);
  end if;
end function;

// this may fail is L is not classical
intrinsic MaximalToralSubalgebra( L::AlgLie ) -> BoolElt
{A maximal toral subalgebra of L}

  k := BaseRing( L );
  require ISA( Category(k), FldFin ) : 
    "The Lie algebra must be defined over a finite field";
  ok, pmap := IsRestrictable( L );
  require ok : "The Lie algebra must be restrictable";

  return MTSRecurse( L );
end intrinsic;
*/


// this function returns the centraliser of a random regular ss element
// MAKE RECURSIVE???
MTS := function( L )
  repeat
    repeat
      x := Random( L );
    until IsSemisimple( x );
    C := pClosure( L, Centraliser( L, x ) );
  until IsAbelian( C );
  return C;
end function;


// ===============================================================
//
//  Split maximal toral subalgebra
//
// ===============================================================

SMTSrecurse := function( L, k )

  // Base cases: abelian and A1
  Lp := L*L;
  case Dimension( Lp ) :
  when 0 :
    H := Lp;
 
  when 3 :
    repeat 
      H := MTS( Lp );
    until IsSplitToralSubalgebra( Lp, H );
 
  else
    split := false;
    repeat
      H := MTS( Lp );
      if IsSplitToralSubalgebra( Lp, H ) then  
        split := true;
      else
        rvs, rts := RationalRootDecomposition( Lp, H );
      end if;
    until split or exists(M){ M : i in [1..#rts] | 
      (Max([Degree(r):r in rts[i]]) eq 2 and M*M eq M) 
      where M is pClosure(Lp,sub< Lp | Seqset(rvs[i]) >^2) };
  
    if not split then
      Hf := $$( M, k );              //Hf := SMTSrecurse( M, k );
      Cf := pClosure( Lp, Centraliser( Lp, Hf ) );
      H := $$( Cf, k );              //H := SMTSrecurse( Cf, k );
    end if;
  
  end case;
  
  H := pClosure( L, H + Centre(L) );
//  assert IsSplitToralSubalgebra( L, H );
  return H;

end function;


intrinsic SplitMaximalToralSubalgebra( L::AlgLie ) -> AlgLie
{A split maximal toral subalgebra of L}
	/* Cached? */
	if assigned L`SplitMaximalToralSubalgebra then
		return L`SplitMaximalToralSubalgebra;
	end if;

	k := BaseRing( L );
	require ISA( Category(k), FldFin ) : "Not defined over a finite field";
	require Characteristic(k) gt 3 : "Characteristic of base field should be greater than 3";
	require IsRestrictable( L ) and IsReductive( L ) : "Not a restrictable reductive Lie algebra";

	H := SMTSrecurse( L, k );
	L`SplitMaximalToralSubalgebra := H;
	return H;
end intrinsic;


/*intrinsic IsSplitPLieAlgebra( L::AlgLie, pmap::Map[AlgLie,AlgLie] ) -> BoolElt
{True iff L is a split p-Lie algebra for the given p map}
  //?????
  return false;
end intrinsic;*/


// May not work for non-classical algebras
