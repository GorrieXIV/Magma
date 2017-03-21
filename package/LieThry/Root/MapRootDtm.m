freeze;

/*
**  Maps between Root data
** 
**  $Id: MapRootDtm.m 45412 2013-12-03 04:45:18Z don $
** 
** 
**  Scott H Murray
** 
**  February 2006
** 
** 
*/

import "../GrpLie/GrpLie.m" : Unip_ToList, Unip_Normalise,
  WeylActionOnTorus, Torus_Product, copyelt, collectionOrder,
  Torus_Identity, Torus_Term_Rt, Weyl_Normalise, PosToNegFilter;
import "../Repn/Repn.m" : kummerExtension;

RF := recformat< 
  // Required fields
  type : MonStgElt,          // Types implemented so far:
  			     //   "Morphism" : injective morphism
			     //   "Dual" : dual injective morphism
			     //   "Fractional" : injective fractional morphism
			     //   "DualFractional"
			     // Types to implement
			     //   "p-morphism", "folding"
  map_rt : Mtrx,             // the matrix given the action on X
  map_co : Mtrx,             // the matrix given the action on Y
  inj : SeqEnum,             // (co)root index images
  
  // Optional fields
  signs : SeqEnum            // the signs of the morphism
>;


// ====================================================================
//
// Constructing morphisms
//

//  The matrices must be defined over the rationals
function check_matrices(R1,R2,map_rt,map_co : Check := true )
  X1 := RootSpace( R1 );  Y1 := CorootSpace( R1 );
  
  if Nrows(map_rt) ne Dimension(R1) 
  or Ncols(map_co) ne Dimension(R2) then
    return false;
  end if;
    
  if Check then
    return forall{ <x,y> : x in Basis(X1), y in Basis(Y1) 
                         | (x,y) eq (x*map_rt,y*map_co) };
  end if;
  
  return true;
end function;

isIntVect := func< v | forall{ a : a in Eltseq(v) | a in Integers() } >;

// NOTE: The SimpleSigns parameter is never provided by any calling 
// function.  DET 2013-12-03
morphismSigns := function( a : SimpleSigns:=1 )
  if not assigned a`data`signs then  
    R1 := Domain( a );  R2 := Codomain( a );
    inj := a`data`inj;
    n1 := Rank( R1 );  N1 := NumPosRoots( R1 );
    if Category( SimpleSigns ) eq RngIntElt then
      SimpleSigns := [ SimpleSigns : i in [1..2*n1] ];
    end if;
 
    signs := [];
    for r in [1..n1] do
      signs[r] := SimpleSigns[r];
      signs[r+N1] := SimpleSigns[r];
    end for;
    for r in [n1+1..N1] do
      s, t := ExtraspecialPair( R1, r );
      signs[r] := signs[s] * signs[t] *
    	LieConstant_epsilon( R1, s, t ) *
    	LieConstant_epsilon( R2, inj[s], inj[t] );
      signs[r+N1] := signs[s+N1] * signs[t+N1] *
    	LieConstant_epsilon( R1, s+N1, t+N1 ) *
    	LieConstant_epsilon( R2, inj[s+N1], inj[t+N1] );
    end for;
    a`data`signs := signs;
  end if;
  
  return a`data`signs;
end function;

// this function takes a list of integers or a permutation
constructMorphismIms := function( R1, R2, inj : Check:=false );
  // first, check input
  if ExtendedCategory(inj) ne SeqEnum[RngIntElt] and
     Category(inj) ne GrpPermElt then
    return "Invalid right hand side";
  end if;
  // then check root data 
  if not IsSplit(R1) or not IsSplit(R2) then
    return "Root data must be split";
  end if;
  if not IsSemisimple( R1 ) then
    return "R1 must be semisimple";
  end if;

  if Category(inj) eq GrpPermElt then
    inj := Eltseq(inj);
  end if;

  k := BaseRing( R1 );
  X1 := RootSpace( R1 );  Y1 := CorootSpace( R1 );

  n := Rank( R1 );
  F := BaseRing( R1 );
  map_rt := SimpleRoots( R1 )^-1 *
    Matrix( [ Root( R2, inj[r] ) : r in [1..n] ] );
  map_co := SimpleCoroots( R1 )^-1 *
    Matrix( [ Coroot( R2, inj[r] ) : r in [1..n] ] );

  if not check_matrices(R1,R2,map_rt,map_co : Check := Check ) then
    return "The given maps do not define a morphism of root data";
  end if;
  N1 := NumPosRoots(R1);  N2 := NumPosRoots(R2);
  inj :=   [ RootPosition( R2, Root(R1,r)*map_rt ) : r in [1..N1] ];
  if Check then
    coinj := [ CorootPosition( R2, Coroot(R1,r)*map_co ) : r in [1..N1] ];
    if 0 in inj or coinj ne inj then
      return "The given maps do not send roots to roots";
    end if;
  end if;
  
  neg := func< r | (r le N2) select r+N2 else r-N2 >;
  for r in [1..N1] do
    inj[r+N1] := neg(inj[r]);
  end for;

  // Create a "blank" map
  f := UserMapCreateRaw("MapRootDtm", R1, R2);

  integral := CanChangeUniverse( Eltseq(map_rt) cat Eltseq(map_co), Integers() );

  // attach the data
  f`data := rec< RF | 
    type   := integral select "Morphism" else "Fractional",
    map_rt := map_rt, 
    map_co := map_co, 
    inj    := inj>;

  return f;
end function;

// this function takes two matrices or two linear maps
constructMorphismMxs := function( R1, R2, mx1, mx2 : Check := true )
  if not IsSplit(R1) or not IsSplit(R2) then
    return "Root data must be split";
  end if;
  
  k := BaseRing( R1 );
  X1 := RootSpace( R1 );  Y1 := CorootSpace( R1 );
  
  if ISA( Category( mx1 ), Mtrx ) then
    map_rt := ChangeRing( mx1, k );
  elif Category( mx1 ) eq Map then
    map_rt := Matrix( [ mx1(b) : b in Basis(RootSpace(R1)) ] );
  else
    return "Invalid right hand side";
  end if;

  if ISA( Category( mx2 ), Mtrx ) then
    map_co := ChangeRing( mx2, k );
  elif Category( mx2 ) eq Map then
    map_co := Matrix( [ mx2(b) : b in Basis(CorootSpace(R1)) ] );
  else
    return "Invalid right hand side";
  end if;

  if not check_matrices(R1,R2,map_rt,map_co : Check := Check ) then
    return "The given maps do not define a morphism of root data";
  end if;
  N1 := NumPosRoots(R1);  N2 := NumPosRoots(R2);
  inj :=   [ RootPosition( R2, Root(R1,r)*map_rt ) : r in [1..N1] ];
  if Check then
    coinj := [ CorootPosition( R2, Coroot(R1,r)*map_co ) : r in [1..N1] ];
    if 0 in inj or coinj ne inj then
      return "The given maps do not send roots to roots";
    end if;
  end if;
  
  neg := func< r | (r le N2) select r+N2 else r-N2 >;
  for r in [1..N1] do
    inj[r+N1] := neg(inj[r]);
  end for;

  // Create a "blank" map
  f := UserMapCreateRaw("MapRootDtm", R1, R2);

  integral := CanChangeUniverse( Eltseq(map_rt) cat Eltseq(map_co), Integers() );

  // attach the data
  f`data := rec< RF | 
    type:= integral select "Morphism" else "Fractional",
    map_rt := map_rt, 
    map_co := map_co, 
    inj:= inj>;

  return f;
end function;

intrinsic HackobjHomConstrRootDtm(R1::RootDtm, R2::RootDtm, RHS::. : Check:=true ) 
  -> Map
{Internal}
//
// this function is called when a 
//      hom<R1->R2|RHS : Check >
// is called. 
// note that the default for Check is FALSE and can't be changed here.
//
// MUST NOT USE require/error. use
//      return "error message";
// in case of an error.
  return constructMorphismIms( R1, R2, RHS : Check:=Check );
end intrinsic;

intrinsic HackobjHomConstrRootDtmSprs(R1::RootDtmSprs, R2::RootDtmSprs, RHS::. : Check:=true ) 
  -> Map
{Internal}
  return constructMorphismIms( R1,R2,RHS : Check:=Check );
end intrinsic;

intrinsic HackobjHomConstrRootDtm(R1::RootDtm, R2::RootDtm, RHS1::., RHS2::. : Check:=true ) 
  -> Map
{Internal}
//
// this function is called when a 
//      hom<R1->R2|RHS1, RHS2 : Check >
// is called. 
// note that the default for Check is FALSE and can't be changed here.
//
// MUST NOT USE require/error. use
//      return "error message";
// in case of an error.
  return constructMorphismMxs( R1,R2,RHS1,RHS2 : Check:=Check );
end intrinsic;

intrinsic Morphism( R1::RootDtm, R2::RootDtm, rtmap::Mtrx, comap::Mtrx : 
  Check:=true ) -> Map
{The morphism from R1 to R2 defined by rtmap and comap}
  require Parent(rtmap) eq Parent(comap) :
    "The matrices are not of the same type";
  return constructMorphismMxs( R1, R2, rtmap, comap : Check:=Check );
end intrinsic;

intrinsic Morphism( R1::RootDtm, R2::RootDtm, rtmap::Map, comap::Map : 
  Check:=true ) -> Map
{The morphism from R1 to R2 defined by rtmap and comap}
  return constructMorphismMxs( R1, R2, rtmap, comap : Check:=Check );
end intrinsic;

intrinsic Morphism( R1::RootDtm, R2::RootDtm, inj::[RngIntElt] : 
  Check:=true ) -> Map
{The morphism from R1 to R2 defined by injection inj}
  return constructMorphismIms( R1, R2, inj : Check:=Check );
end intrinsic;


intrinsic DualMorphism( R1::RootDtm, R2::RootDtm, rtmap::Mtrx, comap::Mtrx : 
  Check:=true ) -> Map
{The dual morphism from R1 to R2 defined by rtmap and comap}

  require Parent(rtmap) eq Parent(comap) :
    "The matrices are not of the same type";

  k := BaseRing( R1 );
  X1 := RootSpace( R1 );  Y1 := CorootSpace( R1 );

  map_rt := ChangeRing( rtmap, k );
  map_co := ChangeRing( comap, k );

  if Check then
    require forall{ <x,y> : x in Basis(X1), y in Basis(Y1) |
      (x,y) eq (y*map_co,x*map_rt) } :
      "The given maps do not preserve the pairing";
    isIntvect := func< v | forall{ a : a in Eltseq(v) | a in Integers() } >;
  end if;

  N1 := NumPosRoots(R1);  N2 := NumPosRoots(R2);
  inj :=   [ CorootPosition( R2, Root(R1,r)*map_rt ) : r in [1..N1] ];
  if Check then
    coinj := [ RootPosition( R2, Coroot(R1,r)*map_co ) : r in [1..N1] ];
    require 0 notin inj and coinj eq inj :
      "The given maps do not send roots to coroots";
  end if;
  
  neg := func< r | (r le N2) select r+N2 else r-N2 >;
  for r in [1..N1] do
    inj[r+N1] := neg(inj[r]);
  end for;

  // Create a "blank" map
  f := UserMapCreateRaw("MapRootDtm", R1, R2);

  integral := CanChangeUniverse( Eltseq(map_rt) cat Eltseq(map_co), Integers() );

  // attach the data
  f`data := rec< RF | 
    type := integral select "Dual" else "DualFractional",
    map_rt := map_rt, 
    map_co := map_co, 
    inj:= inj>;

  return f;
end intrinsic;

intrinsic DualMorphism( R1::RootDtm, R2::RootDtm, rtmap::Map, comap::Map : 
  Check:=true ) -> Map
{The dual morphism from R1 to R2 defined by rtmap and comap}
  map_rt := Matrix( [ rtmap(b) : b in Basis(RootSpace(R1)) ] );
  map_co := Matrix( [ comap(b) : b in Basis(CorootSpace(R1)) ] );

  return DualMorphism( R1, R2, map_rt, map_co : Check:=Check );
end intrinsic;

intrinsic DualMorphism( R1::RootDtm, R2::RootDtm, inj::[RngIntElt] : 
  Check:=true ) -> Map
{The dual morphism from R1 to R2 defined by injection inj}

  require IsSemisimple( R1 ) : "R1 must be semisimple";
  n := Rank( R1 );
  map_rt := SimpleRoots( R1 )^-1 *
    Matrix( [ Root( R2, inj[r] ) : r in [1..n] ] );
  map_co := SimpleCoroots( R1 )^-1 *
    Matrix( [ Coroot( R2, inj[r] ) : r in [1..n] ] );

  return DualMorphism( R1, R2, map_rt, map_co : Check:=Check );
end intrinsic;

intrinsic RootImages( h::Map[RootDtm,RootDtm] ) -> []
{Images of the roots under h}
  return h`data`inj;
end intrinsic;

intrinsic RootPermutation( h::Map[RootDtm,RootDtm] ) -> GrpPermElt
{Images of the roots under h}
  R := Domain( h );
  require h in Aut( R ) : "Not an automorphism";
  if Rank(R) eq 0 then  return Sym(1)!1;  end if;
  return Sym(2*NumPosRoots(R))!h`data`inj;
end intrinsic;


intrinsic UserMapImageMapRootDtm(f::Map, x::.) -> BoolElt, .
{Internal}
// MUST NOT USE require/error here
//
// If successful:  return true, the-result [which must be in the domain]
//          else:  return false, error-message-string
//
// If no image allowable, make the body of the function be:
//         return false, "Illegal coercion";
//

  R1 := Domain( f );  R2 := Codomain( f );
  case f`data`type :
  when "Morphism", "Fractional" :
    case Category(x) :
    when ModTupFldElt :
      V := Parent(x);
      if not (assigned V`RootDatum and V`RootDatum eq Domain(f)) then
   	return false, "Not in the domain";
      elif IsInRootSpace(x) then
   	return true, RootSpace(R2)!(x*(f`data`map_rt));
      elif IsInCorootSpace(x) then
   	return true, CorootSpace(R2)!(x*(f`data`map_co));
      end if;
    when RootDtm :
      if not x subset R1 then return false, "Not a subdatum of the domain"; end if;
      return true, sub< R2 |  RootSpace(R1)*(f`data`map_rt), 
                            CorootSpace(R1)*(f`data`map_co) >;
    end case;

  when "Dual","DualFractional" :
    case Category(x) :
    when ModTupFldElt :
      V := Parent(x);
      if not (assigned V`RootDatum and V`RootDatum eq Domain(f)) then
   	return false, "Not in the domain";
      end if;
      if IsInRootSpace(x) then
   	return true, CorootSpace(R2)!(x*(f`data`map_rt));
      elif IsInCorootSpace(x) then
   	return true, RootSpace(R2)!(x*(f`data`map_co));
      end if;
    when RootDtm :
      if not x subset R1 then return false, "Not a subdatum of the domain"; end if;
      return true, sub< R2 | CorootSpace(R1)*(f`data`map_co), 
                               RootSpace(R1)*(f`data`map_rt) >;
    end case;
  end case;
 
  return false, "Illegal coercion"; 
end intrinsic;


intrinsic UserMapPreimageMapRootDtm(f::Map, x::.) -> BoolElt, .
{Internal}
// (Function)
// Attempt to compute the preimage y of x under map f.  x can be anything
// so suitable checks as to whether (x)@@f is meaningful should be done
//
// MUST NOT USE require/error here
//
// If successful:  return true, the-result [which must be in the domain]
//          else:  return false, error-message-string
//
// If no image allowable, make the body of the function be:
//         return false, "Illegal coercion";


    return false, "not yet implemented";   
end intrinsic;



/*
 * intrinsic UserMapPrintMapRootDtm(f::Map, level::MonStgElt)
 * {Internal}
 * // (Procedure)
 * // Print x at given level (string; test for equality with "Maximal", etc.)
 * // 
 * // 
 * //  use the default for now
 * // 
 * // 
 * end intrinsic;
 */

// Are these definitions correct???
intrinsic IsInjective( a::Map[RootDtm,RootDtm] ) -> BoolElt
{True iff a is an injective map}
  return Rank( a`data`map_rt ) eq Dimension( Domain(a) );
end intrinsic;

intrinsic IsSurjective( a::Map[RootDtm,RootDtm] ) -> BoolElt
{True iff a is a surjective map}
  return Rank( a`data`map_rt ) eq Dimension( Codomain(a) );
end intrinsic;

intrinsic LieAlgebraHomomorphism( a::Map[RootDtm,RootDtm], k::Rng ) -> Map
{The homomorphism of Lie algebras over k induced by a}
  require a`data`type in {"Morphism","Fractional"} :
    "Not a (fractional) morphism";
  deg := Lcm( [ Denominator(x) : x in Eltseq( a`data`map_co ) ] );
  require a`data`type eq "Morphism" or IsUnit( deg ) :
    "The given fractional morphism cannot be realised over the given ring";

  R1 := Domain( a );  R2 := Codomain( a );
  L1 := LieAlgebra( R1, k );
  L2 := (R1 eq R2) select L1 else LieAlgebra( R2, k );
  d1 := Dimension( R1 );  n1 := Rank( R1 );  N1 := NumPosRoots( R1 );
  n2 := Rank( R2 );
  inj := a`data`inj;
  signs := morphismSigns( a );
  
  pos1, neg1, cart1 := StandardBasis( L1 );
  pos2, neg2, cart2 := StandardBasis( L2 );

  rts := [ Eltseq(v) : v in Roots( R1 : Basis:="Root" ) ];
  rtelts1 := pos1 cat neg1;
  rtelts2 := pos2 cat neg2;  
  rteltims := [ signs[r] * rtelts2[inj[r]] : r in [1..2*N1] ];

  cartims := a`data`map_co;
  cartims := [ &+[ cartims[i,j]*cart2[j] : j in [1..n2] ] : i in [1..n1] ];
  
  M := Matrix( rtelts1 cat cart1 )^-1 * Matrix( rteltims cat cartims );
  return iso< L1->L2 | M : Check:=false >, M;
end intrinsic;

intrinsic GroupOfLieTypeHomomorphism( a::Map[RootDtm,RootDtm], k::Rng ) -> Map
{The homomorphism of groups of Lie type over k induced by a}
  require a`data`type in {"Morphism","Fractional"} :
    "Not a (fractional) morphism";
  deg := Lcm( [ Denominator(x) : x in Eltseq( a`data`map_co ) ] );
  if deg eq 1 then
    K := k; rad := func<x | x>;
  else
    K, rad := kummerExtension( k, deg );
  end if;

  R1 := Domain( a );  R2 := Codomain( a );
  G1 := GroupOfLieType( R1, k );
  G2 := (R1 eq R2 and deg eq 1) select G1 else GroupOfLieType( R2, K );
  n1 := Rank( R1 );  d1 := Dimension( R1 );  N1 := NumPosRoots( R1 );
  n2 := Rank( R2 );  N2 := NumPosRoots( R2 );
  W1 := CoxeterGroup( R1 );  W2 := CoxeterGroup( R2 );
  inj := a`data`inj;
  signs := morphismSigns( a );
  A := a`data`map_co;
  simple := forall{ i : i in [1..n1] | inj[i] in [1..n2] };

  ToTorus := function( term )
    return Vector( [ &*[ rad(term[i]^(Integers()!(A[i,j]*deg))) : 
      i in [1..Nrows(A)] ] : j in [1..Ncols(A)] ] );
  end function;
  ToUnipTerm := function( term )
    r := term[1];
    return < inj[r], K!signs[r]*term[2] >;
  end function;
  ToUnipList := function( term )
    return [ ToUnipTerm( term[i] ) : i in [1..#term] ];
  end function;
  ToUnipNorm := function( term )
    return ToUnipList( Unip_ToList( W1, k, term, collectionOrder(G1) ) );
  end function;
  ToWeylTerm := function( term )
    return inj[term];
  end function;
  ToWeyl := function( term ) 
    t := Torus_Identity( R2, k );
    for i in [#term..1 by -1] do  //t;
      WeylActionOnTorus( R2, k, ~t, [inj[term[i]]] : left );
      t := Torus_Product( R2, k, t, 
        Torus_Term_Rt( R2, k, inj[term[i]], signs[term[i]] ) ); 
      term[i] := ToWeylTerm( term[i] );
    end for;
    return t, term;
  end function;
  
  ToNormalised := function( term )  
    ret := CreateLieGroupElement(G2);
    ret`u := ToUnipNorm( term`u );
    ret`h := ToTorus( term`h );
    h, ret`w := ToWeyl( term`w );  
    ret`h := Torus_Product( R2, K, ret`h, h );
    ret`up := ToUnipNorm( term`up );
    if simple then
      Weyl_Normalise( R2, K, ~ret`w );
      ret`filter := PosToNegFilter( R2, WordToPerm( W2, ret`w ) );
      ret`u := Unip_Normalise( G2, ret`u );
      ret`up := Unip_Normalise( G2, ret`up );
      return ret;
    else
      // this normalises the Weyl terms
      new := elt< G2 | ret`u, ret`h >;
      for r in ret`w do  new *:= elt< G2 | r >;  end for;
      new *:= elt< G2 | ret`up >;
      return new;
    end if;
  end function;

  f := function( x )
    if IsNormalised( x ) then
      return ToNormalised( x );
    else
      ret := CreateLieGroupElement(G2);
      list := Eltlist(x);
      i := 1;
      while i le #list do
        if Category(list[i]) eq ModTupFldElt then
          list[i] := ToTorus( list[i] );
        elif Category(list[i]) eq Tup and #list[i] eq 2 then
          list[i] := ToUnipTerm( list[i] );
        elif Category(list[i]) eq SeqEnum and
        not IsNull(list[i]) and Category(Universe(list[i])) eq SetCart then
          list[i] := ToUnipList( list[i] );
        elif Category(list[i]) eq SeqEnum and not IsNull(list[i]) then
          list[i] := ToUnipNorm( list[i] );
        elif Category(list[i]) eq RngIntElt then
          Insert( ~list, i, Torus_Term_Rt( W2, k, inj[list[i]], signs[list[i]] ) );
          i +:= 1;
          list[i] := ToWeylTerm( list[i] );
        elif Category(list[i]) eq GrpLieElt then
          list[i] := ToNormalised( list[i] );
        end if;
        i +:= 1;
      end while;
      ret`List := list;
      return ret;
    end if;
  end function;
  return hom< G1 -> G2 | x :-> f(x) >;
end intrinsic;



  

// ================================================================
//
// Duality maps
//
// ================================================================
/*
computeDualIndexImages := function( phi )
  R1 := phi`Domain;  R2 := phi`Codomain; 
  phiX := phi`Root;  phiY := phi`Coroot;
  V := VectorSpace( FieldOfFractions( BaseRing(R2) ), Dimension(R2) );
  N := NumPosRoots( R1 );  M := NumPosRoots( R2 );
  idx :=   [ CorootPosition( R2, (V!Root(R1,r))*phiX )     : r in [1..N] ];
  coidx := [ RootPosition( R2, (V!Coroot(R1,r))*phiY ) : r in [1..N] ];
  neg := func< r | (r le M) select r+M else r-M >;
  for r in [1..N] do
    idx[r+N] := neg(idx[r]);  coidx[r+N] := neg(coidx[r]);
  end for;
  return 0 notin idx and idx eq coidx, idx;
end function;    

intrinsic RootSystemDualHomomorphism( R1::RootDtm, R2::RootDtm,
            phiX::ModMatRngElt, phiY::ModMatRngElt ) -> Rec
{Construct the root datum dual homomorphism with the given maps}
  require Dimension(R1) eq Nrows(phiX) : "phiX has the wrong number of rows";
  require Dimension(R1) eq Nrows(phiY) : "phiY has the wrong number of rows";
  require Dimension(R2) eq Ncols(phiX) : "phiX has the wrong number of columns";
  require Dimension(R2) eq Ncols(phiX) : "phiX has the wrong number of columns";
  phi := rec< RootDtmMapFormat | Domain := R1, Codomain := R2, 
              Root := phiX, Coroot := phiY, Kind := "dual homomorphism" >;
  good, idx := computeDualIndexImages( phi );
  if good then
    phi`Index := idx;
    return phi;
  else
    error "Not a valid dual homomorphism";
  end if;
end intrinsic;

intrinsic RootSystemDualHomomorphism( R1::RootDtm, R2::RootDtm, idx::[RngIntElt] ) -> Rec
{Construct the root datum dualhomomorphism with the given simple index images}
  require IsSemisimple( R1 ) : "R1 must be semisimple";
  n := Rank( R1 );
  F := FieldOfFractions( BaseRing( R1 ) );
  V := VectorSpace( F, Dimension(R2) );
  A := ChangeRing( SimpleRoots( R1 ), F );
  phiX := Matrix( A )^-1 *
          Matrix( [ V | Coroot( R2, idx[r] ) : r in [1..n] ] );
  B := ChangeRing( SimpleCoroots( R1 ), F );
  phiY := Matrix( B )^-1 *
          Matrix( [ V | Root( R2, idx[r] ) : r in [1..n] ] );
  phi := rec< RootDtmMapFormat | Domain := R1, Codomain := R2, 
              Root := phiX, Coroot := phiY, Kind := "dual homomorphism" >;
  good, newidx := computeDualIndexImages( phi );
  if good and idx eq newidx[[1..#idx]] then
    phi`Index := newidx;
    return phi;
  else
    error "Not a valid homomorphism";
  end if;
end intrinsic;

*/

// ================================================================
//
// Standard maps
//
// ================================================================
intrinsic IdentityMap( R::RootDtm ) -> Map
{The identity map from R to R}
  id := IdentityMatrix( Rationals(), Dimension(R) );
  return hom< R -> R | id, id >;
end intrinsic;


intrinsic IdentityMorphism( R::RootDtm ) -> Map
{The trivial automorphism of R}
  id := IdentityMatrix( Rationals(), Dimension(R) );
  return hom< R -> R | [id,id] >;
end intrinsic;

intrinsic IdentityAutomorphism( R::RootDtm ) -> Map
{The trivial automorphism of R}
  id := IdentityMatrix( Rationals(), Dimension(R) );
  return hom< R -> R | [id,id] >;
end intrinsic;


