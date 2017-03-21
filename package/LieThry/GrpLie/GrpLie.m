freeze;

/*
  $Id: GrpLie.m 49776 2015-02-09 12:00:39Z don $

  Scott Murray, Sergei Haller. 

  Magma code for computing in finite groups of Lie type, with elements 
  represented by their bruhat decomposition:
    $$uh\dot{w}u'$$
  where $u = \bigprod_{r\in\Phi^+} x_r(\la_r)$, $h\in T\iso Y\tens k^\times$,
  $w\in W$ and $u' = \bigprod_{r\in\Phi^+, wr\in\Phi^-} x_r(\la_r)$.
  Elements are multiplied using the commutator relations.
  See either of R.W. Carter's books for more details.

  This top-level magma code is intended as a first step towards
  writing C code for the magma kernel.

  We make extensive use of the Coxeter group implementation of Don
  Taylor.
  
*/

import "../Root/Const.m":       multiplicationData, cartanInteger, maxMultiplicity;
import "../Root/RootDtm.m":     computeOrbitReps, existsCoveringStructure;
import "../GrpCox/GrpCox.m":      reflMat;

import "../Root/Const.m":       lie_eta;
import "../Root/RootDtmSprs.m": lie_eta_sprs;

declare verbose VerboseGrpLie,  1; // verbosity level; not yet used
declare verbose SHdebugGrpLie,  2; // debug output used by SH

// ===================================================================
//
//  Lie type groups
//
//  Functions for multiplying elements of the Lie type group,
//  written as Bruhat decompositions.
//
//  Elements of a lie type group can be represented in two ways:
//    as a record with fields u, h, w, up and filter; or
//    as a List consisting of the above, together with torus elements,
//      Weyl elements,
//
// ===================================================================

declare attributes GrpLie :
  IsFinite, Order, Method, collectionOrder,
  SeparateHallPolynomials;

declare attributes RootDtm:
  InverseHallPolynomials,      HallPolynomials,
  InverseHallPolynomialsPapi,  HallPolynomialsPapi;

forward allHallPolynomials;
import "../Root/RootDtmSprs.m": hallPolysSprs;

defaultMethod := "Default";

      hallMethods_M := [ "MSymbolicFromLeft",   "MSymbolicFromOutside",   "SymbolicClassical"    ];
    directMethods_M := [ "MCollectionFromLeft", "MCollectionFromOutside", "Classical"            ];

      hallMethods_C := [ "SymbolicToLeft",     "SymbolicFromLeft",    "SymbolicFromOutside"   ];
    directMethods_C := [ "CollectionToLeft",   "CollectionFromLeft",  "CollectionFromOutside" ];

      hallMethods   := /*   hallMethods_M cat */   hallMethods_C cat [ "SymbolicClassical" ];
    directMethods   := /* directMethods_M cat */ directMethods_C cat [         "Classical" ];

      leftMethods_M := [ "MCollectionFromLeft",    "MSymbolicFromLeft"    ];
  additiveMethods_M := [ "MCollectionFromOutside", "MSymbolicFromOutside" ];

      leftMethods_C := [ "CollectionFromLeft",     "SymbolicFromLeft"     ];
     rightMethods_C := [ "CollectionToLeft",       "SymbolicToLeft"       ];
  additiveMethods_C := [ "CollectionFromOutside",  "SymbolicFromOutside"  ];

 classicalMethods   := [ "Classical",              "SymbolicClassical"    ];

      leftMethods   := /*     leftMethods_M cat */     leftMethods_C cat     rightMethods_C;
  additiveMethods   := /* additiveMethods_M cat */ additiveMethods_C cat   classicalMethods;


choose_method := procedure(G, Method);
    K := BaseRing(G);
    R := RootDatum(G);
  
    // have some restrictions on SymbolicClassical
    if Method in classicalMethods then
        if Category(R) eq RootDtmSprs 
        and Seqset(R`ExtraspecialSigns) eq {-1}
        then
            G`Method := Method;
        else
            error "Classical methods are only available for sparse root data with signs -1";
        end if;
    
    // if the user specified a method, use it.
    elif Method in hallMethods cat directMethods then
        G`Method := Method;

    // default Symbolic metod is SymbolicFromOutside
    elif Method eq "Symbolic" then
        if Category(R) eq RootDtmSprs 
        and Seqset(R`ExtraspecialSigns) eq {-1}
        then
            G`Method := "SymbolicClassical";
        else
            G`Method := "SymbolicFromOutside";
        end if;

    // default Collection method is CollectionFromOutside
    elif Method eq "Collection" then
        if Category(R) eq RootDtmSprs 
        and Seqset(R`ExtraspecialSigns) eq {-1}
        then
            G`Method := "Classical";
        else
            G`Method := "CollectionFromOutside";
        end if;

    // now the method must be "Default"
    elif Method ne "Default" then
        error "Invalid Method parameter";

    // for sparse root data use SymbolicClassical where implemented and SymbolicFromOutside otherwise
    elif Category(R) eq RootDtmSprs then    
        if Seqset(R`ExtraspecialSigns) eq {-1} then
            if ISA(Type(K),FldFunRat) then            //
                G`Method := "SymbolicClassical";      // Classical is faster than SymbolicClassical
            else                                      // unless the field is very bad (e.g. FldFunRat)
                G`Method := "Classical";              // 
            end if;                                   //
        else
            G`Method := "SymbolicFromOutside";
        end if;

    // Apparently, the new collection code is much faster than evaluation
    // of Hall polys. Use CollectionFromOutside by defaut!
    else
        G`Method := "CollectionFromOutside";

    end if;
end procedure;

computeHalls := procedure( ~G  )
  if   G`Method in directMethods then
    return;
  elif G`Method in hallMethods then
    vtime SHdebugGrpLie : _ := allHallPolynomials( G );
    // _ := separateHallPolynomials( G );
  else
    // we actually should never get here!!!
    error "Invalid Method parameter";
  end if;
end procedure;

/* this is the only intrinsic that really does the work     */
/* all others call this one eventually                      */
intrinsic GroupOfLieType( R::RootDtm, k::Rng : 
Normalising := true, Method := defaultMethod ) -> GrpLie
{The group of Lie type with root datum R over the ring k}
  require IsReduced(R) : "Root datum must be reduced";
  require not IsTwisted(R) : "Root datum is twisted. Use TwistedGroupOfLieType.";
  G := CreateLieGroup(R, k, Normalising);
  if Category(R) eq RootDtmSprs then 
    if Method[1..2] in {"CC","CH"} then 
        Method := Method[2..#Method];
        printf "Note: Method changed from C%o to %o\n", Method, Method;
    end if;
  end if;
  choose_method(G, Method);
  computeHalls( ~G );
  n := Rank(R);
  // precompute coreflection matrices for simple roots.
  // this is essential for multiplication
  for i in [1..n] do _:=reflMat(R,i,"Standard",true); end for;
  return G;
end intrinsic;
intrinsic GroupOfLieType( R::RootDtm, q::RngIntElt : Normalising := true, 
Method := defaultMethod ) -> GrpLie
{The group of Lie type with root datum R over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( R, GF(q) : Normalising:=Normalising,Method:=Method );
end intrinsic;

intrinsic GroupOfLieType( W::GrpPermCox, k::Rng : 
        Normalising := true, 
        Method := defaultMethod ) -> GrpLie
{The group of Lie type with Weyl group W over the ring k}
  return GroupOfLieType( RootDatum(W), k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic GroupOfLieType( W::GrpPermCox, q::RngIntElt : Normalising := true, 
Method := defaultMethod ) -> GrpLie
{The group of Lie type with Weyl group W over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( RootDatum(W), GF(q) : Normalising:=Normalising,Method:=Method );
end intrinsic;

intrinsic GroupOfLieType( W::GrpMat, k::Rng : 
        Normalising := true, 
        Method := defaultMethod ) -> GrpLie
{The group of Lie type with Weyl group W over the ring k}
  return GroupOfLieType( RootDatum(W), k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic GroupOfLieType( W::GrpMat, q::RngIntElt : Normalising := true, 
Method := defaultMethod ) -> GrpLie
{The group of Lie type with Weyl group W over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( RootDatum(W), GF(q) : Normalising:=Normalising,Method:=Method );
end intrinsic;

intrinsic GroupOfLieType( C::AlgMatElt, k::Rng : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Cartan matrix C over the ring k}
  R := RootDatum( C : Isogeny:=Isogeny, Signs:=Signs );
  return GroupOfLieType( R, k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic GroupOfLieType( C::AlgMatElt, q::RngIntElt : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Cartan matrix C over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( C, GF(q) : Isogeny:=Isogeny,Normalising:=Normalising,Method:=Method,Signs:=Signs );
end intrinsic;

intrinsic GroupOfLieType( D::GrphDir, k::Rng : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Dynkin digraph D over the ring k}
  R := RootDatum( D : Isogeny:=Isogeny, Signs:=Signs );
  return GroupOfLieType( R, k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic GroupOfLieType( D::GrphDir, q::RngIntElt : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Dynkin digraph D over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( D, GF(q) : Isogeny:=Isogeny,Normalising:=Normalising,Method:=Method,Signs:=Signs );
end intrinsic;

intrinsic GroupOfLieType( N::MonStgElt, k::Rng : Isogeny := "Ad", 
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Cartan name N over the ring k}
  R := RootDatum( N : Isogeny:=Isogeny, Signs:=Signs );
  return GroupOfLieType( R, k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic GroupOfLieType( N::MonStgElt, q::RngIntElt : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The group of Lie type with Cartan name N over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return GroupOfLieType( N, GF(q) : Isogeny:=Isogeny,Normalising:=Normalising,Method:=Method,Signs:=Signs );
end intrinsic;

intrinsic GroupOfLieType( L::AlgLie : 
Normalising := true, Method := defaultMethod ) -> GrpLie
{The group of Lie type with Lie algebra L}
  G := GroupOfLieType( RootDatum(L), BaseRing(L) : 
    Normalising:=Normalising,Method:=Method );
  G`LieAlgebra := L;
  return G;   
end intrinsic;


intrinsic SimpleGroupOfLieType( X::MonStgElt, n::RngIntElt, k::Rng : Isogeny := "Ad", 
Normalising := true, Method := defaultMethod, Signs:=1 ) -> GrpLie
{The simple group of Lie type with Cartan name X_n over the ring k}
  R := IrreducibleRootDatum( X, n : Isogeny:=Isogeny, Signs:=Signs );
  return GroupOfLieType( R, k : Normalising:=Normalising,Method:=Method );
end intrinsic;
intrinsic SimpleGroupOfLieType( X::MonStgElt, n::RngIntElt, q::RngIntElt : Isogeny := "Ad",
Normalising := true, Method := defaultMethod, Signs := 1 ) -> GrpLie
{The simple group of Lie type with Cartan name N over the field of order q}
  require (q ge 2) and IsPrimePower(q) : "q should be a prime power greater than or equal to 2.";
  return SimpleGroupOfLieType( X, n, GF(q) : Isogeny:=Isogeny,Normalising:=Normalising,Method:=Method,Signs:=Signs );
end intrinsic;

intrinsic IsNormalising( G::GrpLie ) -> BoolElt
{True iff G automatically normalises elements}
  return G`Normalise;
end intrinsic;

/*
 *  SH: dropped. This way we can have GroupOfLieType return the same OBJECT 
 *      when called with the same attributes.
 * 
 * intrinsic SetNormalising( ~G::GrpLie, Normalising::BoolElt )
 * {Set the Normalising flag}
 *   G`Normalise := Normalising;
 * end intrinsic;
 * 
 */

// -------------------------------------------------------------------
//
//  Order
//
intrinsic Order( G::GrpLie ) -> .
{The order of G}
  k := DefRing( G );
  require ISA( Category( k ), Fld ) : "Only implemented for groups over fields";
  if ISA( Category( k ), FldFin ) then
    G`Order := GroupOfLieTypeOrder( RootDatum( G ), #k );
    G`IsFinite := true;
    return G`Order;
  else
    G`IsFinite := false;
    return Infinity();
  end if;
end intrinsic;

intrinsic FactoredOrder( G::GrpLie ) -> .
{The factored order of G}
  k := BaseRing( G );
  require ISA( Category( k ), Fld ) : "Only implemented for groups over fields";
  if IsFinite( k ) then
    G`Order := GroupOfLieTypeFactoredOrder( RootDatum( G ), #k );
    G`IsFinite := true;
    return G`Order;
  else
    G`IsFinite := false;
    return Infinity();
  end if;
end intrinsic;

intrinsic '#'( G::GrpLie ) -> .
{The order of G}
  return Order( G );
end intrinsic;


intrinsic IsFinite( G::GrpLie ) -> BoolElt, RngIntElt
{True and the order of G if G is finite, otherwise false.}
     
  if IsFinite(BaseRing(G)) then
    return true, Order(G);
  else
    return false, _;
  end if;

end intrinsic;

// -------------------------------------------------------------------
//
//  Dimension
//
intrinsic Dimension( G::GrpLie ) -> RngIntElt
{The dimension of G}
  return Rank(G) + 2*NumPosRoots(G);
end intrinsic;

// -------------------------------------------------------------------
//
//  abelian or not
//

intrinsic IsAbelian( G::GrpLie ) -> BoolElt
{True iff semisimple rank of G is 0.}
     /* 
     **   the non-simple cases are
     **       A_1(2)=Sym(3), A_1(3)=Alt(4), B_2(2)=Sym(6), G_2(2)=PSU_3(9),
     **   all of which are non-abelian.
     */
     return SemisimpleRank(G) eq 0;
end intrinsic;

// -------------------------------------------------------------------
//
//  Order of elements
//
intrinsic Order( x::GrpLieElt ) -> .
{The order of x}
  G := Parent( x );
  k := BaseRing( G );
  require ISA( Category( k ), FldFin ) : "Only implemented for groups over finite fields";

  y := Normalise(x);

  if y eq G!1 then
      o := 1;
  elif #Eltlist(y) eq 1 
   and Category(Eltlist(y)[1]) eq ModTupFldElt then
     // torus element
     h := y`h;
     o := LCM( [ Order(a) : a in Eltseq(h) ] );
  elif Seqset(y`u)  eq {0} 
   and Seqset(y`up) eq {0} then
     // in the normaliser of the torus
     W := WeylGroup(G);
     w := &*[W| W.i : i in y`w]; // Weyl elt corresponding to y.
     
     o := Order(w) * Order(y^Order(w));
  else
     error "Only implemented for elements of N";
  end if;
  
  assert y^o eq 1;

  return o;

end intrinsic;


// -------------------------------------------------------------------
//
//  Access and printing
//

intrinsic WeylGroup( G::GrpLie ) -> GrpPermCox
{The Weyl group of G}
  return CoxeterGroup( RootDatum(G) );
end intrinsic;


intrinsic WeylGroup( `GrpFPCox, G::GrpLie ) -> GrpFPCox
{The Weyl group of G as a finitely presented group}
  return CoxeterGroup( GrpFPCox, RootDatum( G ) );
end intrinsic;

intrinsic WeylGroup( `GrpPermCox, G::GrpLie ) -> GrpPermCox
{The Weyl group of G as a permutation group}
  return WeylGroup( G );
end intrinsic;

intrinsic WeylGroup( `GrpMat, G::GrpLie ) -> GrpMat
{The Weyl group of G as a matrix group}
  return CoxeterGroup( GrpMat, RootDatum( G ) );
end intrinsic;


intrinsic BaseRing( g::GrpLieElt ) -> Rng
{The base ring of g}
  return BaseRing(Parent(g));
end intrinsic;

intrinsic Rank( G::GrpLie ) -> RngIntElt
{The reductive rank of G}
  return Dimension( RootDatum(G) );
end intrinsic;

intrinsic ReductiveRank( G::GrpLie ) -> RngIntElt
{The reductive rank of G}
  return Dimension( RootDatum(G) );
end intrinsic;

intrinsic SemisimpleRank( G::GrpLie ) -> RngIntElt
{The semisimple rank of G}
  return Rank( RootDatum(G) );
end intrinsic;

intrinsic CartanMatrix( G::GrpLie ) -> AlgMatElt
{The Cartan matrix of G}
  return CartanMatrix( RootDatum(G) );
end intrinsic;

intrinsic CartanName( G::GrpLie ) -> MonStgElt
{The Cartan name of G}
  return CartanName( RootDatum(G) );
end intrinsic;

intrinsic CoxeterMatrix( G::GrpLie ) -> AlgMatElt
{The Coxeter matrix of G}
  return CoxeterMatrix( RootDatum(G) );
end intrinsic;

intrinsic CoxeterGraph( G::GrpLie ) -> GrphUnd
{The Coxeter graph of G}
  return CoxeterGraph( RootDatum(G) );
end intrinsic;

intrinsic DynkinDigraph( G::GrpLie ) -> GrphDir
{The Dynkin digraph of G}
  return DynkinDigraph( RootDatum(G) );
end intrinsic;

intrinsic DynkinDiagram( G::GrpLie )
{Print the Dynkin diagram of G}
  DynkinDiagram( RootDatum(G) );
end intrinsic;

intrinsic CoxeterDiagram( G::GrpLie )
{Print the Coxeter diagram of G}
  CoxeterDiagram( RootDatum(G) );
end intrinsic;

intrinsic FundamentalGroup( G::GrpLie ) -> GrpAb
{The fundamental group of G}
  return FundamentalGroup( RootDatum(G) );
end intrinsic;

intrinsic IsogenyGroup( G::GrpLie ) -> GrpAb
{The isogeny group of G}
  return IsogenyGroup( RootDatum(G) );
end intrinsic;

intrinsic CoisogenyGroup( G::GrpLie ) -> GrpAb
{The coisogeny group of G}
  return CoisogenyGroup( RootDatum(G) );
end intrinsic;

intrinsic RootSpace( G::GrpLie ) -> GrpAb
{The root space of G}
  return RootSpace( RootDatum(G));
end intrinsic;

intrinsic CorootSpace( G::GrpLie ) -> GrpAb
{The coroot space of G}
  return CorootSpace( RootDatum(G) );
end intrinsic;

intrinsic SimpleRoots( G::GrpLie ) -> GrpAb
{The simple roots of G}
  return SimpleRoots( RootDatum(G) );
end intrinsic;

intrinsic SimpleCoroots( G::GrpLie ) -> GrpAb
{The simple coroots of G}
  return SimpleCoroots( RootDatum(G) );
end intrinsic;

intrinsic NumberOfPositiveRoots( G::GrpLie ) -> RngIntElt
{The number of positive roots of G}
  return NumPosRoots( RootDatum(G) );
end intrinsic;

intrinsic NumPosRoots( G::GrpLie ) -> RngIntElt
{The number of positive roots of G}
  return NumPosRoots( RootDatum(G) );
end intrinsic;

intrinsic Roots( G::GrpLie : Basis := "Standard" ) -> {@@}
{The roots of G}
  return Roots( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic Coroots( G::GrpLie : Basis := "Standard" ) -> {@@}
{The coroots of G}
  return Coroots( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic PositiveRoots( G::GrpLie : Basis := "Standard" ) -> {@@}
{The positive roots of G}
  return PositiveRoots( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic PositiveCoroots( G::GrpLie : Basis := "Standard" ) -> {@@}
{The positive coroots of G}
  return PositiveCoroots( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic Root( G::GrpLie, r::RngIntElt : Basis := "Standard" ) -> .
{The rth root of G}
  return Root( RootDatum(G), r : Basis := Basis );
end intrinsic;

intrinsic Coroot( G::GrpLie, r::RngIntElt : Basis := "Standard" ) -> .
{The rth coroot of G}
  return Coroot( RootDatum(G), r : Basis := Basis );
end intrinsic;

intrinsic RootPosition( G::GrpLie, v : Basis := "Standard" ) -> RngIntElt
{The position of v as a root of G}
  return RootPosition( RootDatum(G), v : Basis := Basis );
end intrinsic;

intrinsic CorootPosition( G::GrpLie, v : Basis := "Standard" ) -> RngIntElt
{The position of v as a coroot of G}
  return CorootPosition( RootDatum(G), v : Basis := Basis );
end intrinsic;


intrinsic HighestRoot( G::GrpLie : Basis := "Standard" ) -> LatElt
{The highest root of G}
  return HighestRoot( RootDatum(G) : Basis:=Basis );
end intrinsic;

intrinsic HighestLongRoot( G::GrpLie : Basis := "Standard" ) -> LatElt
{The highest long root of G}
  return HighestRoot( RootDatum(G) : Basis:=Basis );
end intrinsic;

intrinsic HighestShortRoot( G::GrpLie : Basis := "Standard" ) -> LatElt
{The highest short root of G}
  return HighestShortRoot( RootDatum(G) : Basis:=Basis );
end intrinsic;


intrinsic RootHeight( G::GrpLie, r::RngIntElt  ) -> RngIntElt
{The height of the rth root of G}
  return RootHeight( RootDatum(G), r );
end intrinsic;

intrinsic CorootHeight( G::GrpLie, r::RngIntElt  ) -> RngIntElt
{The height of the rth coroot of G}
  return CorootHeight( RootDatum(G), r );
end intrinsic;

intrinsic RootNorms( G::GrpLie ) -> RngIntElt
{The squares of the root lengths of G}
  return RootNorms( RootDatum(G) );
end intrinsic;

intrinsic CorootNorms( G::GrpLie ) -> RngIntElt
{The squares of the coroot lengths of G}
  return CorootNorms( RootDatum(G) );
end intrinsic;

intrinsic RootNorm( G::GrpLie, r::RngIntElt ) -> RngIntElt
{The square of the length of the rth root of G}
  return RootNorm( RootDatum(G), r );
end intrinsic;

intrinsic CorootNorm( G::GrpLie, r::RngIntElt ) -> RngIntElt
{The square of the length of the rth root of G}
  return CorootNorm( RootDatum(G), r );
end intrinsic;

intrinsic IsLongRoot( G::GrpLie, r::RngIntElt ) -> BoolElt
{True iff the rth root of G is long}
  return IsLongRoot( RootDatum(G), r );
end intrinsic;

intrinsic IsShortRoot( G::GrpLie, r::RngIntElt ) -> BoolElt
{True iff the rth root of G is short}
  return IsShortRoot( RootDatum(G), r );
end intrinsic;

intrinsic AdditiveOrder( G::GrpLie ) -> BoolElt
{The additive order on the positive roots of G}
  return AdditiveOrder( RootDatum(G) );
end intrinsic;


import "../Root/RootDtmSprs.m": collectionOrderSprs;

// return the order used for collection
function collectionOrder( G )
    if not assigned G`collectionOrder then 
        R := RootDatum(G);
        if G`Method in leftMethods then
            G`collectionOrder := [1..NumPosRoots(R)];
        elif G`Method in additiveMethods then

            if Category(R) eq RootDtmSprs then
                G`collectionOrder := collectionOrderSprs(R);
            else
                G`collectionOrder := AdditiveOrder(R);
            end if;
        else
            error "Wrong Method for multiplication in G";
        end if;
    end if;
    return G`collectionOrder;
end function;

function posOrder( order )
    n := #order;
    order := {@ o : o in order @};
    assert #order eq n;
    return [Position(order,i):i in [1..n]];
end function;

intrinsic WeightLattice( G::GrpLie ) -> Lat
{The weight lattice of G}
  return WeightLattice( RootDatum(G) );
end intrinsic;

intrinsic CoweightLattice( G::GrpLie ) -> Lat
{The coweight lattice of G}
  return CoweightLattice( RootDatum(G) );
end intrinsic;

intrinsic FundamentalWeights( G::GrpLie : Basis := "Standard" ) -> AlgMatElt
{The fundamental weights of G}
  return FundamentalWeights( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic FundamentalCoweights( G::GrpLie : Basis := "Standard" ) -> AlgMatElt
{The fundamental weights of G}
  return FundamentalCoweights( RootDatum(G) : Basis := Basis );
end intrinsic;

intrinsic DominantWeight( G::GrpLie, v : Basis := "Standard" ) -> ModTupFldElt, GrpFPCoxElt
{The dominant weight of G in the orbit of the weight v}
  return DominantWeight( RootDatum(G), v : Basis := Basis );
end intrinsic;

intrinsic IsSimple( G::GrpLie ) -> BoolElt
{True iff G is irreducible}
  return IsIrreducible( RootDatum(G) );
end intrinsic;

intrinsic IsSemisimple( G::GrpLie ) -> BoolElt
{True iff G is semisimple}
  return IsSemisimple( RootDatum(G) );
end intrinsic;

intrinsic IsSimplyLaced( G::GrpLie ) -> BoolElt
{True iff G is simply laced}
  return IsSimplyLaced( RootDatum(G) );
end intrinsic;

intrinsic IsWeaklyAdjoint( G::GrpLie ) -> BoolElt
{True iff G is (weakly) adjoint}
  return IsWeaklyAdjoint( RootDatum(G) );
end intrinsic;

intrinsic IsWeaklySimplyConnected( G::GrpLie ) -> BoolElt
{True iff G is (weakly) simply connected}
  return IsWeaklySimplyConnected( RootDatum(G) );
end intrinsic;

intrinsic IsAdjoint( G::GrpLie ) -> BoolElt
{True iff G is adjoint (implies semisimplicity of the root datum).}
  return IsAdjoint( RootDatum(G) );
end intrinsic;

intrinsic IsSimplyConnected( G::GrpLie ) -> BoolElt
{True iff G is simply connected (implies semisimplicity of the root datum).}
  return IsSimplyConnected( RootDatum(G) );
end intrinsic;

intrinsic IsSplit( G::GrpLie ) -> BoolElt
{True iff G is twisted}
  return IsSplit( RootDatum(G) );
end intrinsic;



intrinsic LieAlgebra( G::GrpLie ) -> AlgLie, Map
{The Lie algebra of G}
  return LieAlgebra( RootDatum(G), BaseRing(G) ), AdjointRepresentation( G );
end intrinsic;


// -------------------------------------------------------------------
//
//  Equality, isogeny and isomorphism
//

intrinsic 'eq'( G::GrpLie, H::GrpLie ) -> BoolElt
{True iff G and H are identical}
  return RootDatum(G)                eq RootDatum(H)
     and Category      (BaseRing(G)) eq Category      (BaseRing(H)) 
     and Characteristic(BaseRing(G)) eq Characteristic(BaseRing(H)) 
     and                BaseRing(G)  eq                BaseRing(H);
end intrinsic;

intrinsic IsIsogenous( G::GrpLie, H::GrpLie ) -> BoolElt
{True iff G and H are isogenous}
  require (Category(BaseRing(G)) eq Category(BaseRing(G))) and 
    (Characteristic(BaseRing(G)) eq Characteristic(BaseRing(H))) and 
    (BaseRing(G) eq BaseRing(H)) : "The groups must have the same base field";
  require IsSemisimple(G) and IsSemisimple(H) :
    "The groups must be semisimple";
  ok, _, ad, ad1, ad2, sc, sc1, sc2 := IsIsogenous( RootDatum(G), RootDatum(H) );
  if ok then
    k := BaseRing(G);
    return ok, GroupOfLieType(ad,k), GroupOfLieTypeHomomorphism(ad1,k),
      GroupOfLieTypeHomomorphism(ad2,k),
      GroupOfLieType(sc,k), GroupOfLieTypeHomomorphism(sc1,k),
      GroupOfLieTypeHomomorphism(sc2,k);
  else
    return ok, _,_,_, _,_,_;
  end if;
end intrinsic;

intrinsic IsCartanEquivalent( G::GrpLie, H::GrpLie ) -> BoolElt
{True iff G and H are Cartan equivalent}
  return IsCartanEquivalent( RootDatum(G), RootDatum(H) ) 
     and Category(BaseRing(G)) eq Category(BaseRing(H)) 
     and Characteristic(BaseRing(G)) eq Characteristic(BaseRing(H)) 
     and BaseRing(G) eq BaseRing(H);
end intrinsic;

intrinsic IsAlgebraicallyIsomorphic( G::GrpLie, H::GrpLie ) -> BoolElt
{True iff G and H are isomorphic as algebraic groups}
  if (Category(BaseRing(G)) eq Category(BaseRing(H))) and 
  (Characteristic(BaseRing(G)) eq Characteristic(BaseRing(H))) and 
  (BaseRing(G) eq BaseRing(H)) then
    ok, _, h := IsIsomorphic( RootDatum(G), RootDatum(H) );
    if ok then
      return true, GroupOfLieTypeHomomorphism( h, BaseRing(G) );
    end if;
  end if;   
  return false, _; 
end intrinsic;


intrinsic PrintGrpLie( G::GrpLie, level::MonStgElt, name::MonStgElt )
{Internal.  Printing the group of Lie type G}
    //
    // Possible Print levels: "Minimal", "Default", "Maximal", "Debug", "Magma"
    //
    
    R := RootDatum(G);
    K := BaseRing(G);
    k := DefRing(G);

    is_torus   := NumPosRoots(R) eq 0;
    is_twisted := IsTwisted(G);
    
    if level eq "Magma" then 
        if is_twisted then 
            "FIXME: not correct for twisted groupe";
        end if;
        printf "GroupOfLieType( %o, %o )",
          Sprint( R, "Magma" ),
          Sprint( k, "Magma" );
    else
        type := is_torus   select "Torus group" else 
                is_twisted select "Twisted group of Lie type"
                             else "Group of Lie type";
        if name ne "$" then
            printf "%o: ", name;
        end if;
        if level eq "Minimal" then
            printf "%o", type;
            return;
        else
            if is_torus then
                printf "%o of Dimension %o ", type, Rank(R);
            else
                printf "%o %o", type, TwistedCartanName(R);
            end if;
            printf "over %o", Sprint( k, "Minimal" ); // level 
            if is_twisted then
                printf " with entries over %o", Sprint( K, "Minimal" ); // level 
            end if;
            
            if level eq "Maximal" and not is_torus then
                printf "\nwith isogeny group %o",
                  Sprint( IsogenyGroup(R), "Minimal" ); // level 
            end if;
        end if;
    end if;
end intrinsic;


// ===================================================================
//
//  The unipotent radical
//
//  Methods for multiplying elements of the unipotent radical,
//  ie. elements $u = \bigprod_{r\in\Phi^+} x_r(\la_r)$.
//  This product can be ordered any way that is compatible with the
//  height function.  We use the order of the roots given in the
//  coxeter group, which means that a unipotent element can be
//  represented as an array specifying a field element for each
//  root.  While putting elements into this normal form, we will also
//  represent them as arrays of pairs giving the root's index and a
//  field element.
//  
//  as we now also using additive order, that is, roots are not ordered
//  sith respect to height, but in a way that the sum of any two roots
//  sits between them (if the sum is a root at all).
//
//  we still use a sequence of field elements to represent a normalised
//  unipotent element: e.g.  [10,20,30] corresponds to
//    x1(10) x2(20) x3(30)  if the standard ordering is used and
//    x1(10) x3(30) x2(20)  if the additive ordering [1,3,2] is used.
//
//  if we use pairs, then everything is independant of the used order:
//    x1(10) x2(20) x3(30)   is  [ <1,10>, <2,20>, <3,30> ]
//    x1(10) x3(30) x2(20)   is  [ <1,10>, <3,30>, <2,20> ]
//
// ===================================================================

// -------------------------------------------------------------------
//
// Basic functions
//
// 

// SH: checked
// returns true if x is represented as a sequence of field elements
Unip_IsNormalised := function( x )
  return not ( IsNull( x ) or Category( Universe( x ) ) eq SetCart );
end function;

// SH: checked
Unip_Identity := function( R, k : normalised := true )
  if normalised then
    return [ k | 0 : i in [1..NumPosRoots(R)] ];
  else
    return [];
  end if;
end function;

// SH: checked
Unip_IsOne := function( R, k, x )
  if Unip_IsNormalised( x ) then
    return forall(t){ t : t in x | IsZero(t) };
  else
    return #x eq 0;
  end if;
end function;

// SH: checked
Unip_ToList := function(R, k, elt, order)
  if Unip_IsOne( R, k, elt ) then
    elt := [ CartesianProduct( Integers(), k ) | ];
  elif not Unip_IsNormalised( elt ) then
    ;
  else
    elt := [ CartesianProduct( Integers(), k ) | < i, elt[i] > : i in order | elt[i] ne 0 ];
  end if;
  return elt;
end function;

// SH: checked
Unip_Random := function( R, k, order: normalised := true, 
filter := [true: i in [1..NumPosRoots(R)]] )
  elt := Unip_Identity(R, k);
  for i in [1..NumPosRoots(R)] do
    if filter[i] then elt[i] := Random(k); end if;
  end for;
  if normalised then 
    return elt;
  else
    return Unip_ToList(R, k, elt, order); 
  end if;
end function;

// SH: checked
Unip_Print := procedure( R, k, elt, order )
  PrintTerm := procedure( r, al )
    printf "x%o(%o) ", r, al;
  end procedure;
  // switch to list representation first, taking care of the order
  elt := Unip_ToList(R,k,elt,order);

  // now print
  if #elt eq 0 then
    printf "1"; 
  else
    for term in elt do
      PrintTerm( term[1], term[2] );
    end for;
  end if;

end procedure;

// SH: checked
Unip_Term := function( R, k, r, al )
  return < r, k!al >;
end function;



// -------------------------------------------------------------------
//
// Collection
//
//  These functions deal with sequences of pairs only
//

// returns the commutator
Unip_Comm_ORIG := function( R, u1, u2 )
    r := u1[1]; s := u2[1];
    a := u1[2]; b := u2[2];

    mul := multiplicationData(R, r, s);
    return 
        [ < t, c * a^i * b^j > where i := d[1] where j := d[2]
                               where t := d[3] where c := d[4] : d in mul ] ;
end function;

// that one is faster. 
Unip_Comm := function( R, u1, u2 )
    return [ < d[3], z > : d in multiplicationData(R, u1[1],u2[1]) 
                         | z ne 0 where z is d[4] * u1[2]^d[1] * u2[2]^d[2] ] ;
end function;

//  Code for reordering the terms in a unipotent element.
//  There are two ways we want to do this:
//    Standard order, and
//    U_w^+ then U_w^-.
//  For the second kind we use a filter giving all the 
//  roots in U_w^+.

//  returns a filter for all the positive roots that become
//  negative under the action of w.
PosToNegFilter := function( R, w )
  if Category(w) eq SeqEnum then
    w := WordToPerm(CoxeterGroup(R), Reverse(w));
  else
    w := w^(-1);
  end if;
  N := NumPosRoots(R);
  return [ Booleans() | i^w gt N : i in [1..N] ];
end function;


/*
 * COLLECTION FROM LEFT: 
 *   we collect from left.
 *
 *   elements are exchanged by the rule
 *       x*y -> y*x*[x,y]
 */
Unip_CollectListFromLeft_Std := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);
    // now use neworder[r1] le neworder[r2] to check if root r1 is le root r2.


// Sprintf("----->%o",from);
// order, filter, neworder;
// list;
//    orig := list;

    if #list eq 0 then return [], []; end if;
    if #list eq 1 then
        if filter[list[1][1]] then return list, [];
        else return [], list;
        end if;
    end if;

    k := 2;
    while k le #list do
        // the next condition is just a "less or equal", where "less" is a special one.
        if neworder[list[k][1]] le neworder[list[k-1][1]] then
            j  := k;
            // apparently, the HIGH number of computations "j-1" slows the whole thing 
            // down :) so we just compute it once.
            j1 := j-1;
            repeat
                if list[j][1] eq list[j1][1] then
                    list[j1][2] +:= list[j][2];
                    Remove(~list, j);
                    if list[j1][2] eq 0 then
                        Remove(~list, j1);
                        j   := j1;
                        j1 -:= 1;
                        k  -:= 1;
                    end if;
                    k -:= 1;
                else        // x*y = y*x*[x,y]
                    comm := Unip_Comm( R, list[j1], list[j] ); // [x,y]
                    tmp      := list[j]; 
                    list[j]  := list[j1]; 
                    list[j1] := tmp;
                    if 0 lt #comm then 
                        Insert(~list,j+1,j,comm);
                        k := j; // + #comm; // check if that works for B,C,F,G
                                // this already doesn't work in A if filter is not true everywhere
                    end if;
                end if;
                j   := j1;
                j1 -:= 1;
            until j le 1 or neworder[list[j1][1]] lt neworder[list[j][1]] ;
        end if;
        k +:= 1;k := Max(k,2);
    end while;
    
    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];

//  cpu := Cputime()-cpu;
//  cpu;
//  if cpu gt 0.1 then
//      error "debug";
//  end if;

//    Sprintf("%o, %o\n", ret1,ret2);

    return ret1,ret2;
end function;

/*
 * COLLECTION FROM LEFT for PAPI: 
 *   we collect from left.
 *
 *   elements are exchanged by the rule
 *       x*y -> y*[y,x^-1]*x
 */
Unip_CollectListFromLeft_Papi := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);
    // now use neworder[r1] le neworder[r2] to check if root r1 is le root r2.


// Sprintf("----->%o",from);
// order, filter, neworder;
// list;
//    orig := list;

    if #list eq 0 then return [], []; end if;
    if #list eq 1 then
        if filter[list[1][1]] then return list, [];
        else return [], list;
        end if;
    end if;

    k := 2;
    while k le #list do
        // the next condition is just a "less or equal", where "less" is a special one.
        if neworder[list[k][1]] le neworder[list[k-1][1]] then
            j  := k;
            // apparently, the HIGH number of computations "j-1" slows the whole thing 
            // down :) so we just compute it once.
            j1 := j-1;
            repeat
                if list[j][1] eq list[j1][1] then
                    list[j1][2] +:= list[j][2];
                    Remove(~list, j);
                    if list[j1][2] eq 0 then
                        Remove(~list, j1);
                        j   := j1;
                        j1 -:= 1;
                        k  -:= 1;
                    end if;
                    k -:= 1;
                else         // x*y = y*[y,x^-1]*x
                    comm := Unip_Comm( R, list[j], <list[j1][1],-list[j1][2]> );
                    tmp      := list[j]; 
                    list[j]  := list[j1]; 
                    list[j1] := tmp;
                    if 0 lt #comm then 
                        Insert(~list,j,j1,comm);
                        k := j1; // + #comm; // check if that works for B,C,F,G
                                // this already doesn't work in A if filter is not true everywhere
                    end if;
                end if;
                j   := j1;
                j1 -:= 1;
            until j le 1 or neworder[list[j1][1]] lt neworder[list[j][1]] ;
        end if;
        k +:= 1;
    end while;
    
    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];

//  cpu := Cputime()-cpu;
//  cpu;
//  if cpu gt 0.1 then
//      error "debug";
//  end if;

//    Sprintf("%o, %o\n", ret1,ret2);

    return ret1,ret2;
end function;


/*
 * COLLECTION STRAIGHT: 
 *   we repeatedly walk from left to right exchanging elements that are not in order.
 *   the idea was to walk from left to right and from right to left alternately
 *   but this collection seems to be just much too slow.
 *
 *   elements are exchanged by the rule
 *       x*y -> y*[y,x^-1]*x
 */
Unip_CollectListLeftRight := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);
    // now use neworder[r1] le neworder[r2] to check if root r1 is le root r2.


// Sprintf("----->%o",from);
// order, filter, neworder;
// list;
//    orig := list;

    if #list eq 0 then return [], []; end if;
    if #list eq 1 then
        if filter[list[1][1]] then return list, [];
        else return [], list;
        end if;
    end if;

    repeat
        touched := false;
        k := 2;
        while k le #list do
            // the next condition is just a "less or equal", where "less" is a special one.
            if neworder[list[k][1]] le neworder[list[k-1][1]] then
                if list[k][1] eq list[k-1][1] then
                    list[k-1][2] +:= list[k][2];
                    Remove(~list, k);
                    if list[k-1][2] eq 0 then
                        Remove(~list, k-1);
                        k -:= 1;
                    end if;
                else        // y*x = x*[y,x^-1]*y
                    touched  := true;
                    comm := Unip_Comm( R, list[k], <list[k-1][1],-list[k-1][2]> );
                    tmp      := list[k];
                    list[k]  := list[k-1];
                    list[k-1] := tmp;
                    if 0 lt #comm then
                        Insert(~list,k,k-1,comm);
                        k +:= #comm;
                    end if;
                end if;
            end if;
            k +:= 1;
        end while;
    until not touched;
    
    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];

//  cpu := Cputime()-cpu;
//  cpu;
//  if cpu gt 0.1 then
//      error "debug";
//  end if;

//    Sprintf("%o, %o\n", ret1,ret2);

    return ret1,ret2;
end function;


/*
 * COLLECTION FROM OUTSIDE: 
 *   we collect from left and right at the same time (alternating, actually).
 *
 *   elements are exchanged by the rule
 *       x*y -> y*[y,x^-1]*x
 */
Unip_CollectList_FromOutside := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);
    // now use neworder[r1] le neworder[r2] to check if root r1 is le root r2.


// Sprintf("----->%o",from);
// order, filter, neworder;
//list;
//    orig := list;

    if #list eq 0 then return [], []; end if;
    if #list eq 1 then
        if filter[list[1][1]] then return list, [];
        else return [], list;
        end if;
    end if;

    l := 1;     // left  index
    r := #list; // right index
    while l lt r do
        // go from left
        while l lt r and neworder[list[l+1][1]] gt neworder[list[l][1]] do
            l +:= 1;
        end while;

        // stop the while loop if done:
        if l ge r then break; end if;

        // here neworder[list[l+1][1]] le neworder[list[l][1]] 
        j  := l+1;
        j1 := j-1;
        repeat
            if list[j][1] eq list[j1][1] then
                list[j1][2] +:= list[j][2];
                Remove(~list, j);
                if list[j1][2] eq 0 then
                    Remove(~list, j1);
                    j   := j1;
                    j1 -:= 1;
                    l  -:= 2;
                    r  -:= 2;
                else
                    l  -:= 1;
                    r  -:= 1;
                end if;
            else         // x*y = y*[y,x^-1]*x
                if r eq j then r +:= 1; end if;
                comm := [ < d[3], z > : d in multiplicationData(R, list[j][1],list[j1][1])
                                      | z ne 0 where z is d[4] * list[j][2]^d[1] * (-list[j1][2])^d[2] ];
             // comm := Unip_Comm( R, list[j], <list[j1][1],-list[j1][2]> );
                tmp      := list[j]; 
                list[j]  := list[j1]; 
                list[j1] := tmp;
                if 0 lt #comm then 
                    Insert(~list,j,j1,comm);
                    l := j-2;
                    r +:= #comm;
                end if;
            end if;
            j   := j1;
            j1 -:= 1;
        until j le 1 or neworder[list[j1][1]] lt neworder[list[j][1]] ;

        l +:= 1;
        // fix l and r if we pushed it too hard:
        if l lt 1     then l := 1;     end if;
        if r gt #list then r := #list; end if;

        // stop the while loop if done:
        if l ge r then break; printf "break, l=%o, r=%o\n", l, r; end if;

        while l lt r and neworder[list[r][1]] gt neworder[list[r-1][1]] do
            r -:= 1;
        end while;
        
        // stop the while loop if done:
        if l ge r then break; printf "break, l=%o, r=%o\n", l, r; end if;

        // here, neworder[list[r][1]] le neworder[list[r-1][1]] 
        J  := r-1;
        J1 := r;  // J1 = J+1
        repeat
            if list[J][1] eq list[J1][1] then
                list[J][2] +:= list[J1][2];
                Remove(~list, J1);
                if list[J][2] eq 0 then
                    Remove(~list, J);
                end if;
            else         // x*y = y*[y,x^-1]*x
                if l eq J then l -:= 1; end if;
                comm := [ < d[3], z > : d in multiplicationData(R, list[J1][1],list[J][1])
                                      | z ne 0 where z is d[4] * list[J1][2]^d[1] * (-list[J][2])^d[2] ];
             // comm := Unip_Comm( R, list[J1], <list[J][1],-list[J][2]> );
                tmp      := list[J]; 
                list[J]  := list[J1]; 
                list[J1] := tmp;
                if 0 lt #comm then 
                    Insert(~list,J1,J,comm);
                    J +:= #comm+1;
                    J1 := J+1;
                    r  := J1;
                else
                    J  := J1;
                    J1 +:= 1;
                end if;
            end if;
        until J1 gt #list or neworder[list[J][1]] lt neworder[list[J1][1]] ;

        r -:= 1;
        // fix l and r if we pushed it too hard:
        if l lt 1     then l := 1;     end if;
        if r gt #list then r := #list; end if;
    end while;    
    
    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];

//  cpu := Cputime()-cpu;
//  cpu;
//  if cpu gt 0.1 then
//      error "debug";
//  end if;

//    Sprintf("%o, %o\n", ret1,ret2);

    return ret1,ret2;
end function;

Unip_CollectList_FromOutside_C := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);

    list := InternalGrpLieCollectionFromOutside(R,list,neworder);

    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];
    return ret1,ret2;
end function;

Unip_CollectListFromLeft_Std_C := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    // SH: checked 
    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);

    list := InternalGrpLieCollectionFromLeft(R,list,neworder);

    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];
    return ret1,ret2;
end function;

Unip_CollectListToLeft_Std_C := function( R, list, order : 
filter := [true: i in [1..NumPosRoots(R)]], 
from   := "Unknown" )

    neworder := [order[i]:i in [1..#filter]|    filter[order[i]]] cat
                [order[i]:i in [1..#filter]|not filter[order[i]]];
    neworder := posOrder(neworder);

    list := InternalGrpLieCollectionToLeft(R,list,neworder);

    if not exists(i){ i : i in [1..#list] | not filter[list[i][1]] } then
        i := #list+1;
    end if;
    ret1 := list[ [1..i-1]   ];
    ret2 := list[ [i..#list] ];
    return ret1,ret2;
end function;


Unip_CollectList := function( R, K, list, order, method : 
    filter := [true: i in [1..NumPosRoots(R)]], 
    from   := "Unknown" )

    if   method in leftMethods_M then
        return Unip_CollectListFromLeft_Std     ( R,list,order : filter:=filter, from:=from );
    elif method in additiveMethods_M or Category(R) eq RootDtmSprs then
        return Unip_CollectList_FromOutside     ( R,list,order : filter:=filter, from:=from );
    elif method in leftMethods_C then
        return Unip_CollectListFromLeft_Std_C   ( R,list,order : filter:=filter, from:=from );
    elif method in rightMethods_C then
        return Unip_CollectListToLeft_Std_C     ( R,list,order : filter:=filter, from:=from );
    elif method in additiveMethods_C then
        return Unip_CollectList_FromOutside_C   ( R,list,order : filter:=filter, from:=from );
    end if;

//    return Unip_CollectListFromLeft_Papi  ( R,list,order : filter:=filter, from:=from );
//    return Unip_CollectListLeftRight      ( R,list,order : filter:=filter, from:=from );

end function;

/*
 * intrinsic InternalGrpLieOldCollectionFromLeft(R::RootDtm,seq::.,order::.) -> .
 * {}
 *     r1,r2 := Unip_CollectListFromLeft_Std(R,seq,order);
 *     return r1 cat r2;
 * end intrinsic;
 * 
 * intrinsic InternalGrpLieOldCollectionFromLeft(R::RootDtm,seq::.,order::.) -> .
 * {}
 *     r1,r2 := Unip_CollectList_FromOutside(R,seq,order);
 *     return r1 cat r2;
 * end intrinsic;
 */





// -------------------------------------------------------------------
//
// Conversion and multiplication by collection
//

// SH: checked
Unip_IsOrderedList := function( R, k, list, order )
  porder := posOrder(order);
  for i in [1..#list-1] do
    if porder[list[i][1]] ge porder[list[i+1][1]] then
      return false;
    end if;
  end for;
  return true;
end function;

// SH: checked
Unip_ToNormalised := function( R, k, list, order )
  if Unip_IsNormalised( list ) then  return list;  end if;
  
  if not Unip_IsOrderedList( R, k, list, order ) then
    error "Runtime error in Unip_ToNormalised: list is not in order";
  end if;
  
  elt := Unip_Identity(R,k);
  for term in list do
    elt[term[1]] := term[2];
  end for;
  return elt;
end function;

// SH: checked
Unip_ListInverse:= function( R, k, x )
  for i in [1..#x] do
    x[i][2] := -x[i][2];
  end for;
  Reverse( ~x );
  return x;
end function;

import "classic_mul.m" : Unip_InverseByClassic;

// SH: checked
Unip_InverseByCollection := function( R, k, x, order, method )
  x  :=  Unip_ToList             ( R, k, x, order );
  x  :=  Unip_ListInverse        ( R, k, x );
  x  :=  Unip_CollectList        ( R, k, x, order, method : from := "Unip_InverseByCollection" );
  return Unip_ToNormalised       ( R, k, x, order );
end function;

// SH: checked
// input list; we could do a Unip_ToList first, but 
// this function doesn't make sense for normalised elts.
Unip_NormaliseByCollection := function( G, x )
  R := RootDatum(G);  k := BaseRing(G);  order := collectionOrder(G);
  x  :=  Unip_CollectList        ( R, k, x, order, G`Method : from := "Unip_NormaliseByCollection" );
  return Unip_ToNormalised       ( R, k, x, order );
end function;

// SH: checked
// input list or normalised
Unip_ProductByCollection := function( R, k, x, y, order, method )
  x  :=  Unip_ToList             (R, k, x,       order);  
  y  :=  Unip_ToList             (R, k, y,       order);
  z  :=  Unip_CollectList        (R, k, x cat y, order, method : from := "Unip_ProductByCollection" );
  return Unip_ToNormalised       (R, k, z,       order);
end function;

import "classic_mul.m" : Unip_ProductByClassic;

// SH: checked
// input list or normalised
Unip_SeparateByCollection := function( R, k, x, order, filter, method )
  list  :=  Unip_ToList( R, k, x, order );
  return Unip_CollectList        ( R, k, list, order, method : filter:=filter, from := "Unip_SeparateByCollection" );
end function;

// -------------------------------------------------------------------
//
// Computing Hall polynomials  -- attached to root datum
//

// SH: 06.06.2006: 
//    use _one_ function to compute both multiplication and inverse Hall
//    polynomials (separation polys too, when/if they will be used in future)
//    this has two effects:
//       1. the same SLPolynomialRing is used for both. Thus evaluation will be 
//          faster since the same polynomial of the same ring is only evaluated once.
//       2. the classic method need not compute the "lower" entries (types B,C,D) twice.
//
allHallPolynomials := function( G )
  R := RootDatum( G );

  // assume that the hall polys for mult and inversion are assigned at the same time.
  if G`Method in [ "SymbolicFromLeft",    "SymbolicToLeft"    ] and not assigned R`HallPolynomials
  or G`Method in [ "SymbolicFromOutside", "SymbolicClassical" ] and not assigned R`HallPolynomialsPapi
  then
    k := BaseRing(G);
    N := NumPosRoots( R );
    if N gt 0 then //          \/ note that we use integers here :)
      K := SLPolynomialRing( Integers(), 2*N );  a := [K.i : i in [1..2*N]];
      x := a[[1..N]];  y := a[[N+1..2*N]];
      if Category(R) eq RootDtmSprs
      and G`Method eq "SymbolicClassical"
      and Seqset(R`ExtraspecialSigns) eq {-1} then
        vprint SHdebugGrpLie : "use classic    method for", G`Method;
        vtime  SHdebugGrpLie : mul, inv := hallPolysSprs( R, K, x, y );
      else
        vprint SHdebugGrpLie : "use collection method for", G`Method;
        vtime  SHdebugGrpLie : mul := Unip_ProductByCollection( R, K, x, y, collectionOrder(G), G`Method );
        vtime  SHdebugGrpLie : inv := Unip_InverseByCollection( R, K, x,    collectionOrder(G), G`Method );
      end if;
    else
      mul := [SLPolynomialRing( Integers(), 1 )!0];
      inv := mul;
    end if;

    if   G`Method in [ "SymbolicFromLeft",    "SymbolicToLeft"    ] then
      R`HallPolynomials            := mul;
      R`InverseHallPolynomials     := inv;
    elif G`Method in [ "SymbolicFromOutside", "SymbolicClassical" ] then
      R`HallPolynomialsPapi        := mul;
      R`InverseHallPolynomialsPapi := inv;
    end if;
  end if;
 
  if   G`Method in [ "SymbolicFromLeft",    "SymbolicToLeft"    ] then
    return R`HallPolynomials,     R`InverseHallPolynomials;
  elif G`Method in [ "SymbolicFromOutside", "SymbolicClassical" ] then
    return R`HallPolynomialsPapi, R`InverseHallPolynomialsPapi;
  end if;
end function;


// SH: checked (kind of)
// SEPARATE NOT CURRENTLY IN USE
oldseparateHallPolynomials := function( G )
  R := RootDatum( G );  k := BaseRing( G );
  if not assigned G`SeparateHallPolynomials then
    N := NumPosRoots( R );
    K := SLPolynomialRing( k, N );  a := [K.i : i in [1..N]];
    polys := [];
    x := a[[1..N]];
    for r in [1..N] do
      _, y := Unip_SeparateByCollection(R,K,x, [ i eq r : i in [1..N] ], collectionOrder(G), G`Method );
      Append( ~polys, Unip_ToNormalised(R,K,y) );
    end for;
    G`SeparateHallPolynomials := polys;
  end if;
  return G`SeparateHallPolynomials;
end function;

// SH: checked (kind of)
separateHallPolynomials := function( G )
  R := RootDatum( G );  k := BaseRing( G );
  if not assigned G`SeparateHallPolynomials then
    N := NumPosRoots( R );
    K := SLPolynomialRing( k, N );  a := [K.i : i in [1..N]];
    polys := [];
    for r in [1..N] do
      _, y := Unip_SeparateByCollection( R, K, 
        a[[1..r]] cat [K|0:i in [r+1..N]], [ i eq r : i in [1..N] ], collectionOrder(G), G`Method );
      Append( ~polys, Unip_ToNormalised(R,K,y)[[r+1..N]] );
    end for;
    return polys;
    G`SeparateHallPolynomials := polys;
  end if;
  return G`SeparateHallPolynomials;
end function;



// -------------------------------------------------------------------
//
// Multiplying by Hall polynomials
//
EvaluateSeq := function( seq, val )
    if #val eq 0 then
        return [ Universe(seq)!0         : i in [1..#seq] ];
    else
        nval := #val;
        rnk  := Rank(Universe(seq));
        if nval lt rnk then
            Insert(~val,nval+1,nval,[Universe(val)|0 : i in [nval+1..rnk]]);
        end if;
        return [ Evaluate( seq[i], val ) : i in [1..#seq] ];
    end if;
end function;


// SH: checked
// input list // output normalised
Unip_NormaliseByHall := function( G, list )
  R := RootDatum( G );  k := BaseRing( G );
  if #list eq 0 then  return Unip_Identity( R, k );  end if;
  polys := allHallPolynomials( G );
  order := collectionOrder(G); porder := posOrder(order);
  // split up the list into ordered sublists. and multiply them subsequently.
  breaks := [ i : i in [1..#list-1] | porder[list[i+1][1]] le porder[list[i][1]] ] cat [#list];
  ret := Unip_ToNormalised( R, k, list[[1..breaks[1]]], order );
  for j in [1..#breaks-1] do
    next := Unip_ToNormalised( R, k, list[[breaks[j]+1..breaks[j+1]]], order );
    ret := EvaluateSeq( polys, ret cat next );
  end for;
  return ret;
end function;

// SH: checked
// input list or normalised // output normalised
Unip_ProductByHall := function( G, x, y )
  R := RootDatum( G );  k := BaseRing( G );
  order := collectionOrder(G);
  if Unip_IsNormalised( x ) and Unip_IsNormalised( y ) then
    return EvaluateSeq( allHallPolynomials( G ), x cat y );
  else
    return Unip_NormaliseByHall( G, Unip_ToList( R, k, x, order ) 
                                cat Unip_ToList( R, k, y, order ) );
  end if;
end function;

// SH: checked
// input list or normalised // output normalised
Unip_InverseByHall := function( G, x )
  R := RootDatum( G );  k := BaseRing( G );
  _, polys := allHallPolynomials( G );
  x := Unip_ToNormalised( R, k, x, collectionOrder(G) );  
  return EvaluateSeq( polys, x );
end function;


// SH: not checked
// SEPARATE NOT CURRENTLY IN USE
// input normalised
Unip_SeparateByHall := function( G, x, filter )
  R := RootDatum( G );  k := BaseRing( G );
  N := NumPosRoots( R );  polys := separateHallPolynomials( G );
  if forall{ f : f in filter | f } then
    y := Unip_Identity( R, k );
  elif 3*#[ f : f in filter | f ] gt #filter then
    // right separate
    y, x := $$( G, Unip_InverseByHall(G,x), [ not f : f in filter ] );
    x := Unip_InverseByHall(G,x);
    y := Unip_InverseByHall(G,x);
  else
    separateTerm := func< x, r | 
      x[[1..r-1]] cat [k!0] cat EvaluateSeq( polys[r], x ) >;
    y := x;
    x := [ k | 0 : r in [1..N] ];
    for r in [ r : r in [1..N] | filter[r] ] do
      x[r] := y[r];
      y := Unip_ProductByHall(G,separateTerm( y, r ),
        [0:i in [1..r]] cat y[[r+1..N]] );
    end for;
  end if;
  
  return x, y;
end function;
  


// -------------------------------------------------------------------
//
// Multiplying by best available method
//
// These functions will input normalised or list elements
//

// the next function assumes that hall polys were computed on creation of the group 
// only use halls if explicitly asked for:
useHall := func< G | G`Method in hallMethods >;

// SH: checked
Unip_Normalise := function( G, x )
  if Unip_IsNormalised( x ) then
    return x;
  else
    return Unip_NormaliseByCollection( G, x ); 
/*
 * SH: DON'T USE Hall for Normalisation, only use for multiplication
 *
 *     return useHall(G) 
 *         select Unip_NormaliseByHall( G, x )
 *           else Unip_NormaliseByCollection( G, x );
 */
  end if;
end function;

// SH: checked
Unip_Product := function( G, x, y : normalise := true )
  R := RootDatum(G);  k := BaseRing(G);
  if normalise then
    x := Unip_Normalise(G,x);  y := Unip_Normalise(G,y);
    if   Seqset(x) eq {k!0} then return y;
    elif Seqset(y) eq {k!0} then return x;
    elif useHall(G) then
        return Unip_ProductByHall( G, x, y );
    elif G`Method in classicalMethods then /* and not in hall */
        return Unip_ProductByClassic( R, x, y, collectionOrder(G) );
    else
        return Unip_ProductByCollection( R, k, x, y, collectionOrder(G), G`Method );
    end if;
  else
    return Unip_ToList(R, k, x, collectionOrder(G) ) cat
           Unip_ToList(R, k, y, collectionOrder(G) );
  end if;
end function;

// SH: checked
Unip_Separate := function( G, x, filter )
  // if #[f:f in filter|f] eq 1 then R := RootDatum(G); R`SHcount +:=1; 
  // else #[f:f in filter|f]; end if;
  //  print [ f select 1 else 0 : f in filter ];
  R := RootDatum(G);  k := BaseRing(G);
  return Unip_SeparateByCollection( R, k, x, collectionOrder(G), filter, G`Method );
end function;  

// SH: checked
Unip_Inverse := function( G, x )
  R := RootDatum(G);  k := BaseRing(G);
  if useHall(G) then
      return Unip_InverseByHall( G, Unip_Normalise(G,x) );
  elif G`Method in classicalMethods then /* and not in hall */
      return Unip_InverseByClassic( R, x, collectionOrder(G) );
  else 
      return Unip_InverseByCollection( R, k, x, collectionOrder(G), G`Method );
  end if;
end function;  

// ===================================================================
//
//  The maximal torus
//
//  Functions for multiplying maximal torus elements.
//
// ===================================================================

Torus_Parent := func< R, k | RSpace( k, Dimension(R) ) >;

Torus_Identity := function( R, k )
  d := Dimension(R);
  return Torus_Parent(R,k) ! [ k!1 : i in [1..d] ];
end function;

Torus_IntMxAction := function( t, M )
  V := Parent( t );  t := Eltseq( t );  d := #t;
  v := [ &*[ t[i]^(Integers()!M[i,j]) : i in [1..Nrows(M)] ] : j in [1..Ncols(M)] ];
  return VectorSpace( Universe(v), #v )!v;
end function;

/*
TorusFactRoots := function(t, e)
    d1 := &*e[1 .. #e div 2];
    d2 := &*e[#e div 2 + 1.. #e];
    roots := {r[1] : r in Roots(x^d1 - t)};
    roots := {r[1] : r in Roots(x^d2 - r1), r1 in roots};
    return roots;
end function;
*/

Torus_RatMxAction := function( t, M )
  V := Parent( t );  k := BaseRing( t );  t := Eltseq( t );  d := #t;
  nr := Nrows(M);
  error if exists{ i : i in [1..nr] | t[i] eq 0 }, "invalid torus element";
  P := PolynomialRing( k, 1 ); xm := P.1;
  x := PolynomialRing(k).1;
  ret := { [] };
  for j in [1..Ncols(M)] do
    dens := [ Denominator(M[i,j]) : i in [1..nr] ];
    d := Lcm( dens );
    vals := [Integers() | M[i,j]*d : i in [1..nr] ];
    term := &*[ t[i]^vals[i] : i in [1..nr] ];
//    term := &*[ t[i]^(Integers()!(M[i,j]*d)) : i in [1..Nrows(M)] ];
    if d ne 1 then
	if IsFinite(k) and d gt 1000*#k then
	    terms := {t : t in k | t^d eq term};
	elif d le 10^8 then
	    terms := {t[1] : t in Roots(x^d - term)};
	else
	  "New";
	  d;
	  xm^d - P!term;
	    /*time*/ F := Factorization(xm^d - P!term);
	    F := {f[1] : f in F | TotalDegree(f[1]) eq 1};
	    assert &and{IsUnivariate(f) : f in F}; /* SH: why not use forall here? */
	  terms := { t[1] : t in Roots(UnivariatePolynomial(f)), f in F};
	end if;
      if IsEmpty(terms) then  return {};  end if;
    else
      terms := { term };
    end if;
    ret := { Append( r, t ) : r in ret, t in terms };
  end for;
  return ChangeUniverse( ret, V );
end function;

//[ t[i]^(Integers()!M[i,j]) : i in [1..d] ]

/*Torus_IsOne := function( R, k, t )
  r := Rank( R );  d := Dimension( R );
  V := VectorSpace( Rationals(), d );
  B := SimpleCoroots( R );
  B := [ V | B[i] : i in [1..r] ];
  B := ExtendBasis( B, V );
  B := Matrix( B );
  has, t := Torus_RatMxAction( t, B^-1 );
  if not has then
    return false;
  elif exists( i ){ i : i in [r+1..d] | t[i] ne 1 } then
    return false;
  else
    C := CartanMatrix( R );
    for i in [1..r] do
      if &*[ t[j]^C[j,i] : j in [1..r] ] ne 1 then
        return false;
      end if;
    end for;
    return true;
  end if;
end function;*/


Torus_IsOne := function( R, k, t )
  return forall{ i : i in Eltseq(t) | i eq 1 };
end function;


Torus_Random := function(R, k)
  if IsFinite(k) and #k eq 2 then return Torus_Identity(R,k); end if;
  elt := [];  d := Dimension(R);
  repeat
    a := Random(k);
    if a ne 0 then
        Append(~elt, a);
    end if;
  until #elt eq d;
  return Torus_Parent(R,k) ! elt;
end function;

Torus_Term := function( R, k, v, al )
  d := Dimension(R);
  return Torus_Parent(R,k)![ al^(Integers()!v[i]) : i in [1..d] ];
end function;

Torus_Term_Rt := function( R, k, r, al )
  v := Coroot( R, r );
  return Torus_Term( R, k, v, al );
end function;

Torus_Check := function(R, k, t )
  d := Dimension(R);
  if not t in Torus_Parent(R,k) then return false; end if;
  for i in [1..d] do
    if not IsUnit(t[i]) then  return false;  end if;
  end for;
  return true;
end function;

Torus_Product := function( R, k, x, y )
  d := Dimension(R);
  return Torus_Parent(R,k) ! [ x[i]*y[i] : i in [1..d] ];
end function;

Torus_Power := function( R, k, x, n )
  d := Dimension(R);
  return Torus_Parent(R,k) ! [ x[i]^n : i in [1..d] ];
end function;

Torus_Inverse := function( R, k, x )
  return Torus_Power( R, k, x, -1 );
end function;

Torus_IsEqual := function( R, k, t1, t2 )
  return Torus_IsOne(R,k, Torus_Product(R,k, t1, Torus_Inverse(R,k,t2) ) );
end function;

Torus_Print := procedure( R, k, x )
  printf "%o ", x;
end procedure;



// ===================================================================
//
//  The Weyl group
//
// ===================================================================

// check that this does not repeatedly create the fp group
Weyl_Normalise := procedure( R, k, ~w )
  Wfp := CoxeterGroup( GrpFPCox, R );
  w := Eltseq( Wfp!w );
end procedure;

// THIS IS INEFFICIENT
Weyl_Inverse := function( R, k, w )
  inv := [**];
  for r in Reverse(w) do
    Append( ~inv, r );
    Append( ~inv, Torus_Term_Rt( R, k, r, k!-1 ) );
  end for;
  return inv;
end function;

// THIS IS INEFFICIENT
Weyl_IsEqual := function( R, w, v )
  if w eq v then return true; end if;
  W := CoxeterGroup(R);
  return WordToPerm(W,w) eq WordToPerm(W,v);
end function;

Weyl_Print := procedure( R, w )
  for r in Reverse( w ) do
    printf "n%o ", r;
  end for;
end procedure;

forward WeylActionOnTorus;

declare attributes GrpPermCox : ReflectionTorusElements;

Weyl_ReflectionTorusElements := function( R )
  W := CoxeterGroup(R);
  if not assigned W`ReflectionTorusElements then
    N := NumPosRoots( R );  n := Rank( R );
    perms := SimpleReflectionPermutations( R );
 
    k := Integers();
    id := Torus_Identity( R, k );

    // precompute the torus elements for simple roots
    // and their negatives:
    hs := [ id : r in [1..n] ];
    for r in [1..n] do;
        hs[N+r] := Torus_Term_Rt(R,k,r,-1);
    end for;

    for i in [1..n] do
        orbit := {@ i @};  pos := 1;
        repeat
          s := orbit[pos];
          for j in [1..#perms] do
            r := s^perms[j];
            Include( ~orbit, r );
            if not IsDefined( hs, r ) then 
              h := hs[s];
              WeylActionOnTorus( R, k, ~h, [j] );
              if LieConstant_eta( R, j, s ) eq -1 then
                h :=  Torus_Product( R, k, h, Torus_Term_Rt(R,k,r,-1) );
              end if;

              h := Torus_Product( R, k, h, Torus_Term_Rt(R,k,j,-1) );

              /*   SH: Sep 2006
              **
              **   now, we have
              **        (s_r)dot = h (s_j)dot (s_s)dot (s_j)dot
              **   use (24) and a left version of (24) to normalise Weyl term
              */
              
              js := j^ReflectionPermutation(R,s);
              jsj := js^perms[j];
              if js gt N then
                h :=  Torus_Product( R, k, h, Torus_Term_Rt(R,k,jsj,-1) );
              end if;
              if jsj gt N then
                h :=  Torus_Product( R, k, h, Torus_Term_Rt(R,k,j,-1) );
              end if;

              /* 
              **   now, we have
              **        (s_r)dot = h (s_j s_s s_j)dot
              **   where the Weyl term is normalised
              */
              
              hs[r] := h;

            end if;
          end for;
          pos +:= 1;
        until pos gt #orbit;
    end for;
            
    W`ReflectionTorusElements := hs;
  end if;
  return W`ReflectionTorusElements;
end function;

Weyl_NonsimpleReflection := function( R, k, r )
  return ChangeRing( Weyl_ReflectionTorusElements(R)[r], k ),
    ReflectionWord( R, r );
end function;

Weyl_NonsimpleReflections := function( R, k )
  return ChangeUniverse( Weyl_ReflectionTorusElements(R), RSpace(k,Dimension(R)) ),
    ReflectionWords( R );
end function;

// This function returns a word in W with probability proportional to the size
// of its double coset
Weyl_Random_uniform := function( R, q )
  n := Rank( R );  d := Dimension( R );  N := NumPosRoots( R );
  if n eq 0 then
    return [Integers()|];
  end if;
  W := CoxeterGroup( GrpPermCox, R );
  Wfp, h := CoxeterGroup( GrpFPCox, W );
  incLen := function( words );
    return { w * Wfp.s : s in {1..n} diff RightDescentSet(Wfp,w), w in words};
  end function;
  ordB := q^N * (q-1)^d;
  w0 := h(LongestElement( W ));  
    // Don't use LongestElement(Wfp) to avoid recreating the perm group 
    // on each call.
  l0 := #w0;
  remaining := GroupOfLieTypeOrder( R, q );
  words := { Wfp!1 };  l := 0;
  repeat 
    dcosetsize := ordB * #words * q^(N-l);
    if Random([1..remaining]) le dcosetsize then
       return Eltseq( Random( words ) * w0);
    end if;
    remaining -:= dcosetsize;
    words := incLen( words );  l +:= 1;
  until false;
  error "This should not happen.  Please email magma-bugs@maths.usyd.edu.au";
end function;

// This function just returns a random word in W 
Weyl_Random_fast := function( R, q )
    W     := CoxeterGroup(GrpPermCox, R);
    Wfp,h := CoxeterGroup(GrpFPCox,   W);
    return Eltseq( Random(W)@h );
end function;


// ===================================================================
//
//  Actions
//
//  All actions are right actions by default.
//
// ===================================================================

// SH: checked
TorusActionOnNormUnip := procedure( R, k, ~u, t : left := false )
  N := NumPosRoots( R );
  B := Basis( CorootSpace(R) );
  for r in [1..Dimension(R)] do
    for s in [1..N] do
      m:= t[r]^( Integers()!( Root(R,s), B[r] ) );
      if not left then  u[s] *:= m;
      else              u[s] *:= m^(-1);
      end if;
    end for;
  end for;
end procedure;

// SH: checked
TorusActionOnListUnip := procedure( R, k, ~u, t : left := false )
  B := Basis( CorootSpace(R) );
  for r in [1..Dimension(R)] do
    for i in [1..#u] do
      s := u[i][1];
      m := t[r]^( Integers()!( Root(R,s), B[r] ) );
      if not left then  u[i][2] *:= m;
      else              u[i][2] *:= m^(-1);
      end if;
    end for;
  end for;
end procedure;

// SH: checked
// u: in list or normalized; out: same
TorusActionOnUnip := procedure( R, k, ~u, t : left := false )
  if #u eq 0 or Seqset(Eltseq(t)) eq {1} then 
    return;
  elif Category(Universe(u)) eq SetCart then
    TorusActionOnListUnip( R, k, ~u, t : left := left );
  else
    TorusActionOnNormUnip( R, k, ~u, t : left := left );
  end if;
end procedure;

WeylActionOnTorus := procedure( R, k, ~t, w : left := false )
  if Category(w) eq GrpPermElt then
    w := PermToWord( CoxeterGroup(R), w );
  end if;
  d := Dimension(R);
  V := Torus_Parent( R, k );
  if left then 
    Reverse(~w); 
  end if;
  // coref := CoreflectionMatrices( R );
  // only compute needed matrices
  coref := []; // CoreflectionMatrices( R );
  for r in Seqset(w) do;
    coref[r] := CoreflectionMatrix(R,r);
  end for;
  M := &*[MatrixAlgebra(Integers(),d) | coref[r] : r in w ];
  t := V![ &*[ t[i]^M[i,j] : i in [1..d] ]  : j in [1..d] ];
end procedure;



// SH: checked
// u: in list or normalized; out: list
WeylActionOnUnipOLD := procedure( R, k, ~u, w, order, roots, coroots : left := false )
  W := CoxeterGroup(R);
  if Category(w) eq GrpPermElt then
    w := PermToWord( W, w );
  end if;
//cpu := Cputime();
  u := Unip_ToList( R, k, u, order );
  N := NumPosRoots(R);
  if left then  
    Reverse( ~w );  
    // VERY INEFFICIENT
    for r in w do
      rp := W.r; //ReflectionPermutation(R,r);
      u  := [ < 
                term[1]^rp, 
                term[2]*LieConstant_eta(R,r,term[1])*(IsEven(cartanInteger(R,N,term[1],r)) select 1 else -1)  
              > : term in u ];
    end for;
  else
    // VERY INEFFICIENT
    for r in w do
      rp := W.r; //ReflectionPermutation(R,r);
      u  := [ < 
                term[1]^rp, 
                term[2]* LieConstant_eta(R,r,term[1])
              > : term in u ];
    end for;
  end if;
//Cputime()-cpu;
end procedure;

// u: in: list or normalized; out: list
WeylActionOnUnip := procedure( R, k, ~u, w, order, roots, coroots : left := false )
    W := CoxeterGroup(R);
    if Category(w) eq GrpPermElt then
        wo := PermToWord( W, w );
    else
        wo := w;
    end if;

    if #wo eq 0 then return; end if;
//wo;
//u;
//      uorig := u;
//cpu := Cputime();

    u := Unip_ToList( R, k, u, order );
    N := NumPosRoots(R);
    case Category(R):
    when RootDtm:
        lie_eta_fun := lie_eta;
    when RootDtmSprs:
        lie_eta_fun := function(R,r,s)
            X := R`Type[1][1];
            n := Rank(R);
            rp := InternalGrpLieIndex2Pair(X,n,r,N);
            sp := InternalGrpLieIndex2Pair(X,n,s,N);
            return lie_eta_sprs(X,n,N,R`ExtraspecialSigns,rp,sp);
        end function;
    else:
        error "Unknown Category of a root datum:",  Category(R);
    end case;

    if Characteristic(k) eq 2 then
        if left then
            Reverse( ~wo );
        end if;

        // #w+1 permutations starting with 1, ending w
        perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
        w := perms[#wo+1];
 
        u  := [ < term[1]^w, term[2] >  : term in u ];
    else
        if #wo eq 1 then
            // #w+1 permutations starting with 1, ending w
            s := wo[1];
            // this _is_ sometimes called for non-simple reflections!
            // w := W.s; 
            w := Reflection(W,s);
            v := coroots[s];
            if left then
                C := CartanMatrix(R);
                signs := [ IsEven( (roots[t[1]],v) ) select 1 else -1 : t in u ];
                u  := [ < r^w,
                          u[i][2]
                          * lie_eta_fun(R,s,r)
                          * signs[i] \
                        > where r is u[i][1] : i in [1..#u] ];
            else
                u  := [ < r^w,
                          u[i][2]
                          * lie_eta_fun(R,s,r) \
                        > where r is u[i][1] : i in [1..#u] ];
            end if;
        else
            if maxMultiplicity(R) eq 1 then
                if left then
                    Reverse( ~wo );

                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    phi_w := [ r:r in [1..N] | r^w gt N ];
                    v := &+coroots[phi_w];

                    signs := [ IsEven( (roots[u[i][1]],v) ) select 1 else -1 : i in [1..#u] ];
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]
                              * signs[i] \
                            > where r is u[i][1] : i in [1..#u] ];
                else
                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
                    phi_w := [ r:r in [1..N] | r^w gt N ];
 
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]  \
                            > where r is u[i][1] : i in [1..#u] ];
                end if;
            else
                if left then
                    Reverse( ~wo );

                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    phi_w := [ r:r in [1..N] | r^w gt N ];
                    v := &+coroots[phi_w];

                    signs := [ IsEven( (roots[u[i][1]],v) ) select 1 else -1 : i in [1..#u] ];
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]
                              * signs[i] \
                            > where r is u[i][1] : i in [1..#u] ];
                else
                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]   \
                            > where r is u[i][1] : i in [1..#u] ];
                end if;
            end if;

        end if;
    end if;

//Cputime()-cpu;
/*
 *    assert we have correct result:
 */
 
//      WeylActionOnUnipOLD( R, k, ~uorig, left select Reverse(wo) else wo, order, roots, coroots : left := left );
//      if u ne uorig then
//          error "aaaarrgh", u, uorig;
//      end if;

end procedure;

// u: in: list or normalized; out: list
// THIS IS COPY&PASTE OF WeylActionOnUnip, so actually a bad idea !!!
// but we don't want to compute all roots for sparse root data.
WeylActionOnUnipSprs := procedure( R, k, ~u, w, order : left := false )
    assert ISA(Category(R),RootDtmSprs);
    d := Dimension(R);
    V := RSpace(Integers(),d);
    
    W := CoxeterGroup(R);
    if Category(w) eq GrpPermElt then
        wo := PermToWord( W, w );
    else
        wo := w;
    end if;

    if #wo eq 0 then return; end if;
//wo;
//u;
//      uorig := u;
//cpu := Cputime();

    u := Unip_ToList( R, k, u, order );
    N := NumPosRoots(R);
    lie_eta_fun := function(R,r,s)
        X := R`Type[1][1];
        n := Rank(R);
        rp := InternalGrpLieIndex2Pair(X,n,r,N);
        sp := InternalGrpLieIndex2Pair(X,n,s,N);
        return lie_eta_sprs(X,n,N,R`ExtraspecialSigns,rp,sp);
    end function;

    if Characteristic(k) eq 2 then
        if left then
            Reverse( ~wo );
        end if;

        // #w+1 permutations starting with 1, ending w
        perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
        w := perms[#wo+1];
 
        u  := [ < term[1]^w, term[2] >  : term in u ];
    else
        if #wo eq 1 then
            // #w+1 permutations starting with 1, ending w
            s := wo[1];
            // this _is_ sometimes called for non-simple reflections!
            // w := W.s; 
            w := Reflection(W,s);
            v := V!Coroot(R,s);
            if left then
                C := CartanMatrix(R);
                signs := [ IsEven( (V!Root(R,t[1]),v) ) select 1 else -1 : t in u ];
                u  := [ < r^w,
                          u[i][2]
                          * lie_eta_fun(R,s,r)
                          * signs[i] \
                        > where r is u[i][1] : i in [1..#u] ];
            else
                u  := [ < r^w,
                          u[i][2]
                          * lie_eta_fun(R,s,r) \
                        > where r is u[i][1] : i in [1..#u] ];
            end if;
        else
            if maxMultiplicity(R) eq 1 then
                if left then
                    Reverse( ~wo );

                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    phi_w := [ r:r in [1..N] | r^w gt N ];
                    v := &+[V| Coroot(R,r) : r in phi_w ];

                    signs := [ IsEven( (V!Root(R,u[i][1]),v) ) select 1 else -1 : i in [1..#u] ];
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]
                              * signs[i] \
                            > where r is u[i][1] : i in [1..#u] ];
                else
                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
                    phi_w := [ r:r in [1..N] | r^w gt N ];
 
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]  \
                            > where r is u[i][1] : i in [1..#u] ];
                end if;
            else
                if left then
                    Reverse( ~wo );

                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    phi_w := [ r:r in [1..N] | r^w gt N ];
                    v := &+[V| Coroot(R,r) : r in phi_w ];

                    signs := [ IsEven( (V!Root(R,u[i][1]),v) ) select 1 else -1 : i in [1..#u] ];
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]
                              * signs[i] \
                            > where r is u[i][1] : i in [1..#u] ];
                else
                    // #w+1 permutations starting with 1, ending w
                    perms := [ i eq 1 select W!1 else Self(i-1)*W.wo[i-1] : i in [1..#wo+1] ];
                    w := perms[#wo+1];
 
                    u  := [ < r^w,
                              u[i][2]
                              * &*[ lie_eta_fun(R,wo[i],r^perms[i]) : i in [1..#wo] ]   \
                            > where r is u[i][1] : i in [1..#u] ];
                end if;
            end if;

        end if;
    end if;

end procedure;



// ------------------------------------------------------------------
//
//  Element creation
//


intrinsic Random( G::GrpLie : Uniform:=true ) -> GrpLieElt
{A random element of G}
  R := RootDatum(G);  k := BaseRing(G);
  require Category( k ) eq FldFin : "The base ring must be a finite field";
  require not IsTwisted(R)        : "The group must be untwisted";
  x := CreateLieGroupElement(G);
  x`u  := Unip_Random ( R, k, collectionOrder(G) );
  x`h  := Torus_Random( R, k );
  x`w  := Uniform select Weyl_Random_uniform ( R, #k )
                    else Weyl_Random_fast    ( R, #k );
  x`filter := PosToNegFilter( R, x`w );
  x`up := Unip_Random ( R, k, collectionOrder(G) : filter:=x`filter );
  return x;
end intrinsic;

// returns a normalised 1 in G
normId := function( G )
  R := RootDatum(G);  k := BaseRing(G);
  x := CreateLieGroupElement(G);
  x`u  := Unip_Identity(R,k);  x`w := [];  
  x`up := Unip_Identity(R,k);  x`h := Torus_Identity(R,k);
  x`filter := [Booleans() | false: i in [1..NumPosRoots(R)]];
  return x;
end function;


flattenList := procedure( ~list )
  while exists( i ){ i : i in [1..#list] | Category(list[i]) eq List } do
    new := [**];
    for j in [1..i-1] do
      Append( ~new, list[j] );
    end for;
    for term in list[i] do
      Append( ~new, term );
    end for;
    for j in [i+1..#list] do
      Append( ~new, list[j] );
    end for;
    list := new;
  end while;
end procedure;

intrinsic InternalCheckGrpLieElt( G::GrpLie, lst::List ) -> List
{Internal to check whether a list represents a group of Lie type element}
  k := BaseRing(G);  R := RootDatum(G);  N := NumPosRoots( R );
  d := Dimension( R );  n := Rank( R );
  V := RSpace( k, d );
  Wf := CoxeterGroup( GrpFPCox, R );
  checkTup := function( t )
    if #t ne 2 then return "Invalid unipotent term"; end if;
    c1, r := IsCoercible( Integers(), t[1] );
    c2, a := IsCoercible( k, t[2] );
    if not (c1 and r in [1..2*N]) then
      return "Invalid root in unipotent term";
    elif not c2 then
      return "Invalid ring element in unipotent term";
    else
      return <r,a>;
    end if;
  end function;
    
  flattenList( ~lst );
  newl := [* *];
  for i in [1..#lst] do
    t := lst[i];
    case Category( t ):
    when Tup:
      newt := checkTup( t );
      if Category( newt ) eq MonStgElt then
        error newt, t;
      else
        Append( ~newl, newt );
      end if;
    when SeqEnum:
      c, newt := CanChangeUniverse( t, k );
      if c and not IsNull( t ) then
        if #newt eq N then
          Append( ~newl, newt );
	elif #newt ne 0 then
	  error "Unipotent term", t, "must have length", N;
	end if;
      elif IsNull( t ) or Category(Universe(t)) eq SetCart then
        newt := [ car<Integers(),k> | ];
        for s in t do
	  news := checkTup( s );
          if Category( news ) eq MonStgElt then
            error news, s;
          else
            Append( ~newt, news );
          end if;
	end for;
	Append( ~newl, newt );
      else
        error "Invalid unipotent element", t;
      end if;	  
    when ModTupFldElt,ModTupRngElt:
      c, newt := IsCoercible( V, t );
      if c and Torus_Check(R,k,newt) then
        Append( ~newl, newt );
      else
        error "Invalid torus element", t;
      end if;
    when SetIndx:
      error "Indexed sets are not permitted";
    when RngIntElt:
      if t gt 0 and t le 2*N then
        Append( ~newl, t );
      else
        error "Invalid Weyl term", t;
      end if;
    when GrpFPCoxElt:
      c, newt := IsCoercible( Wf, Eltseq(t) );
      if c then
        newt := Eltseq( newt );
	for r in newt do
	  Append( ~newl, r );
	end for;
      else
        error "Invalid Weyl element", t;
      end if;
    when GrpPermElt:
      W := CoxeterGroup(R);
      c, newt := IsCoercible( W, t );
      if c then
        newt := PermToWord( W, t );
	for r in newt do
	  Append( ~newl, r );
	end for;
      else
        error "Invalid Weyl element", t;
      end if;
    when GrpLieElt:
      c, newt := IsCoercible( G, t );
      if c then
        Append( ~newl, newt );
      else
        error "Invalid group of Lie type term", t;
      end if;
    else
      error "Invalid term";
    end case;
  end for;

  if IsTwisted(G) then
    c := OneCocycle(G);
    // Overgroup of G
    O := Domain(Group(GammaGroup(c)));
    if not IsInTwistedForm( elt<O|newl>, c ) then
      error "The element is not fixed by the cocycle";
    end if;
  end if;

  return newl;
end intrinsic;

// ---------------------------------------------------------------
//
//  Multiplication and normalisation helper functions
//
//  dropped all Lie_LeftMultiplyBy* functions at SVN revision 3438
//
//

Lie_Check := function( G, x, from )
  R := RootDatum(G);
  if x`filter ne PosToNegFilter( R, x`w ) then
    error "Incorrect filter from ",from;
  end if;
  for term in x`up do
    if not x`filter[term[1]] then
      error "up term", term, "not filtered from ", from;
    end if;
  end for;
  return true;
end function;


Lie_Normalise := procedure( G, ~x )
  R := RootDatum(G);  k := BaseRing(G);

  if #x`up eq 0 
  or     Universe(x`up) cmpeq k 
     and Seqset(x`up) eq {k!0} then
    return;
  end if;

  a, x`up := Unip_Separate( G, x`up, [ Booleans() | not b : b in x`filter ] );
  if #a ne 0 then

    if ISA(Category(R),RootDtmSprs) then
      WeylActionOnUnipSprs ( R, k, ~a, x`w, collectionOrder(G) : left );
    else
      d := Dimension(R);
      roots   := Roots(R);
      coroots := Coroots(R);
      ChangeUniverse(~roots,  RSpace(Integers(),d));
      ChangeUniverse(~coroots,RSpace(Integers(),d));
      WeylActionOnUnip ( R, k, ~a, x`w, collectionOrder(G), roots, coroots : left );
    end if;
    TorusActionOnUnip( R, k, ~a, x`h : left );
    x`u := Unip_Product( G, x`u, a : normalise );

  end if;
  // Lie_Check(G,x, "Lie_Normalise");
end procedure;

Lie_UnipNormalise := procedure( G, ~x );
  x`u  := Unip_Normalise( G, x`u );
  x`up := Unip_Normalise( G, x`up );
end procedure;

Lie_UnipUnnormalise := procedure( G, ~x );
  R := RootDatum(G);  k := BaseRing(G);
  x`u  := Unip_ToList( R, k, x`u,  collectionOrder(G) );
  x`up := Unip_ToList( R, k, x`up, collectionOrder(G) );
end procedure;


Lie_RightMultiplyByTorus := procedure( G, ~x, t )  //  u  h  w  up  t
  R := RootDatum(G);  k := BaseRing(G);
  TorusActionOnUnip( R, k, ~x`up, t );           //  u  h  w  t  up
  WeylActionOnTorus( R, k, ~t, x`w : left );     //  u  h  t  w  up
  x`h := Torus_Product( R, k, x`h, t );          //  u  h  w  up

  // Lie_Check(G,x, "Lie_RightMultiplyByTorus");
end procedure;


forward  Lie_RightMultiplyByWeyl;

Lie_RightMultiplyByUnipTerm := procedure( G, ~x, term : normalise := true)
  R := RootDatum(G);  k := BaseRing(G);
  N := NumPosRoots(R);

  if term[2] eq 0 then
    ; // do nothing, but don't return yet

  elif x`w  eq []  
   and x`h  eq Torus_Identity(R,k)
   and x`up eq [k|0: i in [1..N]]
   and term[1] le N then
                                                 //  u term
    x`u  := Unip_Product( G, x`u,  [term] : normalise:=normalise );
                                                 //  u 

  elif term[1] le N then                         //  u  h  w  up term

    x`up := Unip_Product( G, x`up, [term] : normalise:=normalise );     
                                                 //  u  h  w  up
  else
    r := term[1]-N;  t := term[2];               //  u  h  w  up  x_r(t^-1)  h_r(-t)  n_r  x_r(t^-1)
    x`up := Unip_Product( G, x`up, [ < r, t^(-1) > ]  : normalise:=false );
                                                 //  u  h  w  up  h_r(-t)  n_r  x_r(t^-1)

    th,sdot := Weyl_NonsimpleReflection(R,k,r);  //  u  h  w  up  h_r(-t) th  sdot_r  x_r(t^-1)
    
    Lie_RightMultiplyByTorus( G, ~x, 
                Torus_Product( R, k, Torus_Term_Rt( R, k, r, -t ), th ) );
                                                 //  u  h  w  up  sdot_r  x_r(t^-1)
    Lie_Normalise( G, ~x );
    Lie_RightMultiplyByWeyl( G, ~x, sdot );      //  u  h  w  up  x_r(t^-1)

    x`up := Unip_Product( G, x`up, [ < r, t^(-1) > ] : normalise:=false );
                                                 //  u  h  w  up
  end if;

  if normalise then 
    Lie_Normalise( G, ~x );
  end if;
  //assert Lie_Check(R,k,x, "unipterm");
end procedure;

Lie_RightMultiplyByUnip := procedure( G, ~x, u )
  // assume x normalised!!!
  R := RootDatum(G);
  k := BaseRing(G);
  N := NumPosRoots(R);

  if IsEmpty(u) then
    return;

  elif x`w  eq []  
   and x`h  eq Torus_Identity(R,k)
   and x`up eq [k|0: i in [1..N]] 
   and (Category(Universe(u)) ne SetCart    // then it is a sequence of field elts            \ make sure all roots
        or forall{t:t in u|t[1] in [1..N]}) // then it is a sequence of pairs <r,t> = x_r(t)  / are positive!
   then

    x`u  := Unip_Product( G, x`u,  u : normalise );

  elif Category(Universe(u)) ne SetCart then // then it is a sequence of field elts

    x`up := Unip_Product( G, x`up, u : normalise );

  elif Category(Universe(u)) eq SetCart then // then it is a sequence of pairs <r,t> = x_r(t)

    j := 0;
    while exists(i){ i : i in [j+1..#u] | u[i][1] gt N } do 
        // multiply the next block of positive root elements
        x`up := Unip_Product( G, x`up, u[j+1..i-1] : normalise );
        // multiply the next negative root element
        Lie_RightMultiplyByUnipTerm( G, ~x, u[i] );
        j := i;
    end while;
    // multiply the last block of positive root elements
    x`up := Unip_Product( G, x`up, u[j+1..#u] : normalise );

  else
    error "ERROR in GrpLie.m:Lie_RightMultiplyByUnip: we never should get here";
  end if;

  Lie_Normalise( G, ~x );

  //assert Lie_Check(G,x, "unip");
end procedure;





Lie_RightMultiplyByWeylTerm := procedure( G, ~x, r )
  R := RootDatum(G);  k := BaseRing(G);  N := NumPosRoots( R );
  order := collectionOrder(G);
  d := Dimension(R);
  if not ISA(Category(R),RootDtmSprs) then
    roots   := Roots(R);
    coroots := Coroots(R);
    ChangeUniverse(~roots,RSpace(Integers(),d));
    ChangeUniverse(~coroots,RSpace(Integers(),d));
  end if;

  if r gt N then
    r -:= N;
    Lie_RightMultiplyByTorus( G, ~x, Torus_Term_Rt(R,k,r,k!-1) );
  end if;
                                                 // u  h  w  up  n_r
  a, x`up := Unip_Separate( G, x`up, [ i eq r : i in [1..N] ] );
  if Unip_IsOne( R,k,a ) then 
    t := k!0;
  else 
    t := (Unip_IsNormalised(a)) select a[r] else a[1][2];
  end if;                                        //  u  h  w  x_r(t) up n_r

  if ISA(Category(R),RootDtmSprs) then
  WeylActionOnUnipSprs( R, k, ~x`up, [r], order );   //  u  h  w  x_r(t)  n_r  up
  else
  WeylActionOnUnip( R, k, ~x`up, [r], order, roots, coroots );   //  u  h  w  x_r(t)  n_r  up
  end if;
  
  if t ne 0 and x`filter[r] then                 //  u  h  w  x_-r(t^-1)  h_r(-t^-1)  x_r(-t^-1)  up
//  x`up := Unip_Product( G, [ <r, -t^(-1)> ], x`up );
    Insert(~x`up, 1, <r, -t^(-1)>);
                                                 //  u  h  w  x_-r(t^-1)  h_r(-t^-1)  up
    a := [< r+N, t^(-1) >];                      //  u  h  w  a  h_r(-t^-1)  up
    if ISA(Category(R),RootDtmSprs) then
    WeylActionOnUnipSprs( R, k, ~a, x`w, order : left );    
    else
    WeylActionOnUnip( R, k, ~a, x`w, order, roots, coroots : left );    
    end if;
                                                  //  u  h  a  w  h_r(-t^-1)  up
    TorusActionOnUnip( R, k, ~a, x`h : left );   //  u  a  h  w  h_r(-t^-1)  up
//    x`u := Unip_Product( G, x`u, a );            //  u  h  w  h_r(-t^-1)  up
    x`u := Unip_ToList(R, k, x`u, order );
    Insert(~x`u, #x`u+1, #x`u, a );              //  u  h  w  h_r(-t^-1)  up
    ht := Torus_Term_Rt( R, k, r, k!(-t^(-1)) ); //  u  h  w  ht  up
    WeylActionOnTorus( R, k, ~ht, x`w : left );  //  u  h  ht  w  up
    x`h := Torus_Product( R, k, x`h, ht );       //  u  h  w  up
//    Lie_Normalise( G, ~x );

  else                                           //  u  h  w  x_r(t)  n_r  up
    if t ne 0 then
      a := [< r, t >];                           //  u  h  w  a  n_r  up
      if ISA(Category(R),RootDtmSprs) then
      WeylActionOnUnipSprs( R, k, ~a, x`w, order : left );  
      else
      WeylActionOnUnip( R, k, ~a, x`w, order, roots, coroots : left );  
      end if;
                                                 //  u  h  a  w  n_r  up
      TorusActionOnUnip( R, k, ~a, x`h : left ); //  u  a  h  w  n_r  up
//    x`u := Unip_Product( G, x`u, a );
      Insert(~x`u, #x`u+1, #x`u, a );
    end if;                                      //  u  h  w  n_r  up

    len := #x`w; W := CoxeterGroup(R); Wfp := CoxeterGroup(GrpFPCox,W); 
    if r le Rank( R ) then
      x`w := Eltseq( Wfp!(x`w) * Wfp![r] );
      x`filter := [ Booleans() | (i eq r) select (not x`filter[i]) else x`filter[i^W.r] : 
                    i in [1..N] ];
    else
      h, w := Weyl_NonsimpleReflection( R, k, r );
      WeylActionOnTorus( R, k, ~h, x`w : left );
      x`h := Torus_Product( R, k, x`h, h );
      x`w := Eltseq( Wfp!(x`w)*Wfp!w );
      x`filter := PosToNegFilter( R, x`w );
    end if;

    if #x`w lt len then                          //  u  h  w  h_r(-1)  up
      ht := Torus_Term_Rt( R, k, r, k!(-1) );    //  u  h  w  ht  up
      WeylActionOnTorus( R, k, ~ht, x`w : left );//  u  h  ht  w  up
      x`h := Torus_Product( R, k, x`h, ht );     //  u  h  w  up
    end if;

  end if;

  //assert Lie_Check(R,k,x,"weyl");
end procedure;

Lie_RightMultiplyByWeyl := procedure( G, ~x, w )
  Lie_UnipUnnormalise( G, ~x );
  for r in w do
    Lie_RightMultiplyByWeylTerm( G, ~x, r );
  end for;
  Lie_UnipNormalise( G, ~x );

  //assert Lie_Check(R,k,x,"weyl");
end procedure;




Lie_RightMultiplyByBruhat := procedure( G, ~x, y )
//  Lie_UnipUnnormalise( G, ~x );
//  Lie_UnipUnnormalise( G, ~y );

  //cpu := Cputime();
    Lie_RightMultiplyByUnip(  G, ~x, y`u );
  //"Unip :", Cputime()-cpu;

  //cpu := Cputime();
    Lie_RightMultiplyByTorus( G, ~x, y`h );
  //"Torus:", Cputime()-cpu;

  //cpu := Cputime();
    Lie_RightMultiplyByWeyl(  G, ~x, y`w );
  //"Weyl :", Cputime()-cpu;

  //cpu := Cputime();
    Lie_RightMultiplyByUnip(  G, ~x, y`up );
  //"Unip :", Cputime()-cpu;

  //assert Lie_Check(G,x,"bruhat");
end procedure;




// ------------------------------------------------------------------
//
// Normalisation
//

intrinsic IsNormalised( x::GrpLieElt ) -> BoolElt
{True iff x is normalised}
  return not assigned x`List;
end intrinsic;

intrinsic IsNormalized( x::GrpLieElt ) -> BoolElt
{True iff x is normalized}
  return not assigned x`List;
end intrinsic;

copyelt := function( x : newparent:=Parent(x) )
  y := CreateLieGroupElement( newparent );
  if assigned x`List then
    y`List := x`List;
  else
    y`u := x`u;  y`h := x`h;
    y`w := x`w;  y`up := x`up;  y`filter := x`filter;
  end if;
  return y;
end function;

intrinsic Normalise( ~x::GrpLieElt )
{Normalise x}
  if not assigned x`List then return; end if;
  G := Parent(x);  R := RootDatum(G);  k := BaseRing(G);
  list := x`List;
  if #list eq 0 then
    x := normId(G);  return;
  elif Category(list[1]) eq GrpLieElt then
    x := copyelt( list[1] );  pos := 2;
  else
    x := normId(G);  pos := 1;
  end if;
  
//  Lie_UnipUnnormalise( G, ~x ); // REMOVE
  while pos le #list do
    term := list[pos];
    if Category(term) eq ModTupFldElt then
      Lie_RightMultiplyByTorus( G, ~x, term );
    elif Category(term) eq Tup and #term eq 2 then
      Lie_RightMultiplyByUnipTerm( G, ~x, term );
    elif Category(term) eq RngIntElt then
      if term gt Rank(R) then
        y := normId(G);
        Lie_RightMultiplyByWeylTerm( G, ~y, term );
//        print "c1*",y`u,y`h,y`w,y`up;
        Lie_RightMultiplyByTorus( G, ~x, y`h );
        Lie_RightMultiplyByWeyl( G, ~x, y`w );
      else
        Lie_RightMultiplyByWeylTerm( G, ~x, term );
      end if;
    elif Category(term) eq SeqEnum then
      term := Unip_ToList( R, k, term, collectionOrder(G) );
      Lie_RightMultiplyByUnip( G, ~x, term );
    elif Category(term) eq GrpLieElt then
      Lie_RightMultiplyByBruhat( G, ~x, term );
    else
      error "Entry ", pos, " in list not allowed";
    end if;
    pos +:= 1;
    // control length of x`up
  end while;
  Lie_UnipNormalise( G, ~x );
end intrinsic;


// Normalize defined at c-level as synonym for Normalise
intrinsic Normalise( x::GrpLieElt ) -> GrpLieElt
{Normalise x}
  Normalise( ~x );
  return x;
end intrinsic;


procedure unnormalise_internal( ~x : keep_unip_normalised:=false )
  G := Parent(x);
  R := RootDatum(G);  k := BaseRing(G);
  if assigned x`List then return; end if;
  if not keep_unip_normalised then  
    Lie_UnipUnnormalise( G, ~x );
  end if;
  list := [* *];
  if not Unip_IsOne( R, k, x`u ) then
    Append( ~list, x`u );
  end if;
  if  x`h ne Torus_Identity(R,k) then
    Append( ~list, x`h );
  end if;
  for r in x`w do Append( ~list, r ); end for;
  if not Unip_IsOne( R, k, x`up ) then
    Append( ~list, x`up );
  end if;
  x := CreateLieGroupElement(G);
  x`List := list;
end procedure;

// SHOULD UNNORMALISE BE DOCUMENTED?
intrinsic Unnormalise( ~x::GrpLieElt )
{Convert x to an unnormalised element}
    unnormalise_internal( ~x );
end intrinsic;

intrinsic Unnormalize( ~x::GrpLieElt )
{Convert x to an unnormalised element}
    unnormalise_internal( ~x );
end intrinsic;

intrinsic Unnormalise( x::GrpLieElt ) -> GrpLieElt
{An unnormalised element equal to x}
    y := copyelt( x );
    unnormalise_internal( ~y );
    return y;
end intrinsic;

intrinsic Unnormalize( x::GrpLieElt ) -> GrpLieElt
{An unnormalised element equal to x}
    y := copyelt( x );
    unnormalise_internal( ~y );
    return y;
end intrinsic;



// ------------------------------------------------------------------
//
// Element deconstruction
//
intrinsic Bruhat( g::GrpLieElt ) -> GrpLieElt, GrpLieElt, GrpLieElt, GrpLieElt
{The bruhat decomposition of g}
  Normalise( ~g );
  G := Parent(g);
  u := normId(G);  u`u := g`u;
  h := normId(G);  h`h := g`h;
  w := normId(G);  w`w := g`w;  w`filter := g`filter;
  up := normId(G); up`u := g`up;
  return u, h, w, up;
end intrinsic;

intrinsic Eltlist( x::GrpLieElt ) -> GrpLieElt
{The list corresponding to x}
  y := Unnormalise( x );
  return y`List;
end intrinsic;

intrinsic MultiplicativeJordanDecomposition( x::GrpLieElt ) -> GrpLieElt, GrpLieElt
{The multiplicative Jordan decomposition of x}
  rho := StandardRepresentation( Parent(x) : NoWarning );
  inv := RowReductionHomomorphism( rho );
  S, U := MultiplicativeJordanDecomposition( rho(x) );
  return inv(S), inv(U);
end intrinsic;

intrinsic IsSemisimple( x::GrpLieElt ) -> BoolElt
{True iff x is semisimple}
  return IsSemisimple( StandardRepresentation(Parent(x):NoWarning)(x) );
end intrinsic;

intrinsic IsUnipotent( x::GrpLieElt ) -> BoolElt
{True iff x is unipotent}
  G := Parent(x);  rho := StandardRepresentation( G :NoWarning );
  deg := Degree( BaseRing(Codomain(rho)), BaseRing(G) );
  return IsUnipotent( (rho(x))^deg );
end intrinsic;




// ------------------------------------------------------------------
//
// Basic operations
//

intrinsic TorusTerm( G::GrpLie, r::RngIntElt, t::RngElt ) -> GrpLieElt
{The torus term h_r(t) in G}
  require IsUnit(BaseRing(G)!t) : "The ring element must be invertible";
  return elt< G | Torus_Term_Rt( RootDatum(G), BaseRing(G), r, t ) >;
end intrinsic;

listInverse := function( G, list )
  R := RootDatum(G);  k := BaseRing(G);
  inv := [**];
  pos := #list;
  while pos ge 1 do
    term := list[pos];
    if Category(term) eq ModTupFldElt then
      Append( ~inv, Torus_Inverse( R, k, term ) );
    elif Category(term) eq Tup and #term eq 2 then
      Append( ~inv, Unip_ListInverse( R, k, [ term ] )[1] );
    elif Category(term) eq SeqEnum then
      if Category(term[1]) eq Tup then 
        Append( ~inv, Unip_ListInverse( R, k, term ) );
      else
        Append( ~inv, Unip_Inverse( G, term ) );
      end if;
    elif Category(term) eq RngIntElt then
      inv cat:= Weyl_Inverse( R, k, [ term ] );
    elif Category(term) eq GrpLieElt then
      Append( ~inv, Inverse( term ) );
    else
      error "Entry in list not allowed";
    end if;
    pos -:= 1;
  end while;
  return inv;
end function;

intrinsic Inverse( x::GrpLieElt ) -> GrpLieElt
{The inverse of x}
  G := Parent(x);
  y := copyelt(x);
  unnormalise_internal( ~y : keep_unip_normalised );
  y`List := listInverse( G, y`List );
  if G`Normalise or IsNormalised( x ) then
    Normalise( ~y );
  end if;
  return y;
end intrinsic;

intrinsic '*'( x::GrpLieElt, y::GrpLieElt ) -> GrpLieElt
{The product of x and y}
  G := Parent(x);  E := BaseRing(G);
  H := Parent(y);  F := BaseRing(H);

  require RootDatum(G) eq RootDatum(H) : "Elements must be in groups with the same root datum";

  /* first, take care of trivial cases */
  if   (IsNormalised(x) and x eq 1) then return y;
  elif (IsNormalised(y) and y eq 1) then return x;
  end if;

  if Category(E) ne Category(F) or E ne F then
    k := CoveringStructure( BaseRing(G), BaseRing(H) );
    C := BaseExtend( G, k );
    x := CoerceGrpLie( C, x );  y := CoerceGrpLie( C, y );
  else
    C := G;
  end if;
  xlist := (assigned x`List) select x`List else [* x *];
  ylist := (assigned y`List) select y`List else [* y *];
  z := CreateLieGroupElement( C );
  z`List := xlist cat ylist;
  if IsNormalised(x) and IsNormalised(y) then
    Normalise( ~z );
  end if;
  return z;
end intrinsic;

intrinsic 'eq'( x::GrpLieElt, y ::GrpLieElt ) -> BoolElt
{True iff x and y are equal}
  ok, G := ExistsCoveringStructure( Parent(x), Parent(y) );
  require ok : "Elements must be in the same group";
  x := G!x;  y := G!y;
  R := RootDatum(Parent(x));  k := BaseRing(Parent(x));
  Normalise( ~x );  Normalise( ~y );
  return x`u eq y`u and x`up eq y`up and
    Torus_IsEqual(R,k,x`h,y`h) and Weyl_IsEqual(R,x`w,y`w);
end intrinsic;

intrinsic 'eq'( x::GrpLieElt, y ::RngIntElt ) -> BoolElt
{True iff x and y are equal}
  return x eq Parent(x)!y;
end intrinsic;

intrinsic 'eq'( x::RngIntElt, y ::GrpLieElt ) -> BoolElt
{True iff x and y are equal}
  return Parent(y)!x eq y;
end intrinsic;

intrinsic '^'( x::GrpLieElt, n::RngIntElt ) -> GrpLieElt
{The nth power of x}
  if n eq 0 then
    return Parent(x)!1;
  elif n gt 0 then
    power := x;
  else
    power := Inverse(x);  n := -n;
  end if;

  ret := Parent(x)!1;
  while n gt 1 do
    if n mod 2 eq 1 then
      ret *:= power;
    else
    end if;
    n div:= 2;
    power *:= power;
  end while;
  return ret*power;
end intrinsic;

intrinsic PrintGrpLieElt( x::GrpLieElt, level::MonStgElt )
{Internal.  Print x at the given level}
  // first, make sure we have a complete element.
  if IsNormalised( x ) then
    incomplete := not assigned x`u;
  else
    incomplete := not assigned x`List;
  end if;
  if incomplete then
    printf "WARNING: GrpLieElt is incomplete. Use elt<G|...> to create elements of a group of Lie type";
    return;
  end if;
  //
  // Possible Print levels: "Minimal", "Default", "Maximal", "Debug", "Magma"
  //
  if level eq "Magma" then // "Magma" level
    first_weyl := true;
    list := Eltlist(x);
    printf "elt< %o |",  Sprint( Parent(x), level );
    if #list gt 0 then
      for i in [1..#list-1] do
        if Category(list[i]) eq RngIntElt then
          // it is especially nasty if very long weyl elements are printed 
          // a single term per row. print all wayl terms in one line
          if first_weyl then
            printf "\n%o,", Sprint(list[i], level);
            first_weyl := false;
          else
            printf "%o,", Sprint(list[i], level);
          end if;
        else
          printf "\n%o,", Sprint(list[i], level);
          first_weyl := true;
        end if;
      end for;
      printf "\n%o", Sprint(list[#list], level);
    end if;
    printf " /**/ >";
  else
    R := RootDatum(Parent(x));  k := BaseRing(Parent(x));
    if IsNormalised( x ) then
      list := [* x`u, x`h *] cat Seqlist(x`w) cat [* x`up *];
    else
      list := x`List;
    end if;
    one := true;
    for term in list do
      if ISA( Category(term), ModTupRngElt ) then
        if term ne Torus_Identity(R,k) then
          Torus_Print(R, k, term);  one := false;
        end if;
      elif Category(term) eq Tup and #term eq 2 then
        Unip_Print(R, k, [term], collectionOrder(Parent(x)) );  one := false;
      elif Category(term) eq RngIntElt then
        Weyl_Print(R, [term] );  one := false;
      elif Category(term) eq SeqEnum then
        if not Unip_IsOne(R,k,term) then
          Unip_Print( R, k, term, collectionOrder(Parent(x)) );  one := false;
        end if;
      elif Category(term) eq GrpLieElt then
        $$( term, level );  one := false;
      else
        error "Entry in list not allowed";
      end if;
    end for;
    if one then printf "1"; end if;
  end if;
end intrinsic;

intrinsic CoxeterElement( G::GrpLie ) -> GrpLieElt
{The Coxeter element of G}
  c := CoxeterElement( WeylGroup( GrpFPCox, G ) );
  x := CreateLieGroupElement(G);
  x`List := Seqlist(Eltseq(c));
  if G`Normalise then  Normalise( ~x );  end if;
  return x;
end intrinsic;

intrinsic CoxeterNumber( G::GrpLie ) -> GrpLieElt
{The Coxeter number of G}
  return CoxeterNumber( WeylGroup(G) );
end intrinsic;

intrinsic AlgebraicGenerators( G::GrpLie : Type := "Root" ) -> SetEnum
{A set containing the algebraic group generators for G}
  k := BaseRing(G);
  R := RootDatum(G); N := NumPosRoots(R);
  torusGens := function()
    id := Torus_Identity(R,k);  
    z := (not IsFinite(k)) select 2 else PrimitiveElement(k);  
    ret := [G|];
    if IsSimplyConnected(G) or (IsFinite(k) and #k eq 2) then return ret;  end if;
    for r in [1..Rank(G)] do
      v := id;  v[r] := z;
      Append( ~ret, elt<G|v> );
    end for;
    return ret;
  end function;
  require IsField(k) : "Base ring must be a field";
  case Type:
  when "Root":
    rank := SemisimpleRank(G);
    return [G| elt<G|<r,1>> : r in [1..rank] cat [N+1..N+rank] ] cat torusGens();
  when "HighRoot":
    rank := SemisimpleRank(G);
    return [G| elt<G|<r,1>> : r in [1..rank] cat [2*N] ] cat torusGens();
  when "Steinberg":
    error "Not yet implemented";
  else
    error "Invalid Type";
  end case;
end intrinsic;

intrinsic NumberOfAlgebraicGenerators( G::GrpLie ) -> RngIntElt
{The number of algebraic group generators for G}
  return 2*NumPosRoots(G)+Rank(G);
end intrinsic;

intrinsic Nalggens( G::GrpLie ) -> RngIntElt
{The number of algebraic group generators for G}
  return 2*NumPosRoots(G)+Rank(G);
end intrinsic;

intrinsic Generators( G::GrpLie : Type := "Root" ) -> SetEnum
{A set containing the generators for G}
  k := BaseRing(G);
  require IsField(k) : "Base ring must be a field";
  require IsFinite(k) : "Base ring must be a finite field";
  require IsSplit(G) : "Only implemented for split groups";
  R := RootDatum(G); N := NumPosRoots(R);
  torusGens := function()
    id := Torus_Identity(R,k);  
    z := PrimitiveElement(k);  ret := [G|];

    if (IsSimplyConnected(G)) or #k eq 2 then
	  /* SimplyConnected implies semisimple */
	  return ret;
	end if;
	
    for r in [1..Rank(G)] do
      v := id;  v[r] := z;
      Append( ~ret, elt<G|v> );
    end for;
    return ret;
  end function;
  case Type:
  when "Root":
    basis := [ k.1^i : i in [0..Degree(k)-1] ];
    gens := [];  // should be a set
    for r in [1..SemisimpleRank(G)] do
      for b in basis do
        Append( ~gens, elt<G|<r,b>> );
        Append( ~gens, elt<G|<r+N,b>> );
      end for;
    end for;
    gens cat:= torusGens();
    return gens;
  when "HighRoot":
    basis := [ k.1^i : i in [0..Degree(k)-1] ];
    gens := [];  // should be a set
    for r in [1..SemisimpleRank(G)] do
      for b in basis do
        Append( ~gens, elt<G|<r,b>> );
      end for;
    end for;
    for b in basis do
      Append( ~gens, elt<G|<2*N,b>> );
    end for;
    gens cat:= torusGens();
    return gens;
  when "Steinberg":
    error "Not yet implemented";
  else
    error "Invalid Type";
  end case;
end intrinsic;

intrinsic NumberOfGenerators( G::GrpLie ) -> RngIntElt
{The number of generators for G}
  k := BaseRing(G);
  require IsField(k) : "Base ring must be a field";
  require IsFinite(k) : "Base ring must be a finite field";
  return 2*NumPosRoots(G)*Degree(k) + Rank(G);
end intrinsic;

intrinsic Reflection( G::GrpLie, r::RngIntElt  ) -> GrpLieElt
{The representative of the rth reflection in G}
  x := CreateLieGroupElement( G );
  x`List := Seqlist( ReflectionWord( RootDatum(G), r ) );
  if G`Normalise then  Normalise( ~x );  end if;
  return x;
end intrinsic;

intrinsic Reflections( G::GrpLie ) -> GrpLieElt
{The representatives of the reflections in G}
  return [ Reflection( G, r ) : r in [1..NumPosRoots(G)] ];
end intrinsic;



// ------------------------------------------------------------------
//
// Centre and central product decomposition
//
intrinsic CentrePolynomials( G::GrpLie ) -> SetEnum
{The polynomial equations that determine if a torus element of G is in the
centre of G}
  d := Rank( G );  n := SemisimpleRank( G );
  A := Matrix(Integers(),SimpleRoots( G ));
  P<[h]> := PolynomialRing( BaseRing(G), d );
  return { &*[ P | h[i]^A[j,i] : i in [1..d] | A[j,i] gt 0 ] -
           &*[ P | h[i]^(-A[j,i]) : i in [1..d] | A[j,i] lt 0 ] 
           : j in [1..n] };
end intrinsic;

intrinsic CenterPolynomials( G::GrpLie ) -> SetEnum
{The polynomial equations that determine if a torus element of G is in the
center of G}
  return CentrePolynomials( G );
end intrinsic;

/*
 *  intrinsic IsCentral( x::GrpLieElt ) -> BoolElt
 *  {True iff x is in the centre of its parent group}
 *    if x eq 1 then  return true;  end if;
 *    u, h, wdot, up := Bruhat( x );
 *    if u ne 1 or wdot ne 1 or up ne 1 then
 *      return false;
 *    else   
 *      pols := CentrePolynomials( Parent( x ) );
 *      return forall{ p : p in pols | Evaluate( p, Eltseq( Eltlist( x )[1] ) ) eq 0 };
 *    end if;
 *  end intrinsic;
 */


intrinsic IsCentral( x::GrpLieElt ) -> BoolElt
{True iff x is in the centre of its parent group}
  // the 'eq' intrinsic does the bruhat decomposition anyway, so
  // we can safely (from efficiency point of view) do it here.
  u, h, wdot, up := Bruhat( x );

  return      x eq 1 
      or (    u eq 1 and                                                                         
           wdot eq 1 and                                                                         
             up eq 1 and (forall{ p : p in pols | Evaluate( p, vals ) eq 0 }                     
                            where pols is CentrePolynomials( Parent( h ) )                       
                            where vals is Eltseq( Eltlist( h )[1] ) )            );              
end intrinsic;


intrinsic ConnectedCentre( G::GrpLie ) -> GrpLie
{The connected component of the centre of G}
  return GroupOfLieType( Radical(RootDatum(G)), BaseRing(G) );
end intrinsic;
intrinsic ConnectedCenter( G::GrpLie ) -> GrpLie
{The connected component of the centre of G}
  return ConnectedCentre(G);
end intrinsic;

intrinsic CentralProductDecomposition( G::GrpLie ) -> SeqEnum[GrpLie], GrpLie
{The central product decomposition of G}
  D, Z := CentralSumDecomposition( RootDatum(G) );
  k := BaseRing(G);
  return [ GroupOfLieType( R, k ) : R in D ], GroupOfLieType( Z, k );
end intrinsic;

// ------------------------------------------------------------------
//
// Conjugation
//

intrinsic '^:='( ~x::GrpLieElt, y::GrpLieElt )
{Replace x with x ^ y}
  x := Inverse(y) * x * y;
end intrinsic;



intrinsic '^'( x::GrpLieElt, y::GrpLieElt ) -> GrpLieElt
{Conjugate of x by y}
  return Inverse(y) * x *y;
//  z := copyElt(x);
//  z ^:= y;
//  return z;
end intrinsic;


intrinsic Commutator( x::GrpLieElt, y::GrpLieElt ) -> GrpLieElt
{Commutator x^-1 * y^-1 * x * y}
  return Inverse(x) * x^y;
end intrinsic;
















// ==================================================================
//
// New from old
//
// ==================================================================

intrinsic SubsystemSubgroup( G::GrpLie, simples::SeqEnum[RngIntElt] ) -> GrpLie
{The subsystem subgroup of G with the given simples}
  return GroupOfLieType( sub< RootDatum(G) | simples >, BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;

intrinsic SubsystemSubgroup( G::GrpLie, gens::SetEnum[RngIntElt] ) -> GrpLie
{The subsystem subgroup of G with the given simples}
  return GroupOfLieType( sub< RootDatum(G) | gens >, BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;

intrinsic StandardMaximalTorus( G::GrpLie ) -> GrpLie
{The standard maximal torus of G}
  return GroupOfLieType( sub< RootDatum(G) | [] >, BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;

intrinsic SolubleRadical( G::GrpLie ) -> GrpLie
{The soluble radical of G}
  return GroupOfLieType( Radical( RootDatum(G) ), BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;

intrinsic TrivialSubgroup( G::GrpLie ) -> GrpLie
{The trivial subgroup of G}
  R := RootDatum(G);
  U := sub< RootSpace(R) | >;
  V := sub< CorootSpace(R) | >;
  S := sub< R | U, V >;
  return GroupOfLieType( S, BaseRing(G) );
end intrinsic; 

/*intrinsic CentralProductDecomposition( G::GrpLie ) -> SeqEnum
{The central product decomposition of G}
  require IsSemisimple(G) : "The group must be semisimple";
  return [ GroupOfLieType( R, BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method ) :
    R in DirectSumDecomposition( RootDatum(G) ) ];
end intrinsic;*/

intrinsic DirectProduct( G::GrpLie, H::GrpLie ) -> GrpLie
{The direct product of G and H}
  kG := BaseRing(G);  kH := BaseRing(H);
  require ExistsCoveringStructure(kG,kH) and kG eq kH :
    "The base rings must be the same";
  return GroupOfLieType( DirectSum( RootDatum(G), RootDatum(H) ), kG :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;

intrinsic Dual( G::GrpLie ) -> GrpLie
{The dual group of G}
  return GroupOfLieType( Dual( RootDatum(G) ), BaseRing(G) :
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;


// ------------------------------------------------------------------
//
// Coercions.
//


intrinsic InternalExistsCoveringStructureGrpLie( G::GrpLie, H::GrpLie ) -> 
  BoolElt
{Intrinsic for internal use only}
  return InternalExistsCoveringStructureRootDatum( RootDatum(G), RootDatum(H) )
     and ExistsCoveringStructure( BaseRing(G), BaseRing(H) );
end intrinsic;

intrinsic InternalCoveringStructureGrpLie( G::GrpLie, H::GrpLie ) -> GrpLie
{Intrinsic for internal use only}
  return GroupOfLieType( 
    InternalCoveringStructureRootDatum( RootDatum(G), RootDatum(H) ), 
    CoveringStructure( BaseRing(G), BaseRing(H) ) );
end intrinsic;

intrinsic 'subset'( G::GrpLie, H::GrpLie ) -> BoolElt
{True if G1 is a subset of G2}
  require ExistsCoveringStructure( G, H ) : "No covering structure";
  return RootDatum(G) subset RootDatum(H) and 
    BaseRing(G) subset BaseRing(H);
end intrinsic;

intrinsic IsCoercibleGrpLie( G::GrpLie, g::GrpLieElt ) -> BoolElt, GrpLieElt
{Internal intrinsic}

  H := Parent(g);

  if RootDatum(G) eq RootDatum(H) and BaseRing(G) cmpeq BaseRing(H) then
    if collectionOrder(G) eq collectionOrder(H) then
      return true, copyelt(g:newparent:=G);
    else
      return true, elt<G|Eltlist(g)>;
    end if;
  end if;

  ok, T, _, injG, injg := 
    existsCoveringStructure( RootDatum(G), RootDatum(H) );
  if not ok then  return false,_;  end if;
  
  isCoercibleIndex := function( r )
    r := injg[r];
    r := Position( injG, r );
    if r eq 0 then  return false, _;
    else  return true, r;
    end if;
  end function;
  
  WT := CoxeterGroup( T );
  WG := ReflectionSubgroup( WT, injG[[1..SemisimpleRank(G)]] );
  Wg := CoxeterGroup( RootDatum(H) );
  injg := hom< Wg->WT | [ Reflection(WT,injg[i]) : i in [1..Rank(Wg)] ] >;
  isCoerciblePerm := function( w )
    w := injg( w );
    if w in WG then  return true, PermToWord( WG, w : Local );
    else  return false, _;
    end if;
  end function;

  if IsTwisted(G) then
    c := OneCocycle(G);
    O := UntwistedOvergroup(G);
    ok, ng := IsCoercibleGrpLie(O,g);
    if ok and IsInTwistedForm( ng, c ) then
        return true, elt<G|Eltlist(ng)>;
    else 
        return false, _; 
    end if;
  end if;
  
  k := BaseRing( G );  V := RSpace( k, Rank(G) );
  list := Eltlist( g );
  ret := G!1;
  for t in list do
    case Category( t ) :
    when Tup :
      ok1, r := isCoercibleIndex( t[1] );
      ok2, a := IsCoercible( k, t[2] );
      if not (ok1 and ok2) then  return false, _;  end if;
      ret *:= elt<G|<r,a>>;
    when SeqEnum :
      newt := [];
      if Category(Universe(t)) eq SetCart then
        for s in t do
          ok1, r := isCoercibleIndex( s[1] );
          ok2, a := IsCoercible( k, s[2] );
          if not (ok1 and ok2) then  return false, _;  end if;
          Append( ~newt, <r,a> );
        end for;
      else
        ok, u := CanChangeUniverse( t, k );
        if not ok then  return false, _;  end if;
        for r in [1..#u] do
          if u[r] ne 0 then
            ok, s := isCoercibleIndex( r );
            if not ok then  return false, _;  end if;
            Append( ~newt, <s,u[r]> );
          end if;
        end for;
      end if;
      ret *:= elt<G|newt>;
    when ModTupRngElt,ModTupFldElt:
      ok, newt := IsCoercible( V, t );
      if not ok then  return false, _;  end if;
      ret *:= elt<G|newt>;
    when RngIntElt:
      ok, r := isCoercibleIndex( t );
      if not ok then  return false, _;  end if;
      ret *:= elt<G|r>;
    when GrpFPCoxElt:
      for r in Eltseq( t ) do
        ok, s := isCoercibleIndex( t );
        if not ok then  return false, _;  end if;
        ret *:= elt<G|s>;
      end for;
    when GrpPermElt :
      ok, w := isCoerciblePerm( t );
      if not ok then  return false, _;  end if;
      ret *:= elt<G|w>;
    end case;
  end for;
  return true, ret;
end intrinsic;

intrinsic CoerceGrpLie( H::GrpLie, g::GrpLieElt ) -> GrpLieElt
{g interpreted as element of H}
  ok, g := IsCoercibleGrpLie( H, g );
  require ok : "Illegal coercion";
  return g;
end intrinsic;


intrinsic CoercionGrpLie( G::GrpLie, H::GrpLie ) -> Map
{Coercion map from G to H}
  return  hom< G->H | g :-> CoerceGrpLie(H,g) >;
end intrinsic;

intrinsic BaseExtend( G::GrpLie, K::Rng ) -> GrpLie, Map
{Returns a group of Lie type of the same type with a larger base ring}
  k := BaseRing(G);
  ex, co := ExistsCoveringStructure(k,K);
  require ex and co eq K : "K must be an overstructure of the base ring of G";
  H := GroupOfLieType( RootDatum(G), K : 
    Normalising:=IsNormalising(G), Method:=G`Method );
  return H, CoercionGrpLie( G, H );
end intrinsic;

intrinsic ChangeRing( G::GrpLie, K::Rng ) -> GrpLie
{Returns a group of Lie type of the same type over a different ring}
  return GroupOfLieType( RootDatum(G), K : 
    Normalising:=IsNormalising(G), Method:=G`Method );
end intrinsic;











function internalCreateTwistedGrpLie(R,k,K,c,normalising,Method)
    
    // don't think we need that for the twisted grps:
        // precompute coreflection matrices for simple roots.
        // this is essential for multiplication
        // n := Rank(R);
        // for i in [1..n] do _:=reflMat(R,i,"Standard",true); end for;

    J  := [ GammaOrbitsRepresentatives(R,i) : i in [1..NumPosRoots(RelativeRootDatum(R))]];
    pO := PositiveGammaOrbitsOnRoots(R);

    coll := [];
    for j in J, r in j do
        _ := exists(o){o : o in pO | r in o}; 
        coll cat:= Setseq(o);
        Exclude(~pO,o);
    end for;

    G := CreateLieGroup(R,k,K,c,normalising);
    
    G`collectionOrder := coll;

    // these later via varargs
    choose_method(G, Method);
    
    computeHalls( ~G );

    return G;

end function;

intrinsic IsTwisted( G::GrpLie ) -> BoolElt
{Returns true iff the group of Lie type is twisted}
    return IsTwisted(RootDatum(G));
end intrinsic;

intrinsic TwistedGroupOfLieType(R::RootDtm, k::Rng, K::Rng : Normalising:=true, 
  Method:=defaultMethod ) -> GrpLie
{}  // inherit comment

    gamma     := R`GammaAction`gamma;

    // Compute gamma2 = Aut_k(K)
    try 
      gamma2, m2, m3 := AutomorphismGroup( K, k );
    catch e
      error "Unable to compute field automorphism group";
    end try;
    if not ISA(Category(m2), Map) then  
      m2 := m3;  // some versions have an extra returned value
    end if;

    // IsIsomorphic requires gamma2 to be a permutation group.
    // Since the group has to be small, use the regular repn.
    if Category( gamma2 ) ne GrpPerm then
        reg, gamma2 := RegularRepresentation( gamma2, sub< gamma2 | > );
        m2 := reg^-1 * m2;
    end if;
    is_iso, phi := IsIsomorphic( gamma2, gamma );
    require is_iso : "The Gamma group of the root datum must be isomorphic to the field automorphism group";
    m := hom< gamma -> Aut(K) | g :->
      iso< K->K | x :-> x@((g@(phi^-1))@m2) > >;

    // compute c as extension from R`GammaAction  
    G := GroupOfLieType( UntwistedRootDatum(R), K : 
      Normalising:=Normalising, Method:=Method );  //  untwisted form!

    Au := AutomorphismGroup(G);
    A  := GammaGroup(k,Au : Gamma:=gamma, m:=m );

    perm_ac := R`GammaAction`perm_ac;
    codom   := Codomain(perm_ac);

    proj := hom< Au -> codom | a :-> codom!(DataAutLie( a )`g),    // natural hom
                               a :-> GraphAutomorphism(G,a)    >;  // representative map
                                   
    // create a proper name for the representative map
    r := proj^-1; 

    D  := GammaGroup(gamma, codom, hom<gamma->Aut(codom)|g:->iso<codom->codom|x:->x,x:->x>>);

    // lowlevel-access!!!
    D`ind_from := A;
    D`ind_mod  := A; // XXX dummy value!! this should be GG^\circ
    D`ind_proj := proj;
    D`ind_rep  := r;

    if not assigned(A`F) then
         // MyFPGroup ensures that all relators only contain positive exponents. 
         A`F,
         A`f2gamma := MyFPGroup(ActingGroup(A));
         A`Faction := A`f2gamma * A`action;
    end if;

    cc := OneCocycle( D, perm_ac );

    c := Rep(ExtendGaloisCocycle(cc));

    return internalCreateTwistedGrpLie(R,k,K,c,Normalising,Method);

end intrinsic;


intrinsic TwistedGroupOfLieType(R::RootDtm, k::RngIntElt, K::RngIntElt : Normalising:=true, Method:=defaultMethod ) -> GrpLie
{}
    return TwistedGroupOfLieType(R,GF(k),GF(K) : Normalising:=Normalising, Method:=Method );
end intrinsic;


intrinsic TwistedGroupOfLieType( c::OneCoC ) -> GrpLie
{Twisted group of Lie type}

    GG := GammaGroup(c);
    A  := Group(GG);
    
    require ISA(Category(A), GrpLieAuto) : "not a cocycle on Aut_k(G)";

    G := Domain(A);    // untwisted overgroup
    R := RootDatum(G);
    W := WeylGroup(G);
    N := NumPosRoots(R);

    K := BaseRing(G);
    k := GG`k;

    gamma,m := ActingGroup(GG);
    action  := GammaAction(GG);

    ims_for_RD := [Sym(2*N)| ];

    for i in [1..Ngens(gamma)] do
        _,_,_,data := DecomposeAutomorphism(c(gamma.i));
        ims_for_RD[i] := ExtendDynkinDiagramPermutation(R,data`g)*WordToPerm(W,data`i`w) ;
    end for;

    tRD := TwistedRootDatum( R : Twist:=<gamma,ims_for_RD> );

    return internalCreateTwistedGrpLie(tRD,k,K,c,IsNormalising(G),G`Method);

end intrinsic;

intrinsic UntwistedOvergroup( G::GrpLie ) -> GrpLie
{Untwisted overgroup of the twisted group of Lie type}
    
    if IsTwisted(G) then    
      c := OneCocycle(G);
      return Domain(Group(GammaGroup(c)));
    else
      return G;
    end if;
    
end intrinsic;


intrinsic RelativeRootElement( G::GrpLie, delta::RngIntElt, t::[FldElt] ) -> GrpLieElt
{u_delta(t) [SH-phd,(4.5)] }
    K := BaseRing(G);
    
    require t subset K : "wrong field elements";
    
    R := RootDatum(G);
    J := GammaOrbitsRepresentatives(R,delta);
    relrts := RelativeRoots(R);

    // not currently used
    delta2 := Position(relrts, 2 * relrts[delta]);
    if delta2 ne 0 then
      J2 := GammaOrbitsRepresentatives(R,delta2);
    else
      J2 := [Universe(J)|];
    end if;

    require #t eq #J : "wrong number of field elements";

    unG := UntwistedOvergroup(G);

    c := OneCocycle(G);
    gamma, m := ActingGroup(GammaGroup(c));

    autos := [ FieldAutomorphism(unG, m(g)) * c(g) : g in gamma ];

    x := &*[ &*[ u@a : a in autos ] where u is elt<unG|<J[i],t[i]>>
             : i in [1..#J] ];

    return x;
end intrinsic;


