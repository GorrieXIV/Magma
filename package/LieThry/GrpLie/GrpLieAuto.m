freeze;

/*
  $Id: GrpLieAuto.m 48640 2014-10-16 02:18:16Z watkins $

  Package for creating automorphisms of Lie type groups.
  Together with CoxeterGp.m, this file is based on the old Coxeter.m,
  whose history can be found at the end of the file RootDatum.m.

  -------
  Arjeh Cohen, Scott H Murray and D E Taylor

  24 November 2000
  -------
  various additions (Scott H Murray and Sergei Haller)
  
  2003
  -------
  added Lie Algebra automorphisms (Scott H Murray)
  
  2004
  -------
  rewritten to support GrpLieAuto, GrpLieAutoElt objects (Sergei Haller)
  
  September 2004
  -------
*/

import "../Root/Const.m" : maxMultiplicity;
import "GrpLie.m" : copyelt, Unip_ToList, Unip_Normalise, 
  Torus_Identity, Torus_IntMxAction, Torus_RatMxAction, Torus_Parent,
  Torus_Product, Torus_Term_Rt, Weyl_Normalise, WeylActionOnTorus,
  collectionOrder;
import "../Repn/RowRed.m" : WeightBase, rowReduction, nthRoots;
import "../Root/RootDtm.m" : toType;

declare type GrpLieAuto[GrpLieAutoElt];
declare attributes GrpLie:     AutomorphismGroup;
declare attributes GrpLieAuto: G;

declare attributes GrpLieAutoElt : 
          G,        // ::GrpLie,     the Group of Lie type
          A,        // ::GrpLieAuto, the automorphism Group
          m,        // ::Map[G,G],   the actual map
          Data;     // ::Rec,        Decomposition; see below for RecFrmt

dataType := func< G | recformat< 
                      //
                      // note that the order of the multiplication is important:
                      //            f*g*i
                      //
                      f : Aut(k),    // field automorphism
                      g : Sym(l),    // graph automorphism
                      i : G >        // inner automorphism
                      where k is BaseRing(G)
                      where l is SemisimpleRank(G) >;

idFld   := func< G | iso< k -> k | x:->x, x:->x > where k is BaseRing(G) >;
idData  := func< G | rec< dataType(G) | f:=idFld(G), g:=1, i:=1 > >;



/*********************************************************************************
**                                                                              **
**   Printing                                                                   **
**                                                                              **
*********************************************************************************/
intrinsic Print( a::GrpLieAutoElt, level::MonStgElt )
{Prints an object of type GrpLieAutoElt}
     //
     // Possible Print levels: Minimal, Default, Maximal, Magma, Debug
     //
     if level eq "Magma" then
          printf "Magma level not implemented yet";
     elif level eq "Debug" then
          // if in Debug level, only output the minimal information on each
          // attribute, but print ALL of them
          printf    "G: %o\n",  Sprint( assigned(a`G)    select a`G    else "not assigned", "Minimal" );
          printf    "A: %o\n",  Sprint( assigned(a`A)    select a`A    else "not assigned", "Minimal" );
          printf    "m: %o\n",  Sprint( assigned(a`m)    select a`m    else "not assigned", "Minimal" );
          printf "Data: %o",    Sprint( assigned(a`Data) select a`Data else "not assigned", "Minimal" );
     elif level eq "Minimal" then
          printf "Automorphism of %o",  Sprint( a`G, level );
     else
          printf "Automorphism of %o\n",  Sprint( a`G, level );
          printf "given by: %o",        Sprint( a`m, level );
          //
          // if Decomposition is known, do some more output
          //
          if assigned(a`Data) then
               printf "\nDecomposition:\n  %o,\n  %o,\n  %o",
               Sprint( a`Data`f, level ),
               Sprint( a`Data`g, level ),
               Sprint( a`Data`i, level );
          end if;
     end if;
end intrinsic;

intrinsic Print( A::GrpLieAuto, level::MonStgElt )
{Prints an object of type GrpLieAuto}
     //
     // Possible Print levels: Minimal, Default, Maximal, Magma, Debug
     //
     printf "Automorphism group of %o", Sprint( A`G, level );
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Accessing attributes                                                       **
**                                                                              **
*********************************************************************************/
intrinsic Domain( a::GrpLieAutoElt ) -> GrpLie
{Domain of a}
     return a`G;
end intrinsic;
intrinsic Codomain( a::GrpLieAutoElt ) -> GrpLie
{Codomain of a}
     return a`G;
end intrinsic;

intrinsic Mapping( a::GrpLieAutoElt ) -> Map[GrpLie, GrpLie]
{Returns the mapping assosiated with a.}
     return a`m;
end intrinsic;

intrinsic DataAutLie( a::GrpLieAutoElt ) -> Rec
{Internal.  Returns the decomposition data of a. 
Forces computation of the decomposition if not already known.}
     if not assigned a`Data then
       // DecomposeAutomorphism will assign the data.
       _ := DecomposeAutomorphism(a);
     end if;
     return a`Data;
end intrinsic;

intrinsic Parent( a::GrpLieAutoElt ) -> GrpLieAuto
{Internal.  Returns the parent of a.}
     return a`A;
end intrinsic;


intrinsic Domain( A::GrpLieAuto ) -> GrpLie
{Domain of A.}
     return A`G;
end intrinsic;
intrinsic Codomain( A::GrpLieAuto ) -> GrpLie
{Codomain of A.}
     return A`G;
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Basic operations                                                           **
**                                                                              **
*********************************************************************************/

intrinsic '@'( x::GrpLieElt, a::GrpLieAutoElt ) -> GrpLieElt
{Apply a to x}
     require x in Domain(a) : "x must be an element of the domain of a";
     return a`m(x);
end intrinsic;

intrinsic '.'( A::GrpLieAuto, m::RngIntElt ) -> GrpLieAutoElt
{The automorphism with the given map}
     require m eq 0 : "only .0 implemented";
     return One(A);
end intrinsic;  

intrinsic 'in'( a::GrpLieAutoElt, A::GrpLieAuto ) -> BoolElt
{Internal.  Return true iff a is an element of A}
     return Domain(A) cmpeq Domain(a);
end intrinsic;  

function MultiplyData( aData, bData )
     // f1 g1 i1 * f2 g2 i2 = (f1 f2) (g1 g2) (i1^(f2 g2) i2 )
     // since [g1,f2]=1
     return rec< dataType(G) |
                     f := aData`f * bData`f,
                     g := aData`g * bData`g,
                     i := ((aData`i)@FieldAutomorphism(G,bData`f))@GraphAutomorphism(G,bData`g) * bData`i >
            where G is Parent(aData`i);
end function;

intrinsic '*'( a::GrpLieAutoElt, b::GrpLieAutoElt ) -> GrpLieAutoElt
{Multiplication for automorphisms of groups of Lie type.}
     require Parent(a) cmpeq Parent(b) : "automorphisms not compatible" ;

     ab := Automorphism( Mapping(a)*Mapping(b) );

     G := Domain(a);

     // don't _force_ decomposition of a and b,
     // but use it if it exists.
     if assigned(a`Data) and assigned(b`Data) then
          ab`Data := MultiplyData(DataAutLie(a),DataAutLie(b));
     end if;
     
     return ab;
end intrinsic;

function InverseData( aData )
     finv := (aData`f)^-1;  
     ginv := (aData`g)^-1;

     // (f g i)^-1   =   i^-1 g^-1 f^-1   =   i^-1 f^-1 g^-1   =   f^-1 g^-1 (i^-1)^(f^-1 g^-1)
     return rec< dataType(G) |
                    f := finv,
                    g := ginv,
                    i := ((aData`i^-1)@FieldAutomorphism(G,finv))@GraphAutomorphism(G,ginv) >
            where G is Parent(aData`i);
end function;

intrinsic Inverse( a::GrpLieAutoElt ) -> GrpLieAutoElt
{Inverse of automorphisms of groups of Lie type.}
     G := Domain(a);

     if true then //assigned(Mapping(a)`PreImageRule) then
          a1 := Automorphism( Mapping(a)^-1 );
          if assigned(a`Data) then
               a1`Data := InverseData(DataAutLie(a));
          end if;
     else 
          // if Mapping(a) doesn't know its inverse,
          // force decomposition of a:
          a1 := Automorphism( G, InverseData(DataAutLie(a)) );
     end if;
     
     return a1;
end intrinsic;

intrinsic '^'( a::GrpLieAutoElt, b::GrpLieAutoElt ) -> GrpLieAutoElt
{Conjugation of automorphisms of groups of Lie type (b^-1*a*b).}
     return Inverse(b)*a*b;
end intrinsic;


intrinsic '^'( a::GrpLieAutoElt, n::RngIntElt ) -> GrpLieAutoElt
{The n-th power of an automorphism of groups of Lie type.}
     if AbsoluteValue(n) le 3 then
          // carry over the multiplication of data
          if n eq 0 then
               return IdentityAutomorphism( Domain(a) );
          elif n gt 0 then
               return &*[ a : i in [1..n] ];
          else // n lt 0
               return &*[ Inverse(a) : i in [1..-n] ];
          end if;
     else
          // just compute the automorphism. 
          return Automorphism( Mapping(a)^n );
     end if;
end intrinsic;


intrinsic 'eq'( a::GrpLieAutoElt, b::GrpLieAutoElt ) -> GrpLieAutoElt
{Equality for automorphisms of groups of Lie type.}
     data := MultiplyData( DataAutLie(a), InverseData(DataAutLie(b)) );
     return data`f eq idFld(Domain(a))
        and data`g eq Parent(data`g)!1 
        and IsCentral( data`i );
end intrinsic;

intrinsic 'eq'( A::GrpLieAuto, B::GrpLieAuto ) -> GrpLieAutoElt
{Equality for automorphism groups of groups of Lie type.}
     return Domain(A) cmpeq Domain(B);
end intrinsic;

intrinsic IsAlgebraic( a::GrpLieAutoElt ) -> BoolElt
{True iff a is algebraic.}
  return DataAutLie(a)`f eq idFld(Domain(a));
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   Construction                                                               **
**                                                                              **
*********************************************************************************/
intrinsic AutomorphismGroup( G::GrpLie ) -> GrpLieAuto
{Automorphism group of a Group of Lie type}
     if not assigned G`AutomorphismGroup then
          G`AutomorphismGroup := New(GrpLieAuto);
          G`AutomorphismGroup`G := G;
     end if;
     return G`AutomorphismGroup;
end intrinsic;

function PrepareAutomorphism( G );
     a := New(GrpLieAutoElt);
     a`G := G;
     a`A := AutomorphismGroup(G);
     return a;
end function;

intrinsic IdentityAutomorphism( G::GrpLie ) -> GrpLieAutoElt
{The identity automorphism of G.}
     a := PrepareAutomorphism( G );

     a`m := iso< G -> G | x :-> x, x :-> x >;

     a`Data := idData(G);
     
     return a;
end intrinsic;

intrinsic One( A::GrpLieAuto ) -> GrpLieAutoElt
{The identity automorphism in A.}
     return IdentityAutomorphism(Domain(A));
end intrinsic;

intrinsic Id( A::GrpLieAuto ) -> GrpLieAutoElt
{The identity automorphism in A.}
     return One(A);
end intrinsic;



intrinsic Automorphism( m::Map[GrpLie,GrpLie] ) -> GrpLieAutoElt
{The automorphism with the given map.}
  require Domain(m) cmpeq Codomain(m) : "Domain and codomain must be equal";
  require assigned(m`IsHomomorphism) and m`IsHomomorphism : 
    "The map is not known to be a homomorphism";
  require assigned(m`IsSurjective)   and m`IsSurjective and 
          assigned(m`IsInjective)    and m`IsInjective    : 
    "The map is not known to be bijective";
  a := PrepareAutomorphism( Domain(m) );
  a`m := m;
  return a;
end intrinsic;

intrinsic InnerAutomorphism( G::GrpLie, x::GrpLieElt ) -> GrpLieAutoElt
{The inner automorphism of G induced by x.}
     require x in G : "x must be an element of G";
     y := Inverse( x );
     a := PrepareAutomorphism( G );

     a`m := iso< G -> G | g :-> g^x, g :-> g^y >;

     a`Data := idData(G);
     a`Data`i := x;

     return a;
end intrinsic;

intrinsic DiagonalAutomorphism( G::GrpLie, v::ModTupRngElt ) -> GrpLieAutoElt
{The diagonal automorphism of G induced by the vector v.}
     return InnerAutomorphism( G, elt< G | v > );
end intrinsic;

// check if the permutation defines a graph automorphism.
checkPerm := function( R, p, char ) 
  num := Degree( Parent(p) );
  if forall{ <r,s> : r in [s+1..num], s in [1..num] |
  CartanInteger(R,r,s) eq CartanInteger(R,r^p,s^p) } then
    return true;
  else
    if char eq 0 then  return false;  end if;
    // TODO: where is modCI used ????
/*
 *     modCI := function( r, s )
 *       ret := CartanInteger(R,r,s);
 *       if Abs(ret) eq 1 then ret *:= char;
 *       elif Abs(ret) eq char then ret div:= char;
 *       end if;
 *       return ret;
 *     end function;
 */
    q := [ IsLongRoot(R,r) select char else 1 : r in [1..num]];                  
    return forall{ <r,s> : r in [s+1..num], s in [1..num] |
    q[s]*CartanInteger(R,r,s) eq q[r]*CartanInteger(R,r^p,s^p) };
  end if;
end function;


// compute signs 
computeSigns := function( R, p, SimpleSigns )
  n := Rank( R );  N := NumPosRoots( R );
  if Category( SimpleSigns ) eq RngIntElt then
    SimpleSigns := [ SimpleSigns : i in [1..2*n] ];
  end if;
  
  // THIS IS ONLY CORRECT FOR SIMPLES
  case maxMultiplicity( R ) :
  when 1 :
    signs := [];
    for r in [1..n] do
      signs[r] := SimpleSigns[r];
      signs[r+N] := SimpleSigns[r];
    end for;
    for r in [n+1..N] do
      s, t := ExtraspecialPair( R, r );
      signs[r] := signs[s] * signs[t] * LieConstant_epsilon( R, s, t ) *
        LieConstant_epsilon( R, s^p, t^p );
      signs[r+N] := signs[s+N] * signs[t+N] * LieConstant_epsilon( R, s+N, t+N ) *
        LieConstant_epsilon( R, (s+N)^p, (t+N)^p );
    end for;
  when 2 :
    signs := [ 1 : i in [1..2*N] ];
  when 3 :
    signs := [ 1 : i in [1..2*N] ];
  end case;
  return signs;
end function;

G2GraphAuto := function( G )
  k := BaseRing( G );
  R := RootDatum("G2":Signs:=[-1,-1,1,1]);
  h := GroupOfLieType( R, k );
  h := GraphAutomorphism( h, Sym(2)!(1,2));
  S := RootDatum(G);
  H := GroupOfLieType( S, k );
  phi := GroupOfLieTypeHomomorphism( hom< S -> R | [1,2] >, k );
  invphi := GroupOfLieTypeHomomorphism( hom< R -> S | [1,2] >, k );
  return iso< G -> G | x :-> ((x@phi)@h)@invphi >;
end function;




intrinsic GraphAutomorphism( G::GrpLie, p::GrpPermElt : SimpleSigns := 1 ) -> GrpLieAutoElt, GrpPermElt
{The graph automorphism of G induced by the permutation of the (simple) roots p.}
  d := ReductiveRank( G );  n := SemisimpleRank( G );  N := NumPosRoots( G );
  R := RootDatum( G );  W := WeylGroup( G );  k := BaseRing( G );
  
  if toType(R)[1][1] eq "G" and Characteristic(k) eq 3 and p ne p^0 
    and ExtraspecialSigns(R) ne [-1,-1,1,1] then
    return G2GraphAuto(G);
  end if;
  norms := RootNorms( R );
  ChangeUniverse( ~norms, Integers() );
  deg := Degree( Parent(p) );
  require deg eq n or deg eq 2*N : "Invalid permutation degree";
  require checkPerm( R, p, Characteristic(k) ) : "Invalid permutation";
  if deg eq n then  p := ExtendDynkinDiagramPermutation( R, p );  end if;
  pinv := p^-1;
  signs := computeSigns( R, p, SimpleSigns );
  invsigns := [ signs[r^pinv] : r in [1..2*N] ]; 

  simple := forall{ i : i in [1..n] | i^p in [1..n] };
  rts := //simple select [] else
    [ Eltseq(v) : v in Roots( R : Basis:="Root" ) ];

  M := MatrixAlgebra( Rationals(), d );
  V := VectorSpace( Rationals(), d );
  A := SimpleCoroots( R );
  if d ne n then
    A := ExtendBasis( sub< V | [ V | A[i] : i in [1..n] ] >, V );
  end if;
  A := M!Matrix( A );
  A := A^-1 * M!Matrix( [ V | Coroot( R, r^p ) * norms[r^p] : r in [1..n] ] cat 
    [ V | A[i] : i in [n+1..d] ] );
  
  
  ToTorus := procedure( ~term, A )
    term := Rep( Torus_RatMxAction( term, A ) );
  end procedure;
  ToUnipTerm := procedure( ~term, p, signs, uinv )
    r := term[1];
    if r eq r^p then
      pow := term[2];
    else
      pow := (uinv) select nthRoots(term[2],norms[r])[1][1] else
        term[2]^norms[r^p];
    end if;
    term[2] := signs[r]*pow; 
    term[1] := r^p;
  end procedure;
  ToUnipList := procedure( ~term, p, signs, uinv )
    for i in [1..#term] do ToUnipTerm( ~term[i], p, signs, uinv ); end for;
  end procedure;
  ToUnipNorm := procedure( ~term, p, signs, uinv )
    term := Unip_ToList( R, k, term, collectionOrder(G) );
    ToUnipList( ~term, p, signs, uinv );
  end procedure;
  ToWeylTerm := procedure( ~term, p )
    term := term^p;
  end procedure;
  ToWeyl := function( term, p )
    t := Torus_Identity( R, k );
    for i in [#term..1 by -1] do  //t;
      WeylActionOnTorus( R, k, ~t, [term[i]^p] : left );
      t := Torus_Product( R, k, t, 
        Torus_Term_Rt( R, k, term[i]^p, signs[term[i]] ) ); 
      ToWeylTerm( ~term[i], p );
    end for;
    return t, term;
  end function;
  
  ToNormalised := procedure( ~term, p, pinv, A, signs, uinv )
    ToUnipNorm( ~term`u, p, signs, uinv );  ToTorus( ~term`h, A );
    h, term`w := ToWeyl( term`w, p );  
    term`h := Torus_Product( R, k, term`h, h );
    ToUnipNorm( ~term`up, p, signs, uinv );
    if simple then
      Weyl_Normalise( R, k, ~term`w );
      term`filter := [ term`filter[i^pinv] : i in [1..N] ];
      term`u := Unip_Normalise( G, term`u );
      term`up := Unip_Normalise( G, term`up );
    else
      // this normalises the Weyl terms
      term := elt< G | Eltlist( term ) >;
    end if;
  end procedure;

  f := function( x, p, pinv, A, signs, uinv )
    x := copyelt( x );
    if IsNormalised( x ) then
      ToNormalised( ~x, p, pinv, A, signs, uinv );
      //Unnormalise( ~x );
    else
      list := Eltlist(x);
      i := 1;
      while i le #list do
        if Category(list[i]) eq ModTupFldElt then
          ToTorus( ~list[i], A );
        elif Category(list[i]) eq Tup and #list[i] eq 2 then
          ToUnipTerm( ~list[i], p, signs, uinv );
        elif Category(list[i]) eq SeqEnum and
        not IsNull(list[i]) and Category(Universe(list[i])) eq SetCart then
          ToUnipList( ~list[i], p, signs, uinv );
        elif Category(list[i]) eq SeqEnum and not IsNull(list[i]) then
          ToUnipNorm( ~list[i], p, signs, uinv );
        elif Category(list[i]) eq RngIntElt then
          Insert( ~list, i, Torus_Term_Rt( R, k, list[i]^p, signs[list[i]] ) );
          i +:= 1;
          ToWeylTerm( ~list[i], p );
        elif Category(list[i]) eq GrpLieElt then
          ToNormalised( ~list[i], p, pinv, A, signs, uinv );
        end if;
        i +:= 1;
      end while;
      x`List := list;
    end if;
    return x;
  end function;

  a := PrepareAutomorphism( G );
  a`m := iso< G -> G | x :-> f(x,p,pinv,A,      signs,false), 
                       y :-> f(y,pinv,p,A^-1,invsigns,true ) >;

  // TODO: why does this only work if "simple"
  // what is the def. of a "GraphAuto" here???
  if simple and forall{ i : i in [1..n] | signs[i] eq 1 } then
    simplep := Sym(n)!( Eltseq(p)[[1..n]] );
    a`Data   := idData(G); 
    a`Data`g := simplep; 
    //Inverse(a)`Data := idData(G); 
    //Inverse(a)`Data`g := simplep^-1;
  end if;
  
  // TODO: 
  // Is p and signs only for debugging or is it used somewhere?
  return a, p, signs;
end intrinsic;

intrinsic DiagramAutomorphism( G::GrpLie, p::GrpPermElt : SimpleSigns := 1 ) -> GrpLieAutoElt, GrpPermElt
{The graph automorphism of G induced by the permutation of the (simple) roots p.}
  return GraphAutomorphism(G,p:SimpleSigns:=SimpleSigns);
end intrinsic;

intrinsic DualityAutomorphism( G::GrpLie ) -> GrpLieAutoElt
{The duality automorphism of G.}
  N := NumPosRoots( G );
  return GraphAutomorphism( G, Sym(2*N)!([N+1..2*N] cat [1..N]) : 
    SimpleSigns := -1 );
  // TODO
  // SH: what is the defn of the duality automorphism? 
  //     isn't it the composition of the standard graph symmentry and
  //     inner automorphism given by \dot{w_0} ???
  //     If yes, the data should be stored.
end intrinsic;

intrinsic FieldAutomorphism( G::GrpLie, sigma::Map[Fld,Fld] ) -> GrpLieAutoElt
{The automorphism of G induced by the field automorphism sigma.}
  require Domain( sigma ) cmpeq BaseRing( G ) and
        Codomain( sigma ) cmpeq BaseRing( G ) : "Invalid field automorphism";


  // THIS WILL CAUSE ERRORS -- SHM
  sigma`IsHomomorphism := true;
  sigma`IsSurjective := true;
  sigma`IsInjective := true;

  ToTorus := procedure( ~term, sigma )
    term := Parent(term) ! [ sigma(term[i]) : i in [1..#Eltseq(term)] ];
  end procedure;
  ToUnipTerm := procedure( ~term, sigma )
    term[2] := sigma(term[2]);
  end procedure;
  ToUnipList := procedure( ~term, sigma )
    for i in [1..#term] do ToUnipTerm( ~term[i, sigma] ); end for;
  end procedure;
  ToUnipNorm := procedure( ~term, sigma )
    term := [ sigma(t) : t in term ];
  end procedure;
  ToNormalised := procedure( ~term, sigma )
    ToUnipNorm( ~term`u, sigma );  ToTorus( ~term`h, sigma );
    ToUnipNorm( ~term`up, sigma );
  end procedure;

  f := function( x, sigma )
    x := copyelt( x );
    if IsNormalised( x ) then
      ToNormalised( ~x, sigma );
    else
      list := x`List;
      for i in [1..#list] do
        if Category(list[i]) eq ModTupFldElt then
          ToTorus( ~list[i], sigma );
        elif Category(list[i]) eq Tup then
          ToUnipTerm( ~list[i], sigma );
        elif Category(list[i]) eq SeqEnum and
        not IsNull(list[i]) and Category(Universe(list[i])) eq SetCart then
          ToUnipList( ~list[i], sigma );
        elif Category(list[i]) eq SeqEnum and not IsNull(list[i]) then
          ToUnipNorm( ~list[i], sigma );
        elif Category(list[i]) eq GrpLieElt then
          ToNormalised( ~list[i], sigma );
        end if;
      end for;
      x`List := list;
    end if;
    return x;
  end function;

  tau := Inverse( sigma );
  a := PrepareAutomorphism( G );
  a`m := iso< G -> G | x :-> f(x,sigma), x :-> f(x,tau) >;
  a`Data := idData(G);
  a`Data`f := sigma;
//Inverse(a)`Data := idData(G);
//Inverse(a)`Data`f:=tau;
  return a;
end intrinsic;


intrinsic Automorphism( G::GrpLie, Data::Rec ) -> GrpLieAutoElt
{Internal.  The automorphism with the given data.}
     a := Automorphism(  Mapping(FieldAutomorphism( G, Data`f ))
                       * Mapping(GraphAutomorphism( G, Data`g ))
                       * Mapping(InnerAutomorphism( G, Data`i )) );
     a`Data := Data;
     return a;
end intrinsic;  


intrinsic RandomAutomorphism( G::GrpLie ) -> GrpLieAutoElt
{A random automorphism of the group of Lie type G.}
     K := BaseRing(G);
     AutK,_,m := AutomorphismGroup(K,PrimeField(K));
     fld := Random(AutK);
     
     S := Sym(SemisimpleRank(G));
     repeat
          graph := Random(S);
     until checkPerm( RootDatum(G), graph, Characteristic(K) );
     
     inn := Random(G);
     
     return Automorphism( G, rec<dataType(G) | f := m(fld), g:=graph, i:=inn> );
end intrinsic;


intrinsic Random( A::GrpLieAuto ) -> GrpLieAutoElt
{A random automorphism in A.}
     return RandomAutomorphism(Domain(A));
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   Decomposition                                                              **
**                                                                              **
*********************************************************************************/
// install these as intrinsics for debugging:
//
// intrinsic rowReduction( rho::Map : Vectors, NoTorus ) -> .
// {}
//      return rowReduction( rho : Vectors, NoTorus );
// end intrinsic;
// intrinsic WeightBase( rho::Map  ) -> .
// {}
//      return WeightBase( rho );
// end intrinsic;
// intrinsic Torus_RatMxAction( x::Any, y::Any  ) -> .
// {} return Torus_RatMxAction( x,y );
// end intrinsic;

// this avoids the rare case where the standard representation is decomposable
stdRepn := function( G )
  type := toType( RootDatum(G) )[1];
  if type[1] eq "B" and #type[2] eq 2 then
    H := GroupOfLieType( "C2", BaseRing(G) : Isogeny := #IsogenyGroup(G) );
    _, phi := IsAlgebraicallyIsomorphic( G, H );
    rho := StandardRepresentation( H : NoWarning );
    return phi * rho;
  else
    return  StandardRepresentation( G : NoWarning );
  end if;
end function;

intrinsic DecomposeAutomorphism( a::GrpLieAutoElt ) -> GrpLieAutoElt,GrpLieAutoElt,GrpLieAutoElt,Rec
{Decompose an automorphism of a group of Lie type.}
  G := Domain( a );
  if assigned a`Data then
     return FieldAutomorphism( G, a`Data`f ),
            GraphAutomorphism( G, a`Data`g ),
            InnerAutomorphism( G, a`Data`i ),
            a`Data;
  end if;

  require IsSemisimple(G) : "Not a semisimple group"; // should not be necessary
  k := BaseRing( G );  n := Rank( G );
  rho := stdRepn( G );
  red := rowReduction( rho : Vectors, NoTorus );

  // inner
  rho2 := Mapping(a)*rho;
  _, ims := WeightBase( rho2 );
  y1 := red(ims);  i1 := InnerAutomorphism( G, y1 );
  a1 := a * Inverse(i1);

  w0 := LongestElement( CoxeterGroup( GrpFPCox, WeylGroup( G ) ) );
  w0dot := &*[G| elt<G|r> : r in Eltseq(w0) ];
  opp := InnerAutomorphism( G, w0dot );
  b := opp*a1;
  rho2 := Mapping(b)*rho;
  _, ims := WeightBase( rho2 );
  y := red(ims);  // y takes B to b(B)=a1(B-)
  _,_,_,u := Bruhat(y);  i2 := InnerAutomorphism( G, u );
  a2 := a1 * Inverse(i2);
  y := u*y1;
  i := InnerAutomorphism( G, y );  // = i2*i1
  
  // graph
  perm := Sym(n) ! [ Eltlist(a2(elt<G|<i,1>>))[1][1][1] : i in [1..n] ];
  g := GraphAutomorphism( G, perm );
  a3 := a2 * Inverse(g);

  // diagonal
  V := VectorSpace( k, n );
  v := V![ Eltlist(a3(elt<G|<i,1>>))[1][1][2] : i in [1..n] ];
  C := MatrixAlgebra(Rationals(),n)!SimpleRoots(G);  //Fix for non-ss
  solns := Setseq( Torus_RatMxAction(v,C^-1) );  i := 1;
  gens := [ elt<G|<r,1>> : r in [1..SemisimpleRank(G)] ];
  ims := [ a3(g) : g in gens ];
  repeat
    u := solns[i];
    d := DiagonalAutomorphism( G, u );  i +:= 1;
  until forall{ j : j in [1..#gens] | d(gens[j]) eq ims[j] };
  a4 := a3 * Inverse(d);
  
  // field
  p := Characteristic( k );
  if ((p eq 0 and Category(k) eq FldRat) or 
  (p ne 0 and Category(k) eq FldFin and IsPrime(#k))) then
    sigma := iso< k -> k | >;
    f := IdentityAutomorphism( G );
  elif Category(k) eq FldFin then
    l := Eltlist(a4(elt<G|<1,k.1>>))[1][1][2];
    m := Eltlist((Inverse(a4))(elt<G|<1,k.1>>))[1][1][2];
    s := iso< k -> k | l >;  t := iso< k -> k | m >;
    sigma := iso< k -> k | x :-> s(x), y :-> t(y) >;
    f := FieldAutomorphism( G, sigma );
  else
    sigma := iso< k -> k | 
      x :-> Eltlist(a4(elt<G|<1,x>>))[1][1][2], 
      y :-> Eltlist((Inverse(a4))(elt<G|<1,y>>))[1][1][2] >;
    f := FieldAutomorphism( G, sigma );
  end if;
  
  // swap diagonal and graph
  norms := RootNorms( RootDatum( G ) ); ChangeUniverse( ~norms, Integers() );
  u := Parent(u)![ u[r^perm]^norms[r] : r in [1..Rank(G)] ];
  y := elt< G | u > * y;
  i := InnerAutomorphism( G, y );
  
  a`Data := idData(G);
  a`Data`f := sigma;
  a`Data`g := perm;
  a`Data`i := y;

  return f, g, i, a`Data;
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Coercions                                                                  **
**                                                                              **
*********************************************************************************/

intrinsic Coercion( AutG::GrpLieAuto, AutH::GrpLieAuto ) -> Map[GrpLieAuto,GrpLieAuto]
{Coercion map from AutG to AutH.
 Only defined for groups with the same RootDatum and different fields.}

     // do some checks
     G := Domain(AutG);
     H := Domain(AutH);
     require RootDatum(G) cmpeq RootDatum(H) : "Root data must be the same";

     k := BaseRing(G);
     K := BaseRing(H);
     
//
// the following doesn't work for all fields. e.g. not for finite ones:
//
//     require IsSubfield ( k, K ) : "bla bla";  
//
// something like 
//     require IsCoercible( k, K ) : "bla bla";  
// would be even better.
// unfortunately it works only for a Structure and an element.
//

// for now:
     require ( ISA(Category(k), FldFin ) or    
               ISA(Category(k), FldRat ) or    
               ISA(Category(k), FldAlg ) )   and
             ISA(Category(K), FldFunRat) : "Coercion algo for", Category(k), "and", Category(K), "not implemented yet";

     require BaseRing(K) cmpeq k         : "k must be BaseRing(K)";
     

     coerce := function( a )
          data  := DataAutLie( a );
          sigma := data`f; //field part, in Aut(k,k)

          if ISA(Category(k), FldFin) then

               x := PrimitiveElement( k );
               q    := Log( sigma(x) ) mod (#k-1);     //   if q    eq #k then q    := 1; end if;
               qinv := (#k div q)      mod (#k-1);     //   if qinv eq #k then qinv := 1; end if;

               sigmaK    := iso< K -> K | sigma    * Coercion(k,K), [ K.i^q    : i in [1..Rank(K)] ] >;
               sigmaKinv := iso< K -> K | sigma^-1 * Coercion(k,K), [ K.i^qinv : i in [1..Rank(K)] ] >;

               sigmaK    := iso< K -> K | x :-> sigmaK(x), y :-> sigmaKinv(y) >;

          elif ISA(Category(k), FldRat) or ISA(Category(k), FldAlg) then
               
               sigmaFK    := hom< k -> K | x:-> sigma    (x) >;
               sigmaFKinv := hom< k -> K | x:->(sigma^-1)(x) >;
          
               sigmaK     := hom< K -> K | sigmaFK,    [K.i:i in [1..Rank(K)]] >;
               sigmaKinv  := hom< K -> K | sigmaFKinv, [K.i:i in [1..Rank(K)]] >;

               sigmaK     := iso< K -> K | x :-> sigmaK(x), y :-> sigmaKinv(y) >;

          else 
               // ... not implemented yet
          end if;

          return Automorphism( H, rec<dataType(H)| f := sigmaK, 
                                                   g := data`g, 
                                                   i := CoerceGrpLie( H, data`i ) > );
     end function;

     // do the work
     return  hom< AutG -> AutH | a :-> coerce(a) >;

end intrinsic;



intrinsic IsCoercible( A::GrpLieAuto, x::Any ) -> BoolElt, GrpLieAutoElt
{Coerce x into A.}
     case ExtendedCategory(x):
          when Map[GrpLie,GrpLie]:
               if Domain(A) cmpeq Domain(x) then
               // all other checks are done in Automorphism()
                    return true, Automorphism( x );
               else
                    return false, "Domain of the map is not correct";
               end if;
     end case;
     case Category(x):
          when GrpLieAutoElt:
               G := Domain(x); k := BaseRing(G);
               H := Domain(A); K := BaseRing(H);
 
               if x in A then
                    return true, x;
               elif RootDatum(G) cmpeq RootDatum(H) and
                    ( ISA(Category(k), FldFin ) or    
                      ISA(Category(k), FldRat ) or    
                      ISA(Category(k), FldAlg ) )   and
                    ISA(Category(K), FldFunRat)     and
                    BaseRing(K) cmpeq k then
 
                    return true, Coercion( Parent(x), A )(x);
               else
                    return false, "The element is not compatible with the group.";
               end if;
          when RngIntElt:
               if x eq 1 then
                    return true, One(A);
               else
                    return false, "Cannot coerce integers other than 1 into GrpLieAuto";
               end if;
     end case;
     return false, &cat[ "Cannot coerce ", Sprint(ExtendedCategory(x)), " into GrpLieAuto" ] ;
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   AUTOS FOR LIE ALGEBRAS BELOW                                               **
**                                                                              **
*********************************************************************************/


intrinsic IdentityAutomorphism( L::AlgLie ) -> Map
{The identity automorphism of G}
  a := iso< L -> L | a :-> a, a :-> a >;
//  a`Data := idData(G);
  return a, IdentityMatrix( BaseRing(L), Dimension(L) );
end intrinsic;



innerAutGroup := function( L )
  k := BaseRing( L );  d := Dimension( L );
  pos, neg, cart := ChevalleyBasis( L );
  B := Matrix( Reverse(neg) cat cart cat pos );
  R := RootDatum( L );
  G := GroupOfLieType( R, k );
  rho := AdjointRepresentation( G : NoWarning );
  return G,
    map< G -> MatrixAlgebra(k,d) | x :-> B^-1*Matrix(rho(x))*B >;
end function;

intrinsic InnerAutomorphism( L::AlgLie, x::GrpLieElt ) -> Map
{The inner automorphism of L induced by x}
  G, m := innerAutGroup( L );
  require Parent(x) eq G : "Group element is not in the correct group";
  A := m(x);
  return iso< L -> L | A >, A;
end intrinsic;

intrinsic InnerAutomorphismGroup( L::AlgLie ) -> GrpLie, Map
{The group of inner automorphisms of L}
  require Characteristic( BaseRing( L ) ) notin {2,3} :
    "The field of definition must not be of characteristic 2 or 3";
  require IsReductive( L ) : "Only implemented for reductive groups";
  G, m := innerAutGroup( L );
  return G, hom< G -> Aut(L) | x :-> iso< L -> L | m(x) > >, m;
end intrinsic;




intrinsic DiagonalAutomorphism( L::AlgLie, v::ModTupRngElt ) -> Map
{The diagonal automorphism of L induced by the vector v}
  G,h,m := InnerAutomorphismGroup( L );
  g := elt< G | v >;
  return h(g), m(g);
end intrinsic;


permonvect := function( v, p )
  V := Parent( v );
  v := Eltseq( v );  p := p^-1;
  return V![ v[i^p] : i in [1..#v] ];
end function;
  
permonmx := function( A, p )
  q := p^-1;
  return Matrix( [ permonvect(A[i^q],p) : i in [1..Nrows(A)] ] );
end function;



intrinsic GraphAutomorphism( L::AlgLie, p::GrpPermElt : SimpleSigns := 1 ) -> 
  Map, AlgMatElt, GrpPermElt
{The graph automorphism of L induced by the permutation of the (simple) roots p}
  R := RootDatum( L );  k := BaseRing( L );
  d := Dimension( R );  n := Rank( R );  N := NumPosRoots( R );
  
  // this is not right!
//  B := Basis(L);
//  neg := B[[N..1 by -1]];  cart := B[[N+1..N+d]];  pos := B[[N+1+d..2*N+d]];  
  pos, neg, cart := StandardBasis( L );
  norms := RootNorms( R );
  ChangeUniverse( ~norms, Integers() );
  deg := Degree( Parent(p) );
  require deg eq n or deg eq 2*N : "Invalid permutation degree";
  require checkPerm( R, p, Characteristic(k) ) : "Invalid permutation";
  if deg eq n then  p := ExtendDynkinDiagramPermutation( R, p );  end if;
  pinv := p^-1;
  signs := computeSigns( R, p, SimpleSigns );
  invsigns := [ signs[r^pinv] : r in [1..2*N] ]; 

  simple := forall{ i : i in [1..n] | i^p in [1..n] };
  rts := //simple select [] else
    [ Eltseq(v) : v in Roots( R : Basis:="Root" ) ];

  rtelts := pos cat neg;
  rteltims := [ signs[r] * rtelts[r^p] : r in [1..2*N] ];

  M := MatrixAlgebra( Rationals(), d );
  V := VectorSpace( Rationals(), d );
  A := SimpleCoroots( R );
  if d ne n then
    A := ExtendBasis( sub< V | [ V | A[i] : i in [1..n] ] >, V );
  end if;
  A := M!Matrix( A );
  A := A^-1 * M!Matrix( [ V | Coroot( R, r^p ) : r in [1..n] ] cat 
    [ V | A[i] : i in [n+1..d] ] );
  cartims := [ &+[ A[i,j]*cart[j] : j in [1..d] ] : i in [1..d] ];
  
  M := Matrix( rtelts cat cart )^-1 * Matrix( rteltims cat cartims );
  return iso< L->L | M >, M, p;
end intrinsic;

intrinsic DiagramAutomorphism( L::AlgLie, p::GrpPermElt : SimpleSigns := 1 ) -> 
  Map, AlgMatElt, GrpPermElt
{The graph automorphism of L induced by the permutation of the (simple) roots p}
  return GraphAutomorphism(L,p:SimpleSigns:=SimpleSigns);
end intrinsic;

structconsts := function( L )
  n := Dimension( L );  k := BaseRing( L );
  consts := [];
  for i in [1..n] do
    for j in [1..n] do
      Append( ~consts, Eltseq( L.i*L.j ) );
    end for;
  end for;
  return consts;
end function;  

shallowCopyLieAlg := function( L )
  n := Dimension( L );  k := BaseRing( L );
  return LieAlgebra< k, n | structconsts(L) : Rep:="Sparse", Check := false >;
end function;

intrinsic LieAlgebra( R::RootDtm, k::FldFin, p::GrpPermElt ) -> AlgLie
{The twisted Lie algebra}
  m := Order( p );  q := #k;
  K := ext< k | m >;
  LK := LieAlgebra( R, K );  dim := Dimension( LK );
  BK := Basis( K, k );
  e := func< x | &cat[ Eltseq( x[i], k ) : i in [1..dim] ] >;
  Mod := func< i | ((i-1) mod m) + 1 >;  Div := func< i | ((i-1) div m) + 1 >;
  Lk := LieAlgebra< k, dim*m | 
    [ [ e( BK[Mod(i)]*LK.Div(i)*BK[Mod(j)]*LK.Div(j) ) :
    j in [1..dim*m] ] : i in [1..dim*m] ] >;
  h := GraphAutomorphism( LK, p ) * 
    map< LK -> LK | x :-> LK![ a^q : a in Eltseq(x) ] >;
  M := Matrix( [ e( h( BK[Mod(i)]*LK.Div(i) ) ) : i in [1..dim*m] ] );
  L := sub< Lk | ChangeUniverse( Basis(Eigenspace( M, 1 )), Lk ) >; 
  return shallowCopyLieAlg( L );
end intrinsic;


 

intrinsic LieAlgebra( N::MonStgElt, k::FldFin, p::GrpPermElt :
  Isogeny:="Ad" ) -> AlgLie
{The twisted Lie algebra}
  return LieAlgebra( RootDatum( N : Isogeny:=Isogeny ), k, p );
end intrinsic;





intrinsic FrobeniusMap( G::GrpLie, q::RngIntElt ) -> .
{The Frobenius map for G}
  k := BaseRing(G);
  require ISA( Category( k ), FldFin ) : 
    "Not a finite group of Lie type";
  ok1, p1 := IsPrimePower( #k );
  ok2, p2, a2 := IsPrimePower( q );
  require ok1 and ok2 and p1 eq p2 : "Not a valid prime power";
  f := function( x );
    G := Parent( x );  k := BaseRing(G);
    s := FrobeniusMap( k, sub<k|a2> );
    return FieldAutomorphism( G, s )( x );
  end function;
  return f;
end intrinsic;



