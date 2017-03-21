freeze;

/********************************************************************************* 
**                                                                              **
**   $Id: galcohom.m 48480 2014-09-28 02:09:52Z donnelly $                    **
**                                                                              **
**   Sergei Haller <Sergei.Haller@math.uni-giessen.de>                          **
**                                                                              **
**      Magma code for computation of the Galois cohomology for groups of       **
**      Lie type.  That is,  H^1(Gamma,A) where A is Aut_K(G), G  defined       **
**      over k and Gamma = Gal(K:k)                                             **
**                                                                              **
**      Magma code  for computation of maximal (twisted) tori for  groups       **
**      of Lie type over finite fields, their orders and decomposition as       **
**      polynomials in q=|k|                                                    **
**                                                                              **
**      Magma code  for computation of Sylow subgroups for groups of  Lie       **
**      type over finite fields.                                                **
**                                                                              **
**      Magma code  for computation of Sylow subgroups for groups of  Lie       **
**      type over finite fields.                                                **
**                                                                              **
**                                                                              **
*********************************************************************************/

import "../../../Group/GrpCoh/nonab/cohom.m" : check_imgs;
import "GrpLieAuto.m" : checkPerm;

forward AmodAnod;
forward internal_ExtendGaloisCocycle;

forward solveSystemRec;
forward solveSystem;
forward find_any_solution;
forward find_any_solutionRec;

declare verbose verb_galcohom, 2; 
/*
**  use SetVerbose("galcohom", n); to set verbosity level
**
**   1: print some debug output when computing galois cohomology
**
**   2: print the equations used to compute groebner bases
**
*/

/*********************************************************************************
**                                                                              **
**   TODO:  some of the following are fixed! check!                             **
**                                                                              **
**********************************************************************************
**                                                                              **
**                                                                              **
**                                                                              **
*********************************************************************************/

/*********************************************************************************
**                                                                              **
**   EXAMPLES:                                                                  **
**                                                                              **
**********************************************************************************
**                                                                              **
**   Example for using GroebnerBasis and Variety                                **
**                                                                              **

     K := GF(17^2);
     P<[u]> := PolynomialRing(K,3);
     pols := [
          16*u[2]^18 + u[3]^36,
          16*u[1]^18*u[3]^18 + u[2]^36,
          u[1]^36 + 16*u[2]^18
     //     u[1]*u[4] - 1,
     //     u[2]*u[5] - 1,
     //     u[3]*u[6] - 1
     ];
     I := Ideal(pols);
     time Groebner( I : Al:="Walk" );

//   time V := VarietySequence( I, 10, func<t| 0 notin t > );

     GetMemoryUsage();
     time V := VarietySequence( I ); 
     #[ v : v in V | 0 notin v ];
     GetMemoryUsage();

**                                                                              **
**********************************************************************************
**                                                                              **
**   Example for using Galois Cohomology:                                       **
**                                                                              **

     q := 5;
     k := GF(q);
     K := GF(q^2);

     G := GroupOfLieType( "A3", K : Isogeny:="SC" );
     A := AutomorphismGroup(G);

     AGRP := GammaGroup( k, A );
     time GaloisCohomology(AGRP);


     Gamma,m := ActingGroup(AGRP);
     action  := GammaAction(AGRP);

     TrivialOneCocycle( AGRP );

     c := OneCocycle( AGRP, [GraphAutomorphism(G, Sym(3)!(1,3))] );

     x := Random(G);
     IsInTwistedForm( x, c );

     x := elt<G| <1,y>,<3,y @ m(Gamma.1)>> where y is Random(K);
     IsInTwistedForm( x, c );

**                                                                              **
**********************************************************************************
**                                                                              **

     q := 5;
     k := GF(q);
     K := GF(q^2);

     G := GroupOfLieType( "A6", K : Isogeny:="SC" );
     A := AutomorphismGroup(G);

     AGRP := GammaGroup( k, A );
     time GaloisCohomology(AGRP);

**                                                                              **
**********************************************************************************
**                                                                              **

     q := 5;
     k := GF(q);
     K := GF(q^6);

     G := GroupOfLieType( "D4", K : Isogeny:="SC" );
     A := AutomorphismGroup(G);

     AGRP := GammaGroup( k, A );
     time GaloisCohomology(AGRP); // Time: 157.740
     SetVerbose("galcohom",2);
     time GaloisCohomology(AGRP : GBAl:="Walk" );

**                                                                              **
**********************************************************************************
**                                                                              **

Forget infinite fields! until the bug with the autos is fixed.


     k := Rationals();
     P := PolynomialRing(k); x := P.1;

//      K := SplittingField(x^3-x+1);
//      G := GroupOfLieType( "D4", K : Isogeny:="SC" );

     K := SplittingField((x^2+1)); // *(x^2-3));

     G := GroupOfLieType( "A3", K : Isogeny:="SC" );
     A := AutomorphismGroup(G);

     AGRP := GammaGroup( k, A );
     time GaloisCohomology(AGRP : GBAl:="Walk" );

**                                                                              **
**********************************************************************************
**                                                                              **

     G := GroupOfLieType("E6", 5 : Isogeny:="SC", Method := "Collection");
     #TwistedToriOrders(G);

     time
     for type in ["A1", "A2", "A3", "A10",
                  "B2", "B3", "B5",
                  "C2", "C3", "C5",
                  "D4", "D5",
                  "E6", "E7", "E8",
                  "F4", "G2"         ] do

          R := RootDatum(type:Isogeny := "SC");
          printf "TwistedToriOrders( %o ): ",type ;
          time _:=TwistedToriOrders(R);
          IndentPush();
          for q in [2,3,4,5,7,8,9,11,13] do
               printf "q := %o: ",q;
               G := GroupOfLieType( R, q : Method := "Collection" );
               time _:=TwistedTori(G);
          end for;
          IndentPop();
     end for;

**                                                                              **
*********************************************************************************/


// This should be moved
intrinsic 'subset'( A::FldRat, B::FldRat ) -> BoolElt 
{True iff A is a subfield of B}
  return true;
end intrinsic;

intrinsic 'subset'( A::FldFunRat, B::FldFunRat ) -> BoolElt 
{True iff A is a subfield of B}
  return BaseRing(A) subset BaseRing(B);
end intrinsic;

intrinsic 'subset'( A::FldFunRat, B::FldFun ) -> BoolElt 
{True iff A is a subfield of B}
  return A subset BaseRing(B);
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Allan might implement in some future.                                      **
**   for now a VERY inefficient version                                         **
**                                                                              **
*********************************************************************************/
intrinsic XXX_VarietySequence( I::RngMPol, n::RngIntElt, f::UserProgram ) -> SeqEnum
{Internal.  Return at most n elements of the variety of I. 
All elements having condition f, which is a Boolean-valued function}
     m := GetMemoryUsage();
printf "Full Variety ";
time V := VarietySequence( I );
printf "Memory: %o Bytes (becomes inaccurate in long magma sessions)\n", (GetMemoryUsage()-m);
printf "Size: %o Solutions\n", #V;
     ret := [Universe(V)|];
     for v in V do
          if f(v) then 
               Append(~ret,v);
               if #ret ge n then
                    break;
               end if;
          end if;          
     end for;
     return ret;
end intrinsic;

// intrinsic VarietySequence( I::RngMPol, n::RngIntElt, f::UserProgram ) -> SeqEnum
intrinsic VarietySequence( I::RngMPol, n::RngIntElt : Al:="Default" ) -> SeqEnum
{Internal.  Return at most n elements of the variety of I.} 
//All elements having condition f, which is a Boolean-valued function}
     require n eq 1 : "only implemented for n=1";
     pols := Basis(I);
     return Setseq(find_any_solution(pols, Al));
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   This is a special version of FPGroup which rewrites the relations to have  **
**   only positive exponents in the LHS of them (and RHS=1)                     **
**                                                                              **
**   The side effect is that we might have some unnecessary relations.          **
**                                                                              **
*********************************************************************************/
intrinsic MyFPGroup( G::GrpPerm  ) -> GrpFP, Map 
{special version of FPGroup which rewrites the relations to have only positive 
exponents in the LHS of them (and RHS=1)}

     F,f2g := FPGroup(G);

     n := Ngens(F);

     H := FreeGroup(n);
     rels := [ H.i^Order(f2g(F.i)) : i in [1..n] ];

     relwords := [ Eltseq(LHS(r)*RHS(r)^-1) : r in Relations(F) ];
     nrelwords := [];
     for w in relwords do
          nw := [Integers()|];
          for i in [1..#w] do;
               if w[i] gt 0 then
                    Append(~nw, w[i]);
               else // lt 0
                    nw cat:= [ -w[i] : j in [1..Order(f2g(F.-w[i]))-1]];
               end if;
          end for;
          Append(~nrelwords, nw);
     end for;

     rels cat:= [ H!s : s in nrelwords ];
     H := quo<H| rels >;

     h2g:= iso<H->G| [G.i:i in [1..n]]>;

     return H, h2g;

end intrinsic;


/*********************************************************************************
**                                                                              **
**   Construction of a Gamma-Group for a GrpLie and GrpLieAuto                  **
**                                                                              **
*********************************************************************************/
intrinsic GammaGroup( k::Fld, G::GrpLie : Gamma := "unset" ) -> GGrp
{Return the Gamma-group G as a GGrp object.}

     K := BaseRing(G);
     
     try
         ok := k subset K;
     catch e
         error "Unable to compare k with the base field of G";
     end try;
     require ok : "k must be a subfield of the base field of G";

     try 
         gamma, _, m  := AutomorphismGroup( K, k );
     catch e
         error "Unable to compute automorphisms of the base field of G over k";
     end try;

     if Gamma cmpeq "unset" then
         Gamma := gamma;
         // m : Gamma -> Aut(K,k);
     else
         require ISA(Category(Gamma), GrpPerm) : "vararg Gamma must be GrpPerm";
         
         is_iso, ga2ga := IsIsomorphic(Gamma,gamma);
         
         require is_iso : "Gamma must be isomorphic to Aut(K:k)";

         m := ga2ga*m;
     end if;

     action := hom< Gamma-> AutomorphismGroup(G) | gamma :-> FieldAutomorphism(G, m(gamma)) >;
     
     GG := HackobjCreateRaw(GGrp);

     GG`A      := G;
     GG`k      := k;      // K is always accessible as BaseRing(G) 
     GG`Gamma  := Gamma;  // GrpPerm
     GG`action := action;
   
     GG`gamma2fld := m;
     
     return GG;
     
end intrinsic;

intrinsic GammaGroup( k::Fld, A::GrpLieAuto  : Gamma := "unset", m := "unset" ) -> GGrp
{Return the Gamma-group A as a GGrp object.}

     G := Domain(A);
     K := BaseRing(G);
     
     try
         ok := k subset K;
     catch e
         error "Unable to compare k with he base field of A";
     end try;
     require ok : "k must be a subfield of the base field of A";

     if Gamma cmpeq "unset" then
         try 
             Gamma, _, m := AutomorphismGroup( K, k );
         catch e
             error "Unable to compute automorphisms of the base field of A over k";
         end try;
         // TODO: the following only works if k is FldRat, but otherwise there is a bug in map
         // creation. Bug report submitted on 19.02.2005, 21:20
         //     Gamma, _, m := AutomorphismGroup( K );
         // m : Gamma -> Aut(K:k);
     elif m cmpeq "unset" then 
         /* Gamma set, m unset */
         try 
             Gamma, _, m := AutomorphismGroup( K, k );
         catch e
             error "Unable to compute automorphisms of the base field of A over k";
         end try;
     
         require ISA(Category(Gamma), GrpPerm) : "vararg Gamma must be GrpPerm";
         
         gamma, _, m  := AutomorphismGroup( K, k );
         is_iso, ga2ga := IsIsomorphic(Gamma,gamma);
         
         require is_iso : "Gamma must be isomorphic to Aut(K:k)";

         m := ga2ga*m;
     else
         /* Gamma set, m set */
         require ISA(Category(Gamma), GrpPerm) : "vararg Gamma must be GrpPerm";
         require ISA(ExtendedCategory(m), Map[GrpPerm, PowMap] ) : "vararg m must be a map from Gamma to the set of automorphisms of K";
         require Domain(m) cmpeq Gamma : "vararg m must be a map from Gamma to the set of automorphisms of K";
         
     end if;

     action := hom< Gamma->Aut(A) | gamma :->
         iso< A->A | a :-> FieldAutomorphism(G, m(gamma^-1))*a*FieldAutomorphism(G, m(gamma   )),
                     a :-> FieldAutomorphism(G, m(gamma   ))*a*FieldAutomorphism(G, m(gamma^-1)) > >;
          
     GG := HackobjCreateRaw(GGrp);

     GG`A      := A;
     GG`Gamma  := Gamma;  // GrpPerm
     GG`k      := k;      // K is always accessible as BaseRing(G) 
     GG`action := action;
   
     GG`gamma2fld := m;
     
     return GG;
     
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Construction of Cocycles                                                   **
**                                                                              **
**        this works using generic intrinsics from cohom.m                      **
**        (if I didn't miss some silly bug)                                     **
**                                                                              **
*********************************************************************************/


/********************************************************************************* 
**                                                                              **
**   IsInTwistedForm                                                            **
**                                                                              **
**        Given a cocycle c \in Z^1(Gamma,Aut_K(G))                             **
**        and a group element x\in G(K), check if x in G_c(k)                   **
**                                                                              **
*********************************************************************************/
intrinsic IsInTwistedForm( x::GrpLieElt, c::OneCoC ) -> BoolElt
{Returns true iff $x\in G(K)$ is an element of the twisted group of Lie type $G_c(k)$}

     G := Parent(x);
     K := BaseRing(G);
     
     require G cmpeq Domain(Group(GammaGroup(c))) 
          : "Parent(x) and the cocycle do not match";
     
     Gamma, m := ActingGroup(GammaGroup(c));

     return forall{ i : i in [1..Ngens(Gamma)] | 
                  x eq x @ FieldAutomorphism(G, m(Gamma.i)) 
                         @ c(Gamma.i) 
                  };

end intrinsic;



/*********************************************************************************
**                                                                              **
**   Construction of the Galois cohomology   H^1(Gal(K:k), Aut_K(G))            **
**                                                                              **
*********************************************************************************/
intrinsic GaloisCohomology( A::GGrp : GBAl := "Walk", Recompute:=false ) -> SeqEnum[OneCoC]
{Galois cohomology of a GrpLieAuto}

     require Category(Group(A)) eq GrpLieAuto 
           : "A must be a Gamma-group of a GrpLieAuto.";

     if not Recompute and assigned(A`H1) then
          return A`H1;
     end if;

     G := Domain( Group(A) );
     K := BaseRing(G);

     require ISA(Category(K), FldFin) 
          or ISA(Category(K), FldAlg) 
          or ISA(Category(K), FldRat) : "G must be defined over FldFin, FldRat or FldAlg";

     R   := RootDatum(G);
     dim := Dimension(R);
     
     Gamma, m := ActingGroup( A );

     // 1. compute A/A^\circ
     
     AmodB := AmodAnod( G );

     // natural homomorphism from A to AmodB.
     proj := hom< Group(A) -> AmodB | a :-> AmodB!(DataAutLie( a )`g),    // natural hom
                                      a :-> GraphAutomorphism(G,a)    >;  // representative map
                                    
     // create a proper name for the representative map
     r := proj^-1; 

     // 2. compute the induced action of Gamma on A/A^\circ

     // can't use InducedGammaGroup here, compute induced action here:
     
     /*
      *   The galois group acts on A by conjugation.
      *   here is the induced action on AmodB: 
      */
      
     action_on_AmodB_fun :=  function( a, gamma )
          f := FieldAutomorphism( G, m(gamma) );
          return proj( f^-1 * r(a) * f );
     end function;

//     action_on_AmodB := hom< Gamma -> Aut(AmodB) | 
//                    gamma :->  iso< AmodB->AmodB | a :-> action_on_AmodB_fun( a, gamma ) > >;

     /*
      *   compute the action on generators of Gamma and AmodB.
      *   this takes some time but creates a very fast map.
      *   i.e. computations of images is very efficient.
      *   whereas in the above version the map is created immediately
      *   but computing the images takes very long
      */

     action_on_AmodB_hom := 
          hom< Gamma -> AutomorphismGroup(AmodB) | 
                 [ iso< AmodB->AmodB |
                           [ action_on_AmodB_fun( AmodB.j, Gamma.i )
                           : j in [1..Ngens(AmodB)]
                           ]
                      >
                 : i in [1..Ngens(Gamma)]
                 ] >;
     action_on_AmodB := 
          hom< Gamma -> Aut(AmodB) | 
               gamma :->  iso< AmodB->AmodB | a :-> action_on_AmodB_hom(gamma)(a), 
                                              a :-> action_on_AmodB_hom(gamma^-1)(a) > >;

     AmodBGG := GammaGroup( Gamma, AmodB, action_on_AmodB );
     
     // lowlevel-access!!!
     AmodBGG`ind_from := A;
     AmodBGG`ind_mod  := A; // XXX dummy value!! this should be A^\circ
     AmodBGG`ind_proj := proj;
     AmodBGG`ind_rep  := r;

     if not assigned(A`F) then
          // MyFPGroup ensures that all relators only contain positive exponents. 
          A`F,
          A`f2gamma := MyFPGroup(ActingGroup(A));
          A`Faction := A`f2gamma * A`action;
     end if;

     AmodBGG`F       := A`F;
     AmodBGG`f2gamma := A`f2gamma;
     AmodBGG`Faction := A`f2gamma * action_on_AmodB;
     
     // 3. compute H^1(Gamma, A/A^\circ) (finite cohomology)
     H1modB := OneCohomology( AmodBGG );

     // 4. lift every c \in H^1(Gamma, A/A^\circ) to H^1(Gamma, A)

     /*
      *   look below for the reason for fhe number of unknowns
      */
     if   ISA(Category(K), FldFin) then
          nr_indets := dim * Ngens(Gamma);
     elif ISA(Category(K), FldAlg) 
       or ISA(Category(K), FldRat) then
          nr_indets := dim * Ngens(Gamma) * Degree(K);
     else
          // can't enter this place since the fields were required above.
     end if;
     
     F<[t]> := RationalFunctionField( K, nr_indets );
     G_F := GroupOfLieType( R, F );
     
     // TODO: maybe just keep G_F somewhere in an attribute of A?
     //       then there is no need in "internal_ExtendGaloisCocycle"

     vprintf verb_galcohom,1 : "Have to do %o extensions\n", #H1modB;
     A`H1 := [ internal_ExtendGaloisCocycle( c, G_F, GBAl ) : c in H1modB ];
     vprintf verb_galcohom,1 : "-"^40;

     return A`H1;
     
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Extending a Galois cocycle                                                 **
**                                                                              **
*********************************************************************************/
intrinsic ExtendGaloisCocycle( c::OneCoC : GBAl := "Walk" ) -> OneCoC
// K::FldFin, k::FldFin, G::GrpLie, c::Map, 
// m::Map, proj::Map ) -> Map
{Given a cocycle c in $H^1(Gal(K:k), Aut_K(G)/(Aut_K(G))_0 )$ extend the cocycle
to a cocycle in $H^1(Gal(K:k), Aut_K(G))$}
     
     AmodB := GammaGroup( c );

     is_ind, A, _, proj, r := IsInduced(AmodB);
     
     require is_ind
         and Category(Group(A)) eq GrpLieAuto 
           : "The Gamma-group of c must be induced from GrpLieAuto.";
     
     G := Domain(Group(A));
     K := BaseRing(G);

/*     require ISA(Category(K), FldFin) 
          or ISA(Category(K), FldAlg) 
          or ISA(Category(K), FldRat) : "G must be defined over FldFin, FldRat or FldAlg";*/
     
     R   := RootDatum(G);
     dim := Dimension(R);
     
     Gamma   := ActingGroup( AmodB );

     /*
      *   look below for the reason for fhe number of unknowns
      */
     if   ISA(Category(K), FldFin) then
          nr_indets := dim * Ngens(Gamma);
     elif ISA(Category(K), FldAlg) 
       or ISA(Category(K), FldRat) then
          nr_indets := dim * Ngens(Gamma) * Degree(K);
     else
          // can't enter this place since the fields were required above.
          nr_indets := dim * Ngens(Gamma) * Degree(K);
     end if;
     
     F<[t]> := RationalFunctionField( K, nr_indets );
     G_F := GroupOfLieType( R, F );

     return internal_ExtendGaloisCocycle( c, G_F, GBAl );

end intrinsic;

/********************************************************************************* 
**                                                                              **
**   internal function for Extending a Galois cocycle                           **
**                                                                              **
**        used from ExtendGaloisCocycle and GaloisCohomology                    **
**                                                                              **
*********************************************************************************/
extendPerm := function( R, p )
  if Degree(p) eq Rank(R) then
    return ExtendDynkinDiagramPermutation( R, p );
  else
    return p;
  end if;
end function;

function internal_ExtendGaloisCocycle( c, G_F, GBAl )

     AmodB := GammaGroup( c );
     
     _, A, _, proj, r := IsInduced(AmodB);
     
     G := Domain(Group(A));
     K := BaseRing(G);
     
     R   := RootDatum(G);
     dim := Dimension(R);
     
     Gamma, m := ActingGroup( A );
     GammaFP  := A`F;
     f2gamma  := A`f2gamma;

     // the set of relators:
     rels := [ LHS(r) * RHS(r)^-1 : r in Relations(GammaFP) ];

     F := BaseRing(G_F);
     t := [F.i:i in [1..Rank(F)]];

     W := WeylGroup(G);
     CW := CartesianProduct([ W : i in [1..Ngens(Gamma)] ]); 
     if   ISA(Category(K), FldFin) then
          // there are no anisotropic forms over finite fields
          CW := [ <W!1 : i in [1..Ngens(Gamma)]> ];          
     
     else     
     //elif ISA(Category(K), FldAlg) 
     //  or ISA(Category(K), FldRat) then
          //
          // this is just a naive approach!   ! VERY SLOW !
          // TODO! actually, what we do here is computation of the cohomology 
          //       of W*D (with the trivial action of Gamma) by extension from
          //       WD/W \simeq D.
          //
          
          CW := [ cw : cw in CW | 
               forall{word:rel in rels| 
                &*[ extendPerm(R,c(Gamma.i))*                       // \tau_{\sigma_i}
                    &*[W|W.j:j in DataAutLie(r(c(Gamma.i)))`i`w] *  //    w_{\sigma_i}
                    cw[i]                                           //    v_{\sigma_i}
                  : i in word ] eq W!1
               where word is Eltseq(rel)}
           ];
     //else
          // can't enter this place since the fields were required above.
     end if;

     extensions := [];
     for v in CW do

     vprint verb_galcohom,1 : "-"^40;
     vprint verb_galcohom,1 : v;
          
          /*
           *   SETTING UP THE EQUATIONS
           */

          /*
           *   Take generic torus elements. One for each generator of Gamma.
           *             -> look at thrm \ref{thm:ext-coc-gal}
           */

          if   ISA(Category(K), FldFin) then
 
               vectors := [ VectorSpace( F, dim ) | [ t[(i-1)*dim + j] : j in [1 .. dim] ]
                                                  : i in [1..Ngens(Gamma)] ];
          else
          //elif ISA(Category(K), FldAlg)
          //  or ISA(Category(K), FldRat) then
               B := Basis(K);
               vectors := [ VectorSpace( F, dim ) | [ &+[ B[k]*t[((i-1)*dim + j-1)*Degree(K)+k ]
                                                  : k in [1 .. Degree(K)] ]
                                                  : j in [1 .. dim] ]
                                                  : i in [1 .. Ngens(Gamma)] ];
          //else
               // can't enter this place since the fields were required
               // before the call of this functions.
          end if;

          tv := [G_F|  elt< G_F | vectors[i], v[i] >: i in [1..Ngens(Gamma)] ];

          /*
           *   These are the elements in B we are looking for:
           */
          b := [ InnerAutomorphism( G_F, x ) : x in tv ];


          /*
           *   now construct one group equation geq for every relator,
           *   more precisely,
           *             geq = One(G_F)
           *   is the actual group equation.
           */
          Aut_G_F := AutomorphismGroup(G_F);
 
          fld_autos_lie := [Aut_G_F| 
          FieldAutomorphism( G, m( f2gamma(GammaFP.i)) ) : i in [1..Ngens(GammaFP)]];
          fld_autos_fld := [ DataAutLie(a)`f : a in fld_autos_lie ];


          /*
           *   the following if-statement is based on experiments.
           *
           *   the first method for construction of the equations seems
           *   to be faster for finite fields. the second one for number fields.
           */

          vprint verb_galcohom,1 : "Group equations:";
          IndentPush();
          vtime verb_galcohom,1 :
          if   ISA(Category(K), FldFin) then

               geqs := [ &*[Aut_G_F|
                                fld_autos_lie[i]
                              * Aut_G_F!r( c( f2gamma(GammaFP.i) ) )
                              * b[i]
                           : i in Eltseq(rel) ]
                       : rel in rels ] ;

          else 
          //elif ISA(Category(K), FldAlg)
          //  or ISA(Category(K), FldRat) then

               geqs := [ &*[Aut_G_F|
                                Aut_G_F!r( c( f2gamma(GammaFP.word[i]) ) )
                              * InnerAutomorphism( G_F, tv[word[i]]@(Aut_G_F!FieldAutomorphism( G, &*([m(Gamma.0)]cat[ m( f2gamma(GammaFP.word[j]))  : j in [i+1..#word]]) )) )
                           : i in [1..#word] ] where word is Eltseq(rel)
                       : rel in rels ] ;
 
          //else
               // can't enter this place since the fields were required
               // before the call of this functions.
          end if;
          IndentPop();

          /*
           *   Collect the data of the group elements:
           */
          data_geqs := [ DataAutLie( geq )`i`h : geq in geqs ];


          /*
           *   now construct the actual polynomial equations.
           *   more precisely,
           *             pol = Zero(K)
           *   is the actual polynomial equation.
           */
          if   ISA(Category(K), FldFin) then
                P<[u]> := PolynomialRing( K, Rank(F) );
          //elif ISA(Category(K), FldAlg)
          //  or ISA(Category(K), FldRat) then
          else
                P<[u]> := PolynomialRing( K, Rank(F) );
          //else
               // can't enter this place since the fields were required
               // before the call of this functions.
          end if;


          vprint verb_galcohom,1 : "Polynomial equations:";
          IndentPush();

          cpols := CenterPolynomials(G_F);
          vtime verb_galcohom,1 :
          eqns := { Evaluate(cpol, [ P | Numerator(p) : p in Eltseq(data_geq) ])  : data_geq in data_geqs, cpol in cpols };

          vprintf verb_galcohom,1 : "Number of pol eqs: %o\n", #eqns;

          /*
           *   SOLVING THE EQUATIONS
           */

          I := Ideal( eqns );

          vprint verb_galcohom,2 : I;
          IndentPop();

// don't use Groebner directly. only from inside of VarietySequence
// 
// printf "Groebner (%o):\n", GBAl;
// IndentPush();
// time
//           Groebner( I : Al:=GBAl );
// IndentPop();


          // need only one solution with no zeros therein:
          vprintf verb_galcohom,1 : "Variety (%o):\n", GBAl;
          IndentPush();
          vtime verb_galcohom,1 :
          V := VarietySequence( I, 1 : Al:=GBAl ); //, func<t| 0 notin [t[i]:i in [1..#t]] > );
          IndentPop();

          if IsEmpty(V) then
               error "No extensions found";
          end if;
 
// V;Universe(V);
// ChangeUniverse(~V,BaseField(K));
          /*
           *   build up the extended cocycle from a solution:
           */

          if   ISA(Category(K), FldFin) then
                Vnew := V[1];

          else
          //elif ISA(Category(K), FldAlg)
          //  or ISA(Category(K), FldRat) then
               // B := Basis(K); defined above
               deg := Degree(K);
               Vnew := [  &+[ V[1][i+k-1] : k in [1..deg] ] : i in [1..deg*dim by deg] ];
          //else
               // can't enter this place since the fields were required
               // before the call of this functions.
          end if;

          M := Matrix( K, Ngens(Gamma), dim, Vnew );

          Append(~extensions,
                  OneCocycle( A, [ r(c(Gamma.i))*InnerAutomorphism(G,elt<G|M[i],v[i]>) : i in [1..Ngens(Gamma)] ]
                             : Check:=false
                             ));

     end for;
     
     return extensions;
     
end function;












/*********************************************************************************
**                                                                              **
**   Compute the orders of the cyclic components of the twisted torus           **
**   T_w\sigma as sequence of polynomials in q, the order of the field          **
**                                                                              **
*********************************************************************************/
intrinsic TwistedTorusOrder( R::RootDtm, w::GrpPermElt  ) -> SeqEnum
{Computes the orders of the cyclic components of the twisted torus $T_w(k)$
as sequence of polynomials in q, the order of the field}

     require not IsTwisted(R) : "TwistedTorusOrder not implemented for twisted root data yet";

     W  := Parent(w);

     require Category(W) eq GrpPermCox 
         and RootDatum(W) eq R : "w must be an element of the Weyl group";

     l  := Rank(R);
     d  := Dimension(R);

     r  := Order(w);
     
     Wfp, ho := CoxeterGroup( GrpFP, W );
     // ho : W -> Wfp

     word := Eltseq(ho(w));

     Z  := Integers();
     A  := MatrixAlgebra(Z ,d);
     M  := &*[A| CoreflectionMatrix(W,i) : i in word ];

assert Order(M) eq r;

     cp := CharacteristicPolynomial(M);
     P  := Parent(cp);
     AssignNames(~P,["q"]);
     Q := PolynomialRing(Rationals()); Y := Q.1;

     // for type A:
//      iso_type := [ FactorisationToPolynomial(o) : o in OneOfEach(Factorisation(cp))];

     // for all types:
     S<s>  := quo< Q | Y^r-1 >;
//     MA := MatrixAlgebra(R, NumberOfRows(M));
     M1 := (s*M) - A!1; // MA!(s*M) - A!1
     D := SmithForm(M1);
     iso_type := [P| D[i,i] eq 0 select Modulus(S) else D[i,i]: i in [1..NumberOfRows(D)] | D[i,i] ne 1 ];
     
assert cp eq &*iso_type;

     qs := [ k : k in [2..20] | IsPrimePower(k) ];

     expected := [];
     ab_inv := [];
     
     
     for q in qs do;
          Zr := quo< Z | q^r - 1 >;
          Ar := MatrixAlgebra(Zr,d);

          V := RSpace(Zr,d);
          ES := Eigenspace(Ar!(q*M),1);
          j := -1;
          repeat
               j +:= 1;
               B  := Basis(ES);
               ES := sub<V|B>;
          until B eq Basis(ES);
          if j gt 0 then "."^j; end if;
// debug output:
//           if j gt 0 then 
//                q;
//                Zr;
//                Ar!(q*M);
//           end if;
          if #ES ne Evaluate(cp,q) then
               print "BIG FAT WARNING: EigenSpace has WRONG SIZE!!!";
               printf "%o: %o (expected %o)\n", q, #ES, Evaluate(cp,q);
          end if;

          /*
           * We have to do some more work.
           * What we basically do here, is computation of the AdditiveGroup(ES)
           *
           */
 
          F := FreeAbelianGroup(#B);
          rels:= [F|];

          for i in [1..#B] do;
               b := B[i];

               Append(~rels, #sub<ES|b>*F.i);
 
               U := sub<ES|B[1..i-1]>;

               if #U*#sub<ES|b> ne #sub<ES|B[1..i]> then
                    t := #sub<ES|B[1..i]> div #U;
                    if not t*b in U then
                         word;
                    end if;
                    assert t*b in U;
                    sol := Eltseq(Solution(Matrix(B[1..i-1]),t*b));
                    ChangeUniverse(~sol,Z);
                    Append(~rels, t*F.i - &+[sol[j]*F.j : j in [1..i-1]]);
               end if;
          end for;

          A,h := quo<F|rels>;
     
          ab_inv[q] := AbelianInvariants(A);
     end for;
     
     for q in qs do;
          expected[q] := [ Evaluate(p,q): p in iso_type ];
     end for;
     if forall{q:q in qs | AbelianInvariants(AbelianGroup(expected[q])) eq ab_inv[q]} then
          // we are done
     
          // return [* iso_type, cp, t_ordrs, , t_order, w *];
          return iso_type;
     end if;
"Stage 1";
     ab_inv_temp := ab_inv;
     temp_iso_type := iso_type;
     new_iso_type := [];
     i := 1;
     while i le #temp_iso_type do
          if forall{ q:q in qs | expected[q][i] in ab_inv_temp[q] or expected[q][i] eq 1 } then
               Append(~new_iso_type, temp_iso_type[i]);
               Remove(~temp_iso_type, i);
               for q in qs do;
                    Exclude(~ab_inv_temp[q], expected[q][i]);
                    Remove (~expected[q],i);
               end for;
          else
               i +:= 1;
          end if;
     end while;
// temp_iso_type;
// new_iso_type;
     left := [];
     for p in temp_iso_type do;
          found := false;
          factors := &cat[ [f[1] : i in [1..f[2]]] : f in Factorization(p) ];
          for f in factors do
               split := [f,&*Exclude(factors,f)];
               abis := [];
               for q in qs do;
                    abis[q] := AbelianInvariants(AbelianGroup([Evaluate(s,q):s in split]));
               end for;
               if forall{q:q in qs | abis[q] subset ab_inv_temp[q] } then
                    found := true;
                    new_iso_type cat:= split;
                    for q in qs, a in abis[q] do;
                         Exclude(~ab_inv_temp[q],a);
                    end for;
                    break;
               end if;
          end for;
          if not found then
               Append(~left,p);
          end if;
     end for;
// ab_inv_temp := ab_inv;
// temp_iso_type := iso_type;
// new_iso_type := [];
// left := iso_type;
     if not IsEmpty(left) then
//IndentPush();
"Stage 2";
          found := false;
          left := &*left;
          factors := &cat[ [f[1] : i in [1..f[2]]] : f in Factorization(left) ];
          //
          // TODO: to speedup, compute not all partitions at once
          //       but for every partition type separately.
          //       though, the speed is not a problem at all up to rank 10.
          //
          allpart := AllPartitions({1..#factors});
          for p in allpart do
               subtype := [ &*factors[Setseq(s)] : s in p ];
               abis := [];
               for q in qs do;
                    abis[q] := AbelianInvariants(AbelianGroup([Evaluate(s,q):s in subtype]));
               end for;
               if forall{q:q in qs | abis[q] eq ab_inv_temp[q] } then
                    found := true;
                    new_iso_type cat:= subtype;
                    for q in qs, a in abis[q] do;
                         Exclude(~ab_inv_temp[q],a);
                    end for;
                    break;
               end if;
          end for;
          if not found then
               error "no partition found";
          end if;
//IndentPop();
     end if;

assert cp eq &*new_iso_type;

     for q in qs do;
          expected[q] := [ Evaluate(p,q): p in new_iso_type ];
     end for;
     
     if forall{q:q in qs | AbelianInvariants(AbelianGroup(expected[q])) eq ab_inv[q]} then
          // now, finally, we are done
     
          // return [* iso_type, cp, t_ordrs, , t_order, w *];
          return new_iso_type;
     end if;

     print "oops"; word;
     AbelianInvariants(A);
     return iso_type;


end intrinsic;

/*********************************************************************************
**                                                                              **
**   Compute twisted torus T_w\sigma                                            **
**                                                                              **
**   returns a list with three components:                                      **
**    - sequence of orders of cyclic components                                 **
**    - sequence of generators (having orders given in the first sequence)      **
**    - w                                                                       **
**                                                                              **
*********************************************************************************/
intrinsic TwistedTorus( G::GrpLie, w::GrpPermElt : KnownOrder := [] ) -> List
{Computes the twisted torus $T_w(k)$}
     require not IsTwisted(RootDatum(G)) : "TwistedTorus not implemented for twisted groups yet";

     k  := BaseRing(G);
     W  := Parent(w);

     require ISA(Category(k), FldFin) : "G must be defined over a finite field";
     require RootDatum(W) eq RootDatum(G) : "w must be an element of the Weyl group of G";

     R  := RootDatum(G);

     if IsEmpty(KnownOrder) then
          TO := TwistedTorusOrder(R,w);
     else
          TO := KnownOrder;
     end if;

     q  := #k;

     // actual orders over the given field.
     t_ordrs := [ Evaluate(p,q) : p in TO ];

     l  := Rank(R);
     d  := Dimension(R);
     r  := Order(w);
     
     Wfp, ho := CoxeterGroup( GrpFP, W );
     // ho : W -> Wfp

     word := Eltseq(ho(w));

     Z  := Integers();
     A  := MatrixAlgebra(Z ,d);
     M  := &*[A| CoreflectionMatrix(W,i) : i in word ];

assert Order(M) eq r;

     Zr := quo< Z | q^r - 1 >;
     Ar := MatrixAlgebra(Zr,d);

     V := RSpace(Zr,d);
     ES := Eigenspace(Ar!(q*M),1);
     j := -1;
     repeat
          j +:= 1;
          B  := Basis(ES);
          ES := sub<V|B>;
     until B eq Basis(ES);
     if j gt 0 then "."^j; end if;

     /*
      * We have to do some more work.
      * What we basically do here, is computation of the AdditiveGroup(ES)
      *
      */
 
     F := FreeAbelianGroup(#B);
     rels:= [F|];

     for i in [1..#B] do;
          b := B[i];

          Append(~rels, #sub<ES|b>*F.i);
 
          U := sub<ES|B[1..i-1]>;

          if #U*#sub<ES|b> ne #sub<ES|B[1..i]> then
               t := #sub<ES|B[1..i]> div #U;
               if not t*b in U then
                    word;
               end if;
               assert t*b in U;
               sol := Eltseq(Solution(Matrix(B[1..i-1]),t*b));
               ChangeUniverse(~sol,Z);
               Append(~rels, t*F.i - &+[sol[j]*F.j : j in [1..i-1]]);
          end if;
     end for;

     A,h := quo<F|rels>;
     
     ab_inv := AbelianInvariants(A);

     T := AbelianGroup(t_ordrs);
     if not AbelianInvariants(T) eq ab_inv then
          word;
          t_ordrs;
          AbelianInvariants(T);
          ab_inv;
     end if;

assert AbelianInvariants(T) eq ab_inv;

     A1,m := AbelianGroup(T); 
     // A1 \simeq A, same orders of generators;
     id := iso<A->A1|a:->A1!Eltseq(a), a:->A!Eltseq(a)>;

     exponents := [ &+[ES| word[i]*B[i] : i in [1..#word] ] 
                         where word is Eltseq((T.j)@(m*(id^-1)*(h^-1)))
                  : j in [1..#TO] ];
 
     // create the group over the large field:
     K   := GF(q^r);
     xi  := PrimitiveElement(K);
     G_K := BaseExtend(G,K);
     V_K := VectorSpace(K,d);

     /*
      *   Now the generators are THE ONES generating the cyclic
      *   parts of the standard decomposition (orders given by t_ordrs)
      *
      */
     t_gens  := [G_K|   elt<G_K|V_K![ xi^(Z!a) :a in Eltseq(e)]>   : e in exponents ];

     ass := [ Order(t) : t in t_gens ] eq t_ordrs;

     assert ass;

     return [* t_ordrs, t_gens, w *];

end intrinsic;

declare attributes GrpLie: TwistedTori;
declare attributes RootDtm: TwistedToriOrders;



intrinsic TwistedToriOrders( G::GrpLie ) -> SeqEnum
{Returns orders of all maximal twisted tori (up to conjugacy) of G}
     require not IsTwisted(RootDatum(G)) : "TwistedToriOrders not implemented for twisted groups yet";

     k := BaseRing(G);
     require ISA( Category(k), FldFin ) : "G must be defined over a finite field";
     return TwistedToriOrders(RootDatum(G));
end intrinsic;

intrinsic TwistedToriOrders( R::RootDtm ) -> SeqEnum
{Returns orders of all maximal twisted tori (up to conjugacy) of the group with the given root datum.}

     require not IsTwisted(R) : "TwistedToriOrders not implemented for twisted root data yet";

     if not assigned R`TwistedToriOrders then
          W    := CoxeterGroup(R);
          Wfp, ho := CoxeterGroup( GrpFP, W );
          cls  := ConjugacyClasses(W);
          reps := [ r[3] : r in cls ];
/*
 * try to find a representative with smallest possible length + lex order
 * this algo is randomised and doesn't guarantee to give the best possible representative.
 *
 *           for j in [1..#reps] do;
 *                printf "%o -> ", Length(W,reps[j]);
 *                i:=0;
 *                while i lt 10000 do;
 *                     i +:=1;
 *                     c := Random(W);
 *                     v := reps[j]^c;
 *                     if Length(W,v) lt Length(W,reps[j]) 
 *                     or Length(W,v) eq Length(W,reps[j])
 *                     and ho(v) lt ho(reps[j]) then
 *                          reps[j] := v;
 *                          i := 0;
 *                     end if;
 *                end while;
 *                printf "%o\n", Length(W,reps[j]);
 *           end for;
 */
          
          R`TwistedToriOrders := [ [* TwistedTorusOrder(R,w), w *] : w in reps ];
     end if;

     return R`TwistedToriOrders;

end intrinsic;

intrinsic TwistedTori( G::GrpLie ) -> SeqEnum
{Returns all maximal twisted tori (up to conjugacy) of $G$}

     require not IsTwisted(RootDatum(G)) : "TwistedTori not implemented for twisted groups yet";

     if not assigned G`TwistedTori then
          TO := TwistedToriOrders(G);

          G`TwistedTori := [ TwistedTorus( G, t[2] : KnownOrder:=t[1] ) : t in TO ];
     end if;

     return G`TwistedTori;

end intrinsic;



/*********************************************************************************
**                                                                              **
**   Compute rational torus T_w\sigma                                           **
**                                                                              **
**   takes a list returned by TwistedTorus and replaces conjugates the          **
**   sequence of generators into the group G.                                   **
**                                                                              **
**   Uses Lang.                                                                 **
**                                                                              **
*********************************************************************************/
/* commented out -- missing Lang
intrinsic RationalTorus( G::GrpLie, T::List ) -> List
{Returns the rational torus in $G$ isomorphic to the twisted torus $T$.}

     require true : " TODO: require some stuff ";

     if Universe(T[2]) eq G then 
          gen_rat := T[2];
     else
          k := BaseRing(G);
          q := #k;

          F := func< x | Parent(x)![ a^q : a in Eltseq(x) ] >;

          R := RootDatum( G );
          d := Dimension(R);

          rho := StandardRepresentation(G);

          w := T[3];
          wdot := elt<G|w>;

          c := rho(wdot);
print "Lang start.";
          a := Lang(Matrix(c),q);
          // test:
          assert F(a) * a^-1 eq Parent(a)!c;
print "Lang done.";


          gens := T[2];

          G_w := Universe( gens );
          K_w := BaseRing( G_w );
          rho := StandardRepresentation(G_w);

          gen_mats := rho(gens);

          Ka := BaseRing(Parent(a));
          Gl := GL(Rank(a), Ka);
          a  := (Gl!a);

          gen_mats_rat := [GL(Rank(a),k)| (Gl!gen_mat) ^ a : gen_mat in gen_mats ];

          // computation of ohr is OK but
          // ohr itself is VERY SLOW. SKIP THAT FOR NOW!
          //
          ohr := RowReductionHomomorphism(rho);
          gen_rat := [G| ohr(gmr) : gmr in gen_mats_rat ];
     end if;
     
     return [* T[1], gen_rat, T[3] *];

end intrinsic;

*/




FactToString := function(list)
     str := &*[ IntegerToString(l[1]) * "^" * IntegerToString(l[2]) * " * " : l in list ];
     return str[1..#str-3];
end function;

SeqToString := function(seq)
     str := &*[ IntegerToString(l) * ", " : l in seq ];
     return "[ " * str[1..#str-2] * " ]";
end function;

intrinsic PrintSylowSubgroupStructure( G::GrpLie ) 
{Prints the structure of the Sylow subgroups of G}
     k := BaseRing(G);
     W := WeylGroup(G);
     
     fact := FactoredOrder(G);
     print G;
     print "Order(G) is ", FactToString(fact);
     print "Order(W) is ", FactToString(Factorisation(#W));

print "...compute tori...";
     TORI := TwistedTori( G );

print "...compute sylows...";
     for t in fact do
          p := t[1];
          e := t[2];

          if p eq Characteristic(k) then     
               print "  ", p, "(GOOD) : The unipotent subgroup of G";
          else
               pIsGood := (#W mod p) ne 0;
               // now look in which tori p^e is contained:
               if pIsGood then
                    tori := [ torus[1] : torus in TORI | &*torus[1] mod q eq 0 ] where q := p^e;
               else // if p is not good
                    tori := [Parent([1])|];
                    for torus in TORI do                    
                         C := Centraliser(W, torus[3]);
                         gcd := GCD(p^e,#C);
                         f := gcd eq 1 select 0 else Factorisation(gcd)[1][2];
                         // print "centraliser of ", t[4], " has order ", #C, gcd, f ;

                         if &*torus[1] mod (p^(e-f)) eq 0 then
                              Append(~tori, torus[1] cat ((f eq 0) select [] else [-p^f]) );
                         end if;
                    end for;
               end if;

               for torus in tori do
                    _ := exists(e){ f[2] : f in Factorisation(&*torus) | f[1] eq p };
                    print "  ", p, pIsGood select "(good)" else "(bad) ", ":", e, SeqToString(torus);
               end for;

          end if;
     end for;
     
end intrinsic;

intrinsic SylowSubgroup( G::GrpLie, p::RngIntElt ) -> List
{A Sylow p-subgroup of G as a list of orders of generators, generators, and other things.}

     require IsPrime(p) : "Argument p (", p, ") should be prime";

     k := BaseRing(G);
     W := WeylGroup(G);
     Wfp,ho := CoxeterGroup(GrpFP,W);
     word := func<v|Eltseq(ho(v))>;
     
     fact := FactoredOrder(G);

     if exists(t){ factor : factor in fact | factor[1] eq p } then
          e := t[2];

          if p eq Characteristic(k) then
               print "  ", p, "(GOOD) : The unipotent subgroup of G";

               return [* [], 
                    [ elt<G|<r,x>> : x in Basis(k), r in [1..#PositiveRoots(G)] ]
                     *];
          else
               print "...compute tori...";
               TORI := TwistedTori( G );

               pIsGood := (#W mod p) ne 0;
               // now look in which tori p^e is contained:
               if pIsGood then
                    tori := [ torus : torus in TORI | &*torus[1] mod q eq 0 ] where q := p^e;
               else // if p is not good
                    tori := [Universe(TORI)|];
                    for torus in TORI do                    
                         C := Centraliser(W, torus[3]);
                         gcd := GCD(p^e,#C);
                         f := gcd eq 1 select 0 else Factorisation(gcd)[1][2];
                         // print "centraliser of ", t[4], " has order ", #C, gcd, f ;

                         if &*torus[1] mod (p^(e-f)) eq 0 then
//                              torus[2] := torus[2] cat [-p^f];
//                              Append(~torus[2], -p^f);
                              Append(~tori, [* torus[1] cat [-p^f], // add the p-part from the normaliser.
                                               torus[2],
                                               torus[3]
                                             *]   );
                         end if;
                    end for;
               end if;

               //
               // now the sequence tori contains all tori containing a Sylow subgroup.
               // (in case of a bad prime, tori whos normaliser contains a Sylow)
               //

               //
               // now which one do we take??? 
               // the one according to the following algorithm:
               //
               // 1. if p is bad, then choose tose with the smallest part in C_W(w)
               //                 and largest part in the torus.
               //    if p is good, do nothing.
               //
               // 2. after that choose those tori who's Weyl conjugacy class has the 
               //    smallest length. (i.e. the most diagonal torus)
               //
               // 3. if still more than one torus is left, choose one randomly.
               //    or choose the lexicografically smallest one.
               //
               
#tori;
               if not pIsGood then
                    //
                    // 1---choose only those with the smallest part in the centraliser.
                    //
                    min_c_part := Max({ torus[1][#(torus[1])] : torus in tori });
                    tori := [ torus : torus in tori | torus[1][#(torus[1])] eq min_c_part ];
               end if;

               //
               // 2. for now just take the first available torus:
               //    (once Geck-Pfeiffer methods are implemended for Weyl grps,
               //     this will be more or less for free.)
               //
#tori;
               torus := tori[1];     
               _ := exists(f){ f[2] : f in Factorisation(&*torus[1]) | f[1] eq p };
               print "  ", p, pIsGood select "(good)" else "(bad) ", ":", f, SeqToString(torus[1]);

               t_ordrs := torus[1];                 
               t_gens  := torus[2];                 
torus[3];               
               s_ordrs := [Universe(t_ordrs)|];
               s_gens  := [Universe(t_gens)|];

               //
               // create generators coming from the torus:
               //
               for i in [1..#t_gens] do;               
                    if exists(k){ f[2] : f in Factorisation(t_ordrs[i]) | f[1] eq p } then

                         Append(~s_ordrs, p^k );
                         //
                         // It takes some time to raise to a high power.
                         // tori elts. shouldn't be that hard to be multiplied.
                         // chack what's happening here.
                         //
                         // maybe the tori are multiplied 10000 times instead of taking
                         // the entries into the correct power.
                         //
                         Append(~s_gens,  t_gens[i]^ExactQuotient(t_ordrs[i],(p^k)) );
                    end if;
               end for;

               if not pIsGood then
                    G_K := Universe(s_gens);
                    c_ordr := -t_ordrs[#t_ordrs];

                    // if c_ordr is 1 then we are done.

                    if c_ordr gt 1 then
                         time
                         S := SylowSubgroup(Centraliser(W,torus[3]),p);
                         assert #S eq c_ordr;
                         Sfp,hoS := MyFPGroup(S);

                         G_K := Universe(s_gens);
                         K := BaseRing(G_K);
                         l := Rank(G_K);
                         F<[t]> := RationalFunctionField(K, l*Ngens(S) );
                         G_F := BaseExtend(G_K,F);
                         
                         if p ne 2 then
                              wdots := [ (Sidot)^(Order(Sidot) div Order(S.i))
                                                  where Sidot is elt<G_K|S.i>        : i in [1..Ngens(S)] ];
                         elif p eq 2 then
                              wdots := [  Sidot   where Sidot is elt<G_K|S.i>        : i in [1..Ngens(S)] ];
                         end if;

                              // just take all of 
                         for i in [1..Ngens(S)] do;
                              o := Order(S.i);
                              wdot := wdots[i];
                              Append(~s_ordrs, -o );
                              Append(~s_gens, wdot);
                         end for;
                         
//                          hps   := [ elt<G_F|VectorSpace(F,l)!t[(i-1)*l+1..i*l]> : i in [1..Ngens(S)] ];
//                          hws   := [ hps[i]*wdots[i]                             : i in [1..Ngens(S)] ];
//                          
//                          rels  := [ Eltseq(LHS(r)) : r in Relations(Sfp) ];
// 
//                          phs   := [ &*[ hws[i] : i in r ]  : r in rels ];
//                          pols  := Setseq(&join{ { Numerator(p)-Denominator(p) : p in Eltseq(Eltlist(ph)[1])  } : ph in phs });
//                          sol   := Rep(find_any_solution(pols, "Default"));
// 
//                          for i in [1..Ngens(S)] do;
//                               o := Order(S.i);
//                               wdot := wdots[i];
//                          wdots := [ (Sidot)^(Order(Sidot) div Order(S.i))
//                                              where Sidot is elt<G_K|S.i>        : i in [1..Ngens(S)] ];
// //                               
// //                               if wdot^o eq 1 then
// //                                    h := G_K!1;
// //                               else
// //                                    // find the RIGHT torus elements h, such that o(h wdot) = o(w)
// //                                    pols := [ Numerator(p)-Denominator(p) : p in Eltseq(Eltlist(ph)[1]) ];
// //                                    h := elt<G_K|VectorSpace(K,#t)!sol>;
// //                               end if;
//                               Append(~s_ordrs, -o );
//                               Append(~s_gens, wdot);
//                               assert (wdot)^o eq 1;
//                          end for;
                    end if;
                                        
               end if;

               assert forall{i : i in [1..#s_gens] | s_ordrs[i] lt 0 or Order(s_gens[i]) eq s_ordrs[i] };
               
               return [* s_ordrs, s_gens *];

          end if;

     else;
          return [* [ 1 ], [ Id(G) ] *];
     end if;


end intrinsic;





/*********************************************************************************
**                                                                              **
**   AUXILIARY FUNCTIONS                                                        **
**                                                                              **
*********************************************************************************/



/*********************************************************************************
**
**   compute A/A^\circ  for A := Aut_K(G)
**        at the moment, only graph autos are computed.
**
*/
function AmodAnod( G )

//   It is  T/(T \cap A^\circ) = 1  where T - max. Torus of A
//   since T=C is connected (C is the Cartan subgroup)
//   in other words, we don't need outer diagonal representatives.

//   All Graph Automorphisms:

     R := RootDatum(G);
     S := AutoDD(R);
     p := Characteristic( BaseRing(G) );
     
     gens := [ S.i : i in [1..Ngens(S)] | checkPerm( R, S.i, p ) ];
     
     S := sub<S|gens>;
     _ := #S;

     // representative map:
     // m := map<S->AutomorphismGroup(G)| s:-> GraphAutomorphism(G, s) >;

     return S;//, m;

     
end function;











/******************************************************************************
 **
 **   Solving the equations
 **      (these functions are independant from the rest.)
 **
 **/

solveSystemRec := function(eqns, unknowns, solns)
  if unknowns eq 0 then
    return solns;
  end if;

  if IsEmpty(eqns) then
//    eqns:Magma;unknowns;solns;
    roots := BaseRing(Universe(eqns));
  else
    I := Ideal( eqns );
    EI := EliminationIdeal( I, unknowns-1 );
    B := Basis(EI);
    if #B eq 0 then
      roots := BaseRing(I);
    else
      roots := &meet[{eqnRoots[j][1] : j in [1..#eqnRoots]}
      where eqnRoots is Roots(UnivariatePolynomial(B[i]))
      : i in [1..#B]];
    end if;
  end if;

// Torus special:
//   roots := [ r : r in roots | r ne 0 ];

  solns := &join{$$(newEqns, unknowns - 1, {[root] cat soln}) 
    where newEqns is
    [ Universe(eqns)| ev : eqn in eqns | ev ne 0 
      where ev is Evaluate(eqn, unknowns, root)]
    : root in roots, soln in solns};
				
  return solns;
end function;

solveSystem := function( eqns )
  unknowns := Rank( Universe( eqns ) );
  solns := { [] };
  return solveSystemRec( Setseq(eqns), unknowns, solns );
end function;

/**
 **
 **   This is a new version, which goes for depth first
 **   and returns the first found solution (since we only need one).
 **
 **
 **/

function find_any_solutionRec(eqns, unknowns, soln, GBAl)
     if unknowns eq 0 then
          return soln;
     end if;

     I := Ideal( eqns );
     EI := EliminationIdeal( I, unknowns-1 : Al:=GBAl);
     B := Basis(EI);
     if #B eq 0 then
          roots := BaseRing(I);
          if ISA(Category(BaseRing(I)),FldRat) or ISA(Category(BaseRing(I)),FldNum) then
               roots := {BaseRing(I)|1};
          end if;
     else
          roots := &meet[ {eqnRoots[j][1] : j in [1..#eqnRoots]}
                              where eqnRoots is Roots(UnivariatePolynomial(B[i]))
                        : i in [1..#B]];
     end if;

     for root in roots do
          if root eq 0 then continue; end if;
          newEqns := [Universe(eqns)| ev : eqn in eqns | ev ne 0
               where ev := Evaluate(eqn, unknowns, root) ];
          R := $$( newEqns, unknowns - 1, [root] cat soln, GBAl );
          if not IsEmpty(R) then return R; end if;
     end for;

     return [];

end function;

function find_any_solution( eqns, GBAl )
     unknowns := Rank( Universe( eqns ) );
     solns := [];
     ret := find_any_solutionRec( eqns, unknowns, solns, GBAl );
     return IsEmpty(ret) select {} else {ret};
end function;
/******************************************************************************/


// /*                                                                                                          *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                                        '''                                                               *
//  *      DDDDDDD      OOOOO    NN      NN  '''  TTTTTTTT        LL         OOOOO      OOOOO    KK  KK        *
//  *      DD    DD    OO   OO   NNN     NN   ''     TT           LL        OO   OO    OO   OO   KK KK         *
//  *      DD     DD  OO     OO  NNNN    NN          TT           LL       OO     OO  OO     OO  KKKK          *
//  *      DD     DD  OO     OO  NN NN   NN          TT           LL       OO     OO  OO     OO  KKK           *
//  *      DD     DD  OO     OO  NN  NN  NN          TT           LL       OO     OO  OO     OO  KKKK          *
//  *      DD     DD  OO     OO  NN   NN NN          TT           LL       OO     OO  OO     OO  KK KK         *
//  *      DD    DD    OO   OO   NN    NNNN          TT           LL        OO   OO    OO   OO   KK  KK        *
//  *      DDDDDDD      OOOOO    NN     NNN          TT           LLLLLLLL   OOOOO      OOOOO    KK   KK       *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                     BBBBBB    EEEEEEEE  LL         OOOOO     WW          WW      !!                      *
//  *                     BB   BB   EE        LL        OO   OO    WW          WW      !!                      *
//  *                     BB   BB   EE        LL       OO     OO    WW        WW       !!                      *
//  *                     BBBBBB    EEEEEE    LL       OO     OO    WW        WW       !!                      *
//  *                     BB   BB   EE        LL       OO     OO     WW  WW  WW        !!                      *
//  *                     BB    BB  EE        LL       OO     OO     WW  WW  WW        !!                      *
//  *                     BB    BB  EE        LL        OO   OO       WWWWWWWW                                 *
//  *                     BBBBBBB   EEEEEEEE  LLLLLLLL   OOOOO        WWW  WWW         !!                      *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                                 Experimental stuff  --  not finished !!!                                 *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                                                                                                          *
//  *                                                                                                          *
//  */
// 
// 
// 
// 
// 
// /*
// 
// 
// intrinsic AreCohomologousLie( c::Map, b::Map ) -> BoolElt
// { ... Are the cocycles c, b cohomologous? ... }
// 
//      // TODO: Check 1) c,b _are_ cocycles 
//      //             2) c,b are defined for the same GrpLie
//      require   Domain( c ) eq   Domain( b ) and
//              Codomain( c ) eq Codomain( b ) : "Invalid cocycles";
//      
//      Gamma := Domain( c );
//      G := Domain(Codomain( c ));
//      
//      return exists{ a : a in AutosToCheck( G ) |  
//                     forall{ g : g in Generators(Gamma) |
//                                    // g must be replaced by the corresponding field automorphism
//                                    // of G.
//                                    IsAlgebraicallyEqual( b(g),  a * c(g) 
//                                          * Inverse(FieldAut(g)) * Inverse(a) * FieldAut(g) 
//                                         )
//                           }
//                   };
// 
// end intrinsic;
// 
// 
// 
// */
