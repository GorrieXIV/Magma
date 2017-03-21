freeze;

/********************************************************************************* 
**                                                                              **
**   $Id: cohom.m,v 1.35 2005/06/22 11:18:43 gc1007 Exp $                       **
**                                                                              **
**   Sergei Haller <Sergei.Haller@math.uni-giessen.de>                          **
**                                                                              **
**      Magma code  for creation of OneCocycles, computation of the first       **
**      non-abelian  group cohomology.  That is,  H^1(Gamma,A) where A is       **
**      not necessarily abelian.                                                **
**                                                                              **
**      Also the technical implementation of the object OneCoC is in here       **
**      like printing, coercion functions etc.                                  **
**                                                                              **
*********************************************************************************/



declare attributes OneCoC: 
     coc       ,    // the actual map: Gamma -> A
     A         ,    // the Gamma-group of the cocycle
     imgs      ,    // the images of generators of Gamma under the cocycle
     class     ,    // this is the cohomology class (indexed set) of the cocycle (once computed)
     interelts ;    // indexed set of intertwining elements of a class element to the
                    // element class[1] (computed along with the class)



forward check_cocycle;
forward check_imgs;
forward is_in_ker_delta_one;
forward lex_increase;





/********************************************************************************* 
**                                                                              **
**   Construction of a 1-cocycle                                                **
**                                                                              **
**   A     -- a Gamma-group                                                     **
**                                                                              **
**   imgs  -- sequence of images of the generators                              **
**            Gamma.1, Gamma.2, ..., Gamma.n of Gamma under the cocycle         **
**                                                                              **
**   Check -- (optional). For internal use only.                                **
**            If set to false, neither arguments nor cocycle conditions         **
**            are checked.                                                      **
**                                                                              **
*********************************************************************************/
intrinsic OneCocycle( A::GGrp, imgs::SeqEnum : Check := true ) -> OneCoC
{Return a 1-cocycle on A defined by the sequence imgs.}
     //
     // the following check is just a disadvantage of 
     // GrpLieAuto not being derived from Grp
     //
     require ISA(ExtendedCategory(imgs), SeqEnum[GrpElt])
          or ISA(ExtendedCategory(imgs), SeqEnum[GrpLieAutoElt])
          : "Bad argument types\nimgs must be one of SeqEnum[GrpElt], SeqEnum[GrpLieAutoElt]";


     if Check then
          // check if imgs make sense at all
          ret, msg := check_imgs( A, imgs );
          require ret : msg;
     end if;

     // Actually define the map.
 
          if not assigned(A`F) then
               A`F,
               A`f2gamma := FPGroup(A`Gamma);
               A`Faction := A`f2gamma * A`action;
          end if;
 
          F       := A`F;
          Faction := A`Faction;
          gamma2f := Inverse(A`f2gamma);
 
          /*
          **  Implement the Cocycle by this Rule:
          **     let word be some product of generators of F:  word = g_1^e_1 * ... * g_n^e_n
          **     where e_n \in {+1,-1}. set w:=g_n then
          **         c(word) =  c( word' * w    ) = c(word')^w * c(w)
          **         c(word) =  c( word' * w^-1 ) = c(word')^(w^-1) * c(w^-1)
          **                                      = c(word')^(w^-1) * c(w)^(-w^-1)
          **                                      = ( c(word') * c(w)^-1 )^(w^-1)
          */

          function coc_fun( word )
               if IsEmpty(word) then
                    return Id(A`A);
               else
                    i := word[#word];
                    return i gt 0 select Faction( F.i )( coc_fun( Remove(word, #word) ) ) * imgs[i]
                                    else Faction( F.i )( coc_fun( Remove(word, #word) )  * imgs[-i]^-1 );
                                    // note that for i<0 we can use F.i as well: in this case
                                    // F.i is the same as (F.(-i))^-1
               end if;
          end function;

          coc := map< ActingGroup(A) -> Group(A) | g :-> coc_fun( Eltseq(gamma2f(g)) ) >;

     if Check then
          // Check the cocycle condition
          require check_cocycle( A, coc ) : "imgs doesn't define a 1-cocycle on A";
     end if;
 
     alpha := HackobjCreateRaw(OneCoC);

     alpha`coc      := coc;
     alpha`A        := A;
     alpha`imgs     := imgs;

     return alpha;
end intrinsic;


intrinsic OneCocycle( A::GGrp, alpha::Map[Grp,Grp] : Check := true ) -> OneCoC
{Return a 1-cocycle on A defined by the map alpha.}

     if Check then
          // check if map makes sense at all
          require Domain(alpha)   eq ActingGroup(A) : "Domain of alpha must be the group acting on A";
          require Codomain(alpha) eq Group(A)       : "Codomain of alpha must be the group associated with A";
     end if;

     if Check then
          // Check the cocycle condition
          require check_cocycle( A, alpha ) : "alpha is not a 1-cocycle on A";
     end if;

     alph := HackobjCreateRaw(OneCoC);

     alph`coc      := alpha;
     alph`A        := A;
     alph`imgs     := [ alpha(ActingGroup(A).i) : i in [1..Ngens(ActingGroup(A))] ];

     return alph;
end intrinsic;

intrinsic OneCocycle( A::GGrp, alpha::HomGrp : Check := true ) -> OneCoC
{Return a 1-cocycle on A defined by the map alpha.}

     if Check then
          // check if map makes sense at all
          require Domain(alpha)   eq ActingGroup(A) : "Domain of alpha must be the group acting on A";
          require Codomain(alpha) eq Group(A)       : "Codomain of alpha must be the group associated with A";
     end if;

     if Check then
          // Check the cocycle condition
          require check_cocycle( A, alpha ) : "alpha is not a 1-cocycle on A";
     end if;

     alph := HackobjCreateRaw(OneCoC);

     alph`coc      := alpha;
     alph`A        := A;
     alph`imgs     := [ alpha(ActingGroup(A).i) : i in [1..Ngens(ActingGroup(A))] ];

     return alph;
end intrinsic;

intrinsic TrivialOneCocycle( A::GGrp ) -> OneCoC
{Return the trivial one-cocycle on A.}

     return OneCocycle( A, [ Id(A`A): i in [1..Ngens(A`Gamma)] ] : Check:=false );

end intrinsic;






/*********************************************************************************
**                                                                              **
**   Printing                                                                   **
**                                                                              **
*********************************************************************************/
intrinsic HackobjPrintOneCoC( alpha::OneCoC, level::MonStgElt )
{Prints an object of type OneCoC}
     //
     // Possible Print levels: Minimal, Default, Maximal, Magma, Debug
     //
     if level eq "Magma" then
          printf "OneCocycle( %o, %o )",
               Sprint( alpha`A   , level ),
               Sprint( alpha`imgs, level );
     elif level eq "Debug" then
          // if in Debug level, only output the minimal information on each
          // attribute, but print ALL of them
          printf "coc      : %o\n",  Sprint( assigned(alpha`coc      ) select alpha`coc      else "not assigned", "Minimal" );
          printf "A        : %o\n",  Sprint( assigned(alpha`A        ) select alpha`A        else "not assigned", "Minimal" );
          printf "imgs     : %o\n",  Sprint( assigned(alpha`imgs     ) select alpha`imgs     else "not assigned", "Minimal" );
          printf "class    : %o",    Sprint( assigned(alpha`class    ) select alpha`class    else "not assigned", "Minimal" );
     else 
          printf "One-Cocycle ";
          if level eq "Maximal" then
               printf "on the %o", Sprint( alpha`A, "Minimal" ); 
          end if;
          printf "\ndefined by %o", alpha`imgs;
     end if;
end intrinsic;











/*********************************************************************************
**                                                                              **
**   Equality                                                                   **
**                                                                              **
*********************************************************************************/
intrinsic 'eq'( alpha::OneCoC, beta::OneCoC ) -> BoolElt
{Test equality of two 1-cocycles alpha, beta}
     A := GammaGroup(alpha); G := ActingGroup(A);
     B := GammaGroup(beta);  H := ActingGroup(B);
     if Ngens(G) lt Ngens(H) then
          return A eq B // this includes equality of G and H, but they can still have different generating sets.
               and forall{ i : i in [1..Ngens(G)] |  alpha`imgs[i] eq beta(G.i) };
     else
          return A eq B // this includes equality of G and H, but they can still have different generating sets.
               and forall{ i : i in [1..Ngens(H)] |  alpha(H.i) eq beta`imgs[i] };
     end if;
end intrinsic;


/*********************************************************************************
**                                                                              **
**   Map application                                                            **
**                                                                              **
*********************************************************************************/
intrinsic '@'( g::GrpElt, alpha::OneCoC ) -> BoolElt
{The image of g under the cocycle alpha}
     return alpha`coc(g);
end intrinsic;





/*********************************************************************************
**                                                                              **
**   Accessing defining attributes                                              **
**                                                                              **
*********************************************************************************/
intrinsic GammaGroup( alpha::OneCoC ) -> GGrp
{The Gamma-group on which alpha is defined}
     return alpha`A;
end intrinsic;

intrinsic CocycleMap( alpha::OneCoC ) -> Map
{The map defining alpha}
     return alpha`coc;
end intrinsic;




/********************************************************************************* 
**                                                                              **
**   Properties of Cocycles                                                     **
**                                                                              **
*********************************************************************************/
intrinsic IsOneCocycle( A::GGrp, imgs::SeqEnum[GrpElt] ) -> BoolElt, OneCoC
{Returns true iff imgs defines a 1-cocycle.
If true, the 1-cocycle is also returned as the second argument.}
     
     if not check_imgs( A, imgs ) then return false,_; end if;
 
// Create the Cocycle.

     alpha := OneCocycle( A, imgs : Check := false );
      
// Check the cocycle condition

     if not check_cocycle( A, alpha`coc ) then
          return false,_;
     else
          return true,alpha;
     end if;
     
end intrinsic;


intrinsic IsOneCocycle( A::GGrp, alpha::Map[Grp,Grp] ) -> BoolElt, OneCoC
{Returns true iff alpha defines a 1-cocycle.
If true, the 1-cocycle is also returned as the second argument.}
     
// check domain/codomain of alpha:

     if not Domain(alpha)   eq ActingGroup(A) then
          return false, _; // "Domain of alpha must be the group acting on A";
     end if;
     if not Codomain(alpha) eq Group(A) then
          return false, _; // "Codomain of alpha must be the group associated with A";
     end if;
       
// Check the cocycle condition

     if check_cocycle( A, alpha ) then
          alpha := OneCocycle( A, [ alpha(ActingGroup(A).i) : i in [1..Ngens(ActingGroup(A))] ] : Check := false );
          return true, alpha;
     else 
          return false, _;
     end if;
     
end intrinsic;




intrinsic AreCohomologous( alpha::OneCoC, beta::OneCoC ) -> BoolElt, GrpElt
{True iff cocycles alpha, beta are cohomologous with respect to some a in A.
If true, returns the element a as the second return value.}

     require alpha`A eq beta`A : "alpha and beta must be cocycles on the same Gamma-group";

     if assigned alpha`class then
          posb := Position(alpha`class,beta);
          if posb gt 0 then
               posa := Position(alpha`class,alpha);
               return true, (alpha`interelts[posa])^-1 * alpha`interelts[posb];
          else
               return false,_;
          end if;
     elif assigned beta`class then
          posa := Position(beta`class,alpha);
          if posa gt 0 then
               posb := Position(beta`class,beta);
               return true, (beta`interelts[posa])^-1 * beta`interelts[posb];
          else
               return false,_;
          end if;
     else
          A := alpha`A;
          G := ActingGroup(A);
          action := GammaAction(A);
 
          n := Ngens(G);
          imgs_a := alpha`imgs;

          if exists(a){ a : a in Group(A) |
                         forall{ i : i in [1..n] | action(G.i)(a^-1) * imgs_a[i] * a eq beta(G.i) }
                      }
          then
               return true,a;
          else
               return false,_;
          end if;
     end if;
end intrinsic;






/********************************************************************************* 
**                                                                              **
**   Cohomology Class of a 1-cocycle                                            **
**                                                                              **
*********************************************************************************/
function cohomology_class( alpha )
     A      := alpha`A;
     G      := ActingGroup(A);
     action := GammaAction(A);
     
     n := Ngens(G);

     // get the images of the generators of Gamma:
     imgs := alpha`imgs;

     iset := {@ imgs @};
     tset := {@ Id(Group(A)) @};
     
     for a in Group(A) do
          ims := [ action(G.i)(a^-1)  * imgs[i] * a : i in [1..n]];
          if ims notin iset then
               Include(~iset, ims);
               Include(~tset, a);
          end if;
     end for;
     
     return iset, tset;

end function;


intrinsic CohomologyClass( alpha::OneCoC ) -> SetIndx[OneCoC]
{The cohomology class of alpha}
     
     if assigned(alpha`class) then 
          return alpha`class;
     end if;
     
     iset,tset := cohomology_class( alpha );
     
     alpha`class     := {@ OneCocycle( alpha`A, i : Check:=false ) : i in iset @};
     alpha`interelts := tset;

     for b in alpha`class do
          c := b; // This line is VERY IMPORTANT otherwise it just wouldn't work!
          c`class     := alpha`class; 
          c`interelts := alpha`interelts; 
     end for;

     return alpha`class;                   
end intrinsic;





/********************************************************************************* 
**                                                                              **
**   Induced 1-cocycles                                                         **
**                                                                              **
*********************************************************************************/
intrinsic InducedOneCocycle( A::GGrp, B::Grp, alpha::OneCoC ) -> OneCoC
{Returns the cocycle induced by alpha on the induced Gamma-group A/B.}
     return InducedOneCocycle( InducedGammaGroup( A, B ), alpha );
end intrinsic;


intrinsic InducedOneCocycle( AmodB::GGrp, alpha::OneCoC ) -> OneCoC
{Returns the cocycle induced by alpha on the induced Gamma-group AmodB.}

     test, A, _, proj, _ := IsInduced( AmodB );

     require test : "AmodB must be an induced Gamma-Group";
     
     require alpha`A eq A : "alpha must be a 1-cocycle on the group AmodB was induced from";
     
     ind_alpha := map< ActingGroup(AmodB) -> Group(AmodB) | g :-> proj(alpha(g)) >;
     
     return OneCocycle( AmodB, ind_alpha : Check := false );
end intrinsic;








/********************************************************************************* 
**                                                                              **
**   Extending 1-cocycles                                                       **
**                                                                              **
**   alpha  -- a 1-cocycle on an induced Gamma-group                            **
**                                                                              **
*********************************************************************************/
intrinsic ExtendedOneCocycle( alpha::OneCoC : OnlyOne := false ) -> SetEnum[OneCoC]
{Given a 1-cocycle alpha in Z^1(G,A/B), return a list of non-cohomologous 1-cocycles in Z^1(G,A), which induce to alpha.
If the optional argument OnlyOne is set to true, only one extension is returned. This is much more efficient.}

     AmodB := alpha`A;
     test, A, B, proj, rep := IsInduced(AmodB);

     require test : "Gamma-group on which alpha is defined must be induced.";

     action      := GammaAction(A);
     actionAmodB := GammaAction(AmodB);
     G           := ActingGroup(AmodB);
     
     
     //
     //   if IsCentral(A,B) then check if the cocycle is in the Kernel of \delta^1
     //   If not, return with an error immediately
     //
     if     IsCentral(Group(A),Group(B)) and 
        not is_in_ker_delta_one( alpha ) then
          print "cocycle is not in the kernel of delta^1 and thus not extendable (GOOD!)";
          return {};
     end if;
     
     if not assigned(AmodB`F) then
          if assigned(A`F) then
               AmodB`F       := A`F;
               AmodB`f2gamma := A`f2gamma;
          else
               AmodB`F,
               AmodB`f2gamma := FPGroup(ActingGroup(A));
          end if;
          AmodB`Faction := AmodB`f2gamma * AmodB`action;
     end if;

     F := AmodB`F;
     f2gamma := AmodB`f2gamma;
     
     r := [ rep(alpha(G.i)) : i in [1..Ngens(F)]];
     
     // f2gamma maps F.i to G.i !!!
     relators := [ Eltseq(LHS(rel)*RHS(rel)^-1) : rel in Relations(F) ];

     if OnlyOne then
          // need only one solution:
          solvable := 
               exists(sol){ b : b in CartesianProduct([Group(B):i in [1..Ngens(F)]]) | 
                         forall{ eqn : eqn in  list_of_eqns  | eqn eq Id(Group(B)) }
                         where list_of_eqns is [ &*[ action( &*[G| G.rltr[j] : j in [i+1..#rltr]] )
                                                            ( rltr[i] gt 0 select                       r[ rltr[i]] * b[ rltr[i]]
                                                                             else action( G.rltr[i] )( (r[-rltr[i]] * b[-rltr[i]])^-1 )
                                                            ) 
                                                   : i in [1..#rltr] ] 
                                               : rltr in relators ]
               };
     else
          // need all solutions:
          solutions :=
               { b : b in CartesianProduct([Group(B):i in [1..Ngens(F)]]) |
                         forall{ eqn : eqn in  list_of_eqns  | eqn eq Id(Group(B)) }
                         where list_of_eqns is [ &*[ action( &*[G| G.rltr[j] : j in [i+1..#rltr]] )
                                                            ( rltr[i] gt 0 select                       r[ rltr[i]] * b[ rltr[i]]
                                                                             else action( G.rltr[i] )( (r[-rltr[i]] * b[-rltr[i]])^-1 )
                                                            )
                                                   : i in [1..#rltr] ]
                                               : rltr in relators ]
               };
          solvable := #solutions gt 0;
     end if;

     if not solvable then 
          print "cocycle is not extendable";
          return {};
     elif OnlyOne then
          return { OneCocycle( A, [ r[i]*sol[i] : i in [1..Ngens(G)]] : Check := false ) };
     else
          // if we really need ALL (even if some of them are cohomologous to eachother), 
          // then something like this should do it:
          // 
          // ext_coc := { OneCocycle( A, [ r[i]*sol[i] : i in [1..Ngens(G)]] : Check := false ) : sol in solutions };
          // 

          ext_coc := {};
          for sol in solutions do
               gamma := OneCocycle( A, [ r[i]*sol[i] : i in [1..Ngens(G)]] : Check := false );
               if not exists{ beta : beta in ext_coc | gamma in CohomologyClass(beta) } then
                    Include( ~ext_coc, gamma );
                    if &+[ #CohomologyClass(beta) : beta in ext_coc ] eq #solutions then
                         break;
                    end if;
               end if;
          end for;
     end if;
     
     return ext_coc;
     
end intrinsic;



intrinsic ExtendedCohomologyClass( alpha::OneCoC ) -> SetEnum[OneCoC]
{Given a 1-cocycle alpha in Z^1(G,A/B), return a list of non-cohomologous 1-cocycles in Z^1(G,A), which induce to alpha
or to a 1-cocycle cohomologous to alpha.}


     AmodB := alpha`A;
     test, A, B, proj, rep := IsInduced(AmodB);

     require test : "Gamma-group on which alpha is defined must be induced.";

     action      := GammaAction(A);
     actionAmodB := GammaAction(AmodB);
     G           := ActingGroup(AmodB);
     

     //
     //   if IsCentral(A,B) then check if the cocycle is in the Kernel of \delta^1
     //   If not, return with an error immediately
     //
     if     IsCentral(Group(A),Group(B)) and 
        not is_in_ker_delta_one( alpha ) then
          print "cocycle is not in the kernel of delta^1 and thus not extendable";
          return {};
     end if;
 
     if not assigned(AmodB`F) then
          if assigned(A`F) then
               AmodB`F       := A`F;
               AmodB`f2gamma := A`f2gamma;
          else
               AmodB`F,
               AmodB`f2gamma := FPGroup(ActingGroup(A));
          end if;
          AmodB`Faction := AmodB`f2gamma * AmodB`action;
     end if;

     F := AmodB`F;
     f2gamma := AmodB`f2gamma;
     
     // f2gamma maps F.i to G.i !!!
     relators := [ Eltseq(LHS(rel)*RHS(rel)^-1) : rel in Relations(F) ];
     
     ext_coc := {};

     for beta in CohomologyClass( alpha ) do;
          r := [ rep(beta(G.i)) : i in [1..Ngens(F)]];

          // need all solutions:
          solutions :=
               { b : b in CartesianProduct([Group(B):i in [1..Ngens(F)]]) |
                         forall{ eqn : eqn in  list_of_eqns  | eqn eq Id(Group(B)) }
                         where list_of_eqns is [ &*[ action( &*[G| G.rltr[j] : j in [i+1..#rltr]] )
                                                            ( rltr[i] gt 0 select                       r[ rltr[i]] * b[ rltr[i]]
                                                                             else action( G.rltr[i] )( (r[-rltr[i]] * b[-rltr[i]])^-1 )
                                                            )
                                                   : i in [1..#rltr] ]
                                               : rltr in relators ]
               };

          for sol in solutions do
               gamma := OneCocycle( A, [ r[i]*sol[i] : i in [1..Ngens(G)]] : Check := false );
               if not exists{ beta : beta in ext_coc | gamma in CohomologyClass(beta) } then
                    Include( ~ext_coc, gamma );
                    if &+[ #CohomologyClass(beta) : beta in ext_coc ] eq #solutions then
                         break;
                    end if;
               end if;
          end for;
          
     end for;

     // TODO: move this inside the loop once proven that in a 
     //       cohomology class either all cocycles are extendable or none     
     if IsEmpty(ext_coc) then
          print "cocycle is not extendable";
          return {};
     end if;
     
     return ext_coc;
     
end intrinsic;





/*********************************************************************************
**                                                                              **
**   OneCohomology  H^1(Gamma, A)                                               **
**                                                                              **
*********************************************************************************/
intrinsic Cohomology( A::GGrp, n::RngIntElt ) -> SetEnum[OneCoC]
{H^n(Gamma, A) as a set of representatives of the cohomology classes}
     require n eq 1 : "H^n(Gamma, A) for n>1 are not defined in general. Only n=1 implemented.";
     return OneCohomology( A );
end intrinsic

intrinsic OneCohomology( A::GGrp ) -> SetEnum[OneCoC]
{H^1(Gamma, A) as a set of representatives of the cohomology classes}

     if assigned(A`H1) then
          return A`H1;
     end if;

     //
     // if A is a GrpLie or GrpLieAut, call GaloisCohomology
     // provided by galcohom.m 
     //
     if ISA(Category(Group(A)),GrpLie)
     or ISA(Category(Group(A)),GrpLieAuto) then
          return GaloisCohomology(A);
     end if;

     // if A is abelian, it's easy:

     if IsAbelian(Group(A)) then
          return OneCohomologyAb( A );
     end if;


     Gamma := ActingGroup(A);
     action := GammaAction(A);

     // then check if the center is nontrivial and normalised under the action:
     C := Center(Group(A));
     if #C gt 1 then
          // compute C^g for all g \in Gens(Gamma)
          Cgammas := [ sub<Group(A)| [ action(g)(C.i) : i in [1..Ngens(C)]] > : g in Generators(Gamma) ];
          Append(~Cgammas, C);
          
          B := &meet Cgammas;
          
          if #B gt 1 then
               AmodB := InducedGammaGroup( A, B );
               _, _, B := IsInduced(AmodB);

               cs := OneCohomology( AmodB );

               // B is abelian, so checking it is easy anyway:
               if #OneCohomology( B ) eq 1 then
                    print "use only one (central)";
                    A`H1 := &join[ ExtendedOneCocycle( c : OnlyOne := true ) : c in cs ];
               else
                    A`H1 := &join[ ExtendedCohomologyClass( c ) : c in cs ];
               end if;

               return A`H1;
          end if;
     end if;
     
     // Note that Gamma normalises either whole conj. class
     // or no group in it. This is independant of the action!!!    
     //
     if exists(B){ B : N in NormalSubgroups(Group(A)) 
                              | not IsCentral(Group(A),B)     // the center has already been cared for.
                                and IsNormalised(B,action)    // take the smallest which is normalised.
                   where B is N`subgroup
                 } and B ne Group(A) then

          AmodB := InducedGammaGroup( A, B );
          _, _, B := IsInduced(AmodB);

          cs := OneCohomology( AmodB );
          
          if #OneCohomology( B ) eq 1 then
               print "use only one (normal)";
               A`H1 := &join[ ExtendedOneCocycle( c : OnlyOne := true ) : c in cs ];
          else
               A`H1 := &join[ ExtendedCohomologyClass( c ) : c in cs ];
          end if;

          return A`H1;
     end if;
          
     return OneCohomologyFP( A );

end intrinsic;



intrinsic OneCohomologyAb( A::GGrp ) -> SetEnum[OneCoC]
{H^1(Gamma, A) as a set of representatives of the cohomology classes.}

     if assigned(A`H1) then
          return A`H1;
     end if;

     require IsAbelian(Group(A)) : "A is not abelian";
     require IsFinite( Group(A)) : "A is not finite";

     H1 := CohomologyGroup(A`CM,1);

     maps := { map< ActingGroup(A) -> Group(A) | g :-> Inverse(A`a2ab)(A`AB!Eltseq(OneCocycle(A`CM, v)(<g>))) > : v in H1 };
     A`H1 := { OneCocycle( A, m : Check := false ) : m in maps };
     
     return A`H1;

end intrinsic;





intrinsic OneCohomologyFP_( A::GGrp ) -> SetEnum[OneCoC]
{H^1(Gamma, A) as a set of representatives of the cohomology classes}

     if assigned(A`H1) then
          return A`H1;
     end if;

     if not assigned(A`F) then
          A`F,
          A`f2gamma := FPGroup(ActingGroup(A));
          A`Faction := A`f2gamma * A`action;
     end if;
     
     // this one is just cool, heh?
     // 
     //     orbits := [Universe([{@[Id(Group(A))]@}])|];
     // 
     // unfortunately, we don't need this anymore.
     // I'm mourning this nice piece of code.
     //
     
     H1 := {PowerStructure(OneCoC)|};
     
     n := Ngens(A`F);

     CP := CartesianProduct([Group(A):i in [1..n]]);

     /* time */ Z1 := [ tupseq : tup in CP | IsOneCocycle( A, tupseq ) where tupseq is [tup[i]:i in [1..n]] ];
     /* #Z1; */

     while not IsEmpty(Z1) do
          c := OneCocycle( A, Z1[1] : Check:= false );
          Include(~H1,c);
          /* time #CohomologyClass(c); */ 
          for b in CohomologyClass(c) do
               Exclude(~Z1,b`imgs);
          end for;
     end while;

     A`H1 := H1;
     
     return H1;

end intrinsic;

intrinsic OneCohomologyFP( A::GGrp ) -> SetEnum[OneCoC]
{H^1(Gamma, A) as a set of representatives of the cohomology classes}

//      if assigned(A`H1) then
//           return A`H1;
//      end if;

     if not assigned(A`F) then
          A`F,
          A`f2gamma := FPGroup(ActingGroup(A));
          A`Faction := A`f2gamma * A`action;
     end if;
     
     // this one is just cool, heh?
     // 
     //     orbits := [Universe([{@[Id(Group(A))]@}])|];
     // 
     // unfortunately, we don't need this anymore.
     // I'm mourning this nice piece of code.
     //
     
     H1 := {PowerStructure(OneCoC)|};
     
     n := Ngens(A`F);

     CP := CartesianProduct([Group(A):i in [1..n]]);

     Z1 := [ alpha : tup in CP | is1coc where is1coc, alpha := IsOneCocycle(A, [tup[i]:i in [1..n]]) ];

     while not IsEmpty(Z1) do
          c := Z1[1];
          Include(~H1,c);
          for b in CohomologyClass(c) do
               Exclude(~Z1,b);
          end for;
     end while;

     A`H1 := H1;
     
     return H1;

end intrinsic;


/*********************************************************************************
**                                                                              **
**   Twisted group A_\alpha                                                     **
**                                                                              **
**   alpha -- 1-cocycle on A                                                    **
**                                                                              **
**   alpha -- 1-cocycle on Aut(A) is possible in theory (not implemented yet)   **
**                                                                              **
*********************************************************************************/

intrinsic TwistedGroup( A::GGrp, alpha::OneCoC ) -> GGrp
{The Gamma-group obtained by twisting A by the cocycle alpha}

     require A eq alpha`A : "alpha must be a cocycle on A";
     
     Gamma := ActingGroup(A);
     action := GammaAction(A);
     
     star_action := hom< Gamma -> Aut(A) | g :-> iso< A -> A | a :-> action(g   )(a)^alpha(g   ), 
                                                               a :-> action(g^-1)(a)^alpha(g^-1) > >
               where A is Group(A);

     A_al := GammaGroup( Gamma, Group(A), star_action );
     
     // TODO if A is induced from C make A_al induced from C_al
     
     // if the H^1(Gamma, A) is known, compute H^1(Gamma, A_al)
     if assigned A`H1 then
          A_al`H1 := {};
          for beta in A`H1 do
               alphabeta := OneCocycle( A_al, 
                                        map< Gamma->Group(A) | g :-> alpha(g)*beta(g)>
                                        : Check:=false 
                                       );
               Include( ~A_al`H1, alphabeta );
          end for;
     end if;
     
     return A;

end intrinsic;








/********************************************************************************* 
**                                                                              **
**   AUXILIARY FUNCTIONS                                                        **
**                                                                              **
*********************************************************************************/



/*********************************************************************************
**
**   checking parameters
**
*/
function check_cocycle( A, coc_map )

     // expect
     // 
     //        A::GGrp, coc_map::Map
     // 
     // but don't check catregories of parameters since this function 
     // is supposed to be called only from inside of the intrinsics
     // where the categories are already checked.

     if not assigned(A`F) then
          A`F,
          A`f2gamma := FPGroup(ActingGroup(A));
          A`Faction := A`f2gamma * A`action;
     end if;

     F       := A`F;
     f2gamma := A`f2gamma;
     gamma2f := Inverse(f2gamma);
     Faction := A`Faction;
     
     coc_map := f2gamma * coc_map;

     //
     // one more check I could think of is:
     //   
     //   if   action(G.i)(c(G.i))  eq  c(G.i) then
     //        IsDivisibleBy(Order(G.i), Order(c(G.i)))  is a necessary condition.
     //
     //   the problem is that it is not that easy to compute Order(G.i) for a GrpFP
     //
     //     

     rltrs := [ LHS(rel)*RHS(rel)^-1 : rel in Relations(F) ];

     //
     //  images of all relators under c. computed for the word.
     //  compute them one by one and exit as soon as one of them 
     //  leads to a contradictions
     // 
     
     for rltr in rltrs do
          im :=  &*[ Faction(&*g[[i+1..#g]])(coc_map(g[i])) : i in [1..#g] ]
                     where g is [ F![w] : w in Eltseq(rltr) ];
          if im ne Id(A`A) then
               return false;
          end if;
     end for;
     
     return true;
     
end function;



function check_imgs( A, imgs )

// check if imgs is a subset of A

     if not (imgs subset A`A) then
          return false, "imgs must be a subset of A";

     elif not (#imgs eq Ngens(A`Gamma)) then
          return false, "imgs must have the same length as the number of generators of the group acting on A";
//
// check:  if G.i = G.j for some i,j then imgs[i] must be equal to imgs[j]
// don't do that since it will lead to a problem for the cocycle conditions anyway.
//
     else
          return true, _;
     end if;

end function;





/********************************************************************************* 
**
**   the kernel of the last map of the long exact sequence provides additional
**   information about extendability of cocycles.
**   the next function returns true or false and the standard representative 
**   of the image of the cocycle alpha under the map delta^1.
**
*/  
function is_in_ker_delta_one( alpha )

     AmodB := alpha`A;
     _, A, B, _, rep := IsInduced(AmodB);

     G := ActingGroup(A);
     action := GammaAction(A);

     // choose a map t:G->A, s.t. t(g)\in alpha(g) randomly:
     t_imgs := [ <g,rep(alpha(g))> : g in G ]; // what's the best way to do it for large groups?
     t := map< G->Group(A) | t_imgs >;
     
     // now [two_coc] = delta^1([alpha]):
     two_coc := func< gh | Eltseq(B`a2ab(  (action(h))(t(g)) *  t(h) * t(g*h)^-1 where g,h := Explode(gh) )) >;

     // compute the standard representative of [two_coc]
     itc := IdentifyTwoCocycle( B`CM, two_coc );

     return IsZero(itc), itc;

end function;



/********************************************************************************* 
**
**   provided that list is in {1..d}^n, we increase the list
**   in lexicographical order.
**   
*/  
procedure lex_increase( ~list, d )
     for i in [#list..1 by -1] do
          if list[i] eq d then
               list[i] := 1;
          else 
               list[i] +:= 1;
               break;
          end if;
     end for;
end procedure;





















