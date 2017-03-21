freeze;

/*********************************************************************************
**                                                                              **
**   Sergei Haller <Sergei.Haller@math.uni-giessen.de>                          **
**                                                                              **
**   Intrinsics for dealing with GGrp objects.                                  **
**                                                                              **
**   An object of type GGrp is a Gamma-Group, which is a group A with one       **
**   particular fixed action of another group (Gamma) on it.                    **
**                                                                              **
*********************************************************************************/


declare attributes GGrp:
     A         ,    // the group itself
     Gamma     ,    // the acting group
     action    ,    // the action as a map from Gamma to Aut(A)

     F         ,    // GrpFP version of Gamma
     f2gamma   ,    // the isomorphism from F to Gamma
     Faction   ,    // the action of F on grp

     AB        ,    // GrpAb version of A (only possible if A is abelian)
     a2ab      ,    // the isomorphism from A to AB

     ind_from  ,    // if the GGrp was induced, this is the originating GGrp
     ind_mod   ,    //     --- " --- " ---    , this is the normal subgroup as GGrp
     ind_proj  ,    //     --- " --- " ---    , this is the projection
     ind_rep   ,    //     --- " --- " ---    , this is the representative map

     H1        ,    // this is the first cohomology (once computed)
     CM        ,    // this is the ModCoho object in case A is abelian.

     // only for Galois cohomology:

     k,             // the field of definition k (the one from Aut_k(G) )
     gamma2fld ;    // map from Gamma to Aut(K:k);

forward check_action;
forward prepare_cohom_module;
forward prepare_delta_one;


/*********************************************************************************
**                                                                              **
**   Printing                                                                   **
**                                                                              **
*********************************************************************************/
intrinsic HackobjPrintGGrp( A::GGrp, level::MonStgElt )
{Prints an object of type GGrp}
     //
     // Possible Print levels: Minimal, Default, Maximal, Magma, Debug
     //
     if level eq "Magma" then
          printf "GammaGroup( %o, %o, %o )",   
               Sprint( A`Gamma , level ),
               Sprint( A`A     , level ),
               Sprint( A`action, level );
     elif level eq "Debug" then
          // if in Debug level, only output the minimal information on each
          // attribute, but print ALL of them
          printf "A        : %o\n",  Sprint( assigned(A`A        ) select A`A         else "not assigned", "Minimal" );
          printf "Gamma    : %o\n",  Sprint( assigned(A`Gamma    ) select A`Gamma     else "not assigned", "Minimal" );
          printf "action   : %o\n",  Sprint( assigned(A`action   ) select A`action    else "not assigned", "Minimal" );
          printf "F        : %o\n",  Sprint( assigned(A`F        ) select A`F         else "not assigned", "Minimal" );
          printf "f2gamma  : %o\n",  Sprint( assigned(A`f2gamma  ) select A`f2gamma   else "not assigned", "Minimal" );
          printf "Faction  : %o\n",  Sprint( assigned(A`Faction  ) select A`Faction   else "not assigned", "Minimal" );
          printf "AB       : %o\n",  Sprint( assigned(A`AB       ) select A`AB        else "not assigned", "Minimal" );
          printf "a2ab     : %o\n",  Sprint( assigned(A`a2ab     ) select A`a2ab      else "not assigned", "Minimal" );
          printf "ind_from : %o\n",  Sprint( assigned(A`ind_from ) select "[...]"     else "not assigned", "Minimal" );
          printf "ind_mod  : %o\n",  Sprint( assigned(A`ind_mod  ) select "[...]"     else "not assigned", "Minimal" );
          printf "ind_proj : %o\n",  Sprint( assigned(A`ind_proj ) select "[...]"     else "not assigned", "Minimal" );
          printf "ind_rep  : %o\n",  Sprint( assigned(A`ind_rep  ) select "[...]"     else "not assigned", "Minimal" );
          printf "H1       : %o\n",  Sprint( assigned(A`H1       ) select "[...]"     else "not assigned", "Minimal" );
          printf "CM       : %o\n",  Sprint( assigned(A`CM       ) select A`CM        else "not assigned", "Minimal" );
          printf "k        : %o\n",  Sprint( assigned(A`k        ) select A`k         else "not assigned", "Minimal" );
          printf "gamma2fld: %o",    Sprint( assigned(A`gamma2fld) select A`gamma2fld else "not assigned", "Minimal" );
     else
          printf "Gamma-group:  %o\n", Sprint( A`A     , level );
          printf "Gamma-action: %o\n", Sprint( A`action, level );
          printf "Gamma:        %o",   Sprint( A`Gamma , level );

          //
          // if the Gamma-group is induced, do some extra stuff:
          //
          if assigned(A`ind_from) then
                 if level eq "Minimal" then
                    printf "\n(induced)";
               elif level in ["Default", "Maximal"] then
                    printf "\nInduced from another Gamma-group";
               end if;
          end if;
     end if;
end intrinsic;






/********************************************************************************* 
**                                                                              **
**   Accessing attributes                                                       **
**                                                                              **
*********************************************************************************/
intrinsic Group( A::GGrp ) -> Grp
{Returns the Grp object assosiated with A.}
     return A`A;
end intrinsic;

intrinsic GammaAction( A::GGrp ) -> Map[Grp, PowMapAut]
{Returns the action assosiated with A.}
     return A`action;
end intrinsic;

intrinsic ActingGroup( A::GGrp ) -> Grp, Map
{Returns the group acting on A.}
     if assigned(A`gamma2fld) then
          return A`Gamma, A`gamma2fld;
     else 
          return A`Gamma, _;
     end if;
end intrinsic;

intrinsic IsInduced( AmodB::GGrp ) -> BoolElt, GGrp, GGrp, Map, Map
{Returns true if the Gamma-Group was created as an induced Gamma group.
If true, returns the GGrp it was induced from, the normal subgroup as GGrp, 
the projection and the representative maps as further return values.}
     if assigned(AmodB`ind_from) then
          return true, AmodB`ind_from, AmodB`ind_mod, AmodB`ind_proj, AmodB`ind_rep;
     else
          return false, _, _, _, _;
     end if;
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Equality                                                                   **
**                                                                              **
*********************************************************************************/
intrinsic 'eq'( A::GGrp, B::GGrp ) -> BoolElt
{Test equality of two Gamma-groups A,B}
     return A`A      eq B`A 
        and A`Gamma  eq B`Gamma
        and A`action eq B`action;
end intrinsic;



/********************************************************************************* 
**                                                                              **
**   Construction                                                               **
**                                                                              **
**   action -- homomorphism: Gamma -> Aut(A)                                    **
**                                                                              **
**   Gamma  -- (Permutation) group acting on A by the map action                **
**                                                                              **
*********************************************************************************/
intrinsic GammaGroup( Gamma::Grp, A::Grp, action::Map[Grp,PowMapAut] ) -> GGrp
{Return the Gamma-group A as a GGrp object.}
     
     require not ISA(Category(Gamma),GrpAb) : "Gamma must be a multiplicative group";
     
     ret, msg := check_action( Gamma, A, action );
     require ret : msg;
     
     GG := HackobjCreateRaw(GGrp);

     GG`A      := A;
     GG`Gamma  := Gamma;
     GG`action := action;
   
     if ISA(Category(Gamma), GrpFP) then
          GG`F       := Gamma;
          GG`f2gamma := IdentityHomomorphism(Gamma);
          GG`Faction := action;
     end if;

     if IsAbelian(A) then
          GG`AB, GG`a2ab := AbelianGroup(A);
          prepare_cohom_module( GG );
     end if;
     
     return GG;
     
end intrinsic;


intrinsic GammaGroup( Gamma::Grp, A::Grp, action::Map[Grp,GrpAuto] ) -> GGrp
{The Gamma-group A as a GGrp object.}
  return GammaGroup( Gamma, A, 
    hom< Gamma -> Aut(A) | g :-> Aut(A)!action(g) > );
end intrinsic;


/********************************************************************************* 
**                                                                              **
**   Construction of the induced Gamma-Group                                    **
**                                                                              **
**   If B is a normal subgroup of A, normalised by the action of Gamma on A,    **
**   then Gamma also acts in the natural way on the cosets of A/B, thus         **
**   A/B is also a Gamma-group with the induced action.                         **
**                                                                              **
*********************************************************************************/
intrinsic InducedGammaGroup( A::GGrp, B::Grp ) -> GGrp
{The Group A/B as a Gamma-group with the induced Gamma-action. The returned 
Gamma-group will have the information on the Gamma-group it was induced from.}
          
     require ISA(Category(A`A), Category(B)) or
             ISA(Category(B), Category(A`A))   : "B and A must have the same categories";

     require B subset A`A                      : "B must be a subgroup of A";
     require IsNormal(A`A, B)                  : "B must be a normal subgroup of A";
     require IsNormalised( B, A`action )       : "B must be normalised by the group Gamma acting on A";

     G      := ActingGroup(A);
     action := GammaAction(A);
     
     /* AmodB, proj := quo<A`A|B>; */
     proj, AmodB := CosetAction(A`A, B);
     rep := Inverse(proj);
     
     // induced action:
     ind_action := hom< G -> Aut(AmodB) | g :-> 
                          iso< AmodB -> AmodB | a :-> proj(action(g)(rep(a))), a :-> proj(action(g^-1)(rep(a))) >>;
       B_action := hom< G -> Aut(B) | g :-> 
                          iso< B -> B | b :-> action(g)(b), b :-> action(g^-1)(b) >>;

         B := GammaGroup( G,     B,   B_action );
     AmodB := GammaGroup( G, AmodB, ind_action );

     AmodB`ind_from  := A;
     AmodB`ind_proj  := proj;
     AmodB`ind_rep   := rep;
     AmodB`ind_mod   := B;

     if assigned(A`F) then
          AmodB`F       := A`F;       B`F       := A`F;
          AmodB`f2gamma := A`f2gamma; B`f2gamma := A`f2gamma;

          AmodB`Faction := AmodB`f2gamma * AmodB`action;
              B`Faction :=     B`f2gamma *     B`action;
     end if;

     if IsCentral(Group(A),Group(B)) then
          prepare_delta_one( AmodB );
     end if;
     
     return AmodB;

end intrinsic;

intrinsic IsNormalised( B::Grp, action::Map[Grp,PowMapAut] ) -> BoolElt
{Returns true if the group is normalised by the action.}
     G := Domain(action);
     return forall{ i : i in [1..Ngens(G)] | action(G.i)(Generators(B)) subset B };
end intrinsic;




/********************************************************************************* 
**                                                                              **
**   AUXILIARY FUNCTIONS                                                        **
**                                                                              **
*********************************************************************************/
function check_action( Gamma, A, action )

     D := Domain(action);
     C := Codomain(action);

       if not D cmpeq Gamma then
          return false, "action is not an action of G";
     elif not C cmpeq Aut(A) then
          return false, "action is not an action on A";

     // TODO:
     //   actually, action must be a Homomorphism.
     //   but there is currently no way to easily check that in Magma.
     //
     else
          return true, _;
     end if;

end function;





procedure prepare_cohom_module( B ) // B::GGrp, abelian

     if assigned(B`CM) then
          return;
     end if;
     
     G := ActingGroup(B);
     action := GammaAction(B);
     AB := B`AB;
     
     invars := AbelianInvariants(AB);
     d := #invars;
     
     a2ab := B`a2ab;        // former nu
     ab2a := Inverse(a2ab); // former nu1

     // special care needed if G is of type GrpPC:
     if Category(G) eq GrpPC then
          ng := #PCGenerators(G);
     else
          ng := Ngens(G);
     end if;

     // prepare the cohomology module of B:
     mats := [ Matrix(Integers(),d,d, &cat[   Eltseq( (ab2a * action(G.i) * a2ab)(AB.k) )  : k in [1..d]  ]) : i in [1..ng] ];
     B`CM := CohomologyModule( G, invars, mats );
     // print "mats:", mats;
     // print "invars:", invars;

end procedure;

procedure prepare_delta_one( AmodB ) // AmodB::GGrp, induced

     B := AmodB`ind_mod;

     if not assigned(B`CM) then
          prepare_cohom_module( B );
     end if;

     // this one is needed before IdentifyTwoCocycle will work
     _ := CohomologyGroup(B`CM,2);

end procedure;

