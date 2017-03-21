freeze;

// AddAttribute (GrpMat, "Congruence");
declare attributes GrpMat: Congruence, UserWords, SLPGroup, InvMats;
declare attributes GrpMat: AbelianBasis;
declare attributes GrpMat: HirschNumber;
declare attributes GrpMat: SFChangeOfBasis;
declare attributes AlgMat: AbelianBasis, InvMats;
declare attributes AlgMat: UserWords;
declare attributes AlgMat: UserGenerators;
declare attributes GrpGPC: UserGenerators;
RF := recformat< Finite, Subgroup, Map, Virtual, Selberg, Isomorphism, 
                 Image, Relations, 
                 Nilpotent, Soluble, SolubleByFinite, NilpotentByFinite,
                 AbelianByFinite, CentralByFinite, CompletelyReducible >;

intrinsic UserGenerators(G :: GrpGPC) -> []
    { Return the sequence of generators that defined G. }
    if assigned G`UserGenerators then return G`UserGenerators;
    else return [G.i : i in [1 .. NumberOfGenerators(G)]]; end if;
end intrinsic;

