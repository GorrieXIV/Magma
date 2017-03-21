freeze;

import "fix-subgroup.m" : FixSubgroup;
import "find-conjugate.m" : FindConjugate;

import "find-mapping-automorphism.m" : FindMappingAutomorphism;
import "iso-subdirect.m" : IsIsomorphicSubdirectProduct, IsIsomorphicSubdirectProduct_;


IsIsomorphicSemidirectProduct_ := function(G1, S1, T1, G2, S2, T2, S1toS2)
    genS1 := SetToSequence(PCGenerators(S1));
    genS2 := SetToSequence(PCGenerators(S2));

    genT1 := SetToSequence(PCGenerators(T1));
    genT2 := SetToSequence(PCGenerators(T2));

    genG1 := genT1 cat genS1;

    /*  Check if S2 is elementary abelian, if so branch off and use IsGLConjugate code for
        conjugate calculation. Note that most of this code here is copied from below.
        Would be better to be able to call IsConjugate on GrpMat which was GL(n, q)...
    */
    if IsElementaryAbelian(S2) then
        vprint AutomorphismGroupSolubleGroup : "p-group is elementary abelian, preparing to use IsGLConjugate...";
        vprint AutomorphismGroupSolubleGroup : "Computing automorphism group";

        /* Note that we don't need to the permutation rep as we only need the matrix rep */
        vtime AutomorphismGroupSolubleGroup : AutS2 := AutomorphismGroupElementaryAbelianPGroup(S2 :
            construct_pc_representation_if_possible := false);

        vprint AutomorphismGroupSolubleGroup : "|Aut(S)| = ", FactoredOrder(AutS2);
        // vprint AutomorphismGroupSolubleGroup, 3 : "|Aut(S)| = ", FactoredLaTeXOrder(AutS2);

        MapToRepEltS2, phi_AutS2, R_AutS2 := RepresentationAutomorphismGroupPGroup(AutS2);

        genR_AutS2InnT2 := [ R_AutS2 | hom< S2 -> S2 | [ S2 | s^t : s in genS2 ] > @ MapToRepEltS2 : t in genT2 ];
        R_AutS2InnT2 := sub < R_AutS2 | genR_AutS2InnT2 >;

        genR_AutS2InnT1 := [ R_AutS2 | hom < S2 -> S2 | [ S2 | ((s @@ S1toS2) ^ t) @ S1toS2 : s in genS2 ] > @ MapToRepEltS2 : t in genT1 ];
        R_AutS2InnT1 := sub < R_AutS2 | genR_AutS2InnT1 >;

        vprint AutomorphismGroupSolubleGroup : "Computing IsGLConjugate...";
        vtime AutomorphismGroupSolubleGroup : conj, elt := IsGLConjugate(R_AutS2InnT1, R_AutS2InnT2);
        if not conj then
            vprint AutomorphismGroupSolubleGroup : "There is no conjugating element.";
            return false, _;
        end if;

        assert R_AutS2InnT1 ^ elt eq R_AutS2InnT2;

        /* we only need action of matrices as maps, not auto elts */
        RepEltToMap := AutS2`RepEltToMap;

        S1toS2 *:= (elt @ RepEltToMap);
        genR_AutS2InnT1 := [ R_AutS2 | hom < S2 -> S2 | [ S2 | ((s @@ S1toS2) ^ t) @ S1toS2 : s in genS2 ] > @ MapToRepEltS2 : t in genT1 ];
        R_AutS2InnT1 := sub < R_AutS2 | genR_AutS2InnT1 >;
        assert R_AutS2InnT1 eq R_AutS2InnT2;

        img := [ FindConjugate(T2, S2, (r_h @ RepEltToMap)) : r_h in genR_AutS2InnT1 ] cat (genS1 @ S1toS2);
        b, m := IsHomomorphism(G1, G2, [ < genG1[i], img[i] > : i in [1..#genG1] ]);
        if not b then
            vprint AutomorphismGroupSolubleGroup : "Can't construct isomorphism from conjugation action";
            return false, _;
        end if;
        return true, m;
    end if;

    /* Compute the automorphism groups */
    vprint AutomorphismGroupSolubleGroup : "Computing AutS2...";
    vtime AutomorphismGroupSolubleGroup : AutS2 := AutomorphismGroupPGroup_(S2);

    vprint AutomorphismGroupSolubleGroup : "Constructing rep of AutS2...";
    vtime AutomorphismGroupSolubleGroup : MapToRepEltS2, phi_AutS2, R_AutS2 := RepresentationAutomorphismGroupPGroup(AutS2);

    genR_AutS2InnT2 := [ R_AutS2 | hom< S2 -> S2 | [ S2 | s^t : s in genS2 ] > @ MapToRepEltS2 : t in genT2 ];
    R_AutS2InnT2 := sub < R_AutS2 | genR_AutS2InnT2 >;

    genImageOfT1inG2 := [ R_AutS2 | hom < S2 -> S2 | [ S2 | ((s @@ S1toS2) ^ t) @ S1toS2 : s in genS2 ] > @ MapToRepEltS2 : t in genT1 ];
    ImageOfT1inG2 := sub < R_AutS2 | genImageOfT1inG2 >;

    conj, elt := IsConjugate(R_AutS2, ImageOfT1inG2, R_AutS2InnT2);
    if not conj then
        vprint AutomorphismGroupSolubleGroup : "Can't find conjugate to map image of T1 in S2 to image of T2 in S2";
        return false, _;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Conjugating element: ", elt;
    S1toS2 := S1toS2 * ((elt) @@ phi_AutS2);
    genImageOfT1inG2 := [ R_AutS2 | hom < S2 -> S2 | [ S2 | ((s @@ S1toS2) ^ t) @ S1toS2 : s in genS2 ] > @ MapToRepEltS2 : t in genT1 ];
    ImageOfT1inG2 := sub < R_AutS2 | genImageOfT1inG2 >;
    assert ImageOfT1inG2 eq R_AutS2InnT2;

    img := [ FindConjugate(T2, S2, r_h @@ phi_AutS2) : r_h in genImageOfT1inG2 ] cat (genS1 @ S1toS2);
    b, m := IsHomomorphism(G1, G2, [ < genG1[i], img[i] > : i in [1..#genG1] ]);
    if not b then
        vprint AutomorphismGroupSolubleGroup : "Can't construct isomorphism from conjugation action";
        return false, _;
    end if;
    return true, m;
end function;


IsIsomorphicConjugationSearch_ := function(G1, S1, K1, T1, G2, S2, K2, T2, S1toS2)
    S2 := SpecialPresentation(S2);

    genS1 := SetToSequence(PCGenerators(S1));
    genS2 := SetToSequence(PCGenerators(S2));

    genK1 := SetToSequence(PCGenerators(K1));
    genK2 := SetToSequence(PCGenerators(K2));

    genT1 := SetToSequence(PCGenerators(T1));
    genT2 := SetToSequence(PCGenerators(T2));

    genG1 := genT1 cat genS1;

    /* constructing automorphism group */
    vprint AutomorphismGroupSolubleGroup : "Construcing Aut(S2)...";
    vtime AutomorphismGroupSolubleGroup : AutS2 := AutomorphismGroupPGroup(S2);

    vprint AutomorphismGroupSolubleGroup : "Constructing representation for Aut(S2)...";
    vtime AutomorphismGroupSolubleGroup : AutS2_MapToRepElt, phi_AutS2, R_AutS2 := RepresentationAutomorphismGroupPGroup(AutS2);

    vprint AutomorphismGroupSolubleGroup : "Finding AutS2 fixing K2...";
    vtime AutomorphismGroupSolubleGroup : AutS2K := FixSubgroup(AutS2, K2);

    vprint AutomorphismGroupSolubleGroup : "Computing N_S1(T1), N_S2(T2)...";
    N_S1_T1 := Normaliser(G1, T1) meet S1;
    N_S2_T2 := Normaliser(G2, T2) meet S2;

    vprint AutomorphismGroupSolubleGroup : "Finding AutS2K fixing N_S2_T2...";
    vtime AutomorphismGroupSolubleGroup : AutS2KN := FixSubgroup(AutS2K, N_S2_T2);

    /* Compute AutK2 from AutS2KN */
    AutK2 := AutomorphismGroup(K2, genK2, [ [ K2 | k @ ask : k in genK2 ] : ask in Generators(AutS2KN) ] cat
        [ [ k^t : k in genK2 ] : t in genT2 ]);
    genAutK2InnT2 := [ AutK2.i : i in [ Ngens(AutS2KN)+1 .. Ngens(AutK2) ] ];

    vprint AutomorphismGroupSolubleGroup : "Finding mapping automorphism for K1 -> K2...";
    vtime AutomorphismGroupSolubleGroup : b, m := FindMappingAutomorphism(AutS2, K1 @ S1toS2, K2);
    if not b then
        vprint AutomorphismGroupSolubleGroup : "Cannot find mapping automorphism from image of K1 in G2 to K2 ";
        return false, _;
    end if;

    S1toS2 *:= m;
    assert2 K1 @ S1toS2 eq K2;

    vprint AutomorphismGroupSolubleGroup : "Finding mapping automorphism for N_S1(T1) -> N_S2(T2)...";
    vtime AutomorphismGroupSolubleGroup : b, m := FindMappingAutomorphism(AutS2K, N_S1_T1 @ S1toS2, N_S2_T2);
    if not b then
        vprint AutomorphismGroupSolubleGroup : "Cannot find mapping automorphism from image of N_S1_T1 in G2 to N_S2_T2";
        return false, _;
    end if;

    S1toS2 *:= m;
    assert2 K1 @ S1toS2 eq K2;
    assert2 N_S1_T1 @ S1toS2 eq N_S2_T2;

    /* Compute permutation rep of AutK2 */
    vprint AutomorphismGroupSolubleGroup : "Computing the permutation representation of AutK2...";
    vtime AutomorphismGroupSolubleGroup : phi_AutK2, R_AutK2 := PermutationRepresentation(AutK2);
    R_AutK2InnT2 := sub < R_AutK2 | genAutK2InnT2 @ phi_AutK2 >;

    /* Compute representation of AutS2KN */
    if Type(R_AutS2) eq GrpPC then
        /* FixSubgroup will have set RepGroup on AutS2KN */
        R_AutS2KN := AutS2KN`RepGroup;
        phi_AutS2KN := AutS2KN`RepMap;
    else
        /* otherwise we have a perm group */
        assert Type(R_AutS2) eq GrpPerm;
        R_AutS2KN := sub < R_AutS2 | [ AutS2KN.i @ phi_AutS2 : i in [1..Ngens(AutS2KN)] ] >;
        phi_AutS2KN := phi_AutS2; /* NB: Image and Kernel are now irrelevant... */
    end if;

    /* Construct mapping from AutS2KN -> AutK2 */
    AutS2KNtoAutK2 := hom < AutS2KN -> AutK2 | x :-> hom < K2 -> K2 | [ k @ x : k in genK2 ] > >;
    R_AutS2KNtoR_AutK2 := hom < R_AutS2KN -> R_AutK2 | [ ((R_AutS2KN.i @@ phi_AutS2KN) @ AutS2KNtoAutK2) @ phi_AutK2 : i in [1..NDgens(R_AutS2KN)] ] >;

    genImageOfT1inG2 := [ R_AutK2 | (AutK2!hom < K2 -> K2 | [ K2 | ((k @@ S1toS2) ^ t) @ S1toS2 : k in genK2 ] >) @ phi_AutK2 : t in genT1 ];
    ImageOfT1inG2 := sub < R_AutK2 | genImageOfT1inG2 >;

    /* ALTERNATIVE VERSION - SHOULD BE FASTER FOR LARGE EXAMPLES */
    /* Find an elt of Aut(S_2)_{K_2, N_{S_2}(T_2)} that maps {T_1}|_{K_1} |-> {T_2}|_{K_2} */
    ImageOfR_AutK2SNtoR_AutK2 := Image(R_AutS2KNtoR_AutK2);
    b, elt := IsConjugate(ImageOfR_AutK2SNtoR_AutK2, ImageOfT1inG2, R_AutK2InnT2);
    if not b then
        vprint AutomorphismGroupSolubleGroup : "Subgroups are not conjugate...";
        return false, _;
    end if;

    /* Ammend S1toS2 */
    S1toS2 *:= (elt @@ R_AutS2KNtoR_AutK2) @@ phi_AutS2KN;

    /* Check that S1toS2 does actually map the image of T1 in K1 to the image of T2 in K2 */
    if GetAssertions() gt 1 then
        /* Re-compute the image of T1 in G2 using the new S1toS2 */
        genImageOfT1inG2 := [ R_AutK2 | (AutK2!hom < K2 -> K2 | [ K2 | ((k @@ S1toS2) ^ t) @ S1toS2 : k in genK2 ] >) @ phi_AutK2 : t in genT1 ];
        ImageOfT1inG2 := sub < R_AutK2 | genImageOfT1inG2 >;
        assert2 ImageOfT1inG2 eq R_AutK2InnT2;
    end if;

    assert2 K1 @ S1toS2 eq K2;
    assert2 N_S1_T1 @ S1toS2 eq N_S2_T2;

    /* Compute the normaliser and then take the preimage */
    /* NB: as R_AutS2KNtoR_AutK2 isn't necessarily injective we *must* do the preimage
       as the whole group (so that we get the kernel in there too) */
    vprint AutomorphismGroupSolubleGroup : "Computing the normaliser...";
    vtime AutomorphismGroupSolubleGroup : N_R_AutS2KN := Normaliser(ImageOfR_AutK2SNtoR_AutK2, R_AutK2InnT2) @@ R_AutS2KNtoR_AutK2;

    /* Any isomorphism G1 -> G2 can now be formed by S1toS2 * n where n in Normaliser above */
    for r_n in N_R_AutS2KN do
        vprint AutomorphismGroupSolubleGroup : "Trying element of normaliser...";
        S1toS2_ := S1toS2 * (r_n @@ phi_AutS2KN);
        assert2 IsHomomorphism(S1, S2, genS1 @ S1toS2_);
        assert2 K1 @ S1toS2_ eq K2;
        assert2 N_S1_T1 @ S1toS2_ eq N_S2_T2;

        genImageOfT1inG2_ := [ R_AutK2 | (AutK2!hom < K2 -> K2 | [ K2 | ((k @@ S1toS2_) ^ t) @ S1toS2_ : k in genK2 ] >) @ phi_AutK2 : t in genT1 ];
        ImageOfT1inG2_ := sub < R_AutK2 | genImageOfT1inG2_ >;
        assert2 ImageOfT1inG2_ eq R_AutK2InnT2;

        img := [ FindConjugate(T2, K2, (r_t @@ phi_AutK2)) : r_t in genImageOfT1inG2_ ] cat (genS1 @ S1toS2_);
        b, m := IsHomomorphism(G1, G2, [ <genG1[i], img[i]> : i in [1..#genG1] ]);
        if b then
            return true, m;
        end if;
    end for;

    return false, _;
end function;

/*  Performs an isomorphism test between the soluble groups G1 and G2, with the optional
    parameter 'p' which should be a prime dividing the order of G (the calculation
    relies on IsIsomorphic(Syl_p(G_i)) and Aut(Syl_p(G_i)) for i in {1,2}).

    Default value of p is taken to be one which defines the largest Sylow p-subgroup.
*/

intrinsic IsIsomorphicSolubleGroup ( G1 :: GrpPC , G2 :: GrpPC : p := 1 ) -> BoolElt, Map
{Performs an isomorphism test between the soluble groups G1 and G2, with the optional
parameter 'p' which should be a prime dividing the order of G (the calculation
relies on IsIsomorphic(Syl_p(G_i)) and Aut(Syl_p(G_i)) for i = 1,2. Default
value of p is taken to be one which defines the largest Sylow p-subgroup.}

    vprint AutomorphismGroupSolubleGroup : "* IsIsomorphicSolubleGroup *";
    IndentPush();

    /* Test the orders first */
    if #G1 ne #G2 then
        vprint AutomorphismGroupSolubleGroup : "Orders do not match.";
        IndentPop();
        return false, _;
    end if;

    if #G1 eq 1 then
        vprint AutomorphismGroupSolubleGroup : "Trivial groups.";
        IndentPop();
        return true, iso < G1 -> G2 | >;
    end if;

    /* Test if they are the same - this is based on the code in GrpPerm/aut/isogps.m,
       in particular, note the use of Ngens instead of NPCgens */
    if G1 cmpeq G2 then
        vprint AutomorphismGroupSolubleGroup : "Groups are the same.";
        IndentPop();
        return true, iso < G1 -> G2 | [ G2 | G1.i : i in [1..NPCgens(G1)] ] >;
    end if;

    if IsVerbose("AutomorphismGroupSolubleGroup") then
        if #G1 le SmallGroupDatabaseLimit() then
            try
                vprint AutomorphismGroupSolubleGroup : "G1 is : ", IdentifyGroup(G1);
                vprint AutomorphismGroupSolubleGroup : "G2 is : ", IdentifyGroup(G2);
            catch e
                /* sometimes the group can't be determined if it is a specific order (i.e. 1920) */
                vprint AutomorphismGroupSolubleGroup : "Error in IdentifyGroup for order", #G1;
            end try;
        end if;
    end if;

    f := FactoredOrder(G1);
    if #f eq 1 then
        vprint AutomorphismGroupSolubleGroup : "G1 and G2 are p-groups.";
        vtime AutomorphismGroupSolubleGroup : b, m := IsIsomorphicPGroups(G1, G2);
        IndentPop();
        if not b then
            vprint AutomorphismGroupSolubleGroup : "G1 and G2 are not isomorphic";
            return false, _;
        end if;
        return b, m;
    end if;

    if p eq 1 then
        primes := [ f[i][1] : i in [1..#f] ];
        prime_powers := [ f[i][1]^f[i][2] : i in [1..#f] ];
        ParallelSort(~prime_powers, ~primes);
        for p_ in Reverse(primes) do
            K1 := pCore(G1, p_);
            if #K1 gt 1 then
                p := p_;
                break;
            end if;
        end for;
    else
        require IsPrime(p) : "Optional value p should be prime";
        K1 := pCore(G1, p);
        require #K1 ne 1 : "Input group G1 has trivial p-core";
    end if;

    /* construct K2 and test that they are the same size */
    K2 := pCore(G2, p);
    if #K1 ne #K2 then
        vprint AutomorphismGroupSolubleGroup : "p-cores are not same size";
        IndentPop();
        return false, _;
    end if;

    /* construct p' cores and test that they are the same size */
    L1 := pCore(G1, -p);
    L2 := pCore(G2, -p);
    if #L1 ne #L2 then
        vprint AutomorphismGroupSolubleGroup : "p'-cores are not same size";
        IndentPop();
        return false, _;
    end if;

    if #K1 * #L1 eq #G1 then
        vprint AutomorphismGroupSolubleGroup : "Direct Product";
        /* direct product */
        vprint AutomorphismGroupSolubleGroup : "Determining K1 iso K2...";
        vtime AutomorphismGroupSolubleGroup : K_iso, mapK := IsIsomorphicPGroups(K1, K2);
        if not K_iso then
            vprint AutomorphismGroupSolubleGroup : "p-cores are not isomorphic";
            IndentPop();
            return false, _;
        end if;

        vprint AutomorphismGroupSolubleGroup : "Determining L1 iso L2...";
        vtime AutomorphismGroupSolubleGroup : L_iso, mapL := $$(L1, L2);
        if not L_iso then
            vprint AutomorphismGroupSolubleGroup : "p'-cores are not isomorphic";
            IndentPop();
            return false, _;
        end if;

        IndentPop();
        return true, iso < G1 -> G2 | [ < K1.i, K1.i @ mapK > : i in [1..NPCgens(K1)] ] cat
            [ < L1.i, L1.i @ mapL > : i in [1..NPCgens(L1)] ] >;
    elif #L1 gt 1 then
        vprint AutomorphismGroupSolubleGroup : "Subdirect Product";

        G1_QK, G1m_K := quo < G1 | K1 >;
        G1_QL, G1m_L := quo < G1 | L1 >;

        G2_QK, G2m_K := quo < G2 | K2 >;
        G2_QL, G2m_L := quo < G2 | L2 >;

        vprint AutomorphismGroupSolubleGroup : "Determining if G1/K1 is isomorphic to G2/K2...";
        IndentPush();
        b, G1_QKtoG2_QK := $$(G1_QK, G2_QK);
        IndentPop();
        if not b then
            vprint AutomorphismGroupSolubleGroup : "G1/K1 not isomorphic to G2/K2";
            IndentPop();
            return false, _;
        end if;

        vprint AutomorphismGroupSolubleGroup : "Determining if G1/L1 is isomorphic to G2/L2...";
        IndentPush();
        b, G1_QLtoG2_QL := $$(G1_QL, G2_QL);
        IndentPop();
        if not b then
            vprint AutomorphismGroupSolubleGroup : "G1/L1 not isomorphic to G2/L2";
            IndentPop();
            return false, _;
        end if;

        /* TODO: Add fixing stuff in here, so that we check for p-group */
        vprint AutomorphismGroupSolubleGroup : "Constructing subdirect iso...";
        vtime AutomorphismGroupSolubleGroup : b, m := IsIsomorphicSubdirectProduct_(G1, G1_QK, G1m_K, G1_QL, G1m_L, G2, G2_QK, G2m_K, G2_QL, G2m_L, G1_QKtoG2_QK, G1_QLtoG2_QL);
        IndentPop();
        if b then return b, m; end if;
        return b, _;
    else
        T1 := HallSubgroup(G1, -p);
        T2 := HallSubgroup(G2, -p);

        if #G1 eq #T1 * #K1 then
            /* Semidirect product */
            vprint AutomorphismGroupSolubleGroup : "Semidrect Product";
            vprint  AutomorphismGroupSolubleGroup : "Determining if p-Cores are isomorphic...";
            vtime AutomorphismGroupSolubleGroup : K_iso, mapK := IsIsomorphicPGroups(K1, K2);
            if not K_iso then
                vprint AutomorphismGroupSolubleGroup : "p-cores are not isomorphic";
                IndentPop();
                return false, _;
            end if;

            vprint AutomorphismGroupSolubleGroup : "Using semidirect algorithm...";
            IndentPush();
            b, m :=  IsIsomorphicSemidirectProduct_(G1, K1, T1, G2, K2, T2, mapK);
            IndentPop();

            IndentPop();
            if b then return b, m; end if;
            return false, _;
        else
            vprint AutomorphismGroupSolubleGroup : "Conjugation Search";
            /* Construct the full Sylow p-groups */
            S1 := SylowSubgroup(G1, p);
            S2 := SylowSubgroup(G2, p);

            vprint  AutomorphismGroupSolubleGroup : "Determining if Sylow p-subgroups are isomorphic...";
            vtime AutomorphismGroupSolubleGroup : S_iso, mapS := IsIsomorphicPGroups(S1, S2);
            if not S_iso then
                vprint AutomorphismGroupSolubleGroup : "Sylow p-subgroups not isomorphic";
                IndentPop();
                return false, _;
            end if;

            vprint AutomorphismGroupSolubleGroup : "Using conjugation search algorithm...";
            IndentPush();
            vtime AutomorphismGroupSolubleGroup : b, m := IsIsomorphicConjugationSearch_(G1, S1, K1, T1, G2, S2, K2, T2, mapS);
            IndentPop();

            IndentPop();
            if b then return b, m; end if;
            return false, _;
        end if;
    end if;

    return false, _;

end intrinsic;


/* Alternative isomorphism testing where a map isn't needed.  Should generally be faster then
   IsIsomorphicSolubleGroup */
intrinsic IsIsomorphicSolubleGroupNoMap ( G1 :: GrpPC, G2 :: GrpPC : p := 1 ) -> BoolElt
{Performs an isomorphism test between two soluble groups G1 and G2. Returns true if the groups are isomorphic,
false otherwise.}

    /* Trivial test for equality */
    if G1 cmpeq G2 then return true; end if;
    /* Test orders */
    if #G1 ne #G2 then return false; end if;
    /* Use identify group if possible... */
    if #G1 le SmallGroupDatabaseLimit() then
        try
            b := IdentifyGroup(G1) eq IdentifyGroup(G2);
            ident := true;
        catch e
            /* sometimes the group can't be determined if it is a specific order (i.e. 1920) */
            ident := false;
            vprint AutomorphismGroupSolubleGroup : "Error in IdentifyGroup for order", #G1;
        end try;
        if ident then return b; end if;
    end if;

    f := FactoredOrder(G1);
    if #f eq 1 then
        vprint AutomorphismGroupSolubleGroup : "G1 and G2 are p-groups.";
        vtime AutomorphismGroupSolubleGroup : b, m := IsIsomorphicPGroups(G1, G2);
        IndentPop();
        if not b then
            vprint AutomorphismGroupSolubleGroup : "G1 and G2 are not isomorphic";
            return false, _;
        end if;
        return b, m;
    end if;

    if p eq 1 then
        primes := [ f[i][1] : i in [1..#f] ];
        prime_powers := [ f[i][1]^f[i][2] : i in [1..#f] ];
        ParallelSort(~prime_powers, ~primes);
        for p_ in Reverse(primes) do
            K1 := pCore(G1, p_);
            if #K1 gt 1 then
                p := p_;
                break;
            end if;
        end for;
    else
        require IsPrime(p) : "Optional value p should be prime";
        K1 := pCore(G1, p);
        require #K1 ne 1 : "Input group G1 has trivial p-core";
    end if;

    /* construct K2 and test that they are the same size */
    K2 := pCore(G2, p);
    if #K1 ne #K2 then
        vprint AutomorphismGroupSolubleGroup : "p-cores are not same size";
        IndentPop();
        return false, _;
    elif #K1 le SmallGroupDatabaseLimit() and IdentifyGroup(K1) ne IdentifyGroup(K2) then
        vprint AutomorphismGroupSolubleGroup : "p-cores are not the same (IdentifyGroup)";
        IndentPop();
        return false;
    end if;

    /* construct p' cores and test that they are the same size */
    L1 := pCore(G1, -p);
    L2 := pCore(G2, -p);
    if #L1 ne #L2 then
        vprint AutomorphismGroupSolubleGroup : "p'-cores are not same size";
        IndentPop();
        return false, _;
    elif #L1 le SmallGroupDatabaseLimit() and IdentifyGroup(L1) ne IdentifyGroup(L2) then
        vprint AutomorphismGroupSolubleGroup : "p'-cores are not the same (IdentifyGroup)";
        IndentPop();
        return false;
    end if;

    if #K1 * #L1 eq #G1 then
        vprint AutomorphismGroupSolubleGroup : "Direct Product";
        if #K1 le SmallGroupDatabaseLimit() and #L1 le SmallGroupDatabaseLimit() then
            /* We have already checked that they are identified above */
            IndentPop();
            return true;
        end if;
    end if;

    /* Fall back on default algorithm :-( */
    vprint AutomorphismGroupSolubleGroup : "Unable to quickly determine if isomorphic, falling back to full algorithm...";
    vtime AutomorphismGroupSolubleGroup : b, _ := IsIsomorphicSolubleGroup(G1, G2 : p := p);
    IndentPop();
    return b, _;
end intrinsic;
