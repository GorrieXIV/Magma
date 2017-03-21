freeze;

import "fix-subgroup.m" : FixSubgroup;
import "find-conjugate.m" : FindConjugate, FindConjugate_;

import "aut-subdirect.m" : AutomorphismGroupOfSubdirectProduct__;
import "aut-direct.m" : AutomorphismGroupOfDirectProduct_;

import "attributes.m" : AutomorphismGroupSolubleGroup_ComputeAutSKN_OrbitLimit;


/* Process data for carrying around the PC rep data */
PCRepProcessDataRF := recformat <
    S : GrpPC,                              /* S sylow p-subgroup */
    T : GrpPC,                              /* T hall p'-subgroup */
    InnG : GrpPC,                           /* PC group of G/Z(G) */
    phi_InnG : Map,                         /* Homomorphism G -> G/Z(G) */
    R_N_NoInn : GrpPC,                      /* Rep of Aut(S) which fixes T, no inners */
    R_NtoR_N_NoInn : Map,                   /* Map from rep Aut(S) which fixes T to no inner */
    R_N_NoInn_to_SLP : Map,                 /* Map from R_N_NoInn to SLP (for evaluating using RepGroup) */
    InnG_to_RepGroup : Map,                 /* Map from InnG to RepGroup */
    pc_group : Tup,                         /* A`PCGroup, or equivalently < A`RepGroup, A`RepMap > */
    AutS_fixT_MapToRepElt : UserProgram     /* The MapToRepElt function for Aut(S) */
>;


/*  Convert an automorphism map (not necessarily a GrpAutoElt) into its
    PC representation (for SnTnn - don't need to fix S first...).
*/
AutomorphismMapToPCElt_Semidirect := function (a, A)

    /* Take data from process_data record */
    process_data := A`PCRepData;
    T := process_data`T;
    S := process_data`S;
    G := A`Group;
    MapToRepElt := process_data`AutS_fixT_MapToRepElt;
    phi_InnG := process_data`phi_InnG;
    InnG := process_data`InnG;
    /* Map which takes rep elt form of normaliser to one with inner auts
       removed */
    R_NtoR_N_NoInn := process_data`R_NtoR_N_NoInn;
    R_N_NoInn := process_data`R_N_NoInn;
    R_N_NoInn_to_SLP := process_data`R_N_NoInn_to_SLP;
    InnG_to_RepGroup := process_data`InnG_to_RepGroup;
    RepGroup := A`RepGroup;

    /* find the elt of g s.t. conjugation of T by g is equivalent to action of a on T */
    b, g := IsConjugate(G, T, T @ a);
    error if not b, "Subgroups are not conjugate (SnTnn)";

    /* a now fixes T */
    a_fixT := a * hom < G -> G | [ G.i ^ (g^-1) : i in [1..NPCgens(G)] ] : Check := false >;
    /* restrict to S for which we have a PC rep */
    a_fixT := hom < S -> S | [ S.i @ a_fixT : i in [1..NPCgens(S)] ] : Check := false >;
    /* This is the PC rep of the non Inn (Out) part */
    r_a_out := a_fixT @ MapToRepElt @ R_NtoR_N_NoInn;

    a_out := Evaluate(r_a_out @ R_N_NoInn_to_SLP, A);
    a_inn := a_out^-1 * a;

    /* a_inn should act on G by conjugation */
    g2 := FindConjugate(G, G, a_inn);

    return Evaluate(r_a_out @ R_N_NoInn_to_SLP, RepGroup) * (g2 @ phi_InnG @ InnG_to_RepGroup);

end function;


/*  Convert an automorphism map (not necessarily a GrpAutoElt) into its
    PC representation (for SnnTnn - need to fix S first..).
*/
AutomorphismMapToPCElt_ConjugateSearch := function (a, A)

    /* Take data from process_data record */
    process_data := A`PCRepData;
    T := process_data`T;
    S := process_data`S;
    G := A`Group;
    InnG := process_data`InnG;
    phi_InnG := process_data`phi_InnG;
    MapToRepElt := process_data`AutS_fixT_MapToRepElt;

    R_N_NoInn_to_SLP := process_data`R_N_NoInn_to_SLP;
    InnG_to_RepGroup := process_data`InnG_to_RepGroup;
    RepGroup := A`PCGroup[1];

    /* Map which takes rep elt form of normaliser to one with inner auts
       removed */
    R_NtoR_N_NoInn := process_data`R_NtoR_N_NoInn;
    R_N_NoInn := process_data`R_N_NoInn;

    /* find the elt of g s.t. conjugation of T by g is equivalent to action of a on T */
    b, gS := IsConjugate(G, S, S @ a);
    error if not b, "S and S @ a are not conjugate (SnnTnn)";

    /* a now fixes S */
    a_fixS := a * hom < G -> G | [ G.i ^ (gS^-1) : i in [1..NPCgens(G)] ] : Check := false >;
    assert2 (S @ a_fixS) eq S;

    /* Again, a_fixS should act on T by conjugation */
    b, gT := IsConjugateInSubgroup(G, Normaliser(G, S), T, T @ a_fixS);
    error if not b, "T and T @ a_fixS are not conjugate";

    /* a now fixes S and T */
    a_fixS_fixT := a_fixS * hom < G -> G | [ G.i ^ (gT^-1) : i in [1..NPCgens(G)] ] : Check := false >;
    assert2 (T @ a_fixS_fixT) eq T;
    assert2 (S @ a_fixS_fixT) eq S;

    /* restrict to S for which we have a PC rep */
    a_fixS_fixT := hom < S -> S | [ S.i @ a_fixS_fixT : i in [1..NPCgens(S)] ] : Check := false >;

    /* This is the PC rep of the non Inn (Out) part */
    r_a_out := (a_fixS_fixT @ MapToRepElt) @ R_NtoR_N_NoInn;

    a_out := Evaluate(r_a_out @ R_N_NoInn_to_SLP, A);
    a_inn := a_out^-1 * a;

    /* a_inn should act on G by conjugation */
    b, g2 := FindConjugate_(G, G, a_inn);
    error if not b, "a_inn action on G is not conjugation.";

    return Evaluate(r_a_out @ R_N_NoInn_to_SLP, RepGroup) * (g2 @ phi_InnG @ InnG_to_RepGroup);

end function;


/*  Constructs a PC Presenetation for the automorphism group of a soluble group G. */
ConstructAutomorphismGroupPCRep := procedure ( ~process_data, A, AutomorphismMapToPCElt : check_relations := false )

    InnG := process_data`InnG;
    phi_InnG := process_data`phi_InnG;
    R_N_NoInn := process_data`R_N_NoInn;

    G := A`Group;

    /* Catch edge cases with PC -> FPGroup irregularities */
    if NPCgens(R_N_NoInn) eq 0 then
        error if #InnG eq 0, "Representation has no generators.";
        /* TODO: this is slow */
        // pc_to_auto_map := hom < InnG -> A | [ A.i : i in [1..NPCgens(InnG)] ] >;
        F, phi_F := FPGroup(InnG); F_to_A := hom < F -> A | [ A.i : i in [1..Ngens(A)] ] >;
        h := hom < A -> InnG | x :-> AutomorphismMapToPCElt(x, A), y :-> (y @@ phi_F) @ F_to_A >;
        process_data`pc_group := < InnG, h >;
        return;
    end if;

    /* NPCgens(InnG) could be 0 */
    F := FreeGroup(NPCgens(R_N_NoInn) + NPCgens(InnG));
    F_relations := [];

    /* Construct F1 for R_N_NoInn */
    F1 := FPGroup(R_N_NoInn);
    F1_relations := Relations(F1);
    W1 := SLPGroup(Ngens(F1));
    h1 := hom < F1 -> W1 | [ W1.i : i in [1..Ngens(W1)] ] >;

    /* Construct rewriting hom */
    F1toF := hom < F1 -> F | [ F.i : i in [1..Ngens(F1)] ] >;

    /* Construct F2 for InnG */
    if NPCgens(InnG) gt 0 then
        F2, F2_phi := FPGroup(InnG);
        F2toF := hom < F2 -> F | [ F.(Ngens(F1)+i) : i in [1..NPCgens(InnG)] ] >;
        /* NB: this map *cannot* be constructed directly (must act as rewriter) */
        InnGtoF := F2_phi^-1 * F2toF;
    end if;

    /* check if the relations from R_N_NoInn hold in A */
    Rels1 := [ (r[2]^-1 * r[1]) @ h1 : r in F1_relations ];
    A1 := Evaluate(Rels1, A);

    for i in [1..#F1_relations] do
        r := (F1_relations[i][1] @ F1toF) = (F1_relations[i][2] @ F1toF);

        if A1[i] ne Id(A) then
            /* the relation does not hold in A, needs to be extended */
            assert NPCgens(InnG) gt 0;
            n := FindConjugate(G, G, A1[i]);
            r[2] := r[2] * (n @ phi_InnG @ InnGtoF);
            if r[1] eq r[2] then
                /* Trivial relation */
                continue;
            end if;
        end if;

        Append(~F_relations, r);
    end for;

    if NPCgens(InnG) gt 0 then
        /* Add the relations for InnG */
        F_relations cat:= [ (r[1] @ F2toF) = (r[2] @ F2toF) : r in Relations(F2) ];

        /* Add the cross relations */
        for i in [1..Ngens(F2)] do
            for j in [1..Ngens(F1)] do
                second_chunk := ((InnG.i @@ phi_InnG) @ A.j) @ phi_InnG;
                relation := F.(i+Ngens(F1))^(F.j) = second_chunk @ InnGtoF;

                /* Check that the relation isn't trivial */
                lhs := Eltseq(relation[1]);
                rhs := Eltseq(relation[2]);
                if #lhs eq 3 and #rhs eq 1 then
                    if lhs[1] eq -1 * lhs[3] and lhs[2] eq rhs[1] then
                        continue;
                    end if;
                end if;
                Append(~F_relations, relation);
            end for;
        end for;
    end if;

    if check_relations or GetAssertions() gt 1 then
        W := SLPGroup(Ngens(F));
        h := hom < F -> W | [ W.i : i in [1..Ngens(W)] ] >;
        A_Check := Evaluate([ (r[2]^-1 * r[1]) @ h : r in F_relations ], A);
        assert { a : a in A_Check } eq { Id(A) };
    end if;

    Q, phi_Q := quo < GrpPC : F | F_relations >;
    error if not IsConsistent(Q), "The PC presentation is not consistent";

    /* TODO: This is really slow!! */
    //pc_to_auto_map := hom < Q -> A | [ A.i : i in [1..NPCgens(Q)] ] >;
    F_to_A := hom < F -> A | [ A.i : i in [1..NPCgens(Q)] ] >;
    h := hom < A -> Q | x :-> AutomorphismMapToPCElt(x, A), y :-> (y @@ phi_Q) @ F_to_A >;

    process_data`pc_group := < Q, h >;

end procedure;


/*  Computes the automorphism group of the soluble group G where both S and T are
    not normal (the more complex of the two SnTnn SnnTnn cases).

    G - soluble group
    S - sylow p-subgroup of G
    K - pCore of G
    T - Hall p'-subgroup of G
*/

AutomorphismGroupConjugationSearch_ := function (G, S, K, T)

    genS := [ G | s : s in PCGenerators(S) ];
    genT := [ G | t : t in PCGenerators(T) ];
    genG := genT cat genS;

    NST := Normaliser(G, T) meet S;

    vprint AutomorphismGroupSolubleGroup, 2 : "pRanks(S) = ", pRanks(S);
    vprint AutomorphismGroupSolubleGroup : "Computing Aut(S)";

    /* Passing CharacteristicSubgroups only filters out at the top layer, so still need to do
       FixSubgroup calculation */
    vtime AutomorphismGroupSolubleGroup : AutS := AutomorphismGroupPGroup_(S: CharacteristicSubgroups := [ K ]);

    vprint AutomorphismGroupSolubleGroup : "|Aut(S)| = ", FactoredOrder(AutS);
    // vprint AutomorphismGroupSolubleGroup, 3 : "|Aut(S)| = ", FactoredLaTeXOrder(AutS);

    AutS_MapToRepElt, phi_AutS, R_AutS := RepresentationAutomorphismGroupPGroup(AutS);

    vprint AutomorphismGroupSolubleGroup : "Computing AutSK...";
    vtime AutomorphismGroupSolubleGroup : AutSK := FixSubgroup(AutS, K : reduce_before_orbit := false);

    vprint AutomorphismGroupSolubleGroup : "|N_S(T)| = ", #NST;

    /* Check that we should compute AutSKN */
    compute_AutSKN := true;
    if IsVerbose("AutomorphismGroupSolubleGroupDoNotComputeAutSKN") then
        vprint AutomorphismGroupSolubleGroup : "Skipping computation of AutSKN (verbose setting)";
        compute_AutSKN := false;
    end if;

    if compute_AutSKN then
        vprint AutomorphismGroupSolubleGroup : "Computing AutSKN...";
        /* allow override for orbit limit */
        if IsVerbose("AutomorphismGroupSolubleGroupAutSKNIgnoreOrbitLimit") then
            orbit_limit := 0;
        else
            orbit_limit := AutomorphismGroupSolubleGroup_ComputeAutSKN_OrbitLimit;
        end if;

        vtime AutomorphismGroupSolubleGroup : AutSKN := FixSubgroup(AutSK, NST : reduce_before_orbit := true,
            orbit_limit := orbit_limit);
        /* check if the orbit-sabiliser failed to finish */
        if Type(AutSKN) eq BoolElt then
            vprint AutomorphismGroupSolubleGroup : "FixSubgroup: Orbit limit exceeded!";
            compute_AutSKN := false;
        end if;
    end if;

    if not compute_AutSKN then
        vprint AutomorphismGroupSolubleGroup : "Skipping computation of AutSKN...";
        AutSKN := AutSK;
    end if;

    if Type(R_AutS) eq GrpPC then
        /* note that FixSubgroup ensures that the generators of AutSKN and R_AutSKN will match */
        R_AutSKN := AutSKN`PCGroup[1];
    else
        vprint AutomorphismGroupSolubleGroup : "Computing R_AutSKN...";
        vtime AutomorphismGroupSolubleGroup : R_AutSKN := sub < R_AutS | [ AutSKN.i @ AutS_MapToRepElt : i in [ 1..Ngens(AutSKN) ] ] >;
    end if;

    genK := [ K | k : k in PCGenerators(K) ];

    /* If K is large and AutSKN is soluble, then we should try to construct AutK properly,
       and then potentially get a PC rep - does PermutationRepresentation need to construt whole
       automorphism group ? */
    computed_AutK := false;
    if IsVerbose("AutomorphismGroupSolubleGroupComputeAutK") then
        /* NB we only bother doing this if we have a PC rep for AutSKN */
        if Type(R_AutSKN) eq GrpPC then
            vprint AutomorphismGroupSolubleGroup : "AutomorphismGroupSolubleGroupComputeAutK is set, and R_AutSKN is soluble...";
            vprint AutomorphismGroupSolubleGroup, 2 : "pRanks(K) = ", pRanks(K);

            K := SpecialPresentation(K);
            vprint AutomorphismGroupSolubleGroup : "Computing Aut(K)";
            vtime AutomorphismGroupSolubleGroup : AutK := AutomorphismGroupPGroup(K);
            vprint AutomorphismGroupSolubleGroup : "|Aut(K)| =", FactoredOrder(AutK);
            // vprint AutomorphismGroupSolubleGroup, 3 : "|Aut(K)| =", FactoredLaTeXOrder(AutK);

            vprint AutomorphismGroupSolubleGroup : "Testing if Aut(K) is soluble...";
            vtime AutomorphismGroupSolubleGroup : m, phi_AutK, R_AutK := PCGroupAutomorphismGroupPGroup(AutK);

            if m then
                vprint AutomorphismGroupSolubleGroup : "Aut(K) is soluble, we have a PC representation for it";
                computed_AutK := true;
            end if;
        end if;
    end if;

    if not computed_AutK then
        if Type(R_AutSKN) eq GrpPC then
            AutK_gens_from_AutSKN := [ [ K | k @ x : k in genK ] : x in PCGenerators(AutSKN) ];
        else
            AutK_gens_from_AutSKN := [ [ K | k @ AutSKN.i : k in genK ] : i in [1..Ngens(AutSKN)] ];
        end if;

        /* subgroup of AutK that contains the restriction of AutSKN and InnT to K */
        AutK := AutomorphismGroup(K, genK, AutK_gens_from_AutSKN cat
            [ [ k^t : k in genK ] : t in genT ]);

        /* Can't avoid this, AutK isn't necessarily soluble */
        vprint AutomorphismGroupSolubleGroup : "Computing the permutation representation for AutK";
        vtime AutomorphismGroupSolubleGroup : phi_AutK, R_AutK := PermutationRepresentation(AutK);

        vprint AutomorphismGroupSolubleGroup, 3 : "Created perm rep and IsSoluble(R_AutK)", IsSoluble(R_AutK);
    end if;

    /* Construct mapping from AutSKN to AutK, used later */
    AutSKNtoAutK := hom < AutSKN -> AutK | x :-> hom < K -> K | [k @ x : k in genK] > >;

    /* Construct restriction map from R_AutSKN to R_AutK */
    vprint AutomorphismGroupSolubleGroup : "Computing R_AutSKN -> R_AutK";
    //vtime AutomorphismGroupSolubleGroup : R_AutSKNtoR_AutK := hom < R_AutSKN -> R_AutK | [ R_AutK | ((R_AutSKN.i @@ phi_AutS) @ AutSKNtoAutK) @ phi_AutK : i in [ 1 .. Ngens(R_AutSKN) ] ] >;

    /* If both R_AutK and R_AutSKN are PC groups then must do this differently... */
    /* TODO: This has been fixed in the development version, so this should be updated */
    if Type(R_AutK) eq GrpPC and Type(R_AutSKN) eq GrpPC then
        genAutKInnT := [ AutK!hom < K -> K | [ K.i ^ T.j : i in [1..NPCgens(K)] ] > : j in [1..NPCgens(T)] ];
        R_AutKInnT := sub < R_AutK | [ genAutKInnT[i] @ phi_AutK : i in [1..#genAutKInnT] ] >;

        R_AutSKNtoR_AutK := hom < R_AutSKN -> R_AutK | [ R_AutK | (AutSKN.i @ AutSKNtoAutK) @ phi_AutK : i in [1..Ngens(AutSKN)] ] >;
        assert IsHomomorphism(R_AutSKNtoR_AutK);
        /*R_AutKAutSKN := sub < R_AutK | [ (AutSKN.i @ AutSKNToAutK) @ phi_AutK : i in Ngens(AutSKN) ] >;*/
        R_AutKAutSKN := Image(R_AutSKNtoR_AutK);
    else
        genAutKInnT := [ AutK.i : i in [NDgens(R_AutSKN)+1..Ngens(AutK)] ];
        R_AutKInnT := sub < R_AutK | [ R_AutK.i : i in [NDgens(R_AutSKN)+1..Ngens(R_AutK)] ] >;
        R_AutKAutSKN := sub < R_AutK | [ R_AutK.i : i in [1..NDgens(R_AutSKN)] ] >;
        /* NB: we are assuming that the gens of the perm rep of Aut(K) match the gens of Aut(K)...*/
        vtime AutomorphismGroupSolubleGroup : R_AutSKNtoR_AutK := hom < R_AutSKN -> R_AutK | [ R_AutK | R_AutK.i : i in [1..NDgens(R_AutSKN)] ] >;
    end if;

    /* Compute the normaliser in AutK of InnT restricted to K, mapped back to AutSKN */
    vprint AutomorphismGroupSolubleGroup : "Computing normaliser";
    vtime AutomorphismGroupSolubleGroup : R_N_AutKAutSKN := Normaliser(R_AutK, R_AutKInnT) meet R_AutKAutSKN;

    vprint AutomorphismGroupSolubleGroup : "Mapping normaliser back to Aut(S)";
    vprint AutomorphismGroupSolubleGroup : "Not GrpPC -> GrpPerm";
    vtime AutomorphismGroupSolubleGroup : R_N_AutSKN := R_N_AutKAutSKN @@ R_AutSKNtoR_AutK;

    vprint AutomorphismGroupSolubleGroup : "Constructing reps of generators of NST in Aut(S)_{K, N_S(T)}";
    vtime AutomorphismGroupSolubleGroup : R_genAutSKNInnSKN := [ hom < S -> S | [ s^c : s in genS ] > @ AutS_MapToRepElt : c in PCGenerators(NST) ];
    R_AutSKNInnS := sub < R_AutSKN | R_genAutSKNInnSKN >;

    /* Make initial coset for use in search.  Know that inner auts fixing S and T will extend */
    R_Coset := R_N_AutSKN meet R_AutSKNInnS;

    imgs := [];

    /* Check through the generators of R_N_AutSKN to check if they work (they can be factored out
       in the coset rep). */
    r_gens_for_r_coset := [ R_N_AutSKN | ];
    vprint AutomorphismGroupSolubleGroup : "Running through all gens of normaliser...";
    vtime AutomorphismGroupSolubleGroup : for r_n in Generators(R_N_AutSKN) do
        n := r_n @@ phi_AutS;
        nk := n @ AutSKNtoAutK;
        img := [ FindConjugate(T, K, nk^-1 * a * nk) : a in genAutKInnT ] cat (genS @ n);
        b, m := IsHomomorphism(G, G, [ < genG[i], img[i] > : i in [1..#genG] ]);
        if b then
            Append(~imgs, img);
            Append(~r_gens_for_r_coset, r_n);
        end if;
    end for;

    /* Construct new R_Coset consisting of any new auts which were found to extend */
    R_Coset := sub < R_AutSKN | [ R_Coset | r : r in Generators(R_Coset) ] cat r_gens_for_r_coset >;

    vprint AutomorphismGroupSolubleGroup : "Computing double coset representatives";
    vtime AutomorphismGroupSolubleGroup : R_N_AutSKN_T := DoubleCosetRepresentatives(R_N_AutSKN, R_Coset, R_Coset);

    vprint AutomorphismGroupSolubleGroup : "Number of double coset reps: ", #R_N_AutSKN_T;

    /* Run through the cosets and search for more autos which extend */
    if #R_N_AutSKN_T gt 1 then
        /* first coset rep is identity */
        i := 2;
        vprint AutomorphismGroupSolubleGroup : "Running through coset reps...";

        vtime AutomorphismGroupSolubleGroup : while i le #R_N_AutSKN_T do
            r_n := R_N_AutSKN_T[i];
            n := r_n @@ phi_AutS;
            nk := n @ AutSKNtoAutK;
            img := [ FindConjugate(T, K, nk^-1 * a * nk) : a in genAutKInnT ] cat (genS @ n);
            b, m := IsHomomorphism(G, G, [ < genG[i], img[i] > : i in [1..#genG] ]);
            if b then
                Append(~imgs, img);
                R_Coset := sub < R_AutSKN | [ r : r in Generators(R_Coset) ] cat [ r_n ] >;
                R_N_AutSKN_T := DoubleCosetRepresentatives(R_N_AutSKN, R_Coset, R_Coset);
                vprint AutomorphismGroupSolubleGroup : "#R_N_AutSKN_T = ", #R_N_AutSKN_T;
                i := 1;
            end if;
            i +:= 1;
        end while;
    end if;

    /* Branch for creating PC Rep if R_Coset is soluble */
    if IsSoluble(R_Coset) then
        vprint AutomorphismGroupSolubleGroup : "R_Coset is soluble, creating PC rep for R_Coset...";
        R_Coset_PC, phi_R_Coset_PC := PCGroup(R_Coset);

        NGTmeetNGS := Normaliser(G, T) meet Normaliser(G, S);
        genAutSKNInn := [ hom < S -> S | [ S.i ^ NGTmeetNGS.j : i in [1..NPCgens(S)] ] > : j in [1..NPCgens(NGTmeetNGS)] ];
        R_Coset_PC_Inn := sub < R_Coset_PC | [ (h @ AutS_MapToRepElt) @ phi_R_Coset_PC : h in genAutSKNInn ] >;
        R_Coset_PC_NoInn, R_Coset_PCtoR_Coset_PC_NoInn := quo < R_Coset_PC | R_Coset_PC_Inn >;

        vprint AutomorphismGroupSolubleGroup : "Constructing automorphisms for PC generators of R_Coset...";
        imgs := [];
        for r_pc_no_inn in PCGenerators(R_Coset_PC_NoInn) do
            r_n := r_pc_no_inn @@ R_Coset_PCtoR_Coset_PC_NoInn @@ phi_R_Coset_PC;
            n := r_n @@ phi_AutS;
            nk := n @ AutSKNtoAutK;
            img := [ FindConjugate(T, K, nk^-1 * a * nk) : a in genAutKInnT ] cat (genS @ n);
            /* Construct another homomorphism, this should not fail */
            b, m := IsHomomorphism(G, G, [ < genG[i], img[i] > : i in [1..#genG] ]);
            error if not b, "Homomorphism is not valid and it should be.";
            Append(~imgs, img);
        end for;

        vprint AutomorphismGroupSolubleGroup : "Starting to construct PC rep for full automorphism group...";
        InnG, phi_InnG := quo < G | Center(G) >;

        /* Construct automorphism group */
        A := AutomorphismGroup2(G, genG, imgs cat [ [ G | h^(InnG.i @@ phi_InnG) : h in genG ] : i in [1..NPCgens(InnG)] ]);
        A`InnerGenerators := [ A.i : i in [#imgs+1..Ngens(A)] ];

        new_map_to_rep_elt := function ( m )
            x := (m @ AutS_MapToRepElt);
            return (R_Coset!x) @ phi_R_Coset_PC;
        end function;

        /* Construct maps used for coercing automorphisms into PC elts */
        W_R_N_NoInn := SLPGroup(NPCgens(R_Coset_PC_NoInn));
        phi_W_R_N_NoInn := hom < R_Coset_PC_NoInn -> W_R_N_NoInn | [ W_R_N_NoInn.i : i in [1..Ngens(W_R_N_NoInn)] ] >;

        /* Assign process data */
        process_data := rec < PCRepProcessDataRF | S := S, T := T, InnG := InnG, phi_InnG := phi_InnG, R_N_NoInn := R_Coset_PC_NoInn,
            R_NtoR_N_NoInn := R_Coset_PCtoR_Coset_PC_NoInn, R_N_NoInn_to_SLP := phi_W_R_N_NoInn,
            AutS_fixT_MapToRepElt := new_map_to_rep_elt >;

        vtime AutomorphismGroupSolubleGroup : ConstructAutomorphismGroupPCRep(~process_data, A, AutomorphismMapToPCElt_ConjugateSearch : check_relations := true);

        A`PCGroup := process_data`pc_group;

        A`RepMap := process_data`pc_group[2];
        A`RepGroup := process_data`pc_group[1];

        process_data`InnG_to_RepGroup := hom < InnG -> A`RepGroup | [ A`RepGroup.(NPCgens(R_Coset_PC_NoInn) + i) : i in [1..NPCgens(InnG)] ] >;

        A`OuterOrder := #process_data`R_N_NoInn;
        A`Order := A`OuterOrder * #InnG;

        map_to_rep_elt := function (m)
            return AutomorphismMapToPCElt_ConjugateSearch (m, A);
        end function;
        A`MapToRepElt := map_to_rep_elt;

        A`PCRepData := process_data;
        A`Soluble := true;
        A`PCGenerators := {@ A.i : i in [1..Ngens(A)] @};

        assert CheckPCRepresentation(A);

        vprint AutomorphismGroupSolubleGroup : "PC rep constructed.";
    else
        A := AutomorphismGroup2(G, genG, imgs cat [ [ G | h^g : h in genG ] : g in genG ]);
        A`InnerGenerators := [ A.i : i in [#imgs+1..Ngens(A)] ];
        A`Soluble := false;

        /* Find the order */
        A`Order := #R_Coset * #G div #(Normaliser(G, T) meet Normaliser(G, S));
    end if;

    vprint AutomorphismGroupSolubleGroup : "Order of automorphism group: ", #A, FactoredOrder(A);
    // vprint AutomorphismGroupSolubleGroup, 3 : "Order of automorphism group:", #A, FactoredLaTeXOrder(A);

    return A;

end function;


/*  Computes the automorphism group of the soluble group G where S is normal and T is
    not normal (G is a semidirect product of S and T).

    G - soluble group
    S - sylow p-subgroup of G
    T - hall p'-subgroup of G
*/
AutomorphismGroupSemidirectProduct_ := function (G, S, T)

    /* The generators of G (split into S and T) */
    genS := [ s : s in PCGenerators(S) ];
    genT := [ t : t in PCGenerators(T) ];

    genG := genT cat genS;

    /*  Check if S is elementary abelian, if so branch off and use GLNormaliser code for
        normaliser calculation. Note that most of this code here is copied from below.
        Would be better to be able to call Normaliser on GrpMat which was GL(n, q)...
    */
    if IsElementaryAbelian(S) then
        vprint AutomorphismGroupSolubleGroup : "p-group is elementary abelian, preparing to use GLNormaliser...";
        vprint AutomorphismGroupSolubleGroup : "Computing automorphism group";

        /* Note that we don't need to the permutation rep as we only need the matrix rep */
        vtime AutomorphismGroupSolubleGroup : AutS := AutomorphismGroupElementaryAbelianPGroup(S);

        vprint AutomorphismGroupSolubleGroup : "|Aut(S)| = ", FactoredOrder(AutS);
        // vprint AutomorphismGroupSolubleGroup, 3 : "|Aut(S)| = ", FactoredLaTeXOrder(AutS);

        MapToRepElt, phi_AutS, R_AutS := RepresentationAutomorphismGroupPGroup(AutS);

        /* if AutS is soluble, then use other code (so that we end up with PC rep) */
        if not IsSoluble(AutS) then
            genAutSInnT := [ hom < S -> S | [ S | s^t : s in genS ] > : t in genT ];

            vprint AutomorphismGroupSolubleGroup : "Converting InnT|S into representation...";
            vtime AutomorphismGroupSolubleGroup : genR_AutSInnT := [ MapToRepElt( h ) : h in genAutSInnT ];

            vprint AutomorphismGroupSolubleGroup : "Computing normaliser...";
            vtime AutomorphismGroupSolubleGroup : R_N := GLNormaliser(sub < AutS`MatrixGroup | genR_AutSInnT >);

            /* we only need action of matrices as maps, not auto elts */
            RepEltToMap := AutS`RepEltToMap;

            vprint AutomorphismGroupSolubleGroup : "Constructing GrpAuto elts from rep elts";
            vtime AutomorphismGroupSolubleGroup : genN := [ r @ RepEltToMap : r in Generators(R_N) ];

            vprintf AutomorphismGroupSolubleGroup : "Extending %o generators to automorphisms of G (#genAutSInnT = %o)", #genN, #genAutSInnT;
            vtime AutomorphismGroupSolubleGroup : imgs := [ [ FindConjugate(T, S, n^-1 * a * n) : a in genAutSInnT ] cat (genS @ n) : n in genN ];

            A := AutomorphismGroup2(G, genG, imgs cat [ [ G | h^g : h in genG ] : g in genG ]);
            A`InnerGenerators := [ A.i : i in [#imgs+1..Ngens(A)] ];
            A`Soluble := false;

            /* Compute the order of A */
            vprint AutomorphismGroupSolubleGroup : "Computing the order of the automorphism group...";
            vtime AutomorphismGroupSolubleGroup : A`Order := #R_N * #G div #Normaliser(G, T);
            vprint AutomorphismGroupSolubleGroup : "Order of automorphism group: ", A`Order, FactoredOrder(A);
            // vprint AutomorphismGroupSolubleGroup, 3 : "Order of automorphism group: ", A`Order, FactoredLaTeXOrder(A);

            return A;
        end if;
    else
        vprint AutomorphismGroupSolubleGroup, 2 : "pRanks(S) = ", pRanks(S);
        vprint AutomorphismGroupSolubleGroup : "Computing Aut(S)";

        vtime AutomorphismGroupSolubleGroup : AutS := AutomorphismGroupPGroup_(S);
        vprint AutomorphismGroupSolubleGroup : "|Aut(S)| = ", FactoredOrder(AutS);
        // vprint AutomorphismGroupSolubleGroup, 3 : "|Aut(S)| = ", FactoredLaTeXOrder(AutS);

        MapToRepElt, phi_AutS, R_AutS := RepresentationAutomorphismGroupPGroup(AutS);
    end if;

    vprint AutomorphismGroupSolubleGroup : "Creating genAutSInnT";
    vtime AutomorphismGroupSolubleGroup : genAutSInnT := [ hom < S -> S | [ S | s^t : s in genS ] > : t in genT ];
    vtime AutomorphismGroupSolubleGroup : genR_AutSInnT := [ MapToRepElt( h ) : h in genAutSInnT ];

    vprint AutomorphismGroupSolubleGroup : "Calculating normliser in Aut(S) of Inn T in Aut(S)";
    vtime AutomorphismGroupSolubleGroup : R_N := Normaliser(R_AutS, sub < R_AutS | genR_AutSInnT >);

    /* check if R_N is soluble, even though it might not be a GrpPC group */
    if Type(R_N) ne GrpPC and IsSoluble(R_N) then
        vprint AutomorphismGroupSolubleGroup : "R_N is soluble - converting to PC groups";

        /* construct PC group */
        R_N, phi_R_N_PC := PCGroup(R_N);

        /* modify RepEltToAutoElt and MapToRepElt */
        RepEltToAutoElt :=  function (r)
            return (r @@ phi_R_N_PC) @@ phi_AutS;
        end function;

        MapToRepElt := function (m)
            return (m @ AutS`MapToRepElt) @ phi_R_N_PC;
        end function;

        /* Update rep for seq of generators for InnT in AutS */
        genR_AutSInnT := genR_AutSInnT @ phi_R_N_PC;
    else
        /* setup RepEltToAutoElt as it hasn't been used so far */
        RepEltToAutoElt := function (r)
            return r @@ phi_AutS;
        end function;
    end if;


    /* Need to take PCGenerators to make sure that they are correctly ordered for conversion
       to PC group.
    */
    if Type(R_N) eq GrpPC then
        NGT := Normaliser(G, T);
        genAutSInnNGT := [ hom < S -> S | [ S.i ^ NGT.j : i in [1..NPCgens(S)] ] > : j in [1..NPCgens(NGT)] ];
        R_N_Inn := sub < R_N | [ MapToRepElt(h) : h in genAutSInnNGT ] cat genR_AutSInnT >;
        R_N_NoInn, R_NtoR_N_NoInn := quo < R_N | R_N_Inn >;
        genN := [ (r @@ R_NtoR_N_NoInn) @ RepEltToAutoElt : r in PCGenerators(R_N_NoInn) ];
    else
        genN := [ r @ RepEltToAutoElt : r in Generators(R_N) ];
    end if;

    /* construct images of the automorphisms of G which fix S and T */
    vprintf AutomorphismGroupSolubleGroup : "Running through %o generators of normaliser and extending to automorphisms of G...", #genN;
    vtime AutomorphismGroupSolubleGroup : imgs := [ [ FindConjugate(T, S, n^-1 * a * n) : a in genAutSInnT ] cat (genS @ n) : n in genN ];

    if Type(R_N) eq GrpPC then
        vprint AutomorphismGroupSolubleGroup : "Starting to construct PC rep for full automorphism group...";

        InnG, phi_InnG := quo < G | Center(G) >;

        A := AutomorphismGroup2(G, genG, imgs cat [ [ G | h^(InnG.i @@ phi_InnG) : h in genG ] : i in [1..NPCgens(InnG)] ]);
        A`InnerGenerators := [ A.i : i in [#imgs+1..Ngens(A)] ];

        /* Construct maps used for coercing automorphisms into PC elts */
        W_R_N_NoInn := SLPGroup(NPCgens(R_N_NoInn));
        phi_W_R_N_NoInn := hom < R_N_NoInn -> W_R_N_NoInn | [ W_R_N_NoInn.i : i in [1..Ngens(W_R_N_NoInn)] ] >;

        /* Assign process data */
        process_data := rec < PCRepProcessDataRF | S := S, T := T, InnG := InnG, phi_InnG := phi_InnG,
            R_N_NoInn := R_N_NoInn,
            R_NtoR_N_NoInn := R_NtoR_N_NoInn,
            R_N_NoInn_to_SLP := phi_W_R_N_NoInn,
            AutS_fixT_MapToRepElt := MapToRepElt
        >;

        ConstructAutomorphismGroupPCRep(~process_data, A, AutomorphismMapToPCElt_Semidirect : check_relations := true);
        vprint AutomorphismGroupSolubleGroup : "PC rep constructed.";

        A`PCGenerators := {@ A.i : i in [1..Ngens(A)] @};

        A`PCGroup := process_data`pc_group;
        A`RepMap := A`PCGroup[2];
        A`RepGroup := A`PCGroup[1];

        process_data`InnG_to_RepGroup := hom < InnG -> A`RepGroup | [ A`RepGroup.(NPCgens(R_N_NoInn) + i) : i in [1..NPCgens(InnG)] ] >;

        A`Soluble := true;

        map_to_rep_elt := function (m)
            return AutomorphismMapToPCElt_Semidirect (m, A);
        end function;
        A`MapToRepElt := map_to_rep_elt;

        A`PCRepData := process_data;
        A`OuterOrder := #R_N_NoInn;
        A`Order := A`OuterOrder * #InnG;

        assert CheckPCRepresentation(A);
    else
        A := AutomorphismGroup2(G, genG, imgs cat [ [ G | h^g : h in genG ] : g in genG ]);
        A`InnerGenerators := [ A.i : i in [#imgs+1..Ngens(A)] ];
        A`Soluble := false;

        /* Set the order of the automorphism group */
        A`Order := #R_N * #G div #Normaliser(G, T);
    end if;

    vprint AutomorphismGroupSolubleGroup : "Order of automorphism group:", #A, FactoredOrder(A);
    // vprint AutomorphismGroupSolubleGroup, 3 : "Order of automorphism group:", #A, FactoredLaTeXOrder(A);

    return A;

end function;


/*  Computes the automorphism group of the soluble group G, with the optional
    parameter 'p' which should be a prime dividing the order of G (the calculation
    relies on Aut(Syl_p(G))).  Default value of p is taken to be one which defines
    the largest Sylow p-subgroup.
*/

intrinsic AutomorphismGroupSolubleGroup ( G :: GrpPC : p := 1) -> GrpAuto
{Computes the automorphism group of the soluble group G, with the optional parameter
'p' which should be a prime dividing the order of G (the calculation relies on
Aut(Syl_p(G))).  Default value of p is taken to be the prime diving the order of G which
defines the largest Sylow p-subgroup.}

    /* for debugging purposes */
    seed_n, seed_i := GetSeed();

    vprint AutomorphismGroupSolubleGroup : "* AutomorphismGroupSolubleGroup *";
    IndentPush();

    if IsVerbose("AutomorphismGroupSolubleGroup", 1) then
        if #G lt SmallGroupDatabaseLimit() then
            try
                vprint AutomorphismGroupSolubleGroup : "Group is", IdentifyGroup(G);
            catch e
                /* sometimes the group can't be determined if it is a specific order (i.e. 1920) */
                vprint AutomorphismGroupSolubleGroup : "Error in IdentifyGroup for order", #G;
            end try;
        end if;
    end if;

    f := FactoredOrder(G);
    if #f eq 0 then
        /* return the trivial automorphism group */
        return AutomorphismGroup(G, [ G | ], [ Parent([ G | ]) | ]);
    end if;

    /* If G is a p-group then branch to appropriate algorithm */
    if #f eq 1 then
        if not IsConditioned(G) then
            G := SpecialPresentation(G);
        end if;
        vprint AutomorphismGroupSolubleGroup : "G is a p-group.  Computing Aut(G)...";
        vtime AutomorphismGroupSolubleGroup : A := AutomorphismGroupPGroup_(G);
        vprint AutomorphismGroupSolubleGroup : "Testing if Aut(G) is soluble...";
        vtime AutomorphismGroupSolubleGroup : b, _, _ := PCGroupAutomorphismGroupPGroup(A);

        if b then
            vprint AutomorphismGroupSolubleGroup : "Aut(G) soluble, we have PC presentation.";
        else
            vprint AutomorphismGroupSolubleGroup : "Aut(G) not soluble.";
        end if;

        /* end of automorphism group soluble group */
        IndentPop();
        return A;
    end if;

    /* If no p set, then take the one that corresponds to largest p-subgroup with non-trivial p-core */
    if p eq 1 then
        primes := [ f[i][1] : i in [1..#f] ];
        prime_powers := [ f[i][1]^f[i][2] : i in [1..#f] ];
        ParallelSort(~prime_powers, ~primes);
        for p_ in Reverse(primes) do
            K := pCore(G, p_);
            if #K gt 1 then
                p := p_;
                break;
            end if;
        end for;
    else
        require IsPrime(p) : "Optional value p should be prime";
        K := pCore(G, p);
        require #K ne 1 : "The input group has trivial p-core";
    end if;

    vprintf AutomorphismGroupSolubleGroup : "|G|=%o, p=%o\n", f, p;

    L := pCore(G, -p);
    if #G eq #L * #K then
        vprint AutomorphismGroupSolubleGroup : "Direct product";
        IndentPush();
        vtime AutomorphismGroupSolubleGroup : A := AutomorphismGroupOfDirectProduct_(G, K, L);
        IndentPop();
    elif #L gt 1 then
        Q_GK, m_GK := quo< G | K >;
        Q_GL, m_GL := quo< G | L >;

        /* this needs to be set here before Aut(Q_GK) is computed... */
        if #FactoredOrder(Q_GK) eq 1 and not IsConditioned(Q_GK) then
            Q_GK := SpecialPresentation(Q_GK);
        end if;

        /* this needs to be set here before Aut(Q_GL) is computed... */
        if #FactoredOrder(Q_GL) eq 1 and not IsConditioned(Q_GL) then
            Q_GL := SpecialPresentation(Q_GL);
        end if;

        vprint AutomorphismGroupSolubleGroup : "Subdirect product";
        IndentPush();

        vprint AutomorphismGroupSolubleGroup : "Computing Aut(G/L)...";
        IndentPush();
        vtime AutomorphismGroupSolubleGroup : AQ_GL := $$(Q_GL);
        IndentPop();

        /* This is a soluble group of size G / K, so maybe want to take new p... */
        vprint AutomorphismGroupSolubleGroup : "Computing Aut(G/K)...";
        IndentPush();
        vtime AutomorphismGroupSolubleGroup : AQ_GK := $$(Q_GK);
        IndentPop();

        /* if L = T then G/L is a p-group and L = O_p'(G/K), so don't need to do this fixsubgroup */
        // if #L ne #HallSubgroup(G, -p) then
        if #FactoredOrder(Q_GL) gt 1 then
            vprint AutomorphismGroupSolubleGroup : "Computing subgroup of Aut(G/K) fixing L...";
            vtime AutomorphismGroupSolubleGroup : AQ_GK := FixSubgroup(AQ_GK, L @ m_GK);
        else
            assert #[ i : i in [1..Ngens(AQ_GK)] | (L @ m_GK) @ AQ_GK.i ne (L @ m_GK) ] eq 0;
            vprint AutomorphismGroupSolubleGroup : "Aut(G/K) already fixes L...";
        end if;

        /* if K = S then G/K is a p'-hall subgroup and K = O_p'(G/L), so don't need to do this fixsubgroup */
        // if #K ne #Sylow(G, p) then
        if (#f - #Factorisation(#G div #K)) eq 0 then
            vprint AutomorphismGroupSolubleGroup : "Computing subgroup of Aut(G/L) fixing K...";
            vtime AutomorphismGroupSolubleGroup : AQ_GL := FixSubgroup(AQ_GL, K @ m_GL);
        else
            assert #[ i : i in [1..Ngens(AQ_GL)] | (K @ m_GL) @ AQ_GL.i ne (K @ m_GL) ] eq 0;
            vprint AutomorphismGroupSolubleGroup : "Aut(G/L) already fixes K...";
        end if;

        /* Compute the automorphism group of the subdirect product */
        vprint AutomorphismGroupSolubleGroup : "Calculating automorphism group for subdirect product...";
        IndentPush();
        vtime AutomorphismGroupSolubleGroup : A := AutomorphismGroupOfSubdirectProduct__(G, K, L, Q_GK, m_GK, Q_GL, m_GL, AQ_GK, AQ_GL);
        IndentPop();

        /* end of subdirect product */
        IndentPop();
    else
        T := HallSubgroup(G, -p);
        if #G eq #K * #T then
            vprint AutomorphismGroupSolubleGroup : "Semidirect product";
            IndentPush();
            A := AutomorphismGroupSemidirectProduct_(G, K, T);
            IndentPop();
        else
            S := SpecialPresentation(Sylow(G, p));
            vprint AutomorphismGroupSolubleGroup : "Conjugation search";
            IndentPush();
            A := AutomorphismGroupConjugationSearch_(G, S, K, T);
            IndentPop();
        end if;
    end if;

    IndentPop(); /* end of automorphism group soluble group */
    return A;
end intrinsic;


/*  Equivalent to AutomorphismGroupSolubleGroup but with p parameter
    required.  For backwards compatability with previous testing code
*/

intrinsic AutomorphismGroupSolubleGroup ( G :: GrpPC , p :: RngIntElt ) -> GrpAuto
{Computes the automorphism group of the soluble group G using the automorphism group of
a Sylow p-subgroup of G.  Setting p to 1 is equivalent to calling AutomorphismGroupSolubleGroup(G).}
    return AutomorphismGroupSolubleGroup(G : p := p);
end intrinsic;


/* Breakout function called from c implementation of automorphism group algorith
   when it starts to struggle */
intrinsic AutomorphismGroupBreakOut ( G :: GrpPC ) -> GrpAuto
{Breakout from c algorithm.}
    vprint AutomorphismGroupSolubleGroup : "Breakout";
    //return AutomorphismGroup(G, [ g : g in PCGenerators(G) ], []);
    return AutomorphismGroupSolubleGroup (G);
end intrinsic;


/* Extension of AutomorphismGroup(Grp, SeqEnum, SeqEnum[SeqEnum]) */
intrinsic AutomorphismGroup2 ( G :: GrpPC, gens :: SeqEnum[GrpPCElt], imgs :: SeqEnum[SeqEnum[GrpPCElt]] ) -> GrpAuto
{Constructs automorphism group of G based on the mappings defined in imgs using generators gens.  Ensures that automorphism
maps are defined by the actual PC generators of G rather than gens.}

    /* Construct automorphism group as normal using 'custom' generating set*/
    A := AutomorphismGroup(G, gens, imgs);

    /* Take generators of G and construct new automorphism group using A */
    genG := [ G.i : i in [1..NPCgens(G)] ];
    return AutomorphismGroup(G, genG, [ genG @ A.i : i in [1..Ngens(A)] ]);

end intrinsic;

intrinsic AutomorphismGroup2 ( G :: Grp, gens :: SeqEnum[GrpElt], imgs :: SeqEnum[SeqEnum[GrpElt]] ) -> GrpAuto
{Constructs automorphism group of G based on the mappings defined in imgs using generators gens.  Ensures that automorphism
maps are defined by the actual PC generators of G rather than gens.}

    /* Construct automorphism group as normal using 'custom' generating set*/
    A := AutomorphismGroup(G, gens, imgs);

    /* Take generators of G and construct new automorphism group using A */
    genG := [ G.i : i in [1..NDgens(G)] ];
    return AutomorphismGroup(G, genG, [ genG @ A.i : i in [1..Ngens(A)] ]);

end intrinsic;
