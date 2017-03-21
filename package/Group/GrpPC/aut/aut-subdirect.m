freeze;

declare verbose ForcePermutationMethodSubdirectProduct, 1;

import "fix-subgroup.m" : FixSubgroup;

/*  INTERNAL
    Computes the automorphism group of a subdirect product given the group G
    and both the quotient groups with relevant maps, and their automorphism groups
*/
AutomorphismGroupOfSubdirectProduct_ := function(G, Q1, m1, Q2, m2, AQ1, AQ2)
    D, i, p := DirectProduct(Q1, Q2);

    genD := [ D | D.i : i in [ 1..NPCgens(D) ] ];

    imgsD := [ [ D | (d @ p[1] @ a @ i[1]) * (d @ p[2] @ i[2]) : d in genD ] : a in Generators(AQ1) ] cat
        [ [ D | (d @ p[1] @ i[1]) * (d @ p[2] @ a @ i[2]) : d in genD ] : a in Generators(AQ2) ];

    AD := AutomorphismGroup(D, genD, imgsD);

    /*
        Create a mapping h: G -> D.
    */
    genG := [ G | G.i : i in [ 1.. NPCgens(G) ] ];
    h := hom< G -> D | [ D | (g @ m1 @ i[1]) * (g @ m2 @ i[2]) : g in genG ] >;

    vprint AutomorphismGroupSolubleGroup : "Computing FixSubgroup(AD, Image(h))...";
    vtime AutomorphismGroupSolubleGroup : ADG := FixSubgroup(AD, Image(h));

    return AutomorphismGroup(G, genG, [ [ G | g @ h @ a @@ h : g in genG ] : a in Generators(ADG) ]);
end function;


/*  Efficiently computes the automorphism group of a subdirect product by constructing each side of the
    direct product and comparing the action of each generator on G/KT (as they must be consistent).

    NB: only computes the permutatation representation of the automorphism group if necessary.
*/
AutomorphismGroupOfSubdirectProduct__ := function(G, K, T, Q_GK, m_GK, Q_GT, m_GT, AQ_GK, AQ_GT)

    /* Remove any PC presentation stuff that will cause problems later on */
    if IsVerbose("ForcePermutationMethodSubdirectProduct") then
        attr := ["MapToRepElt", "RepMap", "RepGroup"];
        for a in attr do
            if assigned AQ_GT``a then
                delete AQ_GT``a;
            end if;
            if assigned AQ_GK``a then
                delete AQ_GK``a;
            end if;
        end for;
    end if;

    Q_GTK, m_GTK := quo < Q_GT | K @ m_GT >;
    Q_GTKgens := [ Q_GTK.i : i in [1..NDgens(Q_GTK)] ];

    /* Fix for AQ_GT and AQ_GK coming from aut-pc.m */
    if not IsVerbose("ForcePermutationMethodSubdirectProduct") and IsSoluble(AQ_GT) then
        /* note: can't use NDgens here as automorphism group dot notation won't work with PCGenerators */
        AQ_GTgens := [ a : a in PCGenerators(AQ_GT) ];
    else
        AQ_GTgens := [ AQ_GT.i : i in [1..Ngens(AQ_GT)] ];
    end if;

    if not IsVerbose("ForcePermutationMethodSubdirectProduct") and IsSoluble(AQ_GK) then
        AQ_GKgens := [ a : a in PCGenerators(AQ_GK) ];
    else
        AQ_GKgens := [ AQ_GK.i : i in [1..Ngens(AQ_GK)] ];
    end if;

    /* construct images for the automorphisms of Q_GTK using the action of automorphisms of
       AQ_GK and AQ_GT on the preimages of generators of Q_GTK */
    imgs := [ Q_GTKgens @@ m_GTK @ a @ m_GTK : a in AQ_GTgens ] cat
        [ Q_GTKgens @@ m_GTK @@ m_GT @ m_GK @ a @@ m_GK @ m_GT @ m_GTK : a in AQ_GKgens ];

    AQ_GTK := AutomorphismGroup(Q_GTK, Q_GTKgens, imgs);

    if not IsSoluble(AQ_GT) and not IsSoluble(AQ_GK) or IsVerbose("ForcePermutationMethodSubdirectProduct") then
        assert Ngens(AQ_GTK) eq (Ngens(AQ_GT) + Ngens(AQ_GK));
    end if;

    /* TODO: this could be a PC rep if possible */
    vprint AutomorphismGroupSolubleGroup : "Created permutation representation for AQ_GTK";
    vtime AutomorphismGroupSolubleGroup : phi_AQ_GTK, R_AQ_GTK := PermutationRepresentation(AQ_GTK);

    vprint AutomorphismGroupSolubleGroup, 3 : "*** R_AQ_GTK is soluble : ", IsSoluble(R_AQ_GTK);

    vprint AutomorphismGroupSolubleGroup : "Creating maps...";

    if not IsVerbose("ForcePermutationMethodSubdirectProduct") and IsSoluble(AQ_GT) then
        phi_AQ_GT := AQ_GT`PCGroup[2];
        R_AQ_GT := AQ_GT`PCGroup[1];
    else
        vprint AutomorphismGroupSolubleGroup : "Creating permutation representation for AQ_GT";
        vtime AutomorphismGroupSolubleGroup : phi_AQ_GT, R_AQ_GT := PermutationRepresentation(AQ_GT);
    end if;

    if not IsVerbose("ForcePermutationMethodSubdirectProduct") and IsSoluble(AQ_GK) then
        phi_AQ_GK := AQ_GK`PCGroup[2];
        R_AQ_GK := AQ_GK`PCGroup[1];
    else
        vprint AutomorphismGroupSolubleGroup : "Creating permutation representation for AQ_GK";
        vtime AutomorphismGroupSolubleGroup : phi_AQ_GK, R_AQ_GK := PermutationRepresentation(AQ_GK);
    end if;

    R_AQ_GTtoR_AQ_GTK := hom < R_AQ_GT -> R_AQ_GTK | [ R_AQ_GTK.i : i in [1..NDgens(R_AQ_GT)] ] >;
    // assert IsHomomorphism(R_AQ_GTtoR_AQ_GTK);

    /* NB this is Ngens(AQ_GT) becuase R_AQ_GT could be a PC group */
    R_AQ_GKtoR_AQ_GTK := hom < R_AQ_GK -> R_AQ_GTK | [ R_AQ_GTK.(i + #AQ_GTgens) : i in [1..NDgens(R_AQ_GK)] ] >;
    // assert IsHomomorphism(R_AQ_GKtoR_AQ_GTK);

    vprint AutomorphismGroupSolubleGroup : "Computing intersection of images of maps";
    vtime AutomorphismGroupSolubleGroup : R_AQ_GTK_matching_pairs := Image(R_AQ_GTtoR_AQ_GTK) meet Image(R_AQ_GKtoR_AQ_GTK);

    vprint AutomorphismGroupSolubleGroup, 3 : "SOLUBLE TESTS";
    IndentPush();
    vprint AutomorphismGroupSolubleGroup, 3 : "Intersection: ", IsSoluble(R_AQ_GTK_matching_pairs);
    vprint AutomorphismGroupSolubleGroup, 3 : "Kernel(R_AQ_GTtoR_AQ_GTK): ", IsSoluble(Kernel(R_AQ_GTtoR_AQ_GTK));
    vprint AutomorphismGroupSolubleGroup, 3 : "Kernel(R_AQ_GKtoR_AQ_GTK): ", IsSoluble(Kernel(R_AQ_GKtoR_AQ_GTK));
    IndentPop();

    vprint AutomorphismGroupSolubleGroup : "Creating Inner Automorphism Subgroup";
    vtime AutomorphismGroupSolubleGroup : R_AQ_GTKInn := sub < R_AQ_GTK | [ AQ_GTK!hom < Q_GTK -> Q_GTK | [ Q_GTK.i ^ Q_GTK.j : i in [1..NDgens(Q_GTK)] ] > : j in [1..NDgens(Q_GTK)]] @ phi_AQ_GTK >;

    vprint AutomorphismGroupSolubleGroup : "Computing R_Coset removing the inner automorphisms from R_AQ_GTK_matching_pairs";
    vtime AutomorphismGroupSolubleGroup : R_Coset := R_AQ_GTKInn meet R_AQ_GTK_matching_pairs;

    vprint AutomorphismGroupSolubleGroup : "Calculating the double coset representatives...";
    vtime AutomorphismGroupSolubleGroup : D_R_AQ_GTK_matching_pairs := DoubleCosetRepresentatives(R_AQ_GTK_matching_pairs, R_Coset, R_Coset);

    vprint AutomorphismGroupSolubleGroup : "Number of double coset representatives:", #D_R_AQ_GTK_matching_pairs;

    D, i, p := DirectProduct(Q_GT, Q_GK);
    genD := [ D | D.i : i in [ 1..NDgens(D) ] ];

    /* Create a mapping h: G -> D */
    genG := [ G | G.i : i in [ 1..NDgens(G) ] ];
    h := hom < G -> D | [ D | (g @ m_GT @ i[1]) * (g @ m_GK @ i[2]) : g in genG ] >;

    /* begin constructing pairs of mappings */
    pairs := {@ @};
    R_pairs := {@ @};

    /* If R_AQ_GT is GrpPC then we have AQ_GT`MapToRepElt defined and use this for putting maps into rep elts */
    if Type(R_AQ_GT) eq GrpPerm then
        AQ_GT_map_to_rep_elt := function (m)
            return (AQ_GT!m) @ phi_AQ_GT;
        end function;
        AQ_GT`MapToRepElt := AQ_GT_map_to_rep_elt;
    end if;

    if Type(R_AQ_GK) eq GrpPerm then
        AQ_GK_map_to_rep_elt := function (m)
            return (AQ_GK!m) @ phi_AQ_GK;
        end function;
        AQ_GK`MapToRepElt := AQ_GK_map_to_rep_elt;
    end if;

    /* Now add in inner automorphisms of G, use smaller generating set to minimise the number of auts */
    /* Construct a new generating set if the number of generators is quite big */
    // vprint AutomorphismGroupSolubleGroup : "Attempting to construct smaller generating seq for G to minimise InnG...";
    // innGenG := ConstructNewGeneratingSet(G);
    // vprintf AutomorphismGroupSolubleGroup : "#genG = %o, new #genG = %o\n", #genG, #innGenG;
    innGenG := genG;

    vprint AutomorphismGroupSolubleGroup : "Constructing image of Inn(G) in subdirect product...";
    vtime AutomorphismGroupSolubleGroup : for g in innGenG do
        g_GT := g @ m_GT;
        h_GT := hom < Q_GT -> Q_GT | [ Q_GT.i ^ g_GT : i in [1..NDgens(Q_GT)] ] >;

        g_GK := g @ m_GK;
        h_GK := hom < Q_GK -> Q_GK | [ Q_GK.i ^ g_GK : i in [1..NDgens(Q_GK)] ] >;

        r_GT := h_GT @ AQ_GT`MapToRepElt;
        r_GK := h_GK @ AQ_GK`MapToRepElt;

        Include(~pairs, < r_GT @@ phi_AQ_GT, r_GK @@ phi_AQ_GK >);
        Include(~R_pairs, < r_GT, r_GK >);
    end for;

    vprint AutomorphismGroupSolubleGroup : "Inner automorphism pairs:", #pairs;

    vprint AutomorphismGroupSolubleGroup : "Constructing identity + kernel pairs...";
    vtime AutomorphismGroupSolubleGroup : ker_R_AQ_GTtoR_AQ_GTK := Kernel(R_AQ_GTtoR_AQ_GTK);
    for i in [1..NDgens(ker_R_AQ_GTtoR_AQ_GTK)] do
        Include(~pairs, < ker_R_AQ_GTtoR_AQ_GTK.i @@ phi_AQ_GT, Id(AQ_GK) >);
        Include(~R_pairs, < ker_R_AQ_GTtoR_AQ_GTK.i, Id(R_AQ_GK) >);
    end for;

    vtime AutomorphismGroupSolubleGroup : ker_R_AQ_GKtoR_AQ_GTK := Kernel(R_AQ_GKtoR_AQ_GTK);
    for i in [1..NDgens(ker_R_AQ_GKtoR_AQ_GTK)] do
        Include(~pairs, < Id(AQ_GT), ker_R_AQ_GKtoR_AQ_GTK.i @@ phi_AQ_GK >);
        Include(~R_pairs, < Id(R_AQ_GT), ker_R_AQ_GKtoR_AQ_GTK.i >);
    end for;

    vprint AutomorphismGroupSolubleGroup : "Number of pairs from kernel+inn:", #pairs;

    /* note that D_R_AQ_GTK_matching_pairs[1] = Id(Q_GTK) */
    j := 2;
    while j le #D_R_AQ_GTK_matching_pairs do
        d := D_R_AQ_GTK_matching_pairs[j];
        pair := < d @@ R_AQ_GTtoR_AQ_GTK, d @@ R_AQ_GKtoR_AQ_GTK >;
        Include(~R_pairs, pair);
        Include(~pairs, < pair[1] @@ phi_AQ_GT, pair[2] @@ phi_AQ_GK >);
        j +:= 1;
    end while;

    /* constructed all the pairs, so see if one of the (soon to be) factors in the direct product
       is GrpPerm but soluble, because if both are soluble, then we have Aut(G) sol */

    /* note that phi_R_AQ_GT_pairs : R_AQ_GT_pairs -> R_AQ_GT */
    R_AQ_GT_pairs, phi_R_AQ_GT_pairs := sub < R_AQ_GT | [ pair[1] : pair in R_pairs ] >;
    AQ_GT_pairs_MapToRepElt := AQ_GT`MapToRepElt;
    AQ_GT_pairs_RepMap := phi_AQ_GT;

    /* note that phi_R_AQ_GK_pairs : R_AQ_GK_pairs -> R_AQ_GK */
    R_AQ_GK_pairs, phi_R_AQ_GK_pairs := sub < R_AQ_GK | [ pair[2] : pair in R_pairs ] >;
    AQ_GK_pairs_MapToRepElt := AQ_GK`MapToRepElt;
    AQ_GK_pairs_RepMap := phi_AQ_GK;

    /* if both are soluble, then we can construct a PC rep */
    if IsSoluble(R_AQ_GT_pairs) and IsSoluble(R_AQ_GK_pairs) then

        /* if either is a GrpPerm then we can convert them */
        if Type(R_AQ_GT_pairs) eq GrpPerm then
            vprint AutomorphismGroupSolubleGroup : "R_AQ_GT_pairs is a soluble GrpPerm! Converting...";

            vprint AutomorphismGroupSolubleGroup : "Construcing PCGroup of R_AQ_GT_pairs";
            R_AQ_GT_pairs_, phi_R_AQ_GT_pairs_ := PCGroup(R_AQ_GT_pairs);

            AQ_GT_pairs_MapToRepElt := function (m)
                return (m @ AQ_GT`MapToRepElt) @ phi_R_AQ_GT_pairs_;
            end function;

            /* convert the RepMap */
            AQ_GT_pairs_RepMap *:= phi_R_AQ_GT_pairs_;

            /* finally swap over the group to be the PC one */
            R_AQ_GT_pairs := R_AQ_GT_pairs_;

            /* modify the subgroup mapping too so that pair elements can be put into the PC group */
            phi_R_AQ_GT_pairs := phi_R_AQ_GT_pairs_^-1 * phi_R_AQ_GT_pairs;
        end if;

        if Type(R_AQ_GK_pairs) eq GrpPerm then
            vprint AutomorphismGroupSolubleGroup : "R_AQ_GK_pairs is a soluble GrpPerm! Converting...";

            vprint AutomorphismGroupSolubleGroup : "Construcing PCGroup of R_AQ_GK_pairs";
            R_AQ_GK_pairs_, phi_R_AQ_GK_pairs_ := PCGroup(R_AQ_GK_pairs);

            AQ_GK_pairs_MapToRepElt := function (m)
                return (m @ AQ_GK`MapToRepElt) @ phi_R_AQ_GK_pairs_;
            end function;

            /* convert the RepMap */
            AQ_GK_pairs_RepMap *:= phi_R_AQ_GK_pairs_;

            /* finally swap over the group to be the PC one */
            R_AQ_GK_pairs := R_AQ_GK_pairs_;

            /* modify the subgroup mapping too so that pair elements can be put into the PC group */
            phi_R_AQ_GK_pairs := phi_R_AQ_GK_pairs_^-1 * phi_R_AQ_GK_pairs;
        end if;

        /* direct product of the pairs rep groups */
        PC_D, PC_i, PC_p := DirectProduct(R_AQ_GT_pairs, R_AQ_GK_pairs);

        /* This is the representation of as a PC group */
        vprint AutomorphismGroupSolubleGroup : "Constructing pairs rep inside PC group of direct product";
        vtime AutomorphismGroupSolubleGroup : PC_D_pairs := sub < PC_D | [ ((r[1] @@ phi_R_AQ_GT_pairs) @ PC_i[1]) * ((r[2] @@ phi_R_AQ_GK_pairs) @ PC_i[2]) : r in R_pairs ] >;

        if GetAssertions() gt 1 then
            /* Extra check to ensure that AD fixes Image(h), and then AD induces A (created below) */

            /* Construct automorphism group with generators to match PC generators */
            vprint AutomorphismGroupSolubleGroup : "Constructing images for automorphisms";
            vtime AutomorphismGroupSolubleGroup : imgsD := [ [ D | (d @ p[1] @ (r_a @ PC_p[1] @@ AQ_GT_pairs_RepMap) @ i[1]) *
                (d @ p[2] @ (r_a @ PC_p[2] @@ AQ_GK_pairs_RepMap) @ i[2]) : d in genD ] : r_a in PCGenerators(PC_D_pairs) ];

            /* with the removal of the FixSubgroup, we can remove this AD stuff too */
            AD := AutomorphismGroup(D, genD, imgsD);

            /* check that AD fixes Image(h) */
            Image_h := Image(h);
            for i_ in [1..Ngens(AD)] do
                assert (Image_h @ AD.i_) eq Image_h;
            end for;

            A_from_AD := AutomorphismGroup2(G, genG, [ [ G | g @ h @ AD.i @@ h : g in genG ] : i in [1..Ngens(AD)] ]);
        end if;

        vprint AutomorphismGroupSolubleGroup : "Constructing images for automorphisms";
        vtime AutomorphismGroupSolubleGroup : imgG := [ [ G | ((g @ m_GT @ (r_a @ PC_p[1] @@ AQ_GT_pairs_RepMap) @ i[1])
         * (g @ m_GK @ (r_a @ PC_p[2] @@ AQ_GK_pairs_RepMap) @ i[2])) @@ h : g in genG ] : r_a in PCGenerators(PC_D_pairs) ];

        A := AutomorphismGroup2(G, genG, imgG);
        /* compare with A constructed via AD */
        assert2 #[ i : i in [1..Ngens(A)] | (genG @ A_from_AD.i) ne (genG @ A.i) ] eq 0;

        A`PCGenerators := {@ A.i : i in [1..Ngens(A)] @};
        A`Soluble := true;

        map_to_rep_elt := function (m)
            /* split map into action on G/K and G/T */
            m_T := hom < Q_GT -> Q_GT | [ Q_GT.j @@ m_GT @ m @ m_GT : j in [1..NDgens(Q_GT)] ] : Check := false>;
            m_K := hom < Q_GK -> Q_GK | [ Q_GK.j @@ m_GK @ m @ m_GK : j in [1..NDgens(Q_GK)] ] : Check := false>;
            r_T := (m_T @ AQ_GT_pairs_MapToRepElt);
            r_K := (m_K @ AQ_GK_pairs_MapToRepElt);
            return (r_T @ PC_i[1]) * (r_K @ PC_i[2]);
        end function;
        A`MapToRepElt := map_to_rep_elt;

        A`RepGroup := PC_D_pairs;
        /* TODO: This is too slow! */
        //rep_elt_to_aut_elt := hom < A`RepGroup -> A | [ A.i : i in [1..Ngens(A)] ] >;
        F, phi_F := FPGroup(A`RepGroup); F_to_A := hom < F -> A | [ A.i : i in [1..Ngens(A)] ] >;
        A`RepMap := hom < A -> A`RepGroup | x :-> A`MapToRepElt(x), y :-> (y @@ phi_F) @ F_to_A >;

        A`PCGroup := < A`RepGroup, A`RepMap >;
        A`Order := #A`RepGroup;

        assert CheckPCRepresentation(A);
    else
        /* if the two groups are not soluble, then just do the best we can! */
        /* Automorphism group construction for non soluble case... */

        if GetAssertions() gt 1 then
            /* Check that AD fixes Image(h) */
            imgsD := [ [ D | (d @ p[1] @ a[1] @ i[1]) * (d @ p[2] @ a[2] @ i[2]) : d in genD ] : a in pairs ];
            AD := AutomorphismGroup(D, genD, imgsD);

            vprint AutomorphismGroupSolubleGroup : "Calculating subgroup fixing G...";

            /* check that AD fixes Image(h) */
            Image_h := Image(h);
            for i_ in [1..Ngens(AD)] do
                assert (Image_h @ AD.i_) eq Image_h;
            end for;
        end if;

        A := AutomorphismGroup2(G, genG, [ [ G | ((g @ m_GT @ a[1] @ i[1]) * (g @ m_GK @ a[2]) @ i[2]) @@ h : g in genG ] : a in pairs ]);
        A`Soluble := false;

        if Type(R_AQ_GT_pairs) eq Type(R_AQ_GK_pairs) and Type(R_AQ_GK_pairs) eq GrpPerm then
            R_D, R_i, R_p := DirectProduct(R_AQ_GT_pairs, R_AQ_GK_pairs);
            vprint AutomorphismGroupSolubleGroup : "Constructing pairs rep inside rep group of direct product";
            vtime AutomorphismGroupSolubleGroup : R_D_pairs := sub < R_D | [ ((r[1] @@ phi_R_AQ_GT_pairs) @ R_i[1]) * ((r[2] @@ phi_R_AQ_GK_pairs) @ R_i[2]) : r in R_pairs ] >;

            vprintf AutomorphismGroupSolubleGroup : "Generators of R_D_pairs: %o\nGenerators of A: %o", Ngens(R_D_pairs), Ngens(A);
            A`Order := #R_D_pairs;
            A`RepGroup := R_D_pairs;

            /* construct A with generators corresponding to those of R_D_pairs */
            /* Not useful unless we can find a product of generators of GrpPerm for an arbitrary element */
            /*((g @ m_GT @ (r_a @ PC_p[1] @@ AQ_GT_pairs_RepMap) @ i[1])
                     * (g @ m_GK @ (r_a @ PC_p[2] @@ AQ_GK_pairs_RepMap) @ i[2])) @@ h : g in genG ] : r_a in PCGenerators(PC_D_pairs)*/
            // A := AutomorphismGroup2(G, genG, [ [ G | (g @ m_GT @ a[1] @ i[1]) * (g @ m_GK @ a[2] @ i[2]) @@ h : g in genG ] : a in pairs ]);

            /* ================================================================================== */
            /* removed this due to problems with it being used as the official rep in later calculations */
            // A`RepGroup := R_D_pairs;
            // map_to_rep_elt := function (m)
            //     // m_GT_ := m_GT * m * m_GT^-1;
            //     // error if m_GT_ notin AQ_GT,  "Map cannot be coerced into automorphism group";
            //     rep_GT := (AQ_GT!(m_GT * m * m_GT^-1)) @ phi_AQ_GT;
            //     rep_GK := (AQ_GK!(m_GK * m * m_GK^-1)) @ phi_AQ_GK;
            //     r_d_rep := (rep_GT @ R_i[1]) * (rep_GK @ R_i[2]);
            //     assert2 r_d_rep in R_D_pairs;
            //     return R_D_pairs!r_d_rep;
            // end function;
            // W, phi_W := WordGroup(R_D_pairs);
            // rep_elt_to_auto := function (r)
            //     return Evaluate(r @@ phi_W, A);
            // end function;
            //
            // A`MapToRepElt := map_to_rep_elt;
            // A`RepMap := hom < A -> R_D_pairs | x :-> map_to_rep_elt(x), y :-> rep_elt_to_auto(y) >;
            // CheckPCRepresentation(A);
            /* ================================================================================== */
        end if;
    end if;

    return A;

end function;



/*  Computes the automorphism group of a group G with subdirect product defined
    as the direct product of the quotients G / F1 and G / F2.
*/
AutomorphismGroupOfSubdirectProduct := function(G, F1, F2)
    Q1, m1 := quo< G | F1 >;
    Q2, m2 := quo< G | F2 >;

    vprint AutomorphismGroupSolubleGroup : "Computing Aut(Q1)...";
    vtime AutomorphismGroupSolubleGroup : AQ1 := AutomorphismGroup(Q1);
    // Not necessary - but may speed things up later...
    //AQ1K := FixSubgroup(AQ1, F2 @ m1);

    vprint AutomorphismGroupSolubleGroup : "Computing Aut(Q2)...";
    vtime AutomorphismGroupSolubleGroup : AQ2 := AutomorphismGroup(Q2);
    // Not necessary - but may speed things up later...
    //AQ2T := FixSubgroup(AQ2, F1 @ m2);

    return AutomorphismGroupOfSubdirectProduct_(G, Q1, m1, Q2, m2, AQ1, AQ2);
end function;