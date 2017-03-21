freeze;

/* verbose flag, only used up to 1 currently */
declare verbose PCGroupAutomorphismGroupPGroup, 3;


/* Construct the PC Group of the matrix group created by the action of A on the
   frattini quotient.
*/
ConstructPCGroupOfNonPMatrixGroup := procedure ( ~nonp_action )

    MPC, MPC_phi := PCGroup(nonp_action`matrix_group);
    W, phi_W := WordGroup(nonp_action`matrix_group);
    nonp_action`pc_auto_gens := #nonp_action`auto_gens gt 0 select
        Evaluate([ (m @@ MPC_phi) @@ phi_W : m in PCGenerators(MPC) ], nonp_action`auto_gens)
        else [];
    nonp_action`pc_group := < MPC, MPC_phi >;

    /* ridiculous rewriting needed to preserve pc-generator ordering in words */
    FMPC, FMPC_phi := FPGroup(MPC);
    WFMPC := SLPGroup(Ngens(FMPC));
    FMPC_to_WFMPC := hom < FMPC -> WFMPC | [ WFMPC.i : i in [1..Ngens(FMPC)] ] >;
    _matrix_to_relation := function (matrix)
        /* matrix -> matrix gens -> into PC grp (for elt form) -> rewrite to FP elt -> SLP */
        return < 0, ((matrix @ MPC_phi) @@ FMPC_phi) @ FMPC_to_WFMPC >;
    end function;
    nonp_action`matrix_to_relation := _matrix_to_relation;

end procedure;


/* Converts the action of an automorphism 'a' on a sequence of generators 'gens'
   into a vector.  In resulting images, ignores generators whose indicies are not
   in 'block'.
*/
AutomorphismToVector := function (a, gens, block)

    img_gens := gens @ a;
    zero_block := [ 0 : i in [ 1..#block ] ];
    v := [];

    for i in [1..#gens] do
        if img_gens[i] eq gens[i] then
            v cat:= zero_block;
        else
            img_elt_seq := Eltseq(img_gens[i]);
            v cat:= [ img_elt_seq[i] : i in block ];
        end if;
    end for;

    return v;

end function;


/* Returns a list which gives the indices of generators as determined by the
   pRank function.
*/
pRankGenerators := function (P)
    ranks := [0] cat pRanks(P);
    return [ [ j : j in [ ranks[i]+1 .. ranks[i+1] ] ] : i in [1..#ranks-1] ];
end function;


/* list in which the ith element is the layer index of the ith generator */
GroupGenLayers := function (rank_gens)
    result := [ ];
    for i in [1..#rank_gens] do
        for j in rank_gens[i] do
            result[j] := i;
        end for;
    end for;

    return result;
end function;


/*
    LayerByActionOnFrattiniQuotient

    returns the layer index
*/
LayerByActionOnFrattiniQuotient := function (frattini_quotient_gens_img, gens_to_rank_gens)
    lowest_img_index := #gens_to_rank_gens;
    found := false;
    count := 0;
    for img in frattini_quotient_gens_img do
        es_img := Eltseq(img);
        // check if products contain elements after the frattini quotient,
        // note that the number of elts in the frattini_quotient is the same
        // as #frattini_quotient_gens_img

        // optimisation: changed maxium value of loop to be lowest_img_index
        //               instead of #gens_to_rank_gens
        for j in [#frattini_quotient_gens_img+1..lowest_img_index] do
            count +:= 1;
            if es_img[j] gt 0 then
                // if it is non zero, then we must be mapping into the layer
                // which has the group generator P.j in it.
                lowest_img_index := j;//Minimum(j, lowest_img_index);
                found := true;
                break;
            end if;
        end for;
        if lowest_img_index eq #frattini_quotient_gens_img+1 then
            break;
        end if;
    end for;

    // if not found, then it must be from the bottom layer
    if found then
        return gens_to_rank_gens[lowest_img_index];
    else
        return 1;
    end if;

end function;


LayerByActionOnFrattiniQuotient2 := function (frattini_quotient_gens_img, gens_to_rank_gens, rank_gens)
    layer := #rank_gens+1;
    found := false;
    j_start := #frattini_quotient_gens_img+1;

    for img in frattini_quotient_gens_img do
        //lowest_img_index := Minimum(Depth(img), lowest_img_index);

        es_img := Eltseq(img);
        // check if products contain elements after the frattini quotient,
        // note that the number of elts in the frattini_quotient is the same
        // as #frattini_quotient_gens_img

        // optimisation: changed maxium value of loop to be lowest_img_index
        //               instead of #gens_to_rank_gens

        for j in [j_start..rank_gens[layer-1][#rank_gens[layer-1]]] do
            if es_img[j] gt 0 then
                // if it is non zero, then we must be mapping into the layer
                // which has the group generator P.j in it.
                layer := gens_to_rank_gens[j];//Minimum(j, lowest_img_index);
                found := true;
                break;
            end if;
        end for;
        if layer eq 1 then
            break;
        end if;
    end for;

    // if not found, then it must be from the bottom layer
    if found then
        return layer;
    else
        return 1;
    end if;

end function;


LayerByActionOnFrattiniQuotient3 := function (P, frattini_quotient_gens, frattini_quotient_gens_img, gens_to_rank_gens)

    lowest_index_gen := #gens_to_rank_gens;

    for i in [1..#frattini_quotient_gens_img] do
        if frattini_quotient_gens_img[i] eq frattini_quotient_gens[i] then
            continue;
        end if;

        _img := frattini_quotient_gens_img[i];
        d := Depth(_img);

        while d gt 0 and d le #frattini_quotient_gens_img do
            _img := LeadingTerm(_img)^-1 * _img;
            d := Depth(_img);
        end while;

        if d ne 0 then
            lowest_index_gen := Minimum(lowest_index_gen, Depth(_img));
        end if;

    end for;

    return gens_to_rank_gens[lowest_index_gen];

end function;

/*
    Current the version that's used - maybe try to optimise this?
*/
LayerByActionOnFrattiniQuotient4 := function (frattini_quotient_gens, frattini_quotient_gens_img, gens_to_rank_gens, rank_gens : lowest_layer := 1)

    lowest_index_gen := #gens_to_rank_gens;
    layer := #rank_gens+1;

    for i in [1..#frattini_quotient_gens_img] do
        l := LeadingTerm(frattini_quotient_gens_img[i]);
        if l ne frattini_quotient_gens[i] then
            return 1;
        elif LeadingGenerator(l^-1 * frattini_quotient_gens_img[i]) in frattini_quotient_gens then
            return 1;
        end if;
    end for;

    for i in [1..#frattini_quotient_gens_img] do
        if frattini_quotient_gens_img[i] eq frattini_quotient_gens[i] then
            continue;
        end if;

        elt_seq := Eltseq(frattini_quotient_gens_img[i]);

        for j in [#frattini_quotient_gens+1..rank_gens[layer-1][#rank_gens[layer-1]]] do
            if elt_seq[j] gt 0 then
                layer := gens_to_rank_gens[j];
                break;
            end if;
        end for;

        if layer eq 2 then
            break;
        end if;
    end for;

    if layer eq #rank_gens+1 then
        // Check for the identity...
        // if frattini_quotient_gens eq frattini_quotient_gens_img then
            // return 0;
        // else
            return 1;
        // end if;
    else
        return layer;
    end if;

end function;

// LayerByActionOnFrattiniQuotient5 := function (frattini_quotient_gens, frattini_quotient_gens_imgs, gens_to_rank_gens)
//
//     /*
//         Check that it doesn't permute the frattini quotient...
//     */
//     n := #frattini_quotient_gens;
//
//     for i in [1..n] do
//         if frattini_quotient_gens[i] eq frattini_quotient_gens_imgs[i] then
//             continue;
//         end if;
//
//         p := Partition(Eltseq(frattini_quotient_gens_imgs[i]), [n, #frattini_quotient_gens_imgs[i] - n]);
//         /*
//             this is not acting as id on frattini_quotient_gens
//         */
//         if p[1] ne [ j eq i select 1 else 0 : j in [1..n] ] then
//             return 1;
//         else
//
//
//     end for;
//
// end function;


/* Returns the lowest rank which the frattini quotient gens (frattini_quotient_gens) are
   mapped into by the automorphism 'a' using the gens_to_rank_gens
*/
AutomorphismLayer := function (process_data, a)
    return LayerByActionOnFrattiniQuotient4(process_data`frattini_quotient_gens, process_data`frattini_quotient_gens @ a, process_data`gens_to_rank_gens, process_data`rank_gens);
end function;


AutomorphismGroupGeneratorsByLayer := procedure (~process_data)

    categories := [ [] : i in [1..#process_data`rank_gens] ];
    for i in [1..#process_data`Agens] do
        j := AutomorphismLayer(process_data, process_data`Agens[i]);
        Append(~categories[j], i);
    end for;
    process_data`layers_Agens := categories;

end procedure;


/* Takes a LayerRF record 'layer' and constructs attributes layer`S and layer`change_of_basis
   using layer`V and layer`basis.
*/
BuildLayerSubspace := procedure (~layer)

    vprint PCGroupAutomorphismGroupPGroup : "Building layer subspace";
    layer`S := sub < layer`V | layer`basis >;

    if #layer`basis gt 0 then
        layer`change_of_basis := Matrix([ layer`S!(layer`V!layer`basis[i]) : i in [1..#layer`basis] ])^-1;
        if #layer`basis gt Ngens(layer`W) then
            layer`W := SLPGroup(#layer`basis);
        end if;
    else
        if assigned layer`change_of_basis then
            delete layer`change_of_basis;
        end if;
    end if;

end procedure;


/* Deletes the variable process_data`current_relation and resets current_relation_auto */
ClearCurrentRelation := procedure (~process_data)
    process_data`current_relation := [* *];
    process_data`current_relation_auto := process_data`identity;
end procedure;


forward AutomorphismFromRelation;

/* Appends t_relation to process`current_relation.  If attribute process_data`current_relation
   is not assigned, it initialises the sequence beforehand.
*/
AppendToCurrentRelation := procedure (~process_data, t_relation)

    if not assigned process_data`current_relation then
        ClearCurrentRelation(~process_data);
    else
        if GetAssertions() gt 1 and #process_data`current_relation gt 0 then
            if process_data`current_relation[#process_data`current_relation] cmpeq t_relation then
                error "Loop starting!";
            end if;
        end if;
    end if;

    Append(~process_data`current_relation, t_relation);
    process_data`current_relation_auto *:= AutomorphismFromRelation(process_data, [ t_relation ]);

end procedure;


/* Find the relation in the given layer for the automorphism a and append it to the current relation
   (process_data`current_relation).
*/
AppendRelationToCurrentRelationForAutomorphismInLayer := procedure(~process_data, a, layer_index : under_construction := true)

    if layer_index eq 1 then
        imgs := process_data`frattini_quotient_gens @ a;
        if imgs ne process_data`frattini_quotient_gens then
            /* fix this before this point: dont allow stuff with 1 gen to get through */
            if #Eltseq(imgs[1]) eq 1 then
                mat := process_data`nonp_action`matrix_group![ Eltseq(img) : img in imgs ];
            else
                mat := process_data`nonp_action`matrix_group![ Partition(Eltseq(img), [#imgs, NPCgens(Parent(img)) - #imgs])[1] : img in imgs ];
            end if;
            AppendToCurrentRelation(~process_data, process_data`nonp_action`matrix_to_relation(mat));
        end if;
    else
        v := AutomorphismToVector(a, process_data`frattini_quotient_gens, process_data`layers[layer_index]`group_gens);

        if not (process_data`layers[layer_index]`V!v) in process_data`layers[layer_index]`S then
            /* check that we are constructing the group, not coercing an arbitrary map into it */
            if under_construction then
                vprintf PCGroupAutomorphismGroupPGroup : "About to add generator after: (layer=%o, index=%o)\n", layer_index, #process_data`layers[layer_index]`pauto_gens;

                /* Need to add this automorphism to the layer and rebuild spaces */
                Append(~process_data`layers[layer_index]`pauto_gens, a);
                Include(~process_data`layers[layer_index]`basis, v);

                BuildLayerSubspace(~process_data`layers[layer_index]);

                error if not process_data`layers[layer_index]`V!v in process_data`layers[layer_index]`S, "Not in space - still!";

                IndentPush();
                vprintf PCGroupAutomorphismGroupPGroup : "Added generator: (layer=%o, index=%o)\n", layer_index, #process_data`layers[layer_index]`pauto_gens;
                IndentPop();

                /* Now it should be in the vector space... */
            else
                error "Could not find image for map.";
            end if;
        end if;

        relation_v := (process_data`layers[layer_index]`S!(process_data`layers[layer_index]`V!v)) * process_data`layers[layer_index]`change_of_basis;
        W := process_data`layers[layer_index]`W;
        AppendToCurrentRelation(~process_data, < layer_index,
            &*[ W.i ^ (Integers()!relation_v[i]) : i in Sort(SetToSequence(Support(relation_v))) ] >);
    end if;

end procedure;


/* Find the relation for the automorphism a and append it to the current relation
   (process_data`current_relation).
*/
AppendRelationToCurrentRelationForAutomorphism := procedure(~process_data, a : layer_index := 0, under_construction := true)
    /* Pretty sure that this can be pre-determined in most cases, so maybe check this. */
    if layer_index eq 0 then
        layer_index := AutomorphismLayer(process_data, a);
    end if;
    AppendRelationToCurrentRelationForAutomorphismInLayer(~process_data, a, layer_index : under_construction := under_construction);
end procedure;


/* Returns an automorphism defined by 'relation'. */
AutomorphismFromRelation := function ( process_data, relation )
    return &*[ r[1] eq 0 select Evaluate(r[2], process_data`nonp_action`pc_auto_gens) \
        else Evaluate(r[2], process_data`layers[r[1]]`pauto_gens) : r in relation ];
end function;


/* Returns the automorphism represeing the current relation (cached) */
AutomorphismFromCurrentRelation := function ( process_data )
    return process_data`current_relation_auto;
end function;


/* Returns an expression created by the gens array representing 'relation'.
    - relation: array of relations.
    - gens: array of generators, for each layer.  Note that the first element
        contains generators for the nonp_action level, and so all indices in gens
        are required to be +:= 1.
*/
ExpressionFromRelation := function (process_data, relation, gens)
    return &*[ r[1] eq 0 select Evaluate(r[2], gens[r[1]+1])
        else Evaluate(r[2], gens[r[1]+1]) : r in relation ];
end function;


/*
    CreatePowerTRelationFromCurrentRelation
    - generator: index of generator in layers[layer_index]
    Returns a tuple < generator_index, layer_index, relation > to represent a power relation.
*/
CreatePowerTRelationFromCurrentRelation := function (process_data, generator, layer_index, power)
    return < generator, layer_index, power, process_data`current_relation >;
end function;

CreateIdentityPowerTRelation := function (generator, layer_index, power)
    return < generator, layer_index, power >;
end function;


/* Returns a tuple < lower_gen_index, lower_layer, higher_gen_index, higher_layer, relation> to
   represent a conjugation relation.
*/
CreateConjugationTRelationFromCurrentRelation := function (process_data, lower_generator, lower_layer, higher_generator, higher_layer)
    return < lower_generator, lower_layer, higher_generator, higher_layer, process_data`current_relation >;
end function;

CreateIdentityConjugationTRelation := function (lower_generator, lower_layer, higher_generator, higher_layer)
    return < lower_generator, lower_layer, higher_generator, higher_layer >;
end function;


/* Constructs a power relation from the relation
   - gens : array of arrays in which 1st element contains the nonp_action pc_auto_gens,
        and subsequent indices correspond to auto_gens from layers, i.e. gens[2] = layers[1]`auto_gens
   - t_relation: tuple relation created by CreatePowerTRelationFromCurrentRelation
*/
BuildPowerRelationFromTRelation := function (process_data, gens, t_relation)
    return ((gens[t_relation[2]+1][t_relation[1]])^(t_relation[3]) = ExpressionFromRelation(process_data, t_relation[4], gens));
end function;

BuildIdentityPowerRelationFromTRelation := function (process_data, gens, t_relation)
    return ((gens[t_relation[2]+1][t_relation[1]])^t_relation[3]) = 1;
end function;


/* Constructs a conjugation relation from t_relation.
   - gens : array of arrays in which 1st element contains the nonp_action pc_auto_gens,
        and subsequent indices correspond to auto_gens from layers, i.e. gens[2] = layers[1]`auto_gens
   - t_relation: tuple relation created by CreateConjugationTRelationFromCurrentRelation
*/
BuildConjugationRelationFromTRelation := function (process_data, gens, t_relation)
    result := ExpressionFromRelation(process_data, t_relation[5], gens);
    return ((gens[t_relation[4]+1][t_relation[3]])^(gens[t_relation[2]+1][t_relation[1]]) = result);
end function;

BuildIdentityConjugateRelationFromTRelation := function (gens, t_relation)
    return (gens[t_relation[4]+1][t_relation[3]])^(gens[t_relation[2]+1][t_relation[1]]) = 1;
end function;


/* Takes the automorphism a and checks if is equal to the automorphism represented
   in process_data`current_relation.  If not, it computes the difference, and appends
   this to the relation (by moving up through layers).
*/
BuildCurrentRelationFromAutomorphism := procedure(~process_data, a : clear_current_relation := true, under_construction := true)

    /* check that we want to clear the current relation before the calculation */
    if clear_current_relation then
        ClearCurrentRelation(~process_data);
    end if;

    while true do
        na := process_data`current_relation_auto;//AutomorphismFromCurrentRelation(process_data);
        if na eq a then
            break;
        end if;
        na := na^-1 * a;
        AppendRelationToCurrentRelationForAutomorphism(~process_data, na : under_construction := under_construction);
    end while;

end procedure;


/* Constructs the power relations in the given layer, beginnin with 'start_with_generator' (default is first) */
ConstructPowerRelationsInLayer := procedure(~process_data, test_index : start_with_generator := 1)

    /*
        Setup search_start_layer_index - if set to 0 then the layer index is
        determined between layers 1 and #layers.
    */
    /*search_start_layer_index := 0;
    if test_index eq #process_data`layers then
        search_start_layer_index := test_index;
    end if;*/

    ai := start_with_generator;

    while ai le #process_data`layers[test_index]`pauto_gens do
        vprintf PCGroupAutomorphismGroupPGroup : "Contructing power relation: (layer=%o, index=%o)\n", test_index, ai;
        a := (process_data`layers[test_index]`pauto_gens[ai])^(process_data`p);
        if a eq process_data`identity then
            Append(~process_data`p_relations_identity, CreateIdentityPowerTRelation(ai, test_index, process_data`p));
        else
            BuildCurrentRelationFromAutomorphism(~process_data, a : under_construction := true);
            Append(~process_data`p_relations, CreatePowerTRelationFromCurrentRelation(process_data, ai, test_index, process_data`p));
        end if;
        ai +:= 1;
    end while;

end procedure;


/* Constructs conjugation relations between layers lower_index and higher_index.  If
   start_with_higher_generator is set then the process begins by computing
   layers[higher_index][start_with_higher_generator] ^ layers[lower_index][j] for each j.
*/
ConstructConjugationRelationsBetweenLayers := procedure(~process_data, lower_index, higher_index : start_with_higher_generator := 1)

    /* if the indices are different, then could have one generator in each.
       if they are equal, then they must have more than 1 gen to produce commutator relations */

    if higher_index ne lower_index or #process_data`layers[higher_index]`pauto_gens gt 1 then
        vprintf PCGroupAutomorphismGroupPGroup : "Constructing conjugation relations (lower=%o, higher=%o, higher_index_start=%o)\n", lower_index, higher_index, start_with_higher_generator;
        aj := start_with_higher_generator;
        while aj le #process_data`layers[higher_index]`pauto_gens do
            ai := 1;
            if higher_index eq lower_index then
                bound := aj - 1;
            else
                bound := #process_data`layers[lower_index]`pauto_gens;
            end if;

            while ai le bound do
                a := (process_data`layers[higher_index]`pauto_gens[aj])^(process_data`layers[lower_index]`pauto_gens[ai]);
                if a eq process_data`identity then
                    Append(~process_data`c_relations_identity, CreateIdentityConjugationTRelation(ai, lower_index, aj, higher_index));
                else
                    /* check that we don't have a trivial relation */
                    if a ne (process_data`layers[higher_index]`pauto_gens[aj]) then
                        BuildCurrentRelationFromAutomorphism(~process_data, a : under_construction := true);
                        Append(~process_data`c_relations, CreateConjugationTRelationFromCurrentRelation(process_data, ai, lower_index, aj, higher_index));
                    end if;
                end if;
                ai +:= 1;
            end while;
            aj +:= 1;
        end while;
    end if;

end procedure;


/* Builds the relations for the non-p action (matrix group). Converts the PC
   group of the matrix group into a pc group for the full group, lifing automorphisms
   so that they are consistent on the full group.
*/
ConstructRelationsForNonPAction := procedure (~process_data)

    /* Construct an FP group from the matrix PC Group */
    MPCF, MPCF_phi := FPGroup(process_data`nonp_action`pc_group[1]);
    MPCF_relations := Relations(MPCF);

    /* Construct SLP group for evaluating relations */
    MPCFW := SLPGroup(Ngens(MPCF));
    MPCFW_phi := hom < MPCF -> MPCFW | [ MPCFW.i : i in [1..Ngens(MPCF)] ] >;

    vprint PCGroupAutomorphismGroupPGroup : "Constructing relations for non-p action.";
    IndentPush();
    vprint PCGroupAutomorphismGroupPGroup : "Converting power relations";
    IndentPush();

    /* Convert the power relations. */
    for i in [ 1..Ngens(MPCF) ] do
        vprint PCGroupAutomorphismGroupPGroup : MPCF_relations[i];
        power := #Eltseq(MPCF_relations[i][1]);

        // assume that the power relations come first - is this RISKY?
        lhs_a := Evaluate(MPCF_relations[i][1] @ MPCFW_phi, process_data`nonp_action`pc_auto_gens);

        if lhs_a eq process_data`identity then
            Append(~process_data`p_relations_identity, CreateIdentityPowerTRelation(i, 0, power));
        else
            /* this isn't called in BuildCurrentRelationFromAutomorphism because we need to force in the first
               chunk of the relation from */
            ClearCurrentRelation(~process_data);

            /* current relation need to be 0 and then rhs */
            AppendToCurrentRelation(~process_data, < 0, MPCF_relations[i][2] @ MPCFW_phi >);

            /* this is the power relation of generator i (and i = GeneratorNumber(r[1])) */
            BuildCurrentRelationFromAutomorphism(~process_data, lhs_a : clear_current_relation := false);
            Append(~process_data`p_relations, CreatePowerTRelationFromCurrentRelation(process_data, i, 0, power));
        end if;
    end for;

    IndentPop();
    vprint PCGroupAutomorphismGroupPGroup : "Converting conjugation relations";
    IndentPush();

    /* Convert the conjugation relations */
    for i in [ Ngens(MPCF)+1..#MPCF_relations ] do
        vprint PCGroupAutomorphismGroupPGroup : MPCF_relations[i];

        lhs_eltseq := Eltseq(MPCF_relations[i][1]); /* this should be of the form [ -ai, aj, ai ] i.e. $.aj^$.ai */
        ai := lhs_eltseq[3];
        aj := lhs_eltseq[2];

        /* check the form */
        assert2 ai eq lhs_eltseq[1] * -1;
        assert2 aj ne ai;

        ClearCurrentRelation(~process_data);

        // these should now be the conjugation relations
        if MPCF_relations[i][2] eq Id(MPCF) then
            Append(~process_data`c_relations_identity, CreateIdentityConjugationTRelation(ai, 0, aj, 0));
        else
            lhs_a := Evaluate(MPCF_relations[i][1] @ MPCFW_phi, process_data`nonp_action`pc_auto_gens);
            AppendToCurrentRelation(~process_data, < 0, MPCF_relations[i][2] @ MPCFW_phi >);
            BuildCurrentRelationFromAutomorphism(~process_data, lhs_a);
            Append(~process_data`c_relations, CreateConjugationTRelationFromCurrentRelation(process_data, ai, 0, aj, 0));
        end if;
    end for;

    IndentPop(); IndentPop();

end procedure;


/* Construct the conjugation relations between the non-p layer and the other layers */
ConstructConjugationRelationsBetweenNonPandLayer := procedure(~process_data, layer_index : start_with_generator := 1)

    for ai in [ 1..#process_data`nonp_action`pc_auto_gens ] do
        for aj in [ start_with_generator..#process_data`layers[layer_index]`pauto_gens ] do
             a := (process_data`layers[layer_index]`pauto_gens[aj])^(process_data`nonp_action`pc_auto_gens[ai]);
             if a eq process_data`identity then
                 Append(~process_data`c_relations_identity, CreateIdentityConjugationTRelation(ai, 0, aj, layer_index));
             else
                 if a ne process_data`layers[layer_index]`pauto_gens[aj] then
                     BuildCurrentRelationFromAutomorphism(~process_data, a : under_construction := true);
                     Append(~process_data`c_relations, CreateConjugationTRelationFromCurrentRelation(process_data, ai, 0, aj, layer_index));
                 end if;
             end if;
         end for;
     end for;

end procedure;


/* Checks that the automorphism a is equal to the relation evaulated using process_data */
CheckRelation := function (process_data, relation, a)
    return (a eq AutomorphismFromRelation(process_data, relation));
end function;


/* Runs through the relations in process_data (stored as vectors) and checks that
   they are all consistent. Does not do (i, j, k) checks equivalent to the checks in the
   creation of the pc presentation.
*/
CheckRelations := procedure(~process_data)

    layers := process_data`layers;
    nonp_action := process_data`nonp_action;

    print "Checking p-relations...", #process_data`p_relations;

    for t_relation in process_data`p_relations do
        layer_index := t_relation[2];
        auto_index := t_relation[1];
        power := t_relation[3];
        relation := t_relation[4];

        if layer_index gt 0 then
            gen := layers[layer_index]`pauto_gens[auto_index];
        else
            gen := nonp_action`pc_auto_gens[auto_index];
        end if;
        if gen^power ne AutomorphismFromRelation(process_data, relation) then
            print "p_relation error: ", t_relation;
        end if;
    end for;

    print "Checking p-relations (identity)...", #process_data`p_relations_identity;

    for t_relation in process_data`p_relations_identity do
        layer_index := t_relation[2];
        auto_index := t_relation[1];
        power := t_relation[3];

        if layer_index gt 0 then
            gen := layers[layer_index]`pauto_gens[auto_index];
        else
            gen := nonp_action`pc_auto_gens[auto_index];
        end if;

        if gen^power ne process_data`identity then
            print "p_relation_identity error: ", t_relation;
        end if;

    end for;

    print "Checking conjugation relations...", #process_data`c_relations;

    for t_relation in process_data`c_relations do
        lower_auto := t_relation[1];
        lower_layer := t_relation[2];
        higher_auto := t_relation[3];
        higher_layer := t_relation[4];
        relation := t_relation[5];

        if lower_layer eq 0 then
            lower := nonp_action`pc_auto_gens[lower_auto];
        else
            lower := layers[lower_layer]`pauto_gens[lower_auto];
        end if;

        if higher_layer eq 0 then
            higher := nonp_action`pc_auto_gens[higher_auto];
        else
            higher := layers[higher_layer]`pauto_gens[higher_auto];
        end if;

        if higher^lower ne AutomorphismFromRelation(process_data, relation) then
            print "conjugator relation error: ", t_relation;
        end if;
    end for;

    if #process_data`c_relations_identity gt 0 then
        print "Error: there should be no c_relation_identity relations";
    end if;

end procedure;


/* Constructs the action of the non-p autos on the top layer.

   Fixes any errors in the layer categorisation for gens of A - in particular puts any
   layer 1 stuff into the matrix group, and is careful to check if an equal action on
   matrix group already exists - if so, adds to gen set and higher layer...

   Assumptions:  process_data`nonp_action`auto_gens contains non-id autos of A
*/
ConstructNonPAction := procedure (~process_data)

    n := #process_data`frattini_quotient_gens;
    p := process_data`p;

    F := GL(n, p);
    M := sub< F | >;

    if #process_data`layers_Agens[1] gt 0 then
        P := Parent(process_data`identity)`Group;
        Mgens := [ M.i : i in [1..Ngens(M)] ];

        for ai in process_data`layers_Agens[1] do
            a := process_data`Agens[ai];
            if NPCgens(P) gt 1 then
                N := F![ Partition(Eltseq(P.i @ a), [n, NPCgens(P) - n])[1] : i in [1..n] ];
            else
                N := F![Eltseq(P.1 @ a)];
            end if;

            /* This should NOT happen */
            error if N eq Identity(M), "Matrix should not be the identity on frattini quotient gens";

            if not N in Mgens then
                M := sub < F | Mgens cat [ N ] >;
                Mgens := [ M.i : i in [1..Ngens(M)] ];
                Append(~process_data`nonp_action`auto_gens, a);
            else
                i := Index(Mgens, N);
                process_data`Agens[ai] *:= process_data`nonp_action`auto_gens[i]^-1;
                a := process_data`Agens[ai];
                if a ne process_data`identity then
                    /*
                        Essentially checking if a = A.i (this shouldn't happen, but algorithm could spit
                        out automorphisms which are the same?)

                        TODO: is this necessary?  gens of groups are in a set afterall...
                    */
                    layer_index := AutomorphismLayer(process_data, a);
                    if layer_index gt 1 then
                        Append(~process_data`layers_Agens[layer_index], ai);
                    else
                        error "Automorphism should not be layer 1";
                    end if;
                else
                    error "Automorphism should not be Id";
                end if;
            end if;
        end for;
    end if;

    process_data`nonp_action`matrix_group := M;

end procedure;


/* Constructs process_data which contains all the information needed to build the PC
   presentation for A
*/
ConstructProcessData := function (A)

    P := A`Group;
    f := FactoredOrder(P);
    p := f[1][1];
    e := f[1][2];

    /* Remove automorphisms which are the identity map */
    vprint PCGroupAutomorphismGroupPGroup : "Number of generators of A:", Ngens(A);
    Agens := [ a : a in {@ A.i : i in [1..Ngens(A)] | A.i ne Identity(A) @} ];
    vprint PCGroupAutomorphismGroupPGroup : "Number of generators of A used:", #Agens;

    rank_gens := pRankGenerators(P);
    frattini_quotient_gens := [ P.i : i in rank_gens[1] ];
    gens_to_rank_gens := GroupGenLayers(rank_gens);

    /*
        Create record format for process data that will be carried around
    */
    ProcessDataRF := recformat < p : RngIntElt, rank_gens : SeqEnum, layers_Agens : SeqEnum,
        gens_to_rank_gens : SeqEnum, frattini_quotient_gens : SeqEnum, nonp_action : Rec, layers : SeqEnum,
        p_relations : SeqEnum, c_relations : SeqEnum, p_relations_identity : SeqEnum, c_relations_identity : SeqEnum,
        current_relation : List, current_relation_auto : GrpAutoElt, identity : GrpAutoElt, pc_group : Tup,
        pc_group_gens : SeqEnum, pc_group_gens_autos : SeqEnum, Agens : SeqEnum >;

    process_data := rec < ProcessDataRF | p := p, rank_gens := rank_gens, gens_to_rank_gens := gens_to_rank_gens,
        frattini_quotient_gens := frattini_quotient_gens, p_relations := [], c_relations := [], p_relations_identity := [],
        c_relations_identity := [], identity := Id(A), Agens := Agens >;

    /*
        N.B. We ignore the distinction between non p-automorphisms and p-automorphisms
    */
    AutomorphismGroupGeneratorsByLayer(~process_data);

    /*
        NonPActionRF

        Record format for describing the action of the nonp-autos
    */
    NonPActionRF := recformat < auto_gens : SeqEnum, matrix_group : GrpMat, word_group : Tup, pc_group : Tup,
        pc_auto_gens : SeqEnum, matrix_to_relation : UserProgram >;

    nonp_action := rec < NonPActionRF | auto_gens := [] >;

    process_data`nonp_action := nonp_action;


    /*
        Fix the automorphism layers - check that anything that moves the frattini quotient is in the matrix group
    */
    ConstructNonPAction(~process_data);
    ConstructPCGroupOfNonPMatrixGroup(~process_data`nonp_action);

    /*
        LayerRF record
    */
    LayerRF := recformat< group_gens : SeqEnum, pauto_gens : SeqEnum, V : ModFld, S : ModFld,
        basis : SetIndx, W : GrpSLP, change_of_basis >;
    layers := [ rec < LayerRF | group_gens := [], pauto_gens := [], V := RModule(GF(p), (#frattini_quotient_gens)^2),
        W := SLPGroup(0), basis := {@ @} > ];

    process_data`layers := layers;

    /*
        Now construct the higher layers, which also have spaces in...
    */
    for i in [2..#process_data`layers_Agens] do
        group_gens := rank_gens[i];

        layer := rec < LayerRF | V := RModule(GF(p), #frattini_quotient_gens * #group_gens), basis := {@ @},
            W := SLPGroup(0), group_gens := rank_gens[i], pauto_gens := [] >;

        layer`S := sub < layer`V | >;

        Append(~process_data`layers, layer);

        for ai in process_data`layers_Agens[i] do
            a := process_data`Agens[ai];
            v := process_data`layers[i]`V!AutomorphismToVector(a, frattini_quotient_gens, group_gens);

            if v notin process_data`layers[i]`S then
                Include(~process_data`layers[i]`basis, v);
                Append(~process_data`layers[i]`pauto_gens, a);

                BuildLayerSubspace(~process_data`layers[i]);
            else
                /* if the action on this layer is already covered, we need to find it, and then
                   add appropriate auto to later layer */

                /* clear the current relation */
                ClearCurrentRelation(~process_data);
                /* construct the relation which corresponds to the action on *this* layer */
                AppendRelationToCurrentRelationForAutomorphismInLayer(~process_data, a, i : under_construction := true);

                /* current_relation_auto is now the map which has the same action on this layer */
                na := process_data`current_relation_auto * a^-1;

                /* move on to the next generator if its the identity */
                if na eq Identity(A) then continue; end if;

                /* if not then put in the correct layer! */
                na_layer := AutomorphismLayer(process_data, na);
                error if na_layer le i, "Layer must be higher!";

                if na notin process_data`Agens then
                    vprintf PCGroupAutomorphismGroupPGroup : "Adding generator to layer %o\n", na_layer;
                    /* add the generator to the list */
                    Append(~process_data`Agens, na);
                    /* add the layer information too */
                    Append(~process_data`layers_Agens[na_layer], #process_data`Agens);
                else
                    vprint PCGroupAutomorphismGroupPGroup : "Discarding unused generator A.%o\n", ai;
                end if;
            end if;
        end for;
    end for;

    /*
        Go through each of the layers, and compute the powers of elts and commutators of each
        pair of elts in each layer
    */
    for j in [1..#process_data`layers] do
        ConstructPowerRelationsInLayer(~process_data, j);

        for i in [1..j] do
            ConstructConjugationRelationsBetweenLayers(~process_data, i, j);
        end for;
    end for;

    /*
        Now construct relations between layers and nonp-action
    */
    if #process_data`nonp_action`pc_auto_gens gt 0 then

        /*
            Fix for generators being added here - need to re run the whole process on new gens...
        */
        count_check := [ #process_data`layers[i]`pauto_gens : i in [1..#process_data`layers] ];

        ConstructRelationsForNonPAction(~process_data);

        for i in [2..#process_data`layers] do
            vprint PCGroupAutomorphismGroupPGroup : "Constructing conjugation relations between non-p and layer:", i;
            ConstructConjugationRelationsBetweenNonPandLayer(~process_data, i);
            vprint PCGroupAutomorphismGroupPGroup : "Conjugation Relations: ", #process_data`c_relations;
        end for;

        count_check2 := [ #process_data`layers[i]`pauto_gens : i in [1..#process_data`layers] ];

        if count_check ne count_check2 then

            vprint PCGroupAutomorphismGroupPGroup : "New generator added in constructing nonp action relations...";

            count_diff := [ count_check2[i] - count_check[i] : i in [1..#count_check] ];
            count_diff_pos := [ i : i in [1..#count_diff] | count_diff[i] ne 0 ];

            /* j is the index of the layer */
            for j in count_diff_pos do
                /* If count_diff[j] is 1, then want to start with the last gen of
                   process_data`layers[j]`p_auto_gens */
                start_with_generator := #process_data`layers[j]`pauto_gens - count_diff[j] + 1;
                vprintf PCGroupAutomorphismGroupPGroup : "Constructing power relations, starting (layer=%o, index=%o)\n", j, start_with_generator;

                IndentPush();
                ConstructPowerRelationsInLayer(~process_data, j : start_with_generator := start_with_generator);
                IndentPop();

                vprintf PCGroupAutomorphismGroupPGroup : "Constructing conjugation relations, starting (higher_layer=%o, start_with_generator=%o)\n", j, start_with_generator;
                IndentPush();
                for i in [1..j] do
                    ConstructConjugationRelationsBetweenLayers(~process_data, i, j : start_with_higher_generator := start_with_generator);
                end for;
                IndentPop();

                //vprintf PCGroupAutomorphismGroupPGroup : "Constructing conjugation relations between non-p and (layer=%o, start_with_generator=%o)\n", j, start_with_generator;

                //ConstructConjugationRelationsBetweenNonPandLayer(~process_data, j : start_with_generator := start_with_generator);
            end for;
        end if;
    end if;

    return process_data;

end function;

/* Attempts to construct a PC elt from the map m and process_data */
AutomorphismMapToPCElt := function (m, A)

    /* check that A is sensible */
    error if not assigned A`PCRepData, "PCRepData attribute must be set";
    error if not IsConditioned(A`Group), "Underlying group must be conditioned";

    /* check that the domain and codomain are correct! */
    error if not Domain(m) cmpeq A`Group, "Domain of the map is not correct for this automorphism group";
    error if not Codomain(m) cmpeq A`Group, "Codomain of the map is not correct for this automorphism group";

    /* Fix for testing the identity map */
    P := Domain(m);
    if [ P.i @ m : i in [1..NPCgens(P)] ] eq [ P.i : i in [1..NPCgens(P)]] then
        return Id(A`RepGroup);
    end if;

    /* set under_construction to be false so that it will fail if the map can't be represented */
    BuildCurrentRelationFromAutomorphism(~A`PCRepData, m : under_construction := false);
    return ExpressionFromRelation(A`PCRepData, A`PCRepData`current_relation, A`PCRepData`pc_group_gens);

end function;


/* Constructs a PC group and stores it in process_data`pc_group */
ConstructPCGroupFromProcessData := procedure(~process_data, A)

    F_Ngens := [ #process_data`nonp_action`pc_auto_gens ] cat [ #process_data`layers[i]`pauto_gens : i in [1..#process_data`layers] ];
    F := FreeGroup(&+F_Ngens);
    Fgens := Partition([ F.i : i in [1..Ngens(F)] ], F_Ngens);

    F_relations := [];

    for relation in process_data`p_relations do
        Append(~F_relations, BuildPowerRelationFromTRelation(process_data, Fgens, relation));
    end for;

    for relation in process_data`p_relations_identity do
        Append(~F_relations, BuildIdentityPowerRelationFromTRelation(process_data, Fgens, relation));
    end for;

    for relation in process_data`c_relations do
        r := BuildConjugationRelationFromTRelation(process_data, Fgens, relation);
        e := Eltseq(r[2]);
        if #e eq 1 and Eltseq(r[1])[2] eq e[1] then
            vprint PCGroupAutomorphismGroupPGroup : "Trivial relation: ", r;
        else
            Append(~F_relations, r);
        end if;
    end for;

    vprint PCGroupAutomorphismGroupPGroup : "Number of generators:", F_Ngens;
    vprint PCGroupAutomorphismGroupPGroup : "All relations: ", F_relations;

    Q, Q_phi := quo < GrpPC : F | F_relations : Check := false >;
    error if not IsConsistent(Q), "The PC presentation for automorphism group of p-group is not consistent";
    process_data`pc_group_gens := [ f @ Q_phi : f in Fgens ];

    /* note that this is still Q here */
    process_data`pc_group_gens_autos := process_data`nonp_action`pc_auto_gens cat &cat[ layer`pauto_gens : layer in process_data`layers ];

    /* TODO: This is too slow for large Q for some reason - fix this! */
    // pc_to_auto_map := hom < Q -> A | [ process_data`pc_group_gens_autos[i] : i in [1..NPCgens(Q)]] >;
    F_to_auto_map := hom < F -> A | [ process_data`pc_group_gens_autos[i] : i in [1..NPCgens(Q)]] >;

    h := hom < A -> Q | x :-> AutomorphismMapToPCElt(x, A), y :-> (y @@ Q_phi) @ F_to_auto_map >;
    process_data`pc_group := < Q, h >;

end procedure;


/* Construct a pc-presentation for an automorphism group of a conditioned p-group.  Assumes that A has been created
via AutomorphismGroupPGroup (which is the default algorithm for p-groups via AutomorphismGroup). */
intrinsic PCGroupAutomorphismGroupPGroup ( A :: GrpAuto : check_relations := false ) -> BoolElt, Map, GrpPC
{Attempt to construct a pc-representation for the automorphism group A of a conditioned p-group P.  The automorphism group
must have been construced using the native AutommorphismGroup intrinsic, or any equivalent alias.}

    if assigned A`PCRepData then
        return true, A`PCRepData`pc_group[2], A`PCRepData`pc_group[1];
    end if;

    if assigned A`Soluble and assigned A`PCGroup and A`Soluble then
        return true, A`PCGroup[2], A`PCGroup[1];
    end if;

    require IsPrimePower(#A`Group) : "Input should be a group of automorphisms of a p-group";
    require IsConditioned(A`Group) : "Input should be a group of automorphisms of a conditioned p-group";

    if not IsSolubleAutomorphismGroupPGroup(A) then
        return false, _, _;
    end if;

    process_data := ConstructProcessData(A);

    if check_relations then
        CheckRelations(~process_data);
    end if;

    ConstructPCGroupFromProcessData(~process_data, A);

    A`Soluble := true;
    A`PCGroup := process_data`pc_group;
    A`PCRepData := process_data;
    A`PCGenerators := {@ a : a in process_data`pc_group_gens_autos @};

    map_to_rep_elt := function (m)
        return AutomorphismMapToPCElt(m, A);
    end function;
    A`MapToRepElt := map_to_rep_elt;

    A`RepMap := A`PCGroup[2];
    A`RepGroup := A`PCGroup[1];

    /* check that the resulting rep is the same order as the group (both trivial to compute)*/
    assert #A eq #process_data`pc_group[1];

    return true, A`RepMap, A`RepGroup;

end intrinsic;


/* Determines if the automorphism group A is soluble by testing the solublility of the matrix group part
   of the automorphism group (generated by A`Group`Automorphisms`Autos) */
intrinsic IsSolubleAutomorphismGroupPGroup ( A :: GrpAuto ) -> BoolElt
{Given a group of automorphisms A of a p-group, where A has been constructed using AutomorphismGroup or any equivalent
alias, determine if A is soluble.}

    P := A`Group;
    f := FactoredOrder(P);

    require #f eq 1 : "Input should be a group of automorphisms of a p-group";

    if assigned A`Soluble then
        return A`Soluble;
    end if;

    p := f[1][1];
    e := f[1][2];

    if IsElementaryAbelian(P) then
        /* GL(n,p) is Aut(P), and only soluble for 2, 2 and 2, 3 (and p, 1) */
        A`Soluble := (f[1] eq <2, 2> or f[1] eq <2, 3> or e eq 1);
    else
        require assigned P`Automorphisms : "Input group must have been created by internal AutomorphismGroup or equivalent alias";
        /*  N.B. This code is different to PCGroupAutomorphismGroupPGroup because it doesn't care if A.j acts on top
            layer as id...
        */
        n := pRanks(P)[1];
        M := GL(n, p);
        H := sub < M | [ M![ Partition(Eltseq(P.i @ A.j), [n, NPCgens(P) - n])[1] : i in [1..n] ] : j in [1..#P`Automorphisms`Autos] ] >;
        A`Soluble := LMGIsSoluble(H);
    end if;

    return A`Soluble;

end intrinsic;

/* Alias for IsSolubleAutomorphismGroupPGroup */
intrinsic IsSolvableAutomorphismGroupPGroup ( A :: GrpAuto ) -> BoolElt
{Given a group of automorphisms A of a p-group, where A has been constructed using AutomorphismGroup or any equivalent
alias, determine if A is soluble.}
    return IsSolubleAutomorphismGroupPGroup(A);
end intrinsic;