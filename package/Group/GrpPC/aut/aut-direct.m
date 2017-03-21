freeze;

/*  Computes the automorphism group of G, where G is a direct product of
    K and H which are characteristic subgroups
    N.B. Assumes that the generators of G can be split into gens of H and
    gens of K.
    G - soluble group with special presentation
    H - char subgroup of G
    K - char subgroup of G
*/
AutomorphismGroupOfDirectProduct := function (G, H, K)

    genH := [ G | h : h in PCGenerators(H) ];
    genK := [ G | k : k in PCGenerators(K) ];

    AH := AutomorphismGroup(H);
    AK := AutomorphismGroup(K);

    imgs := [ (genH @ a) cat genK : a in Generators(AH) ] cat [ genH cat (genK @ a) : a in Generators(AK) ];

    return AutomorphismGroup2(G, genH cat genK, imgs);

end function;


/*  Computes the automorphism group of soluble G where G is a direct product of
    Sylow p-subgroup S and Hall p'-subgroup T.
    N.B. assumes that SpecialPresentation has been called on G.
*/
AutomorphismGroupOfDirectProduct_ := function (G, S, T)

    genS := [ S | s : s in PCGenerators(S) ];
    genT := [ T | t : t in PCGenerators(T) ];

    vprint AutomorphismGroupSolubleGroup : "Computing automorphism group of p-group";
    vtime AutomorphismGroupSolubleGroup : AutS := AutomorphismGroupPGroup_(S);

    b, _, _ := PCGroupAutomorphismGroupPGroup(AutS);

    vprint AutomorphismGroupSolubleGroup : "Computing automorphism group of p'-group";
    vtime AutomorphismGroupSolubleGroup : AutT := AutomorphismGroupSolubleGroup(T);

    /* Need to compute the PC group if possible */
    if IsSoluble(AutS) and IsSoluble(AutT) then
        vprint AutomorphismGroupSolubleGroup : "Automorphism group is soluble";

        /* compute the PC group of Aut(G) */
        PC_AutS := AutS`PCGroup[1];
        PC_AutT := AutT`PCGroup[1];

        PC_AutG, i, p := DirectProduct(PC_AutS, PC_AutT);

        /* construct the imgs using the PC rep */
        imgs := [ (genS @ (PC_AutG.i @ p[1] @@ AutS`RepMap)) cat (genT @ (PC_AutG.i @ p[2] @@ AutT`RepMap)) : i in [1..NPCgens(PC_AutG)] ];
        A := AutomorphismGroup2(G, genS cat genT, imgs);

        A`PCGenerators := {@ A.i : i in [1..Ngens(A)] @};

        /* N.B. the generators of A will match the PC generators of rep */
        /* TODO: this is too slow */
        // rep_elt_to_auto_elt := hom < PC_AutG -> A | [ A.i : i in [1..Ngens(A)] ] >;
        F, phi_F := FPGroup(PC_AutG); F_to_A := hom < F -> A | [ A.i : i in [1..Ngens(A)] ] >;

        map_to_rep_elt := function (m)
           m_S := hom < S -> S | genS @ m : Check := false >;
           r_S := m_S @ AutS`MapToRepElt;
           m_T := hom < T -> T | genT @ m : Check := false >;
           r_T := m_T @ AutT`MapToRepElt;
           return (r_S @ i[1]) * (r_T @ i[2]);
        end function;
        A`MapToRepElt := map_to_rep_elt;

        h := hom < A -> PC_AutG | x :-> map_to_rep_elt(x), y :-> (y @@ phi_F) @ F_to_A >;
        A`PCGroup := < PC_AutG, h >;

        A`RepMap := A`PCGroup[2];
        A`RepGroup := A`PCGroup[1];

        A`Soluble := true;
    else
        imgs := [ (genS @ AutS.i) cat genT : i in [1..Ngens(AutS)] ] cat [ genS cat (genT @ AutT.i) : i in [1..Ngens(AutT)] ];
        A := AutomorphismGroup2(G, genS cat genT, imgs);

        A`Soluble := false;
    end if;

    A`Order := #AutS * #AutT;
    return A;

end function;
