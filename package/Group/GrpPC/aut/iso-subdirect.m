freeze;

import "aut-direct.m" : AutomorphismGroupOfDirectProduct;
import "aut-subdirect.m" : AutomorphismGroupOfSubdirectProduct;
import "find-mapping-automorphism.m" : FindMappingAutomorphism;
import "fix-subgroup.m" : FixSubgroup;


/*
    INTERAL

    Calculates if the subdirect product is isomorphic or not and results the result
    and necessary map.
*/
IsIsomorphicSubdirectProduct_ := function (G1, G1_QK, G1_mK, G1_QL, G1_mL, G2, G2_QK, G2_mK, G2_QL, G2_mL, G1_QKtoG2_QK, G1_QLtoG2_QL)

    /* A little paranoid checking... */
    assert #Kernel(G1_QKtoG2_QK) eq 1;
    assert #Kernel(G1_QLtoG2_QL) eq 1;

    D1, i1, p1 := DirectProduct(G1_QK, G1_QL);
    D2, i2, p2 := DirectProduct(G2_QK, G2_QL);

    D1toD2_works, D1toD2 := IsHomomorphism(D1, D2,
        [ D2 | (d @ p1[1] @ G1_QKtoG2_QK @ i2[1]) * (d @ p1[2] @ G1_QLtoG2_QL @ i2[2]) : d in PCGenerators(D1) ]);

    if not D1toD2_works then
        vprint AutomorphismGroupSolubleGroup : "Cannot construct homomorphism between direct products D1 -> D2";
        return false, _;
    end if;

    G1_to_D1 := hom < G1 -> D1 | [ D1 | (g @ G1_mK @ i1[1]) * (g @ G1_mL @ i1[2]) : g in PCGenerators(G1) ] >;
    G2_to_D2 := hom < G2 -> D2 | [ D2 | (g @ G2_mK @ i2[1]) * (g @ G2_mL @ i2[2]) : g in PCGenerators(G2) ] >;

    G1_in_D1 := Image(G1_to_D1);/*sub < D1 | [ D1 | (g @ G1_mK @ i1[1]) * (g @ G1_mL @ i1[2]) : g in PCGenerators(G1) ] >;*/
    G2_in_D2 := Image(G2_to_D2);/*sub < D2 | [ D2 | (g @ G2_mK @ i2[1]) * (g @ G2_mL @ i2[2]) : g in PCGenerators(G2) ] >;*/

    /*
        Need to check that G1_in_D1 is mapped to G2_in_D2
    */
    G1_in_D2 := G1_in_D1 @ D1toD2;
    if not G1_in_D2 eq G2_in_D2 then
        vprint AutomorphismGroupSolubleGroup : "Image of G1_in_D2 does not map to G2_in_D2...";

        vprint AutomorphismGroupSolubleGroup : "Constructing Aut(D2)...";
        vtime AutomorphismGroupSolubleGroup : AD2 := AutomorphismGroupSolubleGroup(D2);

        /*
           Actually want to search through automorphisms which also fix the image of G2 in D2,
           but this isn't exploited here - yet!
        */

        vprint AutomorphismGroupSolubleGroup : "Searching for automorphism to map G1_in_D2 -> G2_in_D2...";
        vtime AutomorphismGroupSolubleGroup : b, m := FindMappingAutomorphism(AD2, G1_in_D2, G2_in_D2);

        if b then
            vprintf AutomorphismGroupSolubleGroup : "Found automorphism: %o\n", m;
            D1toD2 *:= m;
            assert2 G1_in_D1 @ D1toD2 eq G2_in_D2;
        else
            vprint AutomorphismGroupSolubleGroup : "Could not find automorphism mapping G1_in_D2 to G2_in_D2";
            return false, _;
        end if;
    end if;

    b, h := IsHomomorphism(G1, G2, [ G2 | g @ G1_to_D1 @ D1toD2 @@ G2_to_D2 : g in PCGenerators(G1) ]);
    if b then
        return b, h;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Computing subgroup of AD2 which fixes image of G2 in D2";
    vtime AutomorphismGroupSolubleGroup : AD2_G2inD2 := FixSubgroup(AD2, G2_in_D2);

    vprint AutomorphismGroupSolubleGroup : "Computing representation of fix subgroup automorphism group...";
    vtime AutomorphismGroupSolubleGroup : phi_AD2_G2inD2, R_AD2_G2inD2 := PermutationRepresentation(AD2_G2inD2);

    vprint AutomorphismGroupSolubleGroup : "Iterating over automorphisms to find isomorphism...";
    vtime AutomorphismGroupSolubleGroup : for x in R_AD2_G2inD2 do
        b, h := IsHomomorphism(G1, G2, [ G2 | g @ G1_to_D1 @ D1toD2 @ (x @@ phi_AD2_G2inD2) @@ G2_to_D2 : g in PCGenerators(G1) ]);
        if b then
            return b, h;
        end if;
    end for;

    vprint AutomorphismGroupSolubleGroup : "Subdirect product iso couldn't construct homomorphism";
    return false, _;

end function;


IsIsomorphicSubdirectProduct__ := function (G1, K1, L1, G1_QK, G1_mK, G1_QL, G1_mL, G2, K2, L2, G2_QK, G2_mK, G2_QL, G2_mL, G1_QKtoG2_QK, G1_QLtoG2_QL)

    /* These have already been computed (propbably) during the iso tests for G1_QKto */
    A_G2_QK := AutomorphismGroupSolubleGroup(G2_QK);
    A_G2_QL := AutomorphismGroupSolubleGroup(G2_QL);

    b_K, alpha_K := FindMappingAutomorphism(A_G2_QK, /* L2/K2 */ L2 @ G2_mK, /* L1/K1 @ G1_QK->G2_QK */G1_QK);
    if not b_K then return false, _; end if;
    b_L, alpha_L := FindMappingAutomorphism(A_G2_QL, /* K2/L2 */ K2 @ G2_mL, /* L1/K1 @ G1_QL->G2_QL */G1_QL);
    if not b_L then return false, _; end if;

    // A_K := AutomorphismGroupSolubleGroup(G2_QK);
    // A_L := AutomorphismGroupSolubleGroup(G2_QL);
end function;


IsIsomorphicSubdirectProduct := function(G1, K1, L1, G2, K2, L2)
    G1_QK, G1_mK := quo< G1 | K1 >;
    G1_QL, G1_mL := quo< G1 | L1 >;

    G2_QK, G2_mK := quo< G2 | K2 >;
    G2_QL, G2_mL := quo< G2 | L2 >;

    vprint AutomorphismGroupSolubleGroup : "Computing IsIsomorphic(G1/K1, G2/K2)...";
    vtime AutomorphismGroupSolubleGroup : K_iso, G1_QKtoG2_QK := IsIsomorphic(G1_QK, G2_QK);
    if not K_iso then
        vprint AutomorphismGroupSolubleGroup : "Cannot contruct isomorphism: G1/K1 is not isomorphic to G2/K2";
        return false, _;
    end if;

    vprint AutomorphismGroupSolubleGroup : "Computing IsIsomorphic(G1/L1, G2/L2)...";
    vtime AutomorphismGroupSolubleGroup : L_iso, G1_QLtoG2_QL := IsIsomorphic(G1_QL, G2_QL);
    if not L_iso then
        vprint AutomorphismGroupSolubleGroup : "Cannot contruct isomorphism: G1/L1 is not isomorphic to G2/L2";
        return false, _;
    end if;

    return IsIsomorphicSubdirectProduct_(G1, G1_QK, G1_mK, G1_QL, G1_mL, G2, G2_QK, G2_mK, G2_QL, G2_mL, G1_QKtoG2_QK, G1_QLtoG2_QL);
end function;