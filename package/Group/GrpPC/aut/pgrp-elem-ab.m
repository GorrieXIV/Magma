freeze;

/*  Compute the automorphism group of an elementary abelian P group.  Constructs the automorphism
    group via a GL matrix group, and preserves the matrix group for later calculations

    P - elementary abelian p-group
*/

intrinsic AutomorphismGroupElementaryAbelianPGroup ( P :: GrpPC : construct_pc_representation_if_possible := true ) -> GrpAuto
{Computes the automorphism group of an elementary abelian p-group.  Option to construct a pc-represention if possible.}

    f := FactoredOrder(P);
    require #f eq 1 : "Input group must be a p-group";
    require IsElementaryAbelian(P) : "Input group must be elementary abelian";

    vprint AutomorphismGroupSolubleGroup : "Using AutomorphismGroupElementaryAbelianPGroup algorithm...";

    p := f[1][1];
    e := f[1][2];

    M := GL(e, p);

    Z := Integers();

    Pgens := [ P.i : i in [1..NPCgens(P)] ];
    imgs := [ [ &*[ P.j^(Z!gen[j]) : j in [1..#gen] ] : gen in Partition(Eltseq(M.i), e) ] : i in [1..Ngens(M)] ];
    A := AutomorphismGroup(P, Pgens, imgs);

    /* Test if soluble */
    if construct_pc_representation_if_possible and (e eq 1 or f[1] eq <2, 2> or f[1] eq <3, 2>) then
        /* Know that perm rep won't be slow, note don't set A`MapToRepElt here */
        phi_A, R_A := PermutationRepresentation(A);

		vprint AutomorphismGroupSolubleGroup : "Constructing PC Presentation for soluble automorphism group...";

        /* create PC group */
        PC_R_A, phi_R_A := PCGroup(R_A);

        A_PCGenerators := {@ (r_a @@ phi_R_A) @@ phi_A : r_a in PCGenerators(PC_R_A) @};

        /* re-create the automorphism group with the polycylic generators */
        A_ := AutomorphismGroup(P, Pgens, [ Pgens @ a : a in A_PCGenerators ]);

        A_`PCGenerators := A_PCGenerators;

        /* construct mapping for Map -> GrpPCElt */
        map_to_rep_elt := function (m)
            a := A!m;
            // error if not b, "Map cannot be coerced into automorphism group";
            r :=  (a @ phi_A) @ phi_R_A;
            return r;
        end function;
        A_`MapToRepElt := map_to_rep_elt;

        /* RepEltToMap is required to be consistent with case where not soluble */
        A_`RepEltToMap := phi_R_A^-1 * phi_A^-1;

        /* construct + set new rep mapping and rep group attributes */
        A_`RepMap := hom < A_ -> PC_R_A | a :-> (a @ phi_A) @ phi_R_A , r :-> (r @@ phi_R_A) @@ phi_A >;
        A_`RepGroup := PC_R_A;

        /* set the PCGroup attribute for compatability with rest of system */
        A_`PCGroup := < A_`RepGroup, A_`RepMap >;

        A_`Soluble := true;

        return A_;
    else
        vprint AutomorphismGroupSolubleGroup : "Not soluble, creating matrix group representation...";
        /* If not soluble, construct rep from matrix group */
        A`MatrixGroup := M;
        A`Order := Order(M);

        W_M, phi_M := WordGroup(M);
        M`SLPGroup := W_M;
        M`SLPGroupHom := phi_M;

        /* construct mapping for Map -> GrpMatElt */
        map_to_rep_elt := function (m)
            return M![ Eltseq(P.i @ m) : i in [1..NPCgens(P)] ];
        end function;
        A`MapToRepElt := map_to_rep_elt;

        rep_elt_to_auto_elt := function (m)
            return Evaluate(m @@ M`SLPGroupHom, [A.i : i in [1..Ngens(A)]]);
        end function;

        map_to_auto_elt := function (m)
            return rep_elt_to_auto_elt(map_to_rep_elt(m));
        end function;

        /* construct + set new rep mapping and rep group attribute */
        A`RepGroup := M;
        A`RepMap := hom < A -> M | a :-> rep_elt_to_auto_elt(map_to_rep_elt(a)), m :-> rep_elt_to_auto_elt(m) >;

        /* special RepEltToMap function, as coercing into automorphisms
           via word group is expensive and sometimes unnecessary */
        rep_elt_to_map := function (r)
            return hom < P -> P | [ P!r[i] : i in [1..NPCgens(P)] ] >;
        end function;
        A`RepEltToMap := rep_elt_to_map;

        A`Soluble := false;
    end if;

    return A;

end intrinsic;
