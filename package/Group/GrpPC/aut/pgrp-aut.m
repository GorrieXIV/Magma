freeze;

/* verbose flag for checking PC presentation on all group elements */
declare verbose CheckPCRepresentationFull, 1;


/*  Checks if p-group is elementary abelian, if so it calls the specialised
    Aut(P) in AutomorphismGroupElementaryAbelianGroup which allows direct
    access to the matrix group for later calculations.

    P - Group to compute Aut(P) of
*/

intrinsic AutomorphismGroupPGroup_ ( P :: GrpPC : CharacteristicSubgroups := []) -> GrpAuto
{Computes the automorphism group of p-group P, using AutomorphismGroupElementaryAbelianPGroup
if P is elementary abelian.}

    require #FactoredOrder(P) eq 1 : "Input group must be a p-group";

    if IsElementaryAbelian(P) then
        /* NB: we deliberately ignore CharacteristicSubgroups here */
        return AutomorphismGroupElementaryAbelianPGroup(P);
    end if;

    IndentPush();
    A := AutomorphismGroupPGroup(P : CharacteristicSubgroups := CharacteristicSubgroups);
    IndentPop();

    return A;

end intrinsic;


/*  Determines if a suitable representation has already been constructed, and if not
    creates a permutation representation as a last resort.  Returns a UserProgram which computes
    the rep elt of a map (rather than a GrpAutoElt), and the usual rep map and group.  Also sets
    A`MapToRepElt, A`RepMap and A`RepGroup respectively.

    - MapToRepElt
        Takes something that behaves like a Map, ie can do elt @ m, and converts
        it to an element in the chosen representation of A

    NB. A representation must set all 3 properties, otherwise a permutation rep will be created.
*/

intrinsic RepresentationAutomorphismGroupPGroup ( A :: GrpAuto ) -> Map, Map, Grp
{Returns the preferred representation for A, generally this will mean that GrpPC, GrpMat and then GrpPerm if
no other available.}

    if not assigned A`MapToRepElt or not assigned A`RepMap or not assigned A`RepGroup then

        /* Attempt to construct PC rep for A.  If this works, then we have properties */
        b := false;
        if Type(A`Group) eq GrpPC then
            vprint AutomorphismGroupSolubleGroup : "Attempting to construct a PC rep for p-group automorphism group...";
            b, phi_A, R_A := PCGroupAutomorphismGroupPGroup(A);
        end if;

        if not b then
            vprint AutomorphismGroupSolubleGroup : "Group not soluble, constructing permutation rep instead...";
            /* Don't have a better alternative, produce a normal perm rep :-(. */
            phi_A, R_A := PermutationRepresentation(A);

            map_to_rep_elt := function (m)
                /* call new intrinsic for old coercion */
                b, a := CoerceByClassAction(A, m);
                error if not b, "Could not coerce map into automorphism group.";
                return a @ phi_A;
            end function;

            A`MapToRepElt := map_to_rep_elt;
        end if;

        A`RepMap := phi_A;
        A`RepGroup := R_A;

    end if;

    return A`MapToRepElt, A`RepMap, A`RepGroup;

end intrinsic;
