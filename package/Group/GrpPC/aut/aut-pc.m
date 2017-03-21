freeze;

/* Attach attributes to automorphism group A necessary for assigning a pc rep to A */
intrinsic AssignPCRepresentation ( A :: GrpAuto, pc_generators :: SetIndx[GrpAutoElt], map_to_rep_elt :: Map, rep_map :: Map, rep_group :: GrpPC )
{Attach attributes to A necessary for assigning a pc presentation.}

    A`PCGenerators := pc_generators;
    A`MapToRepElt := map_to_rep_elt;
    A`PCGroup := < rep_group, rep_map >;
    A`RepMap := A`PCGroup[2];
    A`RepGroup := A`PCGroup[1];

    A`Soluble := true;
    A`Order := #A`RepGroup;

end intrinsic;


intrinsic CheckPCRepresentation ( A :: GrpAuto : FullCheck := false, RandomCheckCount := 1 ) -> BoolElt
{Tests that the PC rep attached to the automorphism group A is valid.  If the optional flag FullCheck is true
then each element of A`RepGroup is put through A`RepMap, otherwise random elements from A`RepGroup are chosen
to verify the representation.  The number of such random checks can be set using the RandomCheckCount flag which
defaults to 10.}

    RequiredAttributes := [ "PCGenerators", "MapToRepElt", "PCGroup", "RepMap", "RepGroup", "Soluble" ];

    /* Check that all the attributes have been set */
    for required_attribute in RequiredAttributes do
        error if not assigned A``required_attribute, "Attribute", required_attribute, "not set.";
    end for;

    /* do a full check for the PC rep */
    if IsVerbose("CheckPCRepresentationFull") or FullCheck then
        for r in A`RepGroup do
            assert r eq (r @@ A`RepMap) @ A`RepMap;
        end for;
    else
        for i in [1..RandomCheckCount] do
            r1 := Random(A`RepGroup); r2 := Random(A`RepGroup);
            a1 := r1 @@ A`RepMap; a2 := r2 @@ A`RepMap;

            /* Verify that the RepMap work properly */
            error if (a1 * a2 ne (r1 * r2) @@ A`RepMap), "RepMap isn't consistent.";

            /* Verify that the MapToRepElt works properly */
            error if ((a1 @ A`MapToRepElt) * (a2 @ A`MapToRepElt) ne (a1 * a2) @ A`MapToRepElt),
                "MapToRepElt isn't consistent.";
        end for;
    end if;

    if Type(A`RepGroup) eq GrpPC then
        /* Check that the orders of the generators match up */
        error if [ Order(a) : a in PCGenerators(A) ] ne [ Order(A`PCGroup[1].i) : i in [1..NPCgens(A`PCGroup[1])] ],
            "Orders of generators of PCGenerators(A) don't match the PCGenerators of PCGroup";
    end if;

    return true;

end intrinsic;