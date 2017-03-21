freeze;

/* Construct and attach a pc rep for B, a subgroup of A, from the pc rep of A.  Returns B with
   new generating set (the pc generators). */
SubgroupRepFromPCRep := function (A, B)
    /* Construct rep group for B (pc-group) */
    RepGroup := sub < A`RepGroup | [ B.i @ A`RepMap : i in [1..Ngens(B)] ] >;

    /* Reconstruct B using the new PCGenerators from RepGroup */
    B_PCGenerators := {@ r @@ A`RepMap : r in PCGenerators(RepGroup) @};
    assert #B_PCGenerators eq NPCgens(RepGroup);

    B := sub < A | [ b : b in B_PCGenerators ] >;
    B`PCGenerators := B_PCGenerators;
    B`RepGroup := RepGroup;

    map_to_rep_elt := function (m)
       /* Compute the rep elt in A`RepGroup first */
       r := m @ A`MapToRepElt;
       /* Coerce it into B`RepGroup */
       return B`RepGroup!r;
    end function;
    B`MapToRepElt := map_to_rep_elt;

    /* This is slow..? Still? */
    rep_elt_to_aut := hom < B`RepGroup -> B | [ B.i : i in [1..NPCgens(B)] ] >;
    //F, phi_F := FPGroup(B`RepGroup); F_to_B := hom < F -> B | [ B.i : i in [1..Ngens(B)] ] >;

    // B`RepMap := hom < B -> B`RepGroup | x :-> x @ B`MapToRepElt, y :-> (y @@ phi_F) @ F_to_B >;
    B`RepMap := hom < B -> B`RepGroup | x :-> x @ B`MapToRepElt, y :-> y @ rep_elt_to_aut >;

    B`PCGroup := < B`RepGroup, B`RepMap >;
    B`Soluble := true;

    return B;
end function;

/* Construct and attach a rep for B, a subgroup of A, from the rep of A.  This assumes that the
   rep of A is a GrpPerm, and so the rep for B can either be a GrPerm *or* a GrpPC (in the case
   where B is soluble.  Returns new B (if soluble its generating set is changed to the pc
   generators to match the rep). */
SubgroupRepFromPermRep := function (A, B)
    B`RepGroup := sub < A`RepGroup | [ B.i @ A`RepMap : i in [1..Ngens(B)] ] >;
    map_to_rep_elt := function (m)
        /* NB: we use A's MapToRepElt */
        r := m @ A`MapToRepElt;
        /* Check that this mapping is in B, and not just in A */
        error if r notin B`RepGroup, "Could not coerce map into automorphism group.";
        return r;
    end function;
    B`MapToRepElt := map_to_rep_elt;
    B`RepMap := hom < B -> B`RepGroup | x :-> x @ B`MapToRepElt, y :-> y @@ A`RepMap >;

    /* If the group is soluble, then construct a pc rep for it instead */
    if IsSoluble(B`RepGroup) then
        PC_RepGroup, phi_PC_RepGroup := PCGroup(B`RepGroup);
        B_PCGenerators := {@ (r @@ phi_PC_RepGroup) @@ B`RepMap : r in PCGenerators(PC_RepGroup) @};

        B := sub < A | [ b : b in B_PCGenerators ] >;
        B`PCGenerators := B_PCGenerators;

        B`RepGroup := PC_RepGroup;
        B`MapToRepElt := function (m)
            /* use the map_to_rep_elt for the old B */
            return (m @ map_to_rep_elt) @ phi_PC_RepGroup;
        end function;
        
        F, phi_F := FPGroup(B`RepGroup); F_to_B := hom < F -> B | [ B.i : i in [1..Ngens(B)] ] >; 
        B`RepMap := hom < B -> B`RepGroup | x :-> x @ B`MapToRepElt, y :-> (y @@ phi_F) @ F_to_B >;

        B`PCGroup := < B`RepGroup, B`RepMap >;
        B`Soluble := true;
    else
        B`Soluble := false;
    end if;

    return B;
end function;


intrinsic HasRepresentation ( A :: GrpAuto ) -> BoolElt
{Checks whether the automorphism group A has a representation set.}
    return assigned A`RepGroup and assigned A`RepMap and assigned A`MapToRepElt and assigned A`Soluble
        and assigned A`Order;
end intrinsic;


intrinsic ConstructRepresentationForSubgroup ( A :: GrpAuto, B :: GrpAuto ) -> GrpAuto
{Construct a representation for the subgroup B of an automorphism group A.  A must already
have a representation set.  The generators of B might be changed in this construction (so
that they match those of the representation), and so B is returned.}

    require A`Group eq B`Group : "B must be a subgroup of A."; // This is not a good enough test!!
    require HasRepresentation(A) : "A must have an attached representation.";

    if HasRepresentation(B) then return B; end if;

    if Type(A`RepGroup) eq GrpPerm then
        B := SubgroupRepFromPermRep(A, B);
    elif Type(A`RepGroup) eq GrpPC then
        B := SubgroupRepFromPCRep(A, B);
    else
        error "Unimplemented for representations of type", Type(A`RepGroup);
    end if;

    B`Order := #B`RepGroup;

    return B;

end intrinsic;
