freeze;

/* Returns an indexed set of polycylic generators for given automorphism group. */
intrinsic PCGenerators ( A :: GrpAuto ) -> SetIndx
{An indexed set containing the pc-generators for A}
    require assigned A`PCGenerators : "PCGenerators attribute not set on input group";
    return A`PCGenerators;
end intrinsic;


/* Returns the size of A`PCGenerators */
intrinsic NPCgens ( A :: GrpAuto ) -> RngIntElt
{The number of pc-generators for the automorphism group A}
    require assigned A`PCGenerators : "PCGenerators attribute not set on input group";
    return #A`PCGenerators;
end intrinsic;

/* Internal function for allowing coercion using MapToAutoElt attribute */
intrinsic ApplyForAutgCoerce( f :: Any, map_to_auto_elt :: Any ) -> BoolElt, GrpAutoElt
{For internal use}

    /* check if we already have a GrpAutoElt */
    if Type(f) eq GrpAutoElt then
        return true, f;
    end if;

    try
        x := f @ map_to_auto_elt;
        return true, x;
    catch e
        return false, _;
    end try;

end intrinsic;
