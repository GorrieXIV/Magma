freeze;

import "DBAtlas.m": ATLASDatabase;
import "contents.m": identifyGroup;

declare attributes GrpAtlas:
    Multiplier,
    OuterAutomorphismGroup,
    ATLASDatabase;

//
// Creation: fairly sparse as yet....
//
intrinsic ATLASGroup(N::MonStgElt) -> GrpAtlas
{The ATLAS group data for name N}
    D, p := identifyGroup(N);
    require p ge 0 : "No such group in the ATLAS";

    bpos := D`DecorationInfo[p + 1]`base;
    G := InternalAtlasGroup(N, p, bpos);
    sp := Position(D`SimpleNames, D`DecorationNames[bpos + 1]);
    assert sp ne 0;
    if p eq bpos then
	AssertAttribute(G, "Order", D`SimpleInfo[sp]`order);
	G`Multiplier := D`SimpleInfo[sp]`multiplier;
	G`OuterAutomorphismGroup := D`SimpleInfo[sp]`outer;
    else
	AssertAttribute(G, "Order", D`SimpleInfo[sp]`order *
	    D`DecorationInfo[p + 1]`cfact * D`DecorationInfo[p + 1]`afact
	);
    end if;
    return G;
end intrinsic;

intrinsic AtlasGroup(N::MonStgElt) -> GrpAtlas
{The ATLAS group data for name N}
    return ATLASGroup(N);
end intrinsic;

//
// Printing
//
intrinsic Print(G::GrpAtlas, level::MonStgElt)
{}
    printf "ATLAS group of isomorphism type %o", G`ATLASName;
end intrinsic;

//
// Coercion: impossible for this type of object
//
intrinsic IsCoercible(G::GrpAtlas, S::.) -> BoolElt, Any
{}
    return false, "Illegal coercion.";
end intrinsic;

///
/// Order
///
/*
intrinsic Order(G::GrpAtlas) -> RngIntElt
{The order of an ATLAS group}
    require assigned G`Order : "Order apparently unknown";
    return G`Order;
end intrinsic;
*/

///
/// Multiplier
///
intrinsic Multiplier(G::GrpAtlas) -> RngIntElt
{The multiplicity of an ATLAS group}
    require assigned G`Multiplier : "Multiplier only stored for simple groups at present";
    return &* G`Multiplier;
end intrinsic;
