freeze;

declare type DBAtlas;

declare attributes DBAtlas:
    IndexFileNames, IndexFileAddresses;

//
// Creation
//
ATLASCreate := function()
    D := New(DBAtlas);
    D`IndexFileNames := {@ @};
    D`IndexFileAddresses := [];
    return D;
end function;

//
// Printing
//
intrinsic Print(D::DBAtlas, level::MonStgElt)
{}
    printf "ATLAS database";
end intrinsic;

//
// Coercion: impossible for this type of object
//

ATLAS := ATLASCreate();

function ATLASDatabase()
    return ATLAS;
end function;
