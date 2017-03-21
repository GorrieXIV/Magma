freeze;

declare type DBAtlasKeyMatRep;

declare attributes DBAtlasKeyMatRep:
    group,
    characteristic, exponent,
    degree,
    variant,
    generatingSet, ngens,
    fileid, position;

declare type DBAtlasKeyPermRep;

declare attributes DBAtlasKeyPermRep:
    group,
    degree,
    variant,
    generatingSet, ngens,
    fileid, position;

function matKey(G, x)
    K := New(DBAtlasKeyMatRep);
    K`group := G;
    K`characteristic := x[2];
    K`exponent := x[3];
    K`degree := x[4];
    K`variant := x[5];
    K`generatingSet := x[6];
    K`ngens := x[7];
    K`fileid := x[8];
    K`position := x[9];
    return K;
end function;

fileId := function(x)
    return x`fileid;
end function;

filePos := function(x)
    return x`position;
end function;

intrinsic Group(K::DBAtlasKeyMatRep) -> GrpAtlas
{The group which the designated matrix representation represents}
    return K`group;
end intrinsic;

intrinsic FieldCharacteristic(K::DBAtlasKeyMatRep) -> RngIntElt
{The characteristic of the field of the designated matrix representation}
    return K`characteristic;
end intrinsic;

intrinsic Characteristic(K::DBAtlasKeyMatRep) -> RngIntElt
{The characteristic of the field of the designated matrix representation}
    return K`characteristic;
end intrinsic;

intrinsic FieldExponent(K::DBAtlasKeyMatRep) -> RngIntElt
{The exponent of the field of the designated matrix representation}
    return K`exponent;
end intrinsic;

intrinsic FieldSize(K::DBAtlasKeyMatRep) -> RngIntElt
{The size of the field of the designated matrix representation}
    return K`characteristic ^ K`exponent;
end intrinsic;

intrinsic Field(K::DBAtlasKeyMatRep) -> FldFin
{The field of the designated matrix representation}
    return GF(K`characteristic, K`exponent);
end intrinsic;

intrinsic Degree(K::DBAtlasKeyMatRep) -> RngIntElt
{The degree of the designated matrix representation}
    return K`degree;
end intrinsic;

intrinsic Variant(K::DBAtlasKeyMatRep) -> MonStgElt
{The name of this representation (or string of length 0 if it has none)}
    return K`variant;
end intrinsic;

intrinsic GeneratingSet(K::DBAtlasKeyMatRep) -> RngIntElt
{The generating set used by the designated matrix representation.
A value of 0 indicates a non-standard generating set.}
    return K`generatingSet;
end intrinsic;

intrinsic Ngens(K::DBAtlasKeyMatRep) -> RngIntElt
{The number of generators of the designated matrix representation}
    return K`ngens;
end intrinsic;

intrinsic Print(K::DBAtlasKeyMatRep, level::MonStgElt)
{}
    printf "Matrix rep of degree %o over GF(%o)", Degree(K), FieldSize(K);
    if Variant(K) ne "" then
	printf " named %o", Variant(K);
    end if;
    if level eq "Maximal" then
	if GeneratingSet(K) ne 0 then
	    printf " on std gen set #%o", GeneratingSet(K);
	else
	    printf " with %o (non-std) gens", Ngens(K);
	end if;
    end if;
end intrinsic;

intrinsic IsCoercible(K::DBAtlasKeyMatRep, S::.) -> BoolElt, Any
{}
    return false, "Illegal coercion";
end intrinsic;

function permKey(G, x)
    K := New(DBAtlasKeyPermRep);
    K`group := G;
    K`degree := x[2];
    K`variant := x[3];
    K`generatingSet := x[4];
    K`ngens := x[5];
    K`fileid := x[6];
    K`position := x[7];
    return K;
end function;

intrinsic Group(K::DBAtlasKeyPermRep) -> GrpAtlas
{The group which the designated permutation representation represents}
    return K`group;
end intrinsic;

intrinsic Degree(K::DBAtlasKeyPermRep) -> RngIntElt
{The degree of the designated permutation representation}
    return K`degree;
end intrinsic;

intrinsic Variant(K::DBAtlasKeyPermRep) -> MonStgElt
{The name of this representation (or string of length 0 if it has none)}
    return K`variant;
end intrinsic;

intrinsic GeneratingSet(K::DBAtlasKeyPermRep) -> RngIntElt
{The generating set used by the designated permutation representation.
A value of 0 indicates a non-standard generating set.}
    return K`generatingSet;
end intrinsic;

intrinsic Ngens(K::DBAtlasKeyPermRep) -> RngIntElt
{The number of generators of the designated permutation representation}
    return K`ngens;
end intrinsic;

intrinsic Print(K::DBAtlasKeyPermRep, level::MonStgElt)
{}
    printf "Perm rep of degree %o", Degree(K);
    if Variant(K) ne "" then
	printf " named %o", Variant(K);
    end if;
    if level eq "Maximal" then
	if GeneratingSet(K) ne 0 then
	    printf " on std gen set #%o", GeneratingSet(K);
	else
	    printf " with %o (non-std) gens", Ngens(K);
	end if;
    end if;
end intrinsic;

intrinsic IsCoercible(K::DBAtlasKeyPermRep, S::.) -> BoolElt, Any
{}
    return false, "Illegal coercion";
end intrinsic;
