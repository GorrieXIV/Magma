freeze;

import "config.m": libroot;

names :=
{@ "12aL34", "12aL34d2a", "12bL34", "12bL34d2a", "12M22", "12M22d2",
"12U62", "214U72", "24A8", "25L52", "2A10", "2A11", "2A12", "2A13",
"2A14", "2A5", "2A6", "2A7", "2A8", "2A9", "2aM20", "2bM20", "2cM20", "2Co1",
"2F22", "2F22d2", "2F42", "2F42d2", "2F42d2i", "2G24", "2G24d2", "2G24d2i",
"2HS", "2HSd2", "2J2",
"2J2d2", "2L211", "2L213", "2L213d2", "2L217", "2L217d2", "2L219", "2L219d2i",
"2L223", "2L223d2i", "2L227", "2L229", "2L231", "2L249", "2L27", "2L27d2",
"2L27d2i", "2L34", "2L34d2a", "2M12", "2M12d2", "2M22", "2M22d2", "2O73",
"2O73d2", "2O8m3", "2O8m3d2a", "2O8p3", "2O93", "2Ru", "2S11", "2S14", "2S14i",
"2S411", "2S413", "2S417", "2S419", "2S45", "2S47", "2S47d2", "2S49",
"2S5", "2S5i", "2S62", "2S63", "2S63d2", "2S6", "2S7", "2S7i", "2Suz",
"2Suzd2", "2Sz8", "2U42", "2U42d2", "2U43D8", "2U62", "3A6", "3A7",
"3F22", "3F22d2", "3F24", "3F24d2", "3G23", "3G23d2", "3J3", "3J3d2", "3L34",
"3L34d2a", "3L37", "3L37d2", "3M22", "3M22d2", "3McL", "3McLd2", "3O73",
"3O73d2", "3ON", "3ONd2", "3S6", "3S7", "3Suz", "3Suzd2", "3U311", "3U311d2",
"3U38", "3U62", "4aL34", "4aL34d2a", "4bL34", "4bL34d2a", "4M22", "4M22d2",
"4O8p3S4", "4Sz8d3", "4U62", "53L35", "6A6", "6A7", "6L34", "6L34d2a",
"6M22", "6M22d2", "6S6", "6S7", "6Suz", "6Suzd2", "6U62", "9U43D8", "A10",
"A11", "A12", "A13", "A14", "A15", "A16", "A17", "A18", "A19", "A20", "A21",
"A5", "A6", "A6V4", "A7", "A8", "A9", "Co1", "Co2", "Co3", "E62", "E62d2",
"F22", "F22d2", "F23", "F24", "F24d2",
"F42", "F42d2",
"G23", "G23d2", "G24", "G24d2", "G25",
"He", "Hed2", "HN", "HNd2", "HS", "HSd2",
"J1", "J2", "J2d2", "J3", "J3d2", "J4",
"L211", "L211d2", "L213", "L213d2", "L216", "L216d2", "L216d4",
"L217", "L217d2", "L219", "L219d2", "L223", "L223d2", "L227", "L229", "L231",
"L231d2", "L232", "L232d5", "L249", "L27", "L27d2", "L28", "L28d3", "L311",
"L313", "L33", "L33d2", "L34", "L34d2a", "L35", "L35d2", "L37", "L37d2",
"L38", "L38d2", "L38d3", "L38d6", "L43", "L44", "L45", "L52", "L52d2",
"L62", "L62d2", "L72", "L72d2",
"Ly", "M10", "M11", "M12", "M12d2", "M20", "M22", "M22d2", "M23", "M24",
"McL", "McLd2",
"O10m2", "O10m2d2", "O10p2", "O10p2d2", "O73", "O73d2", "O8m2", "O8m2d2",
"O8m3", "O8m3d2a", "O8m3d2c", "O8m3D8", "O8m3V4", "O8p2", "O8p3", "O8p3S4",
"O93", "O93d2",
"ON", "ONd2", "ONd4",
"PGL29", "R27", "R27d3", "Ru", "S102",
"S10", "S11", "S12", "S13", "S14", "S15", "S16", "S17", "S18", "S19", "S20",
"S21",
"S411", "S413", "S417", "S419", "S44", "S44d2", "S44d4", "S45", "S45d2", "S47",
"S47d2", "S49", "S5", "S62", "S63", "S63d2", "S65", "S6", "S7", "S82", "S83",
"S8", "S9", "Suz", "Suzd2", "Sz32", "Sz32d5", "Sz8", "Sz8d3", "TD42", "TD42d3",
"TD43", "TE62", "TE62d2", "TF42", "TF42d2", "Th", "U311", "U311d2", "U313",
"U316", "U33", "U33d2", "U34", "U34d2", "U34d4", "U35", "U35d2", "U37",
"U38", "U38d2", "U38d3a", "U38d3b", "U38d3c", "U38d6", "U38E9", "U38S3",
"U38S3x3", "U39", "U42", "U42d2", "U43D8", "U43", "U44", "U45", "U52",
"U52d2", "U53", "U54", "U62", "U62d2", "U62S3", "U63", "U72", "U82" @};

intrinsic CharacterTable(N::MonStgElt) -> SeqEnum[AlgChtrElt]
{The character table of the ATLAS group named by N, without a group attached}
    require N in names: "Character table not stored";
    file := libroot() cat "ChtrTables/" cat N cat ".ct";
    X := eval Read(file);
    return X;
end intrinsic;

intrinsic CharacterTable(G::GrpAtlas) -> SeqEnum[AlgChtrElt]
{The character table of the ATLAS group G, without a group attached}
    N := Name(G);
    require N in names: "Character table not stored";
    file := libroot() cat "ChtrTables/" cat N cat ".ct";
    X := eval Read(file);
    return X;
end intrinsic;

intrinsic CharacterTableNames() -> SetEnum[MonStgElt]
{The names of ATLAS groups with stored character tables}
    return names;
end intrinsic;

intrinsic HasCharacterTable(G::GrpAtlas) -> BoolElt
{Whether the group G has stored character table available}
    return Name(G) in names;
end intrinsic;
