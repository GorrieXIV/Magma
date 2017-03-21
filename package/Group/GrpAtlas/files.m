freeze;

declare attributes DBAtlas :
    FileIndexes;

import "filesinfo.m": ATLASFileName;
import "DBAtlas.m": ATLASDatabase;
import "config.m": libroot;

function ATLASwithIndexInfo()
    D := ATLASDatabase();
    if not assigned D`FileIndexes then
	D`FileIndexes := [];
    end if;
    return D;
end function;

function ReadIndex(name)
    F := LibFileOpen(libroot() cat name cat ".ind", "rb");
    Q := [];
    bufsz := 1024;
    repeat
	buf := ReadBytes(F, bufsz);
	assert #buf mod 4 eq 0;
	Q cat:= [Seqint(buf[i .. i + 3], 256): i in [1 .. #buf by 4]];
    until #buf lt bufsz;
    return Q;
end function;

function GetIndex(id)
    D := ATLASwithIndexInfo();
    if not IsDefined(D`FileIndexes, id + 1) then
	D`FileIndexes[id + 1] := ReadIndex(ATLASFileName(id));
    end if;
    return D`FileIndexes[id + 1];
end function;

function FilePosRange(id, pos)
    Idx := GetIndex(id);
    if pos + 2 gt #Idx then
	return <0, 0>;
    end if;
    return <Idx[pos + 1], Idx[pos + 2]>;
end function;
