freeze;

import "DBAtlas.m":
    ATLASDatabase;

import "groups.m":
    decorationNames,
    decorationInfo,
    simpleNames,
    simpleInfo;

declare attributes DBAtlas:
    DecorationNames,
    DecorationInfo,
    SimpleNames,
    SimpleInfo;

function ATLASwithBasicInfo()
    D := ATLASDatabase();
    if not assigned D`DecorationNames then
	D`DecorationNames := decorationNames();
	D`DecorationInfo := decorationInfo();
	D`SimpleNames := simpleNames();
	D`SimpleInfo := simpleInfo();
    end if;
    return D;
end function;

function identifyGroup(N)
    D := ATLASwithBasicInfo();
    p := Position(D`DecorationNames, N) - 1;
    return D, p;
end function;

intrinsic ATLASGroupNames() -> SetIndx
{A sequence of all the ATLAS group names available}
    return Sort(decorationNames());
end intrinsic;

intrinsic AtlasGroupNames() -> SetIndx
{A sequence of all the ATLAS group names available}
    return ATLASGroupNames();
end intrinsic;
