freeze;

declare attributes DBAtlas:
    MaxSubInfo;

declare attributes GrpAtlas:
    MaxSubs;

import "DBAtlas.m": ATLASDatabase;
import "maxinfo.m" : maxinfo;
import "filesinfo.m" : ATLASFileName;
import "files.m" : FilePosRange;
import "config.m" : libroot;

function ATLASwithMaxSubInfo()
    D := ATLASDatabase();
    if not assigned D`MaxSubInfo then
	D`MaxSubInfo := maxinfo();
    end if;
    return D;
end function;

procedure GroupCacheMaxSubs(G)
    if not assigned G`MaxSubs then
	D := ATLASwithMaxSubInfo();
	G`MaxSubs := [ x: x in D`MaxSubInfo | x[1] eq InternalId(G) ];
    end if;
end procedure;

all := func<x | true>;

intrinsic MaxSubKeys(G::GrpAtlas: Select := all) -> SeqEnum
{}
    GroupCacheMaxSubs(G);
    return [x: x in G`MaxSubs | Select(x)];
end intrinsic;

intrinsic NMaxSubs(G::GrpAtlas: Select := all) -> RngIntElt
{The number of maximal subgroups available for ATLAS group G satisfying
selection criterion Select}
    GroupCacheMaxSubs(G);
    return #[x: x in G`MaxSubs | Select(x)];
end intrinsic;

ReadAtlasSLP := function(filename, s, e)
    F := LibFileOpen(libroot() cat filename cat ".dat", "rb");
    Seek(F, s, 0);
    m := 1024;
    n := e - s;
    buf := [];
    state := "inp";
    ngens := 0;
    pos := 1;
    outputs := [];
    repeat
	l := Min(n, m);
	n -:= l;
	buf cat:= ReadBytes(F, l);
	// add 1 because all commands take at least one argument
	while pos + 1 lt #buf do

	    if buf[pos] ne 1 and state eq "inp" then
		B<[x]> := BlackboxGroup(ngens);
		state := "body";
	    end if;

	    case buf[pos]:
	    when 1:	// inp
		error if state ne "inp", "Bargled SLP data";
		ninputs := buf[pos + 1];
		if pos + ninputs + 1 gt #buf then break; end if;
		pos +:= 2;
		assert forall{i: i in [1 .. ninputs] | buf[pos+i-1] eq ngens+i};
		ngens +:= ninputs;
		pos +:= ninputs;
	    when 2:	// oup
		state := "oup";
		noutputs := buf[pos + 1];
		if pos + noutputs + 1 gt #buf then break; end if;
		pos +:= 2;
		outputs cat:= [buf[pos + i]: i in [0 .. noutputs - 1]];
		pos +:= noutputs;
	    when 3:	// mu
		error if state ne "body", "Bargled SLP data";
		if pos + 4 gt #buf then break; end if;
		x[buf[pos + 3]] := x[buf[pos + 1]] * x[buf[pos + 2]];
		pos +:= 4;
	    when 4:	// iv
		error if state ne "body", "Bargled SLP data";
		if pos + 3 gt #buf then break; end if;
		x[buf[pos + 2]] := x[buf[pos + 1]]^-1;
		pos +:= 3;
	    when 5:	// pwr
		error if state ne "body", "Bargled SLP data";
		if pos + 4 gt #buf then break; end if;
		x[buf[pos + 3]] := x[buf[pos + 2]]^buf[pos + 1];
		pos +:= 4;
	    when 6:	// cj
		error if state ne "body", "Bargled SLP data";
		if pos + 4 gt #buf then break; end if;
		x[buf[pos + 3]] := x[buf[pos + 1]] ^ x[buf[pos + 2]];
		pos +:= 4;
	    when 7:	// cjr
		error if state ne "body", "Bargled SLP data";
		if pos + 3 gt #buf then break; end if;
		x[buf[pos + 1]] := x[buf[pos + 1]] ^ x[buf[pos + 2]];
		pos +:= 3;
	    when 8:	// com
		error if state ne "body", "Bargled SLP data";
		if pos + 4 gt #buf then break; end if;
		x[buf[pos + 3]] := (x[buf[pos + 1]], x[buf[pos + 2]]);
		pos +:= 4;
	    when 9:	// cp
		error if state ne "body", "Bargled SLP data";
		if pos + 3 gt #buf then break; end if;
		x[buf[pos + 2]] := x[buf[pos + 1]];
		pos +:= 3;
	    when 10:	// chor
		error "chor operation found; not handled";
	    when 11:	// pwr with large exponent
		error if state ne "body", "Bargled SLP data";
		if pos + 5 gt #buf then break; end if;
		expt := Seqint(buf[[pos+1..pos+2]], 256);
		x[buf[pos + 4]] := x[buf[pos + 3]]^expt;
		pos +:= 5;
	    else
		error "Unknown operation found";
	    end case;
	end while;
	buf := buf[pos..#buf];
	pos := 1;
    until n eq 0;
    assert #buf eq 0;
    if state eq "inp" then
	B<[x]> := BlackboxGroup(Max(ngens, 2));
	state := "body";
    end if;
    if state eq "oup" then
	return [x[i]: i in outputs];
    end if;
    // the default...
    return [x[1], x[2]];
end function;

fileId := func<x | x[#x - 1]>;
filePos := func<x | x[#x]>;

intrinsic MaxSub(K::Tup) -> SeqEnum
{The matrix representation designated by database key K}
    return ReadAtlasSLP(F, r[1], r[2])
	    where r is FilePosRange(fileId(K), filePos(K))
	    where F is ATLASFileName(fileId(K));
end intrinsic;
