freeze;

/*******************************************************************************
				Defines
*******************************************************************************/

Z := IntegerRing();

SEP := "%";

/*******************************************************************************
				Misc
*******************************************************************************/

char_to_seq := func<c | [Z!x: x in Eltseq(c)]>;

/*******************************************************************************
				File IO
*******************************************************************************/

get_ind_name := func<name | Sprintf("%o.ind", name)>;
get_rep_name := func<name, i | Sprintf("%o.r%o", name, i)>;

function get_path(fn)
    return Sprintf("%o/data/RepInt/%o", GetLibraryRoot(), fn);
end function;

procedure write_file(fn, T, comment)
    fn := get_path(fn);
    F := Open(fn, "w");
    if comment cmpne "" then
	fprintf F, "/*\n%o\n*/\n\n", comment;
    end if;
    fprintf F, "%o\n", T[1];
    for i := 2 to #T do
	fprintf F, "%o\n%o\n", SEP, T[i];
    end for;
end procedure;

function read_file_test(fn)
    fn := get_path(fn);
    l, F := ReadTest(fn);
    if not l then
	return false, _;
    end if;

    S := Split(F, SEP);
    T := <eval s: s in S>;
    return true, T;
end function;

function read_file(fn)
    l, T := read_file_test(fn);
    if not l then
	error "File not found:", get_path(fn);
    end if;

    return T;
end function;

/*******************************************************************************
				Make DB
*******************************************************************************/

intrinsic MakeRepsDB(name, G, R, C)
{Data into name}

    C := [char_to_seq(c): c in C];
    ind := <name, C>;
    ind := <C>;
    ind_name := get_ind_name(name);
    write_file(ind_name, ind, "");

    for i := 1 to #C do
	if not IsDefined(R, i) then
	    continue;
	end if;

	M := R[i, 1];
	rep_name := get_rep_name(name, i);
	L := [ActionGenerator(M, i): i in [1 .. Nagens(M)]];
	L := Sprint(L, "Magma");
	rep := <L>;
	write_file(rep_name, rep, R[i]);
    end for;

end intrinsic;

/*******************************************************************************
			    Get from DB (all or abs num)
*******************************************************************************/

intrinsic RepsDBGet(name::MonStgElt, G::Grp) -> SeqEnum, SeqEnum
{All reps for G given by name and corresponding characters}

    ind_name := get_ind_name(name);
//ind_name;
    l, I := read_file_test(ind_name);
    if not l then
	return [], [];
    end if;

    OC := Explode(I);
    R := [];
    C := [];

    for i := 1 to #OC do
	rep_name := get_rep_name(name, i);
	l, F := read_file_test(rep_name);
	if l then
	    L := Explode(F);
	    M := GModule(G, L: Check := false);
	    R[i] := M;
	    C[i] := OC[i];
	end if;
    end for;

    return R, C;

end intrinsic;

intrinsic RepsDBGet(name::MonStgElt, G::Grp, i::RngIntElt) -> ModGrp, SeqEnum
{Rep number i for "name"}

    ind_name := get_ind_name(name);
    I := read_file(ind_name);

    OC := Explode(I);
    range := [1 .. #OC];
    require i in range: "Rep number must be in", range;

    rep_name := get_rep_name(name, i);
    R := read_file(rep_name);
    L := Explode(R);
    M := GModule(G, L: Check := false);

    return M, _; // OC[i]

end intrinsic;

/*******************************************************************************
			    Get from DB (by name, char)
*******************************************************************************/

intrinsic RepsDBGet(
    name::MonStgElt, c::AlgChtrElt: G := Group(Parent(c))
) -> ModGrp
{Rep given by c for name}

    // CR := Parent(c); G := Group(CR);

    c := &+GaloisOrbit(c);

    ind_name := get_ind_name(name);
    l, I := read_file_test(ind_name);
    if not l then
	return false, "File not found";
    end if;

    OC := Explode(I);

    cms := SequenceToMultiset(Eltseq(c));
    OCMS := [SequenceToMultiset(c): c in OC];

    good_i := -1;
    for i := 1 to #OCMS do
	if cms eq OCMS[i] then
	    if good_i lt 0 then
		good_i := i;
	    else
		return false,
		    Sprintf(
			"Non-unique character multisets for %o, %o\n",
			OC[good_i], OC[i]);
	    end if;
	end if;
    end for;

    if good_i lt 0 then
	return false, "Character multiset not found in DB";
    end if;

    rep_name := get_rep_name(name, good_i);
    l, R := read_file_test(rep_name);
    if not l then
	return false, "Rep not stored";
    end if;
    L := Explode(R);
    M := GModule(G, L: Check := false);
    M`Character := c;

    return true, M;

end intrinsic;

/*******************************************************************************
			    Get from DB (by group)
*******************************************************************************/

groups_test := func<G, H, AllowEqualGroup |
    Degree(G) eq Degree(H) and Ngens(G) eq Ngens(H) and
    (AllowEqualGroup select
	(G eq H) else
	forall{i: i in [1 .. Ngens(G)] | G.i eq H.i}
    )>;

function get_name(G: AllowEqualGroup := false)
    if not IsSimple(G) then
	return false, _, _;
    end if;

    f, T := SimpleGroupName(G);
    if not f or #T gt 1 then
	return false, _, _;
    end if;
    
    t, a, b := Explode(T[1]);

    if t cmpeq "A" then
	q := a + 1;
	d := b;
	GG := PSL(q, d);
// "GG:", GG; "G:", G;
	if groups_test(G, GG, AllowEqualGroup) then
// "YES";
	    name := Sprintf("psl%o_%o", q, d);
	    return true, name, GG;
	end if;
    elif t cmpeq "2A" then
	q := a + 1;
	d := b;
	GG := PSU(q, d);
	if groups_test(G, GG, AllowEqualGroup) then
	    name := Sprintf("psu%o_%o", q, d);
	    return true, name, GG;
	end if;
    elif t cmpeq 17 then
	d := a;
	assert b eq 0;
	GG := Alt(d);
	if groups_test(G, GG, AllowEqualGroup) then
	    name := Sprintf("alt%o", d);
	    return true, name, GG;
	end if;
    elif t cmpeq 18 and b cmpeq "J1" then
	// Get standard J1 ...
    end if;

    return false, _, _;
end function;

intrinsic RepsDBGet(G::Grp, c::AlgChtrElt: AllowEqualGroup := false)
    -> BoolElt, ModGrp
{Rep given by c for G}

    require Group(Parent(c)) cmpeq G: "Group of char is not G";

    l, name, GG := get_name(G: AllowEqualGroup := AllowEqualGroup);
    if not l then
	return false, _;
    end if;

    return RepsDBGet(name, c: G := GG);

end intrinsic;

intrinsic RepsDBGet(G::Grp: AllowEqualGroup := false) -> SeqEnum, SeqEnum
{Rep given by c for G}

    l, name, GG := get_name(G: AllowEqualGroup := AllowEqualGroup);
    if not l then
	return [], [];
    end if;

    return RepsDBGet(name, GG);

end intrinsic;

/*******************************************************************************
				Small group DB
*******************************************************************************/

intrinsic RepsSmallGet(G::Grp, num::RngIntElt) -> BoolElt, SeqEnum
{Stored reps for SmallGroup(#G, num)}

    fn := Sprintf("small%o_%o", #G, num);
    l, T := read_file_test(fn);
    if not l then
	return false, _;
    end if;

    L := [GModule(G, Q): Q in T];
    return true, L;

end intrinsic;

intrinsic RepsSmallGet(G::Grp) -> BoolElt, SeqEnum
{Stored reps for SmallGroup G}

    o := #G;
    fn := Sprintf("small%o.ind", o);
    l, T := read_file_test(fn);
    if not l then
	return false, _;
    end if;

    assert #T eq 1;
    Q := T[1];

    ng := Type(G) eq GrpPC select NPCgens(G) else Ngens(G);

    for i in Q do
vprint ZMeataxe: "Try DB", o, i;
	S := SmallGroup(o, i);

	l, f := IsIsomorphic(G, S);
	if l then
	    vprintf ZMeataxe: "Match DB for SmallGroup(%o, %o)\n", o, i;
	    l, L := RepsSmallGet(S, i);
	    if not l then
		break;
	    end if;

	    if S cmpeq G and forall{i: i in [1 .. ng] | S.i eq G.i} then
//"Exact";
		return true, L;
	    end if;

	    LG := [];
	    for M in L do
		r := Representation(M);
		Append(~LG, GModule(G, [r(f(G.i)): i in [1 .. ng]]));
	    end for;
	    return true, LG;
	end if;
    end for;

    return false, _;

end intrinsic;

intrinsic MakeRepsSmall(o, num, L)
{Data into name}

    assert #Group(L[1]) eq o;

    L := <
	Sprint([ActionGenerator(M, i): i in [1 .. Nagens(M)]], "Magma"):
	M in L
    >;

    name := Sprintf("small%o_%o", o, num);
    write_file(name, L, "");

end intrinsic;
