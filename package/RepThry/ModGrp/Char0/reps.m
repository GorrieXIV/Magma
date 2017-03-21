freeze;

/*
Computing irreducible integral modules of finite groups.
Allan Steel, 2001 -- 2009.
*/

/*******************************************************************************
			    Direct parameters
*******************************************************************************/

DEFAULT_PermDegreeLimit := 50000;
DEFAULT_PermDegreeLimit := 10^7;
DIRECT_REP_LIMIT := 20;

/*******************************************************************************
				Verbose
*******************************************************************************/

declare attributes ModRng: IsIrreducible, SchurIndex;

import "char.m": char_is_multiple;
import "clean.m": Nicify, ModuleMaxNorm;
import "meataxe.m": get_irr_char_mult;
import "cond.m": ccond, CCOND_PERM, CCOND_TENS, CCOND_IND;

/*******************************************************************************
				Subgroups defs
*******************************************************************************/

SUBGROUPS_DEFAULT := "default";
SUBGROUPS_NEVER := false;
SUBGROUPS_ALWAYS := true;
SUBGROUPS_DONE := "done";

SUBGROUPS_TRY_ALL_DIM := 100;

SUBGROUPS_MAX_ORDER_COUNT := 10;
PERM_REP_MAX_ORDER_COUNT := 20;

/*******************************************************************************
				Defines
*******************************************************************************/

Z := IntegerRing();
Q := RationalField();
is_Z := func<R | R cmpeq Z>;

AddAttribute(ModGrp, "Character");
AddAttribute(ModRng, "Character");

/*******************************************************************************
                                Characters
*******************************************************************************/

num_fixed_pts := func<g|Degree(Parent(g)) - Degree(g)>;

function MySchurIndex(c)
    try
	si := SchurIndex(c);
	return si;
    catch e
	"SchurIndex fail";
	G := Group(Parent(c));
	printf "G := %m;\n", G;
	"c:", c;
	"c Magma:", c: Magma;
	"CT index:", Index(CharacterTable(G), c);
	error "FAIL";
    end try;
end function;

/*******************************************************************************
                                Subgroups
*******************************************************************************/

sort_subgroup_seq := proc<~Q | Sort(~Q, func<G, H | #H - #G>)>;

procedure include_subgroups(~Q, S: Overlap := false)
    vprintf ZReps: "Include %o more subgroup(s) (currently %o)\n", #S, #Q;
    if Overlap then
        Q := Setseq(Set(Q) join Set(S));
    else
        Q cat:= S;
    end if;
    sort_subgroup_seq(~Q);
    vprintf ZReps: "Now have %o subgroup(s)\n", #Q;
end procedure;

function filter_subgroups_repetition(L, max_order_count)
    vprintf ZReps: "Filter out repetition for %o subgroup(s) (max number %o)\n",
        #L, max_order_count;
    LL := [];
    count := {**};
    for S in L do
        o := #S;
        if Multiplicity(count, o) lt max_order_count then
            Include(~count, o);
            Append(~LL, S);
        end if;
    end for;
    return LL;
end function;

/*******************************************************************************
				Clifford
*******************************************************************************/

Clifford_elab := function(G, N)
    M := GModule(G,N);
    rho := Representation(M);
    A := ActionGroup(M);
    D := sub<Generic(A)|[Transpose(x):x in Generators(A)]>;
    f := hom<G->D | [Transpose((G.-i)@rho):i in [1..Ngens(G)]]>;
    orbs := LineOrbits(D);
    stabs := [Stabilizer(D, Rep(x))@@f: x in orbs];
    return stabs;
end function;

/*******************************************************************************
				Queue Sort
*******************************************************************************/

procedure SortViaMerge(~Q1, ~Q2, cmp)
    // Q1 assumed sorted; Q2 not assumed sorted; append Q2 to Q1 and sort

    Sort(~Q2, cmp);
    N := [];
    i1 := 1;
    i2 := 1;

    while true do

	if i1 gt #Q1 then
	    N cat:= Q2[i2 .. #Q2];
	    break;
	end if;

	if i2 gt #Q2 then
	    N cat:= Q1[i1 .. #Q1];
	    break;
	end if;

	c := cmp(Q1[i1], Q2[i2]);
	if c le 0 then
	    Append(~N, Q1[i1]);
	    i1 +:= 1;
	else
	    Append(~N, Q2[i2]);
	    i2 +:= 1;
	end if;

    end while;

    Q1 := N;
    Q2 := [];
end procedure;

/*******************************************************************************
			    Reduce group
*******************************************************************************/

rfmt := recformat<MapChar, ImapChar, ImapModule>;

function ReduceGroup(G)
return false, _, _;
    if Type(G) eq GrpPC then
	return false, _, _;
    end if;

    if IsSoluble(G) then
	vprintf ZReps: "Move soluble group to PC group (order %o)\n", #G;
	GG, f := PCGroup(G);

	function ImapModule(M)
	    rep := Representation(M);
	    MG := GModule(
		G, [rep(f(G.i)): i in [1 .. Ngens(G)]]: Check := false
	    );
	    return MG;
	end function;

    elif Type(G) eq GrpPerm then

	GG, f := DegreeReduction(G);
	d := Degree(G);
	dd := Degree(G);
	if dd ge d/2 then
	    return false, _, _;
	end if;

	vprintf ZReps: "Move perm group from degree %o to degree %o\n", d, dd;

	function ImapModule(M)
	    MG := GModule(G, ActionGenerators(M));
	    return MG;
	end function;

    else
	// matg
	return false, _, _;
    end if;

    fi := f^-1;

    function MapChar(c)
	return CharacterOfImage(c, f, GG);
    end function;
    function ImapChar(c)
	return CharacterOfImage(c, fi, G);
    end function;

    return true, GG, rec<rfmt |
	MapChar := MapChar,
	ImapChar := ImapChar,
	ImapModule := ImapModule
    >;
end function;

/*******************************************************************************
			Main Internal Function
*******************************************************************************/

intrinsic InternalIrreducibleIntegralModules(
    G::Grp:
	MaxDegree := 0,
	Characters := {},
	CharacterDegrees := {},
	PermDegreeLimit := -1,
	IndexLimit := -1,
	InitialIndex := -1,
	MinPermDegree := 1,
	TensorLimit := 0,
	DirectMeataxeLimit := 300,
	Blackbox := false,
	UseInduction := true,
	IndRec := false,
	UseDegreeReduction := true,
	InductionLimit := 1,
	InductionIndices := {},
	IndIndexLimit := Min(#G, 10^6),
	NewInd := true,
	UseSoluble := false,
	UseSolubleInduction := false,
	AllSubgroups := SUBGROUPS_DEFAULT,
	UseSubgroups := true,
	UseDixon := not Blackbox,
	DixonCharLimit := 40,
	DixonTryDim := 10000,
	DixonSplitLimit := 100,
	TryAll := false,
	GivenReps := [],
	LI := [],
	UseLI := false,
	CleanLimit := 100,
	NoDumpChars := false,
	CondTarget := 0,
	UseDB := false,
	UseSmallDB := true,
	AllowEqualGroup := false,
	NewLIS := false,
	InitialDixonLimit := 0,
	TENSOR_RATIO := 2.8,
	IND_RATIO := 5,
	DynTraces := true,
	EasyLimit := 5 , // 100,
	DumpReps := false,
	CliffordN := 0,
	IND_SUBGROUP_CLASSES_LIMIT := 1000,
	AllowDenoms := false,
	TensorSearch := false,
	WeakTensorSearch := false,
	ModularPrime := 0,
	Reduce,
	UseExt := false
) -> [], [], [], []
{Irreducible integral modules of G, with extended information in
tuples, together with the rational character table of G}

    vprintf ZReps: "Compute Reps of group of order %o\n", #G;

    /***************************************************************************
	Reduction
    ***************************************************************************/

    if AllSubgroups cmpeq 0 then
	AllSubgroups := SUBGROUPS_DEFAULT;
    end if;

    OG := G;
    G_reduced := false;
    GGi := 0;
    CharactersQ := 0;
    OCharactersQ := 0;
    OCharacters := Characters;

    if 1 eq 1 and Reduce then
	G_reduced, GG, GGi := ReduceGroup(G);
	if G_reduced then
	    G := GG;
	    OCharactersQ := {@ c: c in OCharacters @};

	    if #Characters gt 0 then
		vprintf ZReps: "Map %o character(s) to reduced group\n",
		    #Characters;
		vtime ZReps:
		    CharactersQ := {@ GGi`MapChar(c): c in OCharactersQ @};

		Characters := Set(CharactersQ);
	    end if;
	else
	    GG := 0;
	    GGi := 0;
	end if;
    end if;

    /***************************************************************************
	Tensor search
    ***************************************************************************/

    if TensorSearch or WeakTensorSearch and #Characters gt 0 then
	vprint ZReps: "Get rational characters";
	vtime ZReps: rats, ratsi := RationalCharacterTable(G);

	nc := {};
	for c in Characters do
	    "Try RationalTensorSearch for:", c;
	    T := RationalTensorSearch(c);
	    U := T[1];
	    "Got tensor product:", U;
	    Include(~nc, rats[U[1]]);
	    Include(~nc, rats[U[2]]);
	end for;
	Characters := Set(Characters) join nc;
    end if;

    /***************************************************************************
	Chars
    ***************************************************************************/

    WantChars := Characters;
    WantCharDegrees := Set(CharacterDegrees);

    /***************************************************************************
	Option setup
    ***************************************************************************/

    if not UseDixon then
	DixonTryDim := 10^10;
    end if;

    if PermDegreeLimit lt 0 then
	PermDegreeLimit := Max(DEFAULT_PermDegreeLimit, InitialIndex);
    end if;
    if IndexLimit lt 0 then
	IndexLimit := PermDegreeLimit;
    end if;

    LI_max_index := 0;
    if InitialIndex lt 0 then
	InitialIndex := Min(100, IndexLimit);
    end if;
    if #InductionIndices gt 0 then
	InitialIndex := Max(InitialIndex, Max(InductionIndices));
    end if;
    if #LI gt 0 then
	LI_max_index := Max([Index(G, H): H in LI]);
	InitialIndex := LI_max_index;
    end if;

    Z := IntegerRing();
    EXT_SQ := "extsq";
    SYM_SQ := "symsq";
    MOD := "mod";
    PERM := "perm";
    K_TENS := "tens";
    K_TENS_POW := "tens_pow";
    K_IND := "ind";

    TOTAL_TIME := Cputime();

    /***************************************************************************
	Group setup
    ***************************************************************************/

    M := "none";

    if Type(OG) eq ModGrp then
	if BaseRing(OG) cmpeq Z then
	    M := OG;
	end if;
	G := Group(OG);
    end if;

    //require false: "Unsupported group type";

//vprint ZReps: G: Magma;

    /***************************************************************************
	Character setup
    ***************************************************************************/

    vprint ZReps: "Get classes";
    vtime ZReps: num_cl := #Classes(G);
    vprintf ZReps: "%o classes\n", num_cl;

    vprint ZReps: "Get character table";
    vtime ZReps: full_char_table := CharacterTable(G);

    vprint ZReps: "Get rational characters";
    vtime ZReps: rats, ratsi := RationalCharacterTable(G);

    rats_deg := [ Z | Degree(c): c in rats ];
    rats_iset := {@ c: c in rats @};

    CR := CharacterRing(G);
    charz := func<c | Vector(Z, Eltseq(c))>;
    charz_to_char := func<c | CR ! Eltseq(c)>;
    seq_to_charz := func<q | Vector(Z, q)>;
    ratsz := [charz(c): c in rats];
    ratsz_iset := {@ v: v in ratsz @};
    GetChar := func<M | Char(M: IrrChars := rats)>;

    vprint ZReps: "Rational character degrees:", {* Degree(c): c in rats *};

    if not NoDumpChars then
	//vprint ZReps: "Rational chars:", rats;
    end if;

    d := #rats[1];
    char_seq := func<c | [c[i]: i in [1 .. #c]]>;

    USE_HERMITE := true;
    if USE_HERMITE then
	vprint ZReps: "Set up rats matrix space";
	vtime ZReps: rats_mat_space := RationalCharacterTableRSpace(G);
	rats_mat := 0;
    else
	rats_mat := Matrix(Z, d, &cat[char_seq(c): c in rats]);
    end if;

    function decomp_char(c)
	if USE_HERMITE then
	    D := Coordinates(rats_mat_space, Vector(Z, char_seq(c)));
	elif true then
	    D, ker := Solution(rats_mat, Vector(Z, char_seq(c)));
	    assert Dimension(ker) eq 0;
	else
	    D := Decomposition(rats, c);
	end if;
	return [<i, Z!D[i]>: i in [1 .. #rats] | D[i] ne 0];
    end function;

    if MaxDegree ne 0 and MaxDegree lt Degree(rats[#rats]) then
	DS := { 1 .. MaxDegree };
	if #WantChars gt 0 then
	    ;
	elif WantCharDegrees ne {} then
	    WantCharDegrees := WantCharDegrees meet DS;
	else
	    WantCharDegrees := DS;
	end if;
    end if;

    if WantCharDegrees ne {} then
	WantChars := {c: c in rats | Degree(c) in WantCharDegrees};
	vprint ZReps: "Wanted character degrees:", WantCharDegrees;
	vprint ZReps: "Found wanted rational characters:", WantChars;
    end if;

    WantCharsCase := #WantChars gt 0;
    if WantCharsCase then
	// assumes given irred chars:
	WantChars := {decomp_char(&+GaloisOrbit(c))[1, 1]: c in WantChars};
	vprint ZReps: "WantChars indices:", WantChars;
    end if;

    /***************************************************************************
	Schur index setup
    ***************************************************************************/

    rats_schur_indices := [];

    /*
    rats_schur_indices :=
	[MySchurIndex(full_char_table[ratsi[i, 1]]): i in [1 .. #rats]];
    */
    // "rats:", rats; "rats_schur_indices:", rats_schur_indices;

    procedure get_si_seq(~rats_schur_indices, I, ~SI)
	SI := [];
	for i in I do
	    if IsDefined(rats_schur_indices, i) then
		si := rats_schur_indices[i];
	    else
		si := MySchurIndex(full_char_table[ratsi[i, 1]]);
		rats_schur_indices[i] := si;
	    end if;
	    Append(~SI, si);
	end for;
    end procedure;

    procedure get_si(~rats_schur_indices, i, ~si)
	get_si_seq(~rats_schur_indices, [i], ~SI);
	si := SI[1];
    end procedure;

    /**************************************************************************/

    I := [];
    IC := [];
    IS := [];
    history := [];

    function get_II(I, IS, history)
	II := [];
	count := 0;
	for i := 1 to #rats do
	    if not IsDefined(I, i) then
		continue;
	    end if;

	    count +:= 1;
	    OM := I[i];
	    if Group(OM) cmpne OG then
		vprintf ZReps: "Map module of dim %o back to original group\n",
		    Dimension(OM);
		vtime ZReps: M := GGi`ImapModule(OM);
	    else
		M := OM;
	    end if;
	    if assigned OM`SchurIndex then
		assert OM`SchurIndex eq IS[i];
	    end if;
	    M`SchurIndex := IS[i];
	    M`IsIrreducible := true;
	    c := rats[i] * IS[i];
	    if assigned OM`Character then
		assert OM`Character eq c;
	    end if;
	    if Group(OM) cmpne OG then
		if Characters eq { rats[i] } then
		    assert #OCharacters eq 1;
		    c := Rep(OCharacters) * IS[i];
		    vprintf ZReps: "Use original character\n";
		else
		    vprintf ZReps: "Map character back to original group\n";
		    vtime ZReps: c := GGi`ImapChar(c);
		end if;
		assert Group(Parent(c)) eq OG;
	    end if;
	    M`Character := c;
	    II[i] := <M, IS[i], history[i]>;

	end for;

	return II, count;
    end function;

    /***************************************************************************
	Database
    ***************************************************************************/

    if UseDB then
	count := 0;
	if WantCharsCase then
	    want := #WantChars;
	    for i in WantChars do
// "want", i;
		c := rats[i];
		l, DBM := RepsDBGet(G, c: AllowEqualGroup);
		if l then
		    I[i] := DBM;
		    IC[i] := c;
		    IS[i] := ExactQuotient(Dimension(DBM), Degree(c));
		    history[i] := "DB";
		    count +:= 1;
		else
		    if assigned DBM then
			reason := DBM;
		    else
			reason := "";
		    end if;
		    vprintf ZReps: "DB lookup failed (%o) for degree %o\n",
			reason, Degree(c);
		end if;
	    end for;
	else
	    want := #rats;
	    R, C := RepsDBGet(G: AllowEqualGroup);

// "Got R:", R; "Got C:", C;

	    CMS := [SequenceToMultiset(c): c in C];

	    for i := 1 to #rats do
		c := rats[i];
		cms := SequenceToMultiset(Eltseq(c));
		J := [j: j in [1 .. #CMS] | CMS[j] eq cms];
		if #J eq 1 then
		    j := J[1];
		    if IsDefined(R, j) then
			I[i] := R[j];
			IC[i] := c;
			IS[i] := ExactQuotient(Dimension(I[i]), Degree(c));
			history[i] := "DB";
			count +:= 1;
		    end if;
		end if;
	    end for;

// "Now:"; count; want; I;
	    if count eq 0 then
		vprintf ZReps: "DB lookup failed\n";
	    end if;
	end if;

	if count eq want then
	    II, c := get_II(I, IS, history);
	    return II, rats, ratsi;
	end if;
    end if;

    /*
    This is to try to work out possible quick way via tensor, but
    is v slow with many rat chars.

    analyze_tensor := 0 eq 1 or WantCharsCase;
    if analyze_tensor then
	tlist := [[]: i in [1 .. #rats]];
	"Analyze tensor", #rats; time
	for i := 2 to #rats do
	    for j := 2 to i do
		t := rats[i]*rats[j];
		D := decomp_char(t);
		printf "%o, %o: %o\n", i, j, D;
		for t in D do
		    k := t[1];
		    if k ne i and k ne j then
			Append(~tlist[k], <i, j, rats_deg[i], rats_deg[j]>);
		    end if;
		end for;
	    end for;
	end for;
	//tlist;
    end if;
    */

    /***************************************************************************
	Include character into queue
    ***************************************************************************/

    Qchars := {};
    procedure include_char_Q(~Q_new, ~Qchars, c, t, l, r)
	if c in Qchars then
//"Skip char", c;
	    return;
	end if;
	Include(~Qchars, c);
	DD := decomp_char(c);
	//"Decomposed char:", DD;
	Append(~Q_new, <Degree(c), t, l, r, DD>);
//"Include Q_new:", <Degree(c), t, l, r, DD>;
//"Inc", c;
    end procedure;

    procedure include_mod(
	~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
	~extra, ~extrac, ~extras, ~WantChars,
	M, schur, c, h
    )
    /*
    c is character of M (so Schur index included in c.
    */

	d := Dimension(M);
	assert Degree(c) eq d;

	oc := c;
	cz := charz(c);
	ocz := cz;
	if schur eq 0 then
	    error "DIE now!";
	    vprint ZReps: "UNKNOWN SCHUR INDEX";
	    ind := 0;
	    for i := 1 to #rats do
		cc := rats[i];
		si := d div Z!Degree(cc);
		if si*cc eq c then
		    vprint ZReps: "POSSIBLE SCHUR INDEX", si;
		    ind := i;
		    c := cc;
		    schur := si;
		    break;
		end if;
	    end for;
	else
	    if schur gt 1 then
		vprint ZReps: "SCHUR INDEX", schur;
		//cq := [Z!c[i]: i in [1 .. #c]];
		cq := [ExactQuotient(cz[j], schur): j in [1 .. num_cl]];
		cz := seq_to_charz(cq);
		c := CR!cq;
		vprint ZReps: "Irreducible character:", c;
	    end if;
	    ind := Index(ratsz_iset, cz);
	end if;

	if ind eq 0 then
	    vprint ZReps: "CHARACTER NOT FOUND!!!";
//M: Magma;
c;
"schur:", schur;
error "ZReps: CHARACTER NOT FOUND; DIE";
	    if c notin extrac then
		Append(~extra, M);
		Include(~extrac, c);
		Append(~extras, schur);
	    end if;
	    return;
	end if;

	if IsDefined(I, ind) then
	    //vprint ZReps: "Already seen!";
	    return;
	end if;

	vprintf ZReps: "INSERT module of dim %o, index %o\n", d, ind;
	vprintf ZReps: "Irreducible character (including Schur index %o): %o\n",
	    schur, c;

	Exclude(~WantChars, ind);

	//vprint ZReps: "NEW CHAR OF DEG", d;
	if DumpReps then
	    M: Maximal;
	end if;

	I[ind] := M;
	IC[ind] := c;
	IS[ind] := schur;
	history[ind] := Sprint(h);

	if IsOne(c) then
	    return;
	end if;

	//printf "Now: M: %o, c: %o, schur: %o, d: %o\n", M, c, schur, d;

	L := [i: i in [1 .. #rats] | IsDefined(I, i)];
	SC := SymmetricComponents(oc, 2);
	ext_c := rep{x: x in SC | Degree(x) eq Binomial(d, 2)};
	sym_c := rep{x: x in SC | Degree(x) eq Binomial(d + 1, 2)};
	//assert ext_c ne sym_c;

	// Tensor handling

	procedure exact_test(I, cz, /*c,*/ ~rats_schur_indices, ~exact, ~si);
	    //cz := charz(c);
	    ind := Index(ratsz_iset, cz);
	    si := 1;
	    if ind gt 0 then
		exact := not IsDefined(I, ind);
		return;
	    end if;
	    d := cz[1];
	    for i := 1 to #rats_iset do
		if IsDefined(I, i) then
		    continue;
		end if;
		czi := ratsz_iset[i];
		di := czi[1];
		l, q := IsDivisibleBy(d, di);
// REWRITE!
		//if l and q*ci eq c then
		if l and forall{j: j in [1 .. num_cl] | q*czi[j] eq cz[j]} then
		    get_si(~rats_schur_indices, i, ~si);
		    exact := q eq si;
// if exact then "MATCH si", si; c; end if;
		    return;
		end if;
	    end for;
	    exact := false;
	end procedure;

	exact_test(I, charz(ext_c), ~rats_schur_indices, ~exact, ~si);
	if exact then
	    EM := ExteriorSquare(M);
	    vprintf ZReps:
		"Exterior square of dim %o already irreducible\n",
		Dimension(EM);
	    h := <h[1], Dimension(M), "exts", ind>;
	    IndentPush();
	    include_mod(
		~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		~extra, ~extrac, ~extras, ~WantChars,
		EM, si, ext_c, h
	    );
	    IndentPop();
	end if;

	exact_test(I, charz(sym_c), ~rats_schur_indices, ~exact, ~si);
	if exact then
	    SM := SymmetricSquare(M);
	    vprintf ZReps:
		"Symmetric square of dim %o already irreducible\n",
		Dimension(EM);
	    h := <h[1], Dimension(M), "syms", ind>;
	    IndentPush();
	    include_mod(
		~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		~extra, ~extrac, ~extras, ~WantChars,
		SM, si, sym_c, h
	    );
	    IndentPop();
	end if;

	// Tensor with everything else.
	for i := 2 to #rats do
	    if not IsDefined(IC, i) /*or IsOne(IC[i])*/ then
		continue;
	    end if;

/*
"****", i;
I[i];
IC[i];
IS[i];
rats[i];
"%";
IC[i], ExactQuotient(Dimension(I[i]), Z!Degree(IC[i])), rats[i]*IS[i];
assert IC[i]*ExactQuotient(Dimension(I[i]), Z!Degree(IC[i])) eq rats[i]*IS[i];

	    c := oc*IC[i]*
		ExactQuotient(Dimension(I[i]), Z!Degree(IC[i]));
*/

	    s := IS[i];
	    czi := ratsz[i];
	    cz := seq_to_charz([s*ocz[j]*czi[j]: j in [1 .. num_cl]]);
	    c := charz_to_char(cz);

// assert charz(c) eq cz;

	    exact_test(I, cz, ~rats_schur_indices, ~exact, ~si);
	    if exact then
		TM := TensorProduct(M, I[i]);
		assert Dimension(TM) eq Degree(c);
		TM`Character := c;
		vprintf ZReps:
		    "Tensor of dim %o by %o already irreducible\n",
			Dimension(M), Dimension(I[i]);
		h := <h[1], Dimension(M), "dtensor", ind, i>;
		IndentPush();
		include_mod(
		    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		    ~extra, ~extrac, ~extras, ~WantChars,
		    TM, si, c, h
		);
		IndentPop();
	    else
		include_char_Q(~Q_new, ~Qchars, c, K_TENS, ind, i);
	    end if;
	end for;

	/*
	// Tensor powers
	i := 3;
	c := oc^i;
	while Degree(c) le DirectMeataxeLimit do
	    include_char_Q(~Q_new, ~Qchars, c, K_TENS_POW, ind, i);
	    c := c*oc;
	    i +:= 1;
	end while;
	*/
    end procedure;

    /**************************************************************************/

    function SplitHomog(M, c: SeenChars := {})

	q := Dimension(M) div Z!Degree(c);
	Mc := q*c;
	if assigned M`Character then
	    assert M`Character eq Mc;
	else
	    M`Character := Mc;
	end if;

	return IntegralDecomposition(
	    M:
	    Depth := 1,
	    WantChars := [c], SplitChars := [<c, q>],
	    HomogIrredDim := Z!Degree(c),
	    WantSubmodules := false
	);
    end function;

    /***************************************************************************
	Init vars
    ***************************************************************************/

    Q := [];
    Q_new := [];
    extra := [];
    extrac := {@@};
    extras := [];

    MQ := [];

    tried_chars := {};
    dixon_done := {};
    step := 0;

    mod_list := [];
    perm_list := [**];

    /**************************************************************************/

    procedure current_state(I, IS, dixon_done, WantChars, ~seen, ~dixon_try)
	ID := [];
	dixon_try := [];
	for i := 1 to #rats do
	    if IsDefined(I, i) then
		ID[i] := Dimension(I[i]);
	    //elif Degree(rats[i]) le DIRECT_REP_LIMIT then
	    elif Degree(rats[i]) le DixonCharLimit then
		if i notin dixon_done then
		    Append(~dixon_try, i);
		end if;
	    end if;
	end for;
	vprint ZReps: "Current module dims:", ID;
	vprint ZReps: "Current Schur indices:", IS;
	vprint ZReps: "Dixon try:", dixon_try;
	if #WantChars gt 0 then
	    vprint ZReps: "Current WantChars indices:", WantChars;
	end if;

	seen := { IC[i]*IS[i]: i in [1 .. #IC] | IsDefined(IC, i) };
    end procedure;

    /***************************************************************************
	Small DB
    ***************************************************************************/

    if UseSmallDB then

	l, L := RepsSmallGet(G);
	if l then
	    vprintf ZMeataxe: "Small DB reps found with dims: %o\n",
		[Dimension(x): x in L];
	    for M in L do
		c := GetChar(M);

		vprint ZReps: "DB module character:", c;
		ic, si := get_irr_char_mult(c, rats);
		if ic eq 0 then
		    vprint ZReps: "Unknown char", c;
		    continue;
		end if;

		hh := <0, Dimension(M), "DB", 0, 0, 0>;
		vprint ZReps: "Include DB rep", M;
		IndentPush();
		include_mod(
		    ~rats_schur_indices, ~I, ~IC, ~IS,
		    ~Q_new, ~Qchars, ~history,
		    ~extra, ~extrac, ~extras, ~WantChars,
		    M, si, c, hh
		);
		IndentPop();
	    end for;
	end if;
    end if;

    /***************************************************************************
	Dixon
    ***************************************************************************/

    procedure use_dixon(
	i, ~rats_schur_indices,
	~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
	~extra, ~extrac, ~extras, ~WantChars, seen
    )

	STEP_TIME := Cputime();

	c := rats[i];
	cc := full_char_table[ratsi[i, 1]];
	d := Degree(cc);

	if not UseDixon and d gt 1 then
	    return;
	end if;

	get_si(~rats_schur_indices, i, ~si);

DixonEasySplitLimit := 50;
DixonEasySplitLimit := 10;

	fdlimit := Floor(DixonSplitLimit / Degree(cc));

	vprint ZReps: "TRY DIXON for character number", i;
	IndentPush();
	vprint ZReps, 2: "Integral character:", c;
	vprint ZReps, 2: "Complex character:", cc;
	vprint ZReps: "Integral character degree:", Degree(c);
	vprint ZReps: "Complex character degree:", d;
	vprint ZReps: cc;
	// vprint ZReps: "Field degree limit:", fdlimit;
	vprint ZReps: "Schur index:", si;

	Kd := Degree(Universe(Eltseq(cc)));
	KBd := Degree(CharacterField(cc));

	vprintf ZReps: "Default character values field degree: %o\n", Kd;
	vprintf ZReps: "Minimal character field degree: %o\n", KBd;

	dd := d * KBd;
	if dd gt DixonSplitLimit then
	    vprintf ZReps: "Minimal expansion dim %o > limit %o\n", 
		dd, DixonSplitLimit;
	    IndentPop();
	    return;
	end if;

	best := #G le 1000;
	// M := GModule(cc: Best, FieldDegreeLimit := fdlimit);
	if d*Kd le DixonEasySplitLimit then
	    vprint ZReps: "Use default character values field Dixon";
	    vtime ZReps: M := GModule(cc: Best := best);
	else
	    vprint ZReps: "Use minimal character field Dixon";
	    vtime ZReps: M := GModule(cc: Best := best, BestField);
	end if;

	vprint ZReps: "Dixon result:", M;

	if M cmpeq false then
	    vprint ZReps: "Dixon fails";
	    IndentPop();
	    return;
	end if;

	deg := Degree(BaseRing(M));
	dim := Dimension(M);
	dd := dim * deg;
	if dd gt DixonSplitLimit then
	    vprintf ZReps: "Expansion dim %o > limit %o\n", 
		dd, DixonSplitLimit;
	    IndentPop();
	    return;
	end if;

	M := ExpandZ(M: DoClean := false);
	vprint ZReps: "Expanded Dixon result:", M;
	vprintf ZReps:
	    "Clean initial Dixon module of dimension %o\n",
	    Dimension(M);
	vtime ZReps:
	    M := Clean(M);

	q := ExactQuotient(Dimension(M), Z!Degree(c));
	M`Character := q*c;
	SPLIT_TIME := Cputime();
	IndentPush();
	S, B := IntegralDecomposition(
	    M:
	    Depth := 1,
	    SeenChars := seen,
	    WantChars := [c], SplitChars := [<c, q>],
	    WantSubmodules := false
	);
	IndentPop();
	SPLIT_TIME := Cputime(SPLIT_TIME);
	vprint ZReps: "Dixon Decomposition time:", SPLIT_TIME;

	M := S[1];
	vprintf ZReps: "Clean Dixon submodule of dimension %o\n",
	    Dimension(M);
	vtime ZReps:
	    M := Clean(M);

	h := <step, Dimension(M), "dixon", i>;
	STEP_TIME := Cputime(STEP_TIME);
	Append(~h, STEP_TIME);

	IndentPush();
	include_mod(
	    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
	    ~extra, ~extrac, ~extras, ~WantChars, M, si,
	    //q*c,
	    GetChar(M),
	    h
	);
	IndentPop();

	vprint ZReps: "Dixon step time:", STEP_TIME;
	IndentPop();

    end procedure;

    vprint ZReps: "Initial Dixon tries\n";

    if InitialDixonLimit gt 0 then
	dlimit := InitialDixonLimit;
    elif #G ge 10000 then
	dlimit := 1;
    elif #G le 1000 then
	dlimit := 1;
    elif false and IsSoluble(G) and #G le 10000 then
	dlimit := 5;
    else
	dlimit := 3;
    end if;
    dlimit := 1;
    vprintf ZReps: "Character degree limit: %o\n", dlimit;

    seen := {};
    for i := 1 to #rats do
	c := rats[i];
	cc := full_char_table[ratsi[i, 1]];
	d := Degree(cc);
	use := d le dlimit;

	if use then
	    use_dixon(
		i, ~rats_schur_indices,
		~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		~extra, ~extrac, ~extras, ~WantChars, seen
	    );
	    current_state(I, IS, dixon_done, WantChars, ~seen, ~dixon_try);
	end if;

	if #Set(IC) eq #rats or WantCharsCase and #WantChars eq 0 then

	    II, c := get_II(I, IS, history);
	    if c eq #rats then
		extra := [];
	    end if;

	    vprint ZReps: "Now completely finished by Dixon";
	    vprint ZReps: "Total time:", Cputime(TOTAL_TIME);

	    return II, rats, ratsi;
	end if;
    end for;

    /**************************************************************************/

    if M cmpne "none" then
	// Maybe only if M smallish or easily shown irred:
	vprint ZReps: "Get char for initial dim", Dimension(M);
	IndentPush();
	vtime ZReps:
	    c := GetChar(M);
	IndentPop();

	Append(~mod_list, M);
	include_char_Q(~Q_new, ~Qchars, c, MOD, #mod_list, 0);
    end if;

    /**************************************************************************/

    if false and UseSoluble and IsSoluble(G) then
	vprint ZReps: "SOLUBLE; use soluble algorithm";

	if WantCharsCase then
	    SR := [];
	    for i in WantChars do
		c := full_char_table[ratsi[i, 1]];
		vprintf ZReps: "Get soluble rep %o for degree %o\n",
		    i, Degree(c);
		vtime ZReps: rep := Representations(c);
		rep := rep[1, 1];
		if Type(rep) eq ModGrp then
		    M := rep;
		else
		    M := GModule(G, [rep(G.i): i in [1 .. Ngens(G)]]);
		end if;
		Append(~SR, M);
	    end for;
	else
	    vtime ZReps:
		SR := AbsolutelyIrreducibleModules(G, RationalField());
	end if;

	for SM in SR do

	    if WantCharsCase and #WantChars eq 0 then
		break;
	    end if;

	    //, M := ChangeRing(SM, IntegerRing());
	    M := ExpandZ(SM: DoClean := false);
	    M := Clean(M);
	    c := 0;

	    if 1 eq 0 then
		d := Dimension(M);
		possible := {};
		for i := 1 to #rats do
		    cc := rats[i];
		    dcc := Z!cc[1];
		    q, r := Quotrem(d, dcc);
		    if r eq 0 then
			Include(~possible, q*cc);
		    end if;
		end for;
		c := Char(M: Possible := possible);
	    else
		c := GetChar(M);
	    end if;

	    if WantCharsCase and not TryAll then
		if c notin WantChars then
		    if not
			exists{
			    wc: wc in WantChars | char_is_multiple(c, rats[wc])
			}
		    then
			continue;
		    end if;
		end if;
	    end if;

	    MS := 0;
	    ci := Index(rats, c);
	    if ci ge 1 then
		MS := M;
	    else
		for i := 1 to #rats do
		    l, q := char_is_multiple(c, rats[i]);
		    if not l then
			continue;
		    end if;

		    vprintf ZReps:
			"Decompose soluble rep of dim %o (multiplicity %o)\n",
			Dimension(M), q;

		    S := SplitHomog(M, rats[i]);
		    MS := S[1];
		    ci := i;
		    break;
		end for;
	    end if;
	    M := MS;

	    if M cmpne 0 then
		get_si(~rats_schur_indices, ci, ~si);
		c := GetChar(M);

		IndentPush();
		hh := <0, Dimension(M), "sol", 0, 0, 0>;
		include_mod(
		    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		    ~extra, ~extrac, ~extras, ~WantChars,
		    M, si, c, hh
		);
		IndentPop();
	    end if;
	end for;

	current_state(I, IS, dixon_done, WantChars, ~seen, ~dixon_try);

	if WantCharsCase and #WantChars eq 0 or #{M: M in I} eq #I then
	    return get_II(I, IS, history), rats, ratsi;
	end if;
    end if;

    /***************************************************************************
	Given reps
    ***************************************************************************/

    for M in GivenReps do

	c := GetChar(M);

	if false then
	    vprint ZReps: "Include given rep", M;
	    Append(~mod_list, M);
	    include_char_Q(~Q_new, ~Qchars, c, MOD, #mod_list, 0);
	else
	    ic, si := get_irr_char_mult(c, rats);
	    if ic eq 0 then
		vprint ZReps: "Unknown char", c;
		continue;
	    end if;

	    hh := <0, Dimension(M), "given", 0, 0, 0>;
	    vprint ZReps: "Include given rep", M;
//ic, si;
	    IndentPush();
	    include_mod(
		~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		~extra, ~extrac, ~extras, ~WantChars,
		M, si, c, hh
	    );
	    IndentPop();
	end if;
    end for;

    if 1 eq 0 and Type(G) eq GrpMat then
	G2PG, PG := OrbitAction(G, RSpace(G).1);
    else
	G2PG := Coercion(G, G);
	PG := G;
    end if;

    /***************************************************************************
	Include perm reps
    ***************************************************************************/

    procedure include_perm_reps(~Q_new, ~Qchars, ~perm_list, ~PG_sub, range)
if #InductionIndices gt 0 then return; end if;
	vprintf ZReps: "Include perm reps in range %o\n", range;
	PI := [i: i in [1 .. #PG_sub] | Index(PG, PG_sub[i]) in range];
	vprintf ZReps: "Number of reps: %o\n", #PI;
	if #PI eq 0 then
	    return;
	end if;

	PL := [PG_sub[i]: i in PI];
	PI_set := Set(PI);
	PG_sub := [PG_sub[i]: i in [1 .. #PG_sub] | i notin PI_set];
	vprintf ZReps: "Number of remaining reps: %o\n", #PG_sub;

	// already filtered now
	L := PL;
	vprint ZReps: "Indices:", [Index(PG, S): S in L];

//"Subgroups:", L;

	vprintf ZReps: "Get perm reps for %o subgroup(s)\n", #L;
	vtime ZReps: for S in L do
	    if Index(PG, S) gt PermDegreeLimit then continue; end if;
	    f := CosetAction(PG, S);
	    c := CR ! [num_fixed_pts(f(G2PG(t[3]))): t in Classes(G)];
	    Append(~perm_list, f);
	    include_char_Q(~Q_new, ~Qchars, c, PERM, #perm_list, 0);
	end for;
    end procedure;

    /***************************************************************************
	Low ind subgroups
    ***************************************************************************/

    procedure new_low_ind_subgroups(~todo, ~done, ~new)
	/// Assumes todo sorted with smallest ind first

	desc := func<L | {* Index(G, H): H in L *}>;

	printf "In todo: %o, done: %o\n", desc(todo), desc(done);

	if #todo gt 0 then
	    m := Index(G, todo[1]);
	else
	    m := #G + 1;
	end if;

	printf "m: %o\n", m;

	todo := Set(todo);
	keep := [];
	for i := 1 to #done do
	    H := done[i];
	    l := Index(G, H);
	    if l gt m div 2 then
		// printf "i: %o, l: %o, skip\n", i, l;
		Append(~keep, H);
		continue;
	    end if;
	    L := MaximalSubgroups(H);
	    L := [x`subgroup: x in L];
	    // printf "i: %o, l: %o, max subgroups: %o\n", i, l, desc(L);
	    if #L eq 0 then
		continue;
	    end if;
	    todo join:= Set(L);
	    H := L[#L];
	    l := Index(G, H);
	    if l lt m then
		printf "New min m: %o\n", l;
		m := l;
	    end if;
	end for;

	done := keep;
	todo := Setseq(todo);
	Sort(~todo, func<H1, H2 | Index(G, H1) - Index(G, H2)>);
	new := [];
	last := 0;
	for i := 1 to #todo do
	    H := todo[i];
	    l := Index(G, H);
	    assert l ge m;
	    if l eq m then
		Append(~new, H);
		last := i;
	    else
		break;
	    end if;
	end for;
	todo := todo[last + 1 .. #todo];
	done cat:= new;

	printf "Final todo: %o, done: %o, new: %o\n",
	    desc(todo), desc(done), desc(new);

    end procedure;

    LIS_todo := [];
    LIS_done := [G];

    /**************************************************************************/

    function get_low_ind_subgroups(min, max)
	if min gt max or not UseSubgroups then
	    return [], false;
	end if;

	if #LI gt 0 and max le LI_max_index then
	    L := LI;
	elif #InductionIndices eq 1 then 
	    ind := Rep(InductionIndices);
	    vprint ZReps: "USE Exact index", ind;
	    if #LI eq 1 and Index(G, LI[1]) eq ind then
		L := LI;
	    else
		vtime ZReps: L := Subgroups(PG: OrderEqual := #G div ind);
		L := [r`subgroup: r in L];
	    end if;
	elif UseLI or 1 eq 1 and #G gt 10^15 then
	    vprint ZReps: "USE LI";
	    vprintf ZReps:
		"Get subgroups in index range [%o .. %o]\n", min, max;
	    vtime ZReps: L := LowIndexSubgroups(PG, max);
	    L := [S: S in L | Index(PG, S) ge min];
	else
	    vprintf ZReps:
		"Get subgroups in index range [%o .. %o]\n", min, max;
	    vtime ZReps: L := Subgroups(PG: IndexLimit := max);
	    L := [S: r in L | Index(PG, S) ge min where S := r`subgroup];
	end if;

	LL := filter_subgroups_repetition(
	    L, Min(#rats, PERM_REP_MAX_ORDER_COUNT)
	);
	if #LL lt #L then
	    vprintf ZReps: "REDUCED count; was: %o, now: %o\n", #L, #LL;
	    reduced := true;
	else
	    reduced := false;
	end if;
	L := LL;

	Sort(~L, func<G, H | #H - #G>);
	vprint ZReps: "Indices:", [Index(PG, S): S in L];
	return L, reduced;
    end function;

    /***************************************************************************
	Get subgroups
    ***************************************************************************/

    LImax := InitialIndex;
    max_perm_deg := InitialIndex;

    range := [MinPermDegree .. max_perm_deg];

    if not UseSubgroups then
	vprint ZReps: "Not computing any subgroups";
	AllSubgroups := SUBGROUPS_NEVER;

	G_subgroups := [sub<G|>];
	PG_sub := [];
	hard_group := true;

    elif AllSubgroups cmpeq SUBGROUPS_ALWAYS then
	vprint ZReps: "Get all subgroups";
	vtime ZReps: G_subgroups := [S`subgroup: S in Subgroups(G)];
	vprintf ZReps: "#All subgroups: %o\n", #G_subgroups;
	sort_subgroup_seq(~G_subgroups);

	PG_sub := G_subgroups;

	AllSubgroups := SUBGROUPS_DONE;
	hard_group := false;
	LImax := #G;
    else
	if NewLIS then
	    new_low_ind_subgroups(~LIS_todo, ~LIS_done, ~G_subgroups);
	    hard_group := false;
	    ind := Index(G, G_subgroups[1]);
	    range := [ind .. ind];
	else
	    G_subgroups, hard_group := get_low_ind_subgroups(
		MinPermDegree, LImax
	    );
	end if;

	PG_sub := G_subgroups;

	include_subgroups(
	    ~G_subgroups, [sub<G | t[3]>: t in Classes(G)]: Overlap
	);
	sort_subgroup_seq(~G_subgroups);

	vprintf ZReps: "Start with %o subgroup(s)\n", #G_subgroups;
	vprint ZReps: "Indices:", [Index(G, H): H in G_subgroups];

    end if;

    /**************************************************************************/

    if Type(G) eq GrpPerm then
	vprintf ZReps: "Include perm rep G of degree %o\n", Degree(G);
	f := Coercion(G, G);
	c := CR ! [num_fixed_pts(t[3]): t in Classes(G)];
	Append(~perm_list, f);
	include_char_Q(~Q_new, ~Qchars, c, PERM, #perm_list, 0);
    end if;

    vprint ZReps: "Construct initial perm reps";
    sort_subgroup_seq(~PG_sub);

    include_perm_reps(~Q_new, ~Qchars, ~perm_list, ~PG_sub, range);

    /***************************************************************************
	Induction search
    ***************************************************************************/

    ind_list := [];
    ind_seen := {};
    ind_Hchar := <>;

    procedure induction_search(
	~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
	~extra, ~extrac, ~extras, ~WantChars, ~ind_seen, ~ind_Hchar,
	LIS
    )
	if #InductionIndices gt 0 then
	    LIS := [H: H in LIS | Index(G, H) in InductionIndices];
	end if;

	vprint ZReps: "Induction search";
	vprint ZReps: "Subgroup orders:", [#H: H in LIS];
	ITIME := Cputime();

	rdegs := {Degree(c): c in rats};
	maxd := Max(rdegs);
	//seenci := { IC[i]*IS[i]: i in [1 .. #IC] | IsDefined(IC, i) };
	seenci := { i: i in [1 .. #IC] | IsDefined(IC, i) };

	Sort(~LIS, func<G, H | #G - #H>);
	// Backwards so smallest groups first, so best H reps first?
	for H in LIS do

	    if #H eq 1 or #H eq #G then
		continue;
	    end if;
	    ind := Index(G, H);
	    if ind gt IndIndexLimit then
		continue;
	    end if;
	    if not NewInd and ind gt maxd/2 then
		break;
	    end if;
	    if H in ind_seen then
		continue;
	    end if;
	    if UseSolubleInduction and not IsSoluble(H) then
		continue;
	    end if;

	    if WantCharsCase then  // TryAll???
		if #WantChars eq 0 then
		    break;
		end if;
		wrats := {@ rats[i]: i in WantChars @};
		rdegs := {Degree(c): c in wrats};
		maxd := Max(rdegs);
	    else
		wrats := rats_iset;
	    end if;

	    if IsSoluble(H) and #Classes(H) gt IND_SUBGROUP_CLASSES_LIMIT then
		continue;
	    end if;

	    vprintf ZReps:
		"Try subgroup, order %o, index %o; get char table\n", #H, ind;
	    // vprint ZReps: ChiefFactors(H);
	    //H: Magma;

	    vtime ZReps: HX := CharacterTable(H);
	    Hrats, Hratsi := RationalCharacterTable(H);
	    vprint ZReps: "Rational degrees:", {* Degree(x): x in Hrats *};

	    want_hc := [];
	    want_c := [];
	    for hci := 1 to #Hrats do
		hc := Hrats[hci];

		if IsOne(hc) then
		    continue;
		end if;

		c := Induction(hc, G);
		if c in Qchars then
		    continue;
		end if;

/*
Change following to allow for SI in G char.  Following
is missing a direct ind and doing a ind cond later.

D := PerfectGroupDatabase();
G := PermutationGroup(D, 4896, 1);
time R, C := InternalIrreducibleIntegralModules(G: CharacterDegrees:=[144],NewInd);
*/



		ci := Index(wrats, c);
		if ci in seenci then
		    continue;
		end if;
		if ci eq 0 then
		    if NewInd then
			// SI := Hreps[i, 2]; c := c*SI;
			si := MySchurIndex(HX[Hratsi[hci, 1]]);
			vprintf ZReps:
		    "    Include H char deg %o, SI %o, G char deg %o, pos %o\n",
			    Degree(hc), si, Degree(c), #ind_Hchar;
			Append(~ind_Hchar, hc);
			r := #H;
			include_char_Q(
			    ~Q_new, ~Qchars, si*c, K_IND, #ind_Hchar, r
			);
		    end if;
		    continue;
		end if;

		Include(~seenci, ci);
		Append(~want_c, c);
		Append(~want_hc, hc);
	    end for;
	    delete HX, Hrats, Hratsi;

	    if #want_hc gt 0 then
		vprintf ZReps: "Induction subgroup order: %o, index: %o\n",
		    #H, Index(G, H);
		vprint ZReps: "G characters:", want_c;
		vprint ZReps: "H characters:", want_hc;
		vprint ZReps: "H soluble:", IsSoluble(H);


	    /*
	    if #H le 5000 then
		vprint ZReps: "Force subgroups for H";
		vtime ZReps: ns := #Subgroups(H);
		vprint ZReps: "Number:", ns;
	    end if;
	    */

/*
if Degree(H) le 20 then
vprint ZReps: "H:"; H: Magma;
end if;
*/

		TIME := Cputime();
		IndentPush();
		vtime ZReps:
		    /*
		    pl := Min(
			PermDegreeLimit, 10*Min([Degree(c): c in want_hc])
		    ),
		    */
		    /*
		    pl := Z!Min(
			PermDegreeLimit, Max([Degree(c): c in want_c])
		    );
		    tl := pl*2;
		    */
		    Hreps, HC := InternalIrreducibleIntegralModules(
			H:
			// PermDegreeLimit := pl, TensorLimit := tl,
			AllSubgroups := false,
			UseInduction := IndRec,
			NoDumpChars,
			UseSoluble := UseSoluble, //true, //UseSoluble,
			Characters := Set(want_hc),
			NewLIS := NewLIS,
			DynTraces := DynTraces,
			InitialDixonLimit := InitialDixonLimit
		    );
		IndentPop();
		TIME := Cputime(TIME);

		for i in [1 .. #Hreps] do
		    if not IsDefined(Hreps, i) then
			continue;
		    end if;

		    M := Hreps[i, 1];
		    SI := Hreps[i, 2];
		    hc := HC[i];
		    if hc notin want_hc then
			continue;
		    end if;
		    vprintf ZReps: "Got restricted module: %o, SI: %o\n",
			M, SI;

		    STIME := Cputime();
		    c := Induction(hc, G);
		    vprintf ZReps: "Got induced character; degree: %o\n",
			Degree(c);

		    if SI gt 1 and Degree(c) gt 300 then
			vprint ZReps: "Skip since SI > 1 and too big\n";
			continue;
		    end if;

		    cc := c;
		    if cc notin rats then
			"cc:", cc;
			"rats:", rats;
			assert cc in rats;
		    end if;
		    vprintf ZReps: "Good induced character: %o\n", c;
		    IM := Induction(M, G);

		    if SI ne 1 then
			get_si(~rats_schur_indices, Index(rats, c), ~si);
			vprintf ZReps:
			"Restriction has SI %o; induced char has SI %o; SPLIT\n"
			    , SI, si;
			cc := si*c;
//"cc:", cc;
			if Dimension(IM) eq Degree(cc) then
			    c := cc;
			else
			    IMS, ISI := SplitHomog(IM, cc);
			    if ISI[1] eq 0 then
				vprint ZReps: "Failed to split induced module";
				continue;
			    end if;
			    IM := IMS[1];
			    SI := ISI[1];
			    if Dimension(IM) eq Degree(cc) then
				c := cc;
			    else
				c := GetChar(IM);
			    end if;
			end if;
		    end if;

		    vprintf ZReps: "Include induced rep, new SI %o\n", IM, SI;
		    STIME := Cputime(STIME);

		    hh := <0, Dimension(M), "dind", #H, TIME + STIME>;
		    IndentPush();
		    include_mod(
			~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars,
			~history, ~extra, ~extrac, ~extras, ~WantChars,
			IM, SI, c, hh
		    );
		    IndentPop();

		end for;
		current_state(I, IS, dixon_done, WantChars, ~seen, ~dixon_try);
	    end if;
	end for;

	ITIME := Cputime(ITIME);
	vprintf ZReps: "Induction search time: %o\n", ITIME;

    end procedure;

    if UseInduction then
	if CliffordN cmpne 0 then
	    vprint ZReps: "**** CLIFFORD";
	    ind_subgroups := Clifford_elab(G, CliffordN);
	else
	    ind_subgroups := G_subgroups;
	end if;

	//Sort(~ind_subgroups, func<H1, H2 | Index(G, H2) - Index(G, H1)>);
	Sort(~ind_subgroups, func<H1, H2 | Index(G, H1) - Index(G, H2)>);

	induction_search(
	    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
	    ~extra, ~extrac, ~extras, ~WantChars, ~ind_seen, ~ind_Hchar,
	    ind_subgroups
	);
    end if;

    /*
    // Old direct induction.

    if InductionLimit gt 1 then
	vprint ZReps: "Get reps of subgroups for induction up to limit",
	    PermDegreeLimit;

	vtime ZReps:
	for Hrec in G_subgroups do
	    // H := Hrec`subgroup;
	    H := Hrec;
	    ind := Index(G, H);
	    if ind eq 1 or ind gt InductionLimit then
		continue;
	    end if;

	    vprint ZReps: "Index:", ind;
	    IndentPush();
	    vtime ZReps:
		Hreps, HC := InternalIrreducibleIntegralModules(
		    H: DirectMeataxeLimit := 20
		);
	    IndentPop();
	    for i in [1 .. #Hreps] do
		if not IsDefined(Hreps, i) then
		    continue;
		end if;
		Hc := HC[i];
		if 1 eq 1 and IsOne(Hc) then
		    continue;
		end if;
		M := Hreps[i, 1];
		SI := Hreps[i, 2];
		c := Induction(Hc, G);
		c := c*SI;
		Append(~ind_list, M);
		include_char_Q(~Q_new, ~Qchars, c, K_IND, #ind_list, 0);
	    end for;
	    delete Hreps, HC;
	end for;

	"ind_list:", ind_list;
    end if;
    */

    /***************************************************************************
	Queue sorting
    ***************************************************************************/

    perms_first := 1 eq 1;
    if perms_first then
	MOD_CMP_LIM := 100;
	MOD_CMP_LIM := 1;
	function Q_cmp(x, y)
	    xd, xt, xl, xr, xc := Explode(x);
	    yd, yt, yl, yr, yc := Explode(y);
	    if Min(xd, yd) ge MOD_CMP_LIM then
		if xt eq MOD and yt eq MOD then
		    return y[1] - x[1];
		elif xt eq MOD then
		    return 1;
		elif yt eq MOD then
		    return -1;
		end if;
	    end if;
	    return yd - xd;
	end function;

	PERM_RATIO := 6;

//TENSOR_RATIO := 2.8;
//TENSOR_RATIO := 1;
//TENSOR_RATIO := 5.8;
//TENSOR_RATIO := 100;
	TENS_LIMIT := 100;
TENS_LIMIT := 10;

	ind_subgroup_cmp_limit := Max(300, #G);

	cmp := func<c, def | c eq 0 select def else c>;

	function Q_cmp_orig(x, y)
	    xd, xt, xl, xr, xc := Explode(x);
	    yd, yt, yl, yr, yc := Explode(y);

	    if xt eq PERM then
		xd := xd/PERM_RATIO;
	    end if;
	    if yt eq PERM then
		yd := yd/PERM_RATIO;
	    end if;

	    if xt eq K_IND then

		if false and yt eq K_IND then
		    /*
		    r entry is order of subgroup.  Prefer case with
		    smaller subgroup if dims are close enough.
		    */

		    ratio := xd/yd;
/*
"x:", x;
"y:", y;
"ratio:", ratio;
"xr - yr:", xr - yr;
*/
		    if
			ratio ge 0.8 and ratio le 1.2 and
			xd le ind_subgroup_cmp_limit
		    then
			return yr - xr;
		    end if;
		end if;

		xd := xd/IND_RATIO;
	    end if;
	    if yt eq K_IND then
		yd := yd/IND_RATIO;
	    end if;

	    if xt eq K_TENS and xd ge TENS_LIMIT then
		xd := xd/TENSOR_RATIO;
	    end if;
	    if yt eq K_TENS and yd ge TENS_LIMIT then
		yd := yd/TENSOR_RATIO;
	    end if;

	    cmp := yd - xd;
	    if cmp ne 0 then
		return cmp;
	    end if;

	    if xt ne yt then
		if xt eq PERM then
		    return 1;
		end if;
		if yt eq PERM then
		    return -1;
		end if;
	    end if;

	    return yl - xl;

	    /*
	    if xt eq PERM then
		if yt eq PERM then
		    return yd - xd;
		end if;
		return cmp(PERM_RATIO*yd - xd, 1);
	    end if;
	    if yt eq PERM then
		return cmp(yd - PERM_RATIO*xd, -1);
	    end if;

	    if xd ne yd then
		return yd - xd;
	    end if;
	    if xt eq MOD and yt eq MOD then
		return #yc - #xc;
	    elif xt eq MOD then
		return 1;
	    elif yt eq MOD then
		return -1;
	    end if;
	    return yl - xl;
	    */
	end function;

	function Q_cmp(x, y)
	    xd, xt, xl, xr, xc := Explode(x);
	    yd, yt, yl, yr, yc := Explode(y);

	    xd := rats_deg[xc[1, 1]];
	    yd := rats_deg[yc[1, 1]];
	    cmp := yd - xd;
	    if cmp ne 0 then
		return cmp;
	    end if;

	    return Q_cmp_orig(x, y);
	end function;

	if 1 eq 1 and (InductionLimit gt 1 or NewInd) then
	    Q_cmp := Q_cmp_orig;
	end if;
	Q_cmp := Q_cmp_orig;
    else
	function Q_cmp(x, y)
	    return y[1] - x[1];
	end function;
    end if;

    /***************************************************************************
	Main loop
    ***************************************************************************/

    while true do
	vprint ZReps: "Sort Q";
	vtime ZReps:
	    SortViaMerge(~Q, ~Q_new, Q_cmp);

	// vprint ZReps: "New Q:", Q;

	STEP_TIME := Cputime();
	step +:= 1;

	vprint ZReps: "\n****";
	vprintf ZReps: "Step %o\n", step;
	vprint ZReps: "Queue len:", #Q;
	//vprint ZReps: "New I:", I;
	//vprint ZReps: "New IC:", IC;
	// MemProfile();

	current_state(I, IS, dixon_done, WantChars, ~seen, ~dixon_try);

	stop := false;
	cont := false;
	while true do

	    if
		(#Q eq 0 and Min(max_perm_deg, LImax) gt PermDegreeLimit) or
		#Set(IC) eq #rats or
		WantCharsCase and #WantChars eq 0
	    then
		stop := true;
		break;
	    end if;

	    if #Q eq 0 then
		d := 0;
	    else
		q := Q[#Q];
		d, t, l, r, char_split := Explode(q);
	    end if;

	    if 1 eq 1 and IsSoluble(G) then
		ext_perm_limit := Max(5*max_perm_deg, 500);
	    else
		ext_perm_limit := max_perm_deg;
	    end if;

	    if
		(d eq 0 or d gt ext_perm_limit) and
		(#PG_sub gt 0 or LImax lt PermDegreeLimit)
	    then
		vprint ZReps: "****";

		nd := 2*max_perm_deg;
		range := [max_perm_deg + 1 .. nd];

		while #PG_sub eq 0 and LImax lt IndexLimit do

		    NLImax := Max(2*LImax, nd);
		    NLImax := Min(NLImax, PermDegreeLimit);
		    vprintf ZReps: "Move to new LImax %o\n", NLImax;

		    if NewLIS then
			PG_sub := [];
			while true do
			    new_low_ind_subgroups(~LIS_todo, ~LIS_done, ~new);
			    PG_sub cat:= new;
			    if #new eq 0 or Index(G, new[1]) ge NLImax then
				break;
			    end if;
			end while;
			vprintf ZReps: "Got new LIS: %o\n",
			    {* Index(G, H): H in PG_sub *};
			range := [1 .. Index(G, PG_sub[#PG_sub])];
		    else
			PG_sub, hard_group := get_low_ind_subgroups(
			    LImax + 1, NLImax
			);
		    end if;
		    LImax := NLImax;

		    if UseInduction then
			induction_search(
			    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars,
			    ~history, ~extra, ~extrac, ~extras, ~WantChars,
			    ~ind_seen, ~ind_Hchar,
			    PG_sub
			);
		    end if;

		    if AllSubgroups cmpeq SUBGROUPS_DEFAULT then
			include_subgroups(~G_subgroups, PG_sub: Overlap);
		    end if;
		end while;

		max_perm_deg := nd;
		vprintf ZReps:
		"Current dim %o; construct new perm reps (new max dim %o)\n",
		    d, nd;
		include_perm_reps(~Q_new, ~Qchars, ~perm_list, ~PG_sub, range);
		//vprint ZReps: "Remaining PG_sub Indices:",
		//[Index(PG, S): S in PG_sub];
		vprint ZReps: "Resort Q";
		vtime ZReps:
		    SortViaMerge(~Q, ~Q_new, Q_cmp);

		vprint ZReps: "****";

		continue;
	    end if;

	    if #Q eq 0 then
		stop := true;
		break;
	    end if;

	    if
		/*not WantCharsCase and*/
false and
		#dixon_try gt 0 and
		d ge DixonTryDim
		/* Degree(char_split) le DixonCharLimit and*/
	    then

		i := dixon_try[1];
		Include(~dixon_done, i);

		use_dixon(
		    i, ~rats_schur_indices,
		    ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		    ~extra, ~extrac, ~extras, ~WantChars, seen
		);

		cont := true;
		break;
	    end if;

	    vprintf ZReps: "%o: dim %o: ", #Q, d;
	    case t:
		when MOD:
		    vprintf ZReps: "Initial module of dim %o",
			Dimension(mod_list[l]);
		when PERM:
		    vprintf ZReps: "Perm of degree %o",
			Degree(Codomain(perm_list[l]));
		when K_IND:
		    if NewInd then
			HC := ind_Hchar[l];
			vprintf ZReps: "Induction of dimension %o by index %o",
			    Degree(HC), Index(G, Group(Parent(HC)));
		    else
			HM := ind_list[l];
			vprintf ZReps: "Induction of dimension %o by index %o",
			    Dimension(HM), Index(G, Group(HM));
		    end if;
		when EXT_SQ:
		    vprintf ZReps: "Ext-sq of dim %o[%o]", Dimension(I[l]), l;
		when SYM_SQ:
		    vprintf ZReps: "Sym-sq of dim %o[%o]", Dimension(I[l]), l;
		when K_TENS_POW:
		    vprintf ZReps: "Tensor power of dim %o[%o] by %o",
			Dimension(I[l]), l, r;
		when K_TENS:
		    vprintf ZReps: "Tensor of dim %o[%o] by dim %o[%o]",
			Dimension(I[l]), l, Dimension(I[r]), r;
	    end case;
	    vprint ZReps: "";

	    //[<Z!Degree(rats[t[1]]), t[2]>: t in char_split];
	    //[Z!Degree(rats[t[1]]): t in char_split];

	    Prune(~Q);

//if d eq 1 then continue; end if;

	    M_char := &+[t[2]*rats[t[1]]: t in char_split];
	    if M_char in tried_chars then
		vprint ZReps: "SKIP: Already tried module with this character!";
		continue;
	    end if;

	    if t in {K_TENS, K_TENS_POW} and
		TensorLimit gt 0 and d gt TensorLimit
	    then
		vprint ZReps: "SKIP: Beyond tensor limit", TensorLimit;
		continue;
	    end if;

	    if t in {PERM} and d gt PermDegreeLimit then
		vprint ZReps: "SKIP: Beyond perm degree limit", PermDegreeLimit;
		continue;
	    end if;

/*
"char_split:", char_split;
"M_char:", M_char;
"WantChars:", WantChars;
*/

	    if
		Blackbox or
		not TryAll and #WantChars gt 0 and d gt EasyLimit
	    then
		e := [t: t in char_split | t[1] in WantChars];
	    else
		e := [t: t in char_split | not IsDefined(I, t[1])];
	    end if;

	    if MaxDegree gt 0 then
		e := [t: t in e | Degree(rats[t[1]]) le MaxDegree];
	    end if;

	    if #e gt 0 then
		break;
	    end if;
	end while;

	if cont then
	    STEP_TIME := Cputime(STEP_TIME);
	    vprint ZReps: "Step time:", STEP_TIME;
	    vprint ZReps: "Current accumulated time:", Cputime(TOTAL_TIME);
	    continue;
	end if;

	if stop then
	    break;
	end if;

	/*
	if d gt DirectMeataxeLimit and t notin {PERM, K_TENS, K_IND} then
	    vprint ZReps: "DirectMeataxeLimit hit now!";
	    break;
	end if;
	*/

	split := [<rats[t[1]], t[2]>: t in char_split];
	want := [rats[t[1]]: t in e];
	full_split := [[full_char_table[j]: j in ratsi[t[1]]]: t in char_split];
	full_want := [[full_char_table[j]: j in ratsi[t[1]]]: t in e];

	/*
	want_sindices := [rats_schur_indices[t[1]]: t in e];
	split_sindices := [rats_schur_indices[t[1]]: t in char_split];
	*/

	get_si_seq(~rats_schur_indices, [t[1]: t in e], ~want_sindices);
	get_si_seq(~rats_schur_indices, [t[1]: t in char_split], ~split_sindices);

	//"want_sindices:", want_sindices;
	//"split_sindices:", split_sindices;

	use_cond := false;

	nicify := true;
	no_clean := false;
	already_irred := false;
	ccond_kind := 0;

	if t eq PERM then
	    /*
	    if #G ge 300000 then
		perm_cond_limit := 150;
	    elif #G ge 100000 then
		perm_cond_limit := 100;
	    else
		perm_cond_limit := 20;
	    end if;
	    */
	    perm_cond_limit := 20;
	    use_cond := Degree(M_char) ge perm_cond_limit or
		Type(G) eq GrpPC or Blackbox;
	    nicify := false;
	    Pf := perm_list[l];
	    P := Codomain(Pf);
	    if use_cond then
		vprintf ZReps: "Perm condensation of degree %o\n", Degree(P);
		h := <step, Degree(P), "pcond", l>;

		CG := G;
		f := Inverse(Pf);
		ccond_kind := CCOND_PERM;
		info := P;
		MaxCond := Degree(P) div 2;
		MaxCond := Min(MaxCond, 300);
	    else
		vprintf ZReps: "Perm rep of degree %o\n", Degree(P);
		M := PermutationModule(P, Z);
		M := GModule(
		    G,
		    [ActionGenerator(M, i): i in [1 .. Ngens(G)]]:
			Check := false
		);
		h := <step, Dimension(M), "perm", l>;
	    end if;
	elif t eq K_TENS then
	    // mod 13 (dim 40), from tens 48, slower with cond
	    M1 := I[l];
	    M2 := I[r];
	    if Dimension(M1) gt Dimension(M2) then
		M1 := I[r];
		M2 := I[l];
	    end if;
	    if want eq [M_char] then
		use_cond := false;
		already_irred := true;
		vprintf ZReps:
		"Direct tensor of dimensions %o and %o already irreducible\n",
		    Dimension(M1), Dimension(M2);
		no_clean := true;
	    else
		// use_cond := Degree(M_char) ge 50;
		use_cond := Degree(M_char) ge 2;
	    end if;
	    if use_cond then
		nicify := false;
		vprintf ZReps: "Tensor condensation of dimensions %o and %o\n",
		    Dimension(M1), Dimension(M2);
		CG := G;
		f := Coercion(G, G);
		ccond_kind := CCOND_TENS;
		info := <M1, M2>;
		h := <step, Degree(M_char), "tcond", l, r>;
		MaxCond := (Dimension(M1) * Dimension(M2)) div 4;
		MaxCond := Min(MaxCond, 300);
	    else
		vprintf ZReps: "Tensor product dimensions %o and %o\n",
		    Dimension(M1), Dimension(M2);
		M := TensorProduct(I[l], I[r]);
		M`Character := M_char;
		h := <step, Dimension(M), "tens", l, r>;
		nicify := false;
	    end if;
	elif t eq MOD then
	    vprintf ZReps: "Initial module of dimension %o\n",
		Dimension(mod_list[l]);
	    M := mod_list[l];
	    h := <step, Dimension(M), "init">;
	elif t eq K_IND then
	    if NewInd then
		Hc := ind_Hchar[l];
		Hcd := Degree(ind_Hchar[l]);
		H := Group(Parent(Hc));
		vprintf ZReps: "Get H rep for char deg %o\n", Hcd;
		HM := 0;

		l, ComplexRepExt := IsIntrinsic("ComplexRepExt");
		if UseExt and l then
		    vprint ZReps: "Try irreducible extension";

		    vtime ZReps: l, HM := ComplexRepExt(Hc);
		    if l then
			vprint ZReps: "Do expansion over Z";
			vtime ZReps: HM := ExpandZ(HM);
		    else
			HM := 0;
		    end if;
		end if;

		if HM cmpeq 0 then
		    use_sol := #H le 100000 and Hcd le 50;
		    use_sol := false;
		use_sol := true;

		    IndentPush();
		    vtime ZReps:
			Hreps, HC := InternalIrreducibleIntegralModules(
			    H:
			    // AllSubgroups := false,
			    UseInduction := IndRec,
			    NoDumpChars,
			    UseSoluble := use_sol,
			    Characters := [Hc],
			    NewLIS := NewLIS,
			    InitialDixonLimit := InitialDixonLimit
			);
		    IndentPop();
    /*
    "H:", H;
    "Hc group:", Group(Parent(Hc));
    "Hc:", Hc;
    "HC:", HC;
    */
		    i := Index(HC, Hc);
		    assert i gt 0;
		    HM := Hreps[i, 1];
		end if;

		/*
		if not Blackbox or Dimension(HM) le 50 then
		    vprint ZReps: "Clean HM";
		    vtime ZReps: HM := Clean(HM);
		end if;
		*/
	    else
		HM := ind_list[l];
		H := Group(HM);
	    end if;

	    use_cond := Degree(M_char) ge 2;
	    nicify := false;
	    if use_cond then
		index := Index(G, Group(HM));
		vprintf ZReps:
		"Induction condensation: #H: %o, index: %o, H rep dim: %o\n",
		    #H, index, Dimension(HM);

		CG := G;
		f := Coercion(G, G);
		ccond_kind := CCOND_IND;
		info := <HM, M_char>;
		h := <step, Degree(M_char), "icond", Dimension(HM), index>;
		MaxCond := (Dimension(HM) * index) div 4;
		MaxCond := Min(MaxCond, 300);
	    else
		vprintf ZReps:
		    "Induction of module of dimension %o by index %o\n",
		    Dimension(HM), Index(G, H);
		M := Induction(HM, G);
		h := <step, Dimension(M), "ind">;
	    end if;
	elif t eq EXT_SQ then
	    vprintf ZReps: "Exterior square of dimension %o\n",
		Dimension(I[l]);
	    M := ExteriorSquare(I[l]);
	    h := <step, Dimension(M), "exts", l>;
	elif t eq SYM_SQ then
	    vprintf ZReps: "Symmetric square of dimension %o\n",
		Dimension(I[l]);
	    M := SymmetricSquare(I[l]);
	    h := <step, Dimension(M), "syms", l>;
	elif t eq K_TENS_POW then
	    vprintf ZReps: "Tensor power of dimension %o by %o\n",
		Dimension(I[l]), r;
	    M := TensorPower(I[l], r);
	    h := <step, Dimension(M), "tensp", l, r>;
	else
	    error "DIE!";
	end if;
	Include(~tried_chars, M_char);

	if nicify then
	    vprint ZMeataxe: "Nicify";
	    IndentPush();
	    vtime ZReps:
		M := Nicify(M);
	    IndentPop();
	end if;

	vprint ZReps: "Decomposition degrees:",
	    [<Z!Degree(rats[t[1]]), t[2]>: t in char_split];
	vprint ZReps: "Want degrees:", [Degree(x): x in want];

	if already_irred then
	    vprint ZReps: "Already irreducible:", M;
	    S := [M];
	    B := [1];
	elif use_cond then
	    SPLIT_TIME := Cputime();
	    IndentPush();

	    ccond(
		G, ccond_kind, M_char, info,
		~AllSubgroups, ~G_subgroups, ~S, ~B:
		    f := f,
		    MaxCond := MaxCond,
		    //MaxUncond := Max([Degree(x): x in want]),
		    HardGroup := hard_group,
		    IrrChars := rats_iset, SeenChars := seen,
		    WantChars := want,
		    SplitChars := split, SplitSchurIndices := split_sindices,
		    FullWantChars := full_want, FullSplitChars := full_split,
		    WantSchurIndices := want_sindices,
		    MaxTries := 1000,
		    FullCharTable := full_char_table,
		    CondTarget := CondTarget,
		    DynTraces := DynTraces,
		    AllowDenoms := AllowDenoms,
		    Blackbox := Blackbox
	    );
	    IndentPop();
	    SPLIT_TIME := Cputime(SPLIT_TIME);

	    delete info;
	else
	    if 0 eq 1 then
		ta := Action(M).1;
		RowSubmatrix(ta, 1, Min(Nrows(ta), 5));
		delete ta;
	    end if;

	    Append(~MQ, M);

	    if not assigned M`Character then
		M`Character := M_char;
	    end if;

	    vprint ZReps: "Splitting:", M;
	    //vprint ZReps: "Decomposition:", split;
	    //vprint ZReps: "Want:", want;

InitDepth := -1;
InitDepth := 0;

	    SPLIT_TIME := Cputime();
	    IndentPush();
	    S, B := IntegralDecomposition(
		M:
		Depth := InitDepth,
		SeenChars := seen,
		WantChars := want, SplitChars := split,
		WantSubmodules := false
	    );
	    IndentPop();
	    SPLIT_TIME := Cputime(SPLIT_TIME);
	end if;

	vprint ZReps: "New modules time:", SPLIT_TIME;

	if Blackbox then
	    IndentPop();
	    vprint ZReps: "Step time:", Cputime(STEP_TIME);
	    vprint ZReps: "Total accumulated time:", Cputime(TOTAL_TIME);
	    return S;
	end if;

	vprint ZReps: "Got modules of dimensions:", [Dimension(x): x in S];
	vprint ZReps: "Schur indices:", B;
	STEP_TIME := Cputime(STEP_TIME);

	SplitIrrChars := [rats[t[1]]: t in char_split];
	for i := 1 to #S do
	    M := S[i];

	    if B[i] eq 0 then
		vprint ZMeataxe: "Skip non-split module", i;
		continue;
	    end if;

	    if (CleanLimit eq 0 or Dimension(M) le CleanLimit)
		and not no_clean
		and is_Z(BaseRing(M))
	    then
		M := Clean(M);
	    end if;

	    hh := h;
	    if true then
		//vprint ZReps: "Get char for dim", Dimension(M);
		IndentPush();
		//vtime ZReps:
/*
		    c := GetChar(M);
*/
		    c := Char(M: IrrChars := SplitIrrChars);
		IndentPop();
		vprintf ZReps: "Include %o (max norm %o)\n",
		    M, ModuleMaxNorm(M);
		IndentPush();
		//Append(~hh, SPLIT_TIME);
		Append(~hh, STEP_TIME);
		include_mod(
		    ~rats_schur_indices, ~I, ~IC, ~IS, ~Q_new, ~Qchars, ~history,
		    ~extra, ~extrac, ~extras, ~WantChars, M, B[i], c, hh
		);
		IndentPop();
	    else
		//c := GetChar(M);
		c := Char(M: IrrChars := SplitIrrChars);
		if c notin extrac then
		    Append(~extra, M);
		    Include(~extrac, c);
		    Append(~extras, 1);
		end if;
	    end if;
	end for;

	vprint ZReps: "Step time:", STEP_TIME;
	vprint ZReps: "Current accumulated time:", Cputime(TOTAL_TIME);
    end while;

    II, c := get_II(I, IS, history);
    if c eq #rats then
	extra := [];
    end if;

    vprint ZReps: "Total time:", Cputime(TOTAL_TIME);

    return II, rats, ratsi;
    //return II, rats, extra, MQ;
    //return II, rats, history, extra, MQ;
end intrinsic;

/*******************************************************************************
			    RationalTensorSearch
*******************************************************************************/

intrinsic RationalTensorSearch(c::AlgChtrElt: DegreeLimit := 0) -> []
{Find index pairs of rational characters whose tensor products include c}

    c := &+GaloisOrbit(c);
    D := Support(Vector(RationalCharacterDecomposition(c)));
    assert #D eq 1;
    ci := Rep(D);

    G := Group(Parent(c));
    C := RationalCharacterTable(G);
    L := [];
    for i := 1 to #C do
	if i eq ci or DegreeLimit gt 0 and Degree(C[i]) gt DegreeLimit then
	    continue;
	end if;
	for j := 1 to i do
	    if j eq ci then continue; end if;
	    T := C[i]*C[j];
	    D := Support(Vector(RationalCharacterDecomposition(T)));
	    if ci in D then
		Append(~L, <j, i, Z!Degree(T)>);
	    end if;
	end for;
    end for;

    //degs := [Z!Degree(c): c in C];
    //Sort(~L, func<t, u | degs[t[1]]*degs[t[2]] - degs[u[1]]*degs[u[2]]>);
    Sort(~L, func<t, u | t[3] - u[3]>);
    return L;

end intrinsic;

/*******************************************************************************
				Wrappers
*******************************************************************************/

function module_from_char(chi, UseInduction)

    if Degree(chi) eq 1 and Norm(chi) eq 1 and SchurIndex(chi) eq 1 
       and DegreeOfCharacterField(chi) eq 1 then
	return ChangeRing(GModule(chi), Z);
    end if;

    G := Group(Parent(chi));
    C, CI := RationalCharacterTable(G);
    X := CharacterTable(G);

    Ci := Index(C, chi);
    if Ci eq 0 then
	Xi := Index(X, chi);
	if Xi eq 0 then
	    return 0;
	end if;
	chi := &+GaloisOrbit(chi);
	Ci := Index(C, chi);
	assert Ci ge 1;
    end if;

    R, C2 := InternalIrreducibleIntegralModules(
	G: Characters := [chi], UseInduction := UseInduction
    );
    // assert C2 eq C;

    M := R[Ci, 1];
    return M;

end function;

intrinsic GModule(chi::AlgChtrElt, Z::RngInt: UseInduction) -> ModGrp
{An irreducible G-module over Z which affords the minimal integral
character containing chi};

    M := module_from_char(chi, UseInduction);
    require M cmpne 0:
	"Character is not absolutely irreducible or irreducible over Q";
    return M;

end intrinsic;

intrinsic GModule(chi::AlgChtrElt, Q::FldRat: UseInduction) -> ModGrp
{An irreducible G-module over Q which affords the minimal integral
character containing chi};

    M := module_from_char(chi, UseInduction);
    require M cmpne 0:
	"Character is not absolutely irreducible or irreducible over Q";

    MQ := ChangeRing(M, Q);
    MQ`IsIrreducible := true;
    if assigned M`SchurIndex then
	MQ`SchurIndex := M`SchurIndex;
    end if;
    return MQ;

end intrinsic;
