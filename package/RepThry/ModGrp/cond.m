freeze;

/*
Automatic composition factors via condensation over GF(q).
AKS, Sep 2003.

Main function:

    PermCond(G, K)

where G is perm group, K finite field.

Options:

	H:		use subgroup H for the condensation
	Range:		choose subgroup with #orbits in this range
	UseClasses:	compute classes of G first to find small subgroups
	NumGens:	number of random generators of condensation algebra
*/

// SetVerbose("Condensation", 0);

DEFAULT_SPLIT_LIMIT := 500;
DEFAULT_SPLIT_LIMIT := 1000;
DEFAULT_SPLIT_LIMIT := 1000000;
PERM_RAND_LOOP := 10;

PERM_SEARCH_DENOM := 10;
PERM_SEARCH_DENOM_FAST := 8;

TENSOR_SEARCH_DENOM := 8;
TENSOR_SEARCH_DENOM_FAST := 8;

INDUCTION_SEARCH_DENOM := 10;
INDUCTION_SEARCH_DENOM_FAST := 8;

USE_DELTA := 0;

USE_INDECOMP_SUM := true;
USE_INDECOMP_SUM := false;

NEWCHOP := true and not USE_INDECOMP_SUM;

/*******************************************************************************
			Subgroup search
*******************************************************************************/

procedure try_subgroup(H, p, dim_func, SearchDim, ~bestd, ~bestH)
    if #H eq 1 or GCD(#H, p) gt 1 then
	return;
    end if;
//"try_subgroup H:", H; //: Maximal;
    n := dim_func(H);
//"got n:", n;
    vprint Condensation: "    Try subgroup:", #H, n;
    d := Abs(n - SearchDim);
    if d lt bestd then
	bestd := d;
	bestH := H;
	vprintf Condensation: "New best: %o (distance %o)\n", n, d;
    end if;
end procedure;

procedure try_elt(~seen, g, p, dim_func, SearchDim, ~bestd, ~bestH)
    if g notin seen then
	Include(~seen, g);
	try_subgroup(sub<Parent(g) | g>, p, dim_func, SearchDim, ~bestd, ~bestH);
    end if;
end procedure;

function find_subgroup_pprime(U, K, dim_func: EasyDim := 100)
/*
Try to find subgroup of U whose order is p-prime and whose cond dim is smallest.
*/

    TIME := Cputime();

    p := Characteristic(K);

    vprintf Condensation:
    "Condensation: search for %o-prime subgroup of group of order %o (%o)\n",
	p, #U, FactoredOrder(U);

    procedure try_subgroup(H, ~best_H, ~best_dim)
	if #H mod p eq 0 then
	    return;
	end if;

	dim := dim_func(H);

	vprintf Condensation:
	    "Consider subgroup of order %o, condensed dim %o\n",
	    FactoredOrder(H), dim;

	if dim lt best_dim then
	    vprintf Condensation:
		"New best p-prime subgroup of order %o, condensed dim %o\n",
		#H, dim;
	    best_H := H;
	    best_dim := dim;
	end if;
    end procedure;

    best_H := 0;
    best_dim := 10^10;

    if IsSoluble(U) then
	vprint Condensation: "Soluble; use Hall subgroup";

	PC, f := PCGroup(U);
	H := HallSubgroup(PC, -p);
	H := H@@f;
	try_subgroup(H, ~best_H, ~best_dim);
    end if;

    for q in PrimeBasis(#U) do
	if best_dim lt EasyDim then break; end if;

	vprintf Condensation: "Try Sylow-%o subgroup\n", q;
	if q eq p then
	    continue;
	end if;

	S := SylowSubgroup(U, q);
	try_subgroup(S, ~best_H, ~best_dim);
	if best_dim lt EasyDim then break; end if;

	N := Normalizer(U, S);
	try_subgroup(N, ~best_H, ~best_dim);
    end for;

    
    vprint Condensation: "Get maximal subgroups";
    vtime Condensation: MS := MaximalSubgroups(U);
    vprintf Condensation: "Try %o maximal subgroup(s)\n", #MS;

    for t in MS do
	if best_dim lt EasyDim then break; end if;
	try_subgroup(t`subgroup, ~best_H, ~best_dim);
    end for;

    vprint Condensation: "p-prime subgroup search time:", Cputime(TIME);

    return best_H;

end function;

function find_subgroup(
    G, K, dim_func, SearchDim, UseClasses:
	FAIL := false, ClassesPhi := 0, pprime_U := 0, pprime_U_phi := 0
)

    if FAIL then
	return G;
    end if;

    if pprime_U cmpne 0 then
	H := find_subgroup_pprime(pprime_U, K, dim_func);
	if H cmpne 0 then
	    return (H);
	    return pprime_U_phi(H);
	end if;
    end if;

    TIME := Cputime();

    vprintf Condensation: "Search for subgroup with SearchDim %o\n", SearchDim;

    seen := {};
    bestd := 10^10;
    bestH := 0;
    bestd_stop_range := [0 .. 50];
bestd_stop_range := {0 .. 50};
    p := Characteristic(K);

    if UseClasses then
	if ClassesPhi cmpne 0 then
	    CG := Domain(ClassesPhi);
	    cl := Classes(CG);
	    cl := [ClassesPhi(t[3]): t in cl];
	else
	    cl := [t[3]: t in Classes(G)];
	end if;

	for g in cl do
	    try_elt(~seen, g, p, dim_func, SearchDim, ~bestd, ~bestH);
	    if bestd in bestd_stop_range then break; end if;
	end for;
    end if;

    L := FactoredOrder(G);
    for t in L do
	if bestd in bestd_stop_range then break; end if;
	q, e := Explode(t);
	if q eq p then
	    continue;
	end if;

	S := SylowSubgroup(G, q);
	try_subgroup(S, p, dim_func, SearchDim, ~bestd, ~bestH);
	if bestd in bestd_stop_range then break; end if;
	if e gt 1 then
	    PC, f := PCGroup(S);
	    SS := CompositionSeries(PC);
	    for i := 2 to #SS - 1 do
		//"    Sylow", q, i;
		try_subgroup(SS[i]@@f, p, dim_func, SearchDim, ~bestd, ~bestH);
	    end for;
	end if;
    end for;

    if bestd gt 0 then
	seeno := {};
	for i := 1 to PERM_RAND_LOOP do
	    if bestd in bestd_stop_range then break; end if;
	    r := Random(G);
	    o := Order(r);
	    if o notin seeno then
		if not IsPrime(o) then
		    Include(~seeno, o);
		end if;
		for d in Divisors(o) do
		    if d lt o then
			try_elt(
			    ~seen, r^d, p, dim_func, SearchDim, ~bestd, ~bestH
			);
			if bestd in bestd_stop_range then break i; end if;
		    end if;
		end for;
	    end if;
	end for;
    end if;

    vprint Condensation: "Subgroup search time:", Cputime(TIME);

    return bestH;
end function;

/*******************************************************************************
			    Generators search
*******************************************************************************/

function random_gens(G, H, n)
    if G subset H then
	return {G!1};
    end if;
    R := {};
    while #R lt n do
        repeat
            g := Random(G);
        until g notin H;
        Include(~R, g);
    end while;
    return R;
end function;

/*******************************************************************************
				Delta word
*******************************************************************************/

function delta(M, D)
    e := Dimension(EndomorphismRing(D));

    printf "delta word for %o in %o, e: %o\n", Dimension(D), Dimension(M), e;

    K := BaseRing(M);
    C := [c: c in Constituents(M) | not IsIsomorphic(c, D)];

/*
D: Maximal;
C: Maximal;
*/

    nag := Nagens(M);
    CA := [Action(c): c in C];
    DA := Action(D);
    MA := Action(M);

    i := Random(1, nag);
    DW := DA.i;
    CW := <CA[j].i: j in [1 .. #CA]>;
    MW := MA.i;

    count := 0;

    while true do
	count +:= 1;
	if count eq 10^10 then
	    error "GIVE UP!";
	end if;

	/*
	"DW:", DW;
	"CW:", CW;
	//"MW:", MW;
	*/
	
	fcp := FactoredCharacteristicPolynomial(DW);
	//"delta word factored char poly:", fcp;
	for t in fcp do
	    f := t[1];
	    if e mod Degree(f) eq 0 then
		//"try:", f;
		EDW := Evaluate(f, DW);
		N := Nullspace(EDW);
/*
"EDW:", EDW;
"N:", N;
[<Rank(Evaluate(f, CW[i])), Nrows(CW[i])>: i in [1 .. #CW]];
*/
		if
		    Dimension(N) eq e and
		    forall{
			i: i in [1 .. #CW] |
			    Rank(Evaluate(f, CW[i])) eq Nrows(CW[i])
		    }
		then
		    "Success with:", f;
		    "Tries:", count;
		    return Evaluate(f, MW), N;
		end if;
	    end if;
	end for;

	repeat
	    r1 := Random(K);
	until r1 ne 0;
	i1 := Random(1, nag);
	repeat
	    r2 := Random(K);
	until r2 ne 0;
	i2 := Random(1, nag);

	DW := r1*DW*DA.i1 + r2*DA.i2;
	MW := r1*MW*MA.i1 + r2*MA.i2;
	CW := <r1*CW[j]*CA[j].i1 + r2*CA[j].i2: j in [1 .. #CW]>;
    end while;
end function;

/*******************************************************************************
				Cond chop
*******************************************************************************/

function try_homs(M, C, cilist, want_DD)
    D := [];
    DI := [];
    DD := [];

    for ci in cilist do
	c := C[ci];

	vprintf Condensation: "Get homs for constituent %o, dim %o to dim %o\n",
	    ci, Dimension(c), Dimension(M);
	IndentPush();
	vtime Condensation: H := AHom(c, M);
	IndentPop();
	vprintf Condensation: "Number of homs: %o\n", Dimension(H);
	if Dimension(H) gt 0 then
	    vprint Condensation: "Get images";
	    vtime Condensation: I := ImageWithBasis(H.1, M: Check := false);
	    Append(~D, I);
	    Append(~DI, ci);

	    if want_DD then
		Append(~DD, I);
		for i := 2 to Dimension(H) do
		    vtime Condensation:
			I := ImageWithBasis(H.i, M: Check := false);
		    Append(~DD, I);
		end for;
	    end if;
	end if;
	delete H;
    end for;

    return D, DI, DD;
end function;

CHECK_MAPS := true;
CHECK_MAPS := false;

NEW_METHOD := 0 eq 1;

function condchop(M: CondConstituentDimLimit := 0)

    /*
    CondConstituentDimLimit = d > 0 => don't uncondense constituents
    with dim > d.
    */

    vprintf Condensation: "CONDENSATION CONSTITUENT SEARCH, DIM %o\n",
	Dimension(M);

    // MemProfile();
    TIME := Cputime();

    if NEW_METHOD then

	vprint Condensation: "Get composition series matrix";
	vtime Condensation: CSM := CompositionSeriesMatrix(M);

	vprint Condensation: "Get constituents";
	vtime Condensation: C, CL := Constituents(M);

	CF := CompositionFactors(M);
	CWM := ConstituentsWithMultiplicities(M);

	vprint Condensation:
	    "CompositionFactors:", CF;
	vprint Condensation: "ConstituentsWithMultiplicities:", CWM;
	//vprint Condensation: "Mapping:", CL;

	m := #C;
	assert Max(CL) eq m;
	/*
	pos := Max([Index(CL, i): i in [1 .. #C]]);
	if pos lt #CL then
	    // Computing the action of the new M is too slow.

	    vprintf Condensation:
		"Last constituent at pos %o of %o\n", pos, #CL;
	    d := &+[Dimension(C[CL[i]]): i in [1 .. pos]];
	    vprintf Condensation: "Get submodule of dim %o (from %o)\n",
		d, Dimension(M);
	    SB := RowSubmatrix(CSM, 1, d);
	    SM := ImageWithBasis(SB, M: Check := false);
	    M := SM;
	else
	    vprint Condensation: "Last constituent at top";
	end if;
	delete CSM;
	*/
    else
	CSM := 0;
	vprint Condensation: "Get constituents";
	vtime Condensation: C, CL := Constituents(M);

	CF := CompositionFactors(M);
	CWM := ConstituentsWithMultiplicities(M);

	vprint Condensation:
	    "CompositionFactors:", CF;
	vprint Condensation:
	    "ConstituentsWithMultiplicities:",
	    CWM;

	if CondConstituentDimLimit gt 0 and not NEW_METHOD then
	    I := [
		i: i in [1 .. #C] | Dimension(C[i]) le CondConstituentDimLimit
	    ];
	    C := [C[i]: i in I];
	    CL := [CL[i]: i in I];
	    CWM := [CWM[i]: i in I];
	    vprint Condensation: "Dim limit:", CondConstituentDimLimit;
	    vprint Condensation: "Reduced constituents:", C;
	end if;
    end if;

    D, DI, DD := try_homs(M, C, [1 .. #C], true);
    vprint Condensation: "Initial direct submodules:", D;
    vprint Condensation: "Full direct submodules:", DD;
    // MemProfile();

    INIT_BOUND := 20;

    cwant := [i: i in [1 .. #C] | i notin DI];

    res := [];
    resI := [];

    BI := [i: i in [1 .. #DD] | Dimension(DD[i]) le INIT_BOUND];
    if #BI eq 0 then
	B := sub<M | >;
    else
	B := &+[DD[i]: i in BI];
    end if;

    /*
    Q, Qf := M / sub<M|>;
    QF := [Qf];
    */

    Q := M;
    QF := <>;
    Qmat := 1;
    step := 0;
    maxpos := 0;
    posdimlim := Dimension(M) div 20;
posdimlim := Dimension(M);
posdimlim := Dimension(M) div 5;

    while true do
	if #cwant eq 0 then
	    break;
	end if;

	step +:= 1;

	STIME := Cputime();

	vprint Condensation: "--------";
	vprint Condensation: "New Step", step;
	IndentPush();
	vprint Condensation: "Current quotient:", Q;
	vprint Condensation: "New submodule base B:", B;
	vprint Condensation: "Wanted modules:", [C[i]: i in cwant];
        vprint Condensation: "Current result quotients:", res;
        vprint Condensation: "Current result quotients indices:", resI;

	vprint Condensation: "Get new quotient";
	if CHECK_MAPS then
	    vtime Condensation: NQ, Qf := Q/B;
	    Append(~QF, Qf);
	else
	    vtime Condensation: NQ := Q/B;
	end if;

	Qm := Morphism(Q, NQ);
	if Qmat cmpeq 1 then
	    NQmat := Qm;
	else
	    NQmat := Qmat * Qm;
	end if;

	//"Qm:", Qm;
	//"Qmat:", Qmat;
	//"Qm:", Parent(Qm);
	//"NQMat:", Parent(NQmat);

	QD, QDI := try_homs(NQ, C, cwant, false);

	if #QD gt 0 then

	    BB2 := Morphism(B, Q);
	    if Qmat cmpeq 1 then
		sol := BB2;
		ker := 0;
	    else
		vprint Condensation: "Get B sol";
		vtime Condensation: sol, ker := Solution(Qmat, BB2);
		//"B sol:", Parent(sol);
		//"B ker:", Dimension(ker);
		sol := VerticalJoin(sol, BasisMatrix(ker));
	    end if;
	    //"B sol join:", Parent(sol);
	    vprint Condensation: "Get B ech", Nrows(sol), Ncols(sol);
	    vtime Condensation: sol := EchelonForm(sol);
	    vprint Condensation: "Get B image";
	    vtime Condensation: BB2 := ImageWithBasis(sol, M: Check := false);

	    if CHECK_MAPS then
		BB := B;
		"Do B imap";
		vtime Condensation: for i := #QF-1 to 1 by -1 do
		    BB := BB @@ QF[i];
		end for;
		assert BB2 eq BB;
		//assert IsIsomorphic(BB2, BB);
	    end if;
	    BB := BB2;

	    for d := 1 to #QD do
		I := QD[d];

		I2 := Morphism(I, NQ);
		vprint Condensation: "Get I sol";
		vtime Condensation: sol, ker := Solution(NQmat, I2);
		//"I sol:", Parent(sol);
		//"I ker:", Parent(ker);
		sol := VerticalJoin(sol, BasisMatrix(ker));
		//"I sol join:", Parent(sol);
		vprint Condensation: "Get I ech", Nrows(sol), Ncols(sol);
		vtime Condensation: sol := EchelonForm(sol);
		vprint Condensation: "Get I image";
		vtime Condensation:
		    I2 := ImageWithBasis(sol, M: Check := false);

		if CHECK_MAPS then
		    "Do I imap";
		    vtime Condensation: for i := #QF to 1 by -1 do
			I := I @@ QF[i];
		    end for;
		    assert I2 eq I;
		    //assert IsIsomorphic(I2, I);
		end if;
		I := I2;

		Append(~res, [BB, I]);
		Append(~resI, QDI[d]);
		Exclude(~cwant, QDI[d]);
	    end for;
	end if;

	Qmat := NQmat;
	Q := NQ;

	if #cwant eq 0 then
	    vprint Condensation: "Step time:", Cputime(STIME);
	    IndentPop();
	    break;
	end if;

	L := [i: i in [1 .. #DD] | i notin BI];

	if NEW_METHOD and step ge 1 then

	    vprint Condensation: "Now wanted modules:", [C[i]: i in cwant];

	    pos := [Index(CL, i): i in cwant];
	    vprint Condensation: "Series pos of wanted:", pos;

	    bestd := 0;
	    bestp := 0;
pos := [Min(pos)];
	    for p in pos do
		if p eq 1 or p le maxpos then
		    continue;
		end if;

		pp := p - 1;
		d := &+[Dimension(C[CL[i]]): i in [1 .. pp]];
		vprintf Condensation: "Try pos %o, dim %o, posdimlim %o\n",
		    pp, d, posdimlim;

		if d le posdimlim and d gt bestd then
		    vprint Condensation: "New max";
		    bestp := pp;
		    bestd := d;
		end if;
	    end for;

	    if bestp gt 0 then
		p := bestp;
		d := bestd;
		vprintf Condensation: "Use CS: pos %o, dim %o\n", p, d;
		vprintf Condensation: "Get submodule of dim %o (from %o)\n",
		    d, Dimension(M);
		SB := RowSubmatrix(CSM, 1, d);

		vprint Condensation: "Get SB prod";
		vtime Condensation: SB := SB * Qmat;
		vprint Condensation: "Get ech, nrows:", Nrows(SB);
		vtime Condensation: SB := BasisMatrix(Rowspace(SB));
		vprint Condensation: "Get image, nrows:", Nrows(SB);
		vtime Condensation: B := ImageWithBasis(SB, Q: Check := false);
		vtime Condensation: "Got B:", B;

		maxpos := p;

		vprint Condensation: "Step time:", Cputime(STIME);
		IndentPop();

		continue;
	    end if;

	    posdimlim *:= 1.1;
	end if;

	if #L eq 0 then
	    vprint Condensation: "Nothing in DD";

	    S := 0;
	    for ci in [1 .. #C] do
		c := C[ci];
		vprintf Condensation:
		    "Get homs for constituent %o, dim %o to quo dim %o\n",
		    ci, Dimension(c), Dimension(Q);
		IndentPush();
		vtime Condensation: H := AHom(c, Q);
		IndentPop();
		vprintf Condensation: "Number of homs: %o\n", Dimension(H);
		if Dimension(H) gt 0 then
		    vtime Condensation: S := ImageWithBasis(
			H.1, Q: Check := false
		    );
		    break;
		end if;
		delete H;
	    end for;
	    if S cmpeq 0 then
		error "FAIL";
	    end if;
	    B := S;
	else
	    i := L[1];
	    B := DD[i];

	    Append(~BI, i);
	    vprint Condensation: "USE DD", i, B;

	    vprint Condensation: "Get B2 prod";
	    B2 := Morphism(B, M);
	    vtime Condensation: B2 := B2 * Qmat;
	    vprint Condensation: "Get B2 ech";
	    vtime Condensation: B2 := BasisMatrix(Rowspace(B2));
	    vprint Condensation: "Get image";
	    vtime Condensation: B2 := ImageWithBasis(B2, Q: Check := false);
	    //"B2:", Parent(B2);

	    if CHECK_MAPS then
		"Use map";
		vtime Condensation: for i := 1 to #QF do
		    B := QF[i](B);
		end for;
		assert B2 eq B;
	    end if;
	    B := B2;
	end if;

	vprint Condensation: "Step time:", Cputime(STIME);
	IndentPop();

	//"Now B:", B;
    end while;

    DM := [CWM[j, 2]: j in DI];
    resM := [CWM[j, 2]: j in resI];

    vprint Condensation: "Found all:", D, res;
    vprintf Condensation: "Indices: %o, %o\n", DI, resI;
    vprintf Condensation: "Multiplicities: %o, %o\n", DM, resM;
    vprint Condensation: "Condensation constituent search time:", Cputime(TIME);

    return D, DM, res, resM, true;

end function;

/*******************************************************************************
				Common split
*******************************************************************************/

default_ngens := func<G, K | 30>;

function split(CM: CondConstituentDimLimit := 0)

    if USE_INDECOMP_SUM then

	vprint Condensation: "Get IndecomposableSummands of", CM;
//CM: Magma;
	IndentPush();
	vtime Condensation: L := IndecomposableSummands(CM);
	IndentPop();
	vprint Condensation: "Got IndecomposableSummands:", L;

	D := [Dimension(S): S in L];
	T := VerticalJoin(<Morphism(S, CM): S in L>);
	CF := D;

    elif USE_DELTA gt 0 then
	CF := Constituents(CM);
	L := [];
	for C in CF do
	    "Do delta for:", C;
	    IndentPush();
	    D := delta(CM, C);
	    IndentPop();
	    DK := Kernel(D);
	    "Kernel dim:", Dimension(DK);
	    best := -1;
	    bestd := 10^10;
	    for i := 1 to Dimension(DK) do
		S := sub<CM | DK.i>;
		d := Dimension(S);
		printf "Vector %o: subdim %o\n", i, d;
		if d lt bestd then
		    bestd := d;
		    best := S;
		end if;
	    end for;
	    Append(~L, S);
	end for;

L := L[#L .. #L];
CF := CF[#CF .. #CF];

	D := [Dimension(S): S in L];
	T := VerticalJoin(<Morphism(S, CM): S in L>);

//"Got S:", S;
//"Got D:", D;
//"Got T:", T;
    elif NEWCHOP then

	direct, directM, R, RM := condchop(
	    CM: CondConstituentDimLimit := CondConstituentDimLimit
	);

	return <direct, directM, R, RM>;

    else
	vprint Condensation: "Get condensed composition series";
	vtime Condensation:
	    T := CompositionSeriesMatrix(CM);

	CF := CompositionFactors(CM);
	D := [Dimension(M): M in CF];

	vprint Condensation: "Number of factors:", #CF;
	vprint Condensation: "Factor dimensions:", D;

//vprintf Condensation: "CM := %m;\n", CM;

	if 0 eq 1 then
	    vprint Condensation: "Get IndecomposableSummands of", CM;
	    IndentPush();
	    vtime Condensation: IS := IndecomposableSummands(CM);
	    IndentPop();
	    vprint Condensation: "Got IndecomposableSummands:", IS;

	    /*
	    vprint Condensation: "Get Socle";
	    IndentPush();
	    vtime Condensation: socle := Socle(CM);
	    IndentPop();
	    vprint Condensation: "Socle:", socle, "Orig CM:", CM;
	    */
	end if;

    end if;

    return <T, CF, D>;
end function;

/*******************************************************************************
				Tensor
*******************************************************************************/

Z := IntegerRing();

function clear_nd(X)
    return X;
end function;

function is_iso(M, N)
    return IsIsomorphic(M, N);
end function;

function decomp_S(M)
    C := ConstituentsWithMultiplicities(M);
    B := <b: b in Basis(GHomOverCentralizingField(t[1], M)), t in C>;
    T := VerticalJoin(B);
    S := [ImageWithBasis(b, M): b in B];
    return S, T, C;
end function;

function tcond_dim(M, N, H)
//"tcond_dim"; "M:", M; "N:", N; "H:", H: Maximal;
    assert GCD(Characteristic(BaseRing(M)), #H) eq 1;

    VM := GetVerbose("Meataxe");
    SetVerbose("Meataxe", 0);
    VS := GetVerbose("Spin");
    SetVerbose("Spin", 0);

//"MH"; time
    MH := Restriction(M, H);
    if M cmpeq N then
	NH := MH;
    else
//"NH"; time
	NH := Restriction(N, H);
    end if;
    NC := ConstituentsWithMultiplicities(NH);
    D := 0;
    for t in ConstituentsWithMultiplicities(MH) do
	C, Me := Explode(t);
	TC := Dual(C);
	for u in NC do
	    if IsIsomorphic(TC, u[1]) then
		Ne := u[2];
		// "Here", Dimension(C), Me, Ne, EndomorphismRing(C);
		D +:= Me*Ne*Dimension(EndomorphismRing(C));
		break;
	    end if;
	end for;
    end for;

    SetVerbose("Meataxe", VM);
    SetVerbose("Spin", VS);

    return D;
end function;

dim_func_perm := func<H | #Orbits(H)>;
dim_func_tensor := func<M1, M2 | func<H | tcond_dim(M1, M2, H)>>;
dim_func_ind := func<G, MH | 
    func<S | InternalInductionCondensationSetup(G, MH, S: CondensedDimOnly)>
>;

function tcond(M, N, H, G_list)

    TZEIT := Cputime();
    ZEIT := Cputime();

    vprint Condensation: "Tensor condensation";

    assert Dimension(M) le Dimension(N);

    vprint Condensation: "Input dimensions:", Dimension(M), Dimension(N);
    vprint Condensation: "Subgroup order:", #H;

    R := BaseRing(M);
    K := FieldOfFractions(R);
    over_Z := R cmpeq Z;
    if over_Z then
	lift := func<X | ChangeRing(X, K)>;
    else
	lift := func<X | X>;
    end if;

    C := [];
    MCI := [];
    Mpos := [];
    NCI := [];
    Npos := [];
    Mi := 1;
    Mp := 1;

    MH := Restriction(M, H);

    if 0 eq 1 and Ngens(H) then
// This is now WRONG!!!  Must handle Dual(N component)
	assert Nagens(MH) eq 1;

	MX := ActionGenerator(MH, 1);
	_, MT, MF := PrimaryRationalForm(lift(MX));
	MTI := lift(MT)^-1;
	MM := lift(M)^MTI;

	if M cmpeq N then
	    NH := MH;
	    NT := MT;
	    NF := MF;
	    NN := MM;
	else
	    NH := Restriction(N, H);
	    NX := ActionGenerator(NH, 1);
	    _, NT, NF := PrimaryRationalForm(lift(NX));
	    NTI := lift(NT)^-1;
	    NN := lift(N)^NTI;
	end if;

	// "MF:", MF;
	// "NF:", NF;

	MC := [];
	NC := [];
	Mi := 1;
	while Mi le #MF do
	    F, Fm := Explode(MF[Mi]);
	    assert Fm eq 1;
	    Me := 1;
	    while Mi + Me le #MF do
		if MF[Mi + Me, 1] eq F then
		    Me +:= 1;
		else
		    break;
		end if;
	    end while;
	    cd := Degree(F);

	    if M cmpeq N then
		Ni := Mi;
		Ne := Me;
		Np := Mp;
	    else
		Ni := 0;
		Ne := 0;
		Np := 1;
		for j := 1 to #NF do
		    if NF[j, 1] eq F then
			Ni := j;
			Ne := 1;
			while Ni + Ne le #NF do
			    if NF[Ni + Ne, 1] eq F then
				Ne +:= 1;
			    else
				break;
			    end if;
			end while;
			break;
		    end if;
		    Np +:= Degree(NF[j, 1]);
		end for;
	    end if;

	    if Ni gt 0 then
		c := GModule(H, [CompanionMatrix(F)]);
		Append(~C, c);
		Append(~MC, <c, Me>);
		Append(~MCI, [Mi .. Mi + Me - 1]);
		Append(~Mpos, Mp);

		Append(~NC, <c, Ne>);
		Append(~NCI, [Ni .. Ni + Ne - 1]);
		Append(~Npos, Np);
	    end if;

	    Mi +:= Me;
	    Mp +:= Me * cd;
	end while;

	// vprint Condensation: "Mpos:", Mpos;
	// vprint Condensation: "Npos:", Npos;

    else
	MS, MT, MC := decomp_S(MH);

	// "MS:", MS;
	// "MC:", MC;

	// Assume each constit in C is first submodule in S iso to C

	MTI := lift(MT)^-1;
	MM := lift(M)^MTI;

	if 1 eq 1 and Dimension(M) le Dimension(N) then
	    NH := Restriction(N, H);
	    Ni := 1;
	    Np := 1;
	    NC := <>;
	    NT := <>;
	    for i := 1 to #MC do
		ci, ei := Explode(MC[i]);
		cd := Dimension(ci);
		Append(~C, ci);
		Append(~MCI, [Mi .. Mi + ei - 1]);
		Append(~Mpos, Mp);

		U := GHomOverCentralizingField(Dual(ci), NH);
		// printf "i: %o, ci: %o, U: %o\n", i, ci, U;
		Ne := Dimension(U);
		if Dimension(U) gt 0 then
		    for h in Basis(U) do
			Append(~NT, Matrix(h));
		    end for;
		    //V := [ImageWithBasis(NH, h): h in Basis(U)];
		    Append(~NC, <ImageWithBasis(U.1, NH), Ne>);
		    Append(~NCI, [Ni .. Ni + Ne - 1]);
		    Append(~Npos, Np);
		    Ni +:= Ne;
		    Np +:= Ne * cd;
		else
		    Append(~NC, <>);
		    Append(~NCI, []);
		    Append(~Npos, Np);
		end if;

		Mi +:= ei;
		Mp +:= ei * cd;
	    end for;

	    if #NT eq 0 then
		NT := Matrix(R, 0, Dimension(NH), []);
	    else
		NT := VerticalJoin(NT);
	    end if;
	    // "First NT:", NT;

	    assert Nrows(NT) le Dimension(NH);
	    if Nrows(NT) lt Dimension(NH) then
                for cj in Constituents(NH) do
                    dcj := Dual(cj);
                    if not exists{c: c in C | is_iso(dcj, c)} then
                        TB := VerticalJoin(
                            [b: b in Basis(GHomOverCentralizingField(cj, NH))]
                        );
                        vprintf Condensation:
			    "Extra N constituent dim: %o, new rows: %o\n",
                            Dimension(cj), Nrows(TB);
                        NT := VerticalJoin(NT, TB);
                    end if;
                end for;
                //"Now NT:", Parent(NT);
	    end if;
	    NTI := lift(NT)^-1;
	    NN := lift(N)^NTI;

	    // vprint Condensation: "MCI:", MCI;
	    // vprint Condensation: "NCI:", NCI;
	    // "Mpos:", Mpos;
	    // "Npos:", Npos;
	else
	    if M cmpeq N then
		NH := MH;
		NS := MS;
		NT := MT;
		NC := MC;

		NTI := MTI;
		NN := MM;
	    else
		NH := Restriction(N, H);
		NS, NT, NC := decomp_S(NH);

		NTI := lift(NT)^-1;
		NN := lift(N)^NTI;
		vprint Condensation: "NC:", NC;
	    end if;

	    Ndone := [false: j in [1 .. #NC]];
	    for i := 1 to #MC do
		ci, ei := Explode(MC[i]);
		cd := Dimension(ci);
		Append(~C, ci);
		Append(~MCI, [Mi .. Mi + ei - 1]);
		Append(~Mpos, Mp);

		dci := Dual(ci);
		if exists(j){j: j in [1 .. #NC] | is_iso(dci, NC[j, 1])}
		then
		    Ni := &+[Z | NC[k, 2]: k in [1 .. j - 1]] + 1;
		    Np := &+[Z |
			NC[k, 2]*Dimension(NC[k, 1]): k in [1 .. j - 1]]+1;
		    ej := NC[j, 2];
		    Append(~NCI, [Ni .. Ni + ej - 1]);
		    Append(~Npos, Np);
		    Ndone[j] := true;
		else
		    Append(~NCI, []);
		    Append(~Npos, 0);
		end if;

		Mi +:= ei;
		Mp +:= ei * cd;
	    end for;

	    Ni := 1;
	    Np := 1;
	    for j := 1 to #NC do
		cj, ej := Explode(NC[j]);
		cd := Dimension(cj);
		if not Ndone[j] then
		    Append(~C, cj);
		    Append(~MCI, []);
		    Append(~Mpos, 0);
		    Append(~NCI, [Ni .. Ni + ej - 1]);
		    Append(~Npos, Np);
		end if;
		Ni +:= ej;
		Np +:= ej * cd;
	    end for;

	    // "Mpos:", Mpos;
	    // "Npos:", Npos;
	end if;
    end if;

    ci := 0;

    vprint Condensation: "Constituents:";
    vprint Condensation: C;
    vprint Condensation: "M constituent indices:";
    vprint Condensation: MCI;
    vprint Condensation: "N constituent indices:";
    vprint Condensation: NCI;

    Q := <>;
    P := <>;

    for i := 1 to #C do
	ci := C[i];
	if #MCI[i] gt 0 and #NCI[i] gt 0 then
	    //Ms := MS[MCI[i, 1]];
	    //Ns := NS[NCI[i, 1]];
	    Ms := MC[i, 1];
	    Ns := NC[i, 1];
	    //"Ms:", Ms;
	    //"Ns:", Ns;
	    Mrep := Representation(Ms);
	    Nrep := Representation(Ns);
	    E := &+[TensorProduct(Mrep(h), Nrep(h)): h in H];
	    E := Matrix(K, E);
	    E := E/#H;
	    //"E:", E;

	    q := BasisMatrix(RowSpace(E));
	    p := Solution(q, E);
	    //"q:", q;
	    //"p:", p;
	    assert IsOne(q*p);

	    Append(~Q, q);
	    Append(~P, p);

	else
	    z := MatrixRing(K, 0)!0;
	    Append(~Q, z);
	    Append(~P, z);
	end if;
    end for;

    // "P:", P;
    // "Q:", Q;
    //"MM:", MM: Maximal;

    MCL := [#q: q in MCI];
    NCL := [#q: q in NCI];

    pdims := [Nrows(q): q in Q];

    vprint Condensation: "MCL:", MCL;
    vprint Condensation: "NCL:", NCL;
    vprint Condensation: "Projection dims:", [Nrows(q): q in Q];
//assert 0 notin pdims;

    d := &+[Z | MCL[i] * NCL[i] * Nrows(Q[i]): i in [1 .. #C]];

    vprint Condensation: "Condensed dimension:", d;

    //error "STOP!";

    MMrep := Representation(MM);
    NNrep := Representation(NN);

    vprint Condensation: "Initial setup time:", Cputime(ZEIT);
    ZEIT := Cputime();

    L := [];
    for g in G_list do
	X := MatrixRing(K, d) ! 0;

	Mg := MMrep(g);
	Ng := NNrep(g);

	X := InternalTensorProductAction(
	    Mg, Ng, <C, MCL, NCL, Mpos, Npos, P, Q>
	);

	Append(~L, X);
    end for;

    vprint Condensation: "Algebra setup time:", Cputime(ZEIT);
    vprint Condensation: "Total time:", Cputime(TZEIT);

    info := <M, N, MT, NT, C, MCI, Mpos, NCI, Npos, Q, MM, NN>;
    return L, info;
end function;

function tuncond(info, V)

    R := BaseRing(V);

    M, N, MT, NT, C, MCI, Mpos, NCI, Npos, Q := Explode(info);

    K := FieldOfFractions(R);

    Md := Dimension(M);
    Nd := Dimension(N);

    U := RMatrixSpace(K, Nrows(V), Md*Nd) ! 0;

    nr := Nrows(V);
    Xi := 1;
    for i := 1 to #C do
	ci := C[i];
	cid := Dimension(ci);
	qi := Q[i];

	Mipos := Mpos[i];
	for mi in MCI[i] do

	    Nipos := Npos[i];
	    for ni in NCI[i] do

		upos := (Mipos - 1) * Nd + Nipos;

		v := Submatrix(V, 1, Xi, nr, Nrows(qi));
		v := Matrix(K, v) * Matrix(K, qi);

		pos := 1;
		for k := 1 to cid do
		    // printf "Copy %o, len %o to %o\n", pos, cid, upos;
		    InsertBlock(~U, Submatrix(v, 1, pos, nr, cid), 1, upos);
		    upos +:= Nd;
		    pos +:= cid;
		end for;

		Xi +:= Nrows(qi);
		Nipos +:= cid;
	    end for; // for ni
	    Mipos +:= cid;
	end for; // for mi
    end for; // for i

    U := TensorProductAction(U, Transpose(MT), NT);
    return U;
end function;

/*******************************************************************************
				Perm Setup
*******************************************************************************/

function perm_setup(
    G, K, H, NumGens, Group:
    SeriesFunc := SeriesFactors, CondConstituentDimLimit := 0
)
    vprintf Condensation: "Subgroup order: %o\n", #H;

    R := Setseq(random_gens(G, H, NumGens));

    vprintf Condensation: "Condensed dimension: %o\n", #Orbits(H);
    vprint Condensation: "Set up condensed module";
    vtime Condensation:
	CM := CondensedModule(H, R, K);

    sinfo := split(CM: CondConstituentDimLimit := CondConstituentDimLimit);
    return CM, sinfo,
	func<T | Uncondense(H, T)>,
	func<U, D | SeriesFunc(U, D, G: Group := Group)>;
end function;

/*******************************************************************************
				Tensor Setup
*******************************************************************************/

function tensor_setup(
    M1, M2, H, NumGens, GG:
    SeriesFunc := SeriesFactors, CondConstituentDimLimit := 0
)
    if Dimension(M1) gt Dimension(M2) then
	T := M1;
	M1 := M2;
	M2 := T;
	vprint Condensation: "Swap inputs";
    end if;

    vprintf Condensation: "Tensor condensation; dims: %o, %o\n",
	Dimension(M1), Dimension(M2);

    vprintf Condensation: "Subgroup order: %o\n", #H;

    G := Group(M1);
    if BaseRing(M1) cmpne BaseRing(M2) or Group(M2) cmpne G then
	error "Incompatible modules!";
    end if;

    R := [Random(G): i in [1 .. NumGens]];

    vprint Condensation: "Set up condensed module";
    vtime Condensation:
	TC, tinfo := tcond(M1, M2, H, R);

    CM := RModule(TC);
    if Dimension(CM) eq 0 then
	vprint Condensation: "Condensed module is trivial!";
	return 0, _,_,_;
    end if;

    sinfo := split(CM: CondConstituentDimLimit := CondConstituentDimLimit);

    return CM, sinfo,
	func<T | tuncond(tinfo, T)>,
	func<U, D | SeriesFunc(U, D, Transpose(M1), M2: Group := GG)>;
end function;

/*******************************************************************************
				Tensor Setup
*******************************************************************************/

function ind_setup(
    G, MH, S, NumGens, GG:
    SeriesFunc := SeriesFactors, CondConstituentDimLimit := 0
)
    vprintf Condensation: "Induction condensation; dim: %o, index %o\n",
	Dimension(MH), Index(G, Group(MH));

    vprintf Condensation: "Subgroup order: %o\n", #S;

    vprint Condensation: "Set up condensed module";
    info := InternalInductionCondensationSetup(G, MH, S);

    vtime Condensation:
	CM := RModule([info`get_ege(Random(G)): i in [1 .. NumGens]]);

    if Dimension(CM) eq 0 then
	vprint Condensation: "Condensed module is trivial!";
	return 0, _,_,_;
    end if;

    sinfo := split(CM: CondConstituentDimLimit := CondConstituentDimLimit);

    vprint Condensation: "Set up induction action";
    vtime Condensation:
	MQ, IQ := info`set_up_action_seqs([G.i: i in [1 .. Ngens(G)]]);

    return CM, sinfo,
	func<T | info`uncond(T)>,
	func<U, D | SeriesFunc(U, D, MQ, IQ: Group := GG)>;
end function;

/*******************************************************************************
			    Full condensation
*******************************************************************************/

function do_cond_inner(
    CM, T, D, uncond, spin, SplitLimit:
    Process := false, SplitStart := 1
)

    vprintf Condensation:
	"Uncondense composition series (number of rows: %o)\n", Nrows(T);
    vtime Condensation:
	U := uncond(T);

    vprint Condensation: "Spin list to uncondensed submodules";
    vprint Condensation: "List dims:", D;

    sv := GetVerbose("Spin");
    if GetVerbose("Condensation") ge 1 then
	SetVerbose("Spin", 1);
    end if;

    vtime Condensation:
	F := spin(U, D);

    SetVerbose("Spin", sv);

    if Process then
	return F;
    end if;

    vprint Condensation: "Fully split modules up to dimension", SplitLimit;
    vprint Condensation: "Original modules of dim:", [Dimension(M): M in F];

    F := [F[i]: i in [SplitStart .. #F] | Dimension(F[i]) ne 0];

    vprint Condensation: "Now modules of dim:", [Dimension(M): M in F];

    if USE_INDECOMP_SUM then
	return F;
    end if;

    STIME := Cputime();
    FF := [];
    for M in F do
	if Dimension(M) le SplitLimit then
	    cf := CompositionFactors(M);
	    FF cat:= cf;
	    if #cf gt 1 then
		vprintf Condensation:
		    "Module of dimension %o splits into %o\n",
		    Dimension(M), [Dimension(m): m in cf];
	    end if;
	else
	    Append(~FF, M);
	end if;
    end for;

    vprint Condensation: "Fully split time:", Cputime(STIME);

    return FF;
end function;

function do_cond(
    CM, sinfo, uncond, spin, SplitLimit: Process := false
)

    if NEWCHOP then

	direct, directM, R, RM := Explode(sinfo);
	vprint Condensation: "NEW Uncondense";
	vprint Condensation: "Direct submodules:", direct;
	vprint Condensation: "Direct multiplicities:", directM;
	vprint Condensation: "Quotient sections:", R;
	vprint Condensation: "Quotient multiplicities:", RM;

	// MemProfile();

	FF := [];

	for di := 1 to #direct do
	    DM := direct[di];
	    vprintf Condensation:
		"Uncondense and spin direct submodule of dim %o\n",
		Dimension(DM);

	    T := Morphism(DM, CM);
	    D := [Dimension(DM)];
	    IndentPush();
	    F := do_cond_inner(
		CM, T, D, uncond, spin, SplitLimit: Process := Process
	    );
	    vprint Condensation: "Got uncondensed submodule:", F[1];
	    mult := #F eq 1 select directM[di] else 1;
	    FF cat:= [<M, mult>: M in F];
	    IndentPop();
	end for;

	// MemProfile();

	for qi := 1 to #R do
	    t := R[qi];
	    RS, RC := Explode(t);

	    vprint Condensation: "Uncondense and spin quotient section:", t;

	    /*
	    T := Morphism(RC, CM);
	    D := [Dimension(RS), Dimension(RC) - Dimension(RS)];
	    */

	    T := Morphism(RS, CM);
	    T := VerticalJoin(T, Morphism(RC, CM));
	    D := [Dimension(RS), Dimension(RC)];

	    //"Quo D:", D;
	    IndentPush();
	    F := do_cond_inner(
		CM, T, D, uncond, spin, SplitLimit: Process := Process,
		SplitStart := 2
	    );
	    mult := #F eq 1 select RM[qi] else 1;
	    FF cat:= [<M, mult>: M in F];
	    vprint Condensation: "Got uncondened quotient module(s):", F;
	    IndentPop();
	end for;

    else
	T, CF, D := Explode(sinfo);
	FF := do_cond_inner(
	    CM, T, D, uncond, spin, SplitLimit: Process := Process
	);

	if Process then
	    return FF, CM;
	end if;

	Sort(~FF, func<m1, m2 | Dimension(m1) - Dimension(m2)>);

	F := [];
	E := [];
	vprint Condensation: "Count multiplicities";
	vtime Condensation:
	    for M in FF do
		seen := false;
		for i := 1 to #F do
		    if IsIsomorphic(M, F[i]) then
			E[i] +:= 1;
			seen := true;
		    end if;
		end for;
		if not seen then
		    Append(~F, M);
		    Append(~E, 1);
		end if;
	    end for;

	FF := [<F[i], E[i]>: i in [1 .. #F]];

    end if;

    Sort(~FF, func<t1, t2 | Dimension(t1[1]) - Dimension(t2[1])>);
    return FF, CM;
end function;

GetSeriesFunc :=
    func<Process | Process select SeriesProcess else SeriesFactors>;

get_pprime_U := func<U | IsTrivial(U) select 0 else U>;

procedure check_mults(F, D)
    d := &+[IntegerRing() | Dimension(t[1])*t[2]: t in F];
    if d eq D then
	vprintf Condensation: "ALL constituents (sum %o) found\n", d;
    else
	vprintf Condensation:
	    "ONLY PARTIAL constituents (sum %o out of %o) found\n", d, D;
    end if;
end procedure;

//function PermCond(
intrinsic PermCond(
    G, U, K:
	Group := G,
	UseClasses := assigned G`Classes,
	SearchDim := 0, H := 0,
	NumGens := default_ngens(G, K),
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	CondConstituentDimLimit := 0,
	Process := false,
	pPrime := false
) -> []
{Permutation condensation of coset action of G on U, over field K
(give 0 for U for perm rep G itself)}
    TIME := Cputime();

    HH := H;
    //if false and IsTrivial(U) then
    if U cmpeq 0 then
	GG := G;
	phi := Coercion(G, G);
        U := sub<G|>;
    else
	phi, GG := CosetAction(G, U);
	if H cmpne 0 then
	    HH := phi(H);
	end if;
    end if;

    vprintf Condensation: "PermCond (deg %o)\n", Degree(GG);

    if HH cmpeq 0 then
	if SearchDim eq 0 then
	    SearchDim := Round(Degree(GG)/PERM_SEARCH_DENOM);
	end if;
	HH := find_subgroup(
	    GG, K, dim_func_perm, SearchDim, UseClasses:
	    ClassesPhi := phi,
	    //pprime_U := get_pprime_U(U), pprime_U_phi := phi
	    pprime_U := pPrime select get_pprime_U(phi(U)) else 0,
	    pprime_U_phi := phi
	);
        vprint Condensation: "Condensation subgroup:", HH: Minimal;
    end if;

    CM, sinfo, uncond, spin := perm_setup(
	GG, K, HH, NumGens, Group:
	    SeriesFunc := GetSeriesFunc(Process),
	    CondConstituentDimLimit := CondConstituentDimLimit
    );
    F, CM := do_cond(CM, sinfo, uncond, spin, SplitLimit: Process := Process);

    check_mults(F, Degree(GG));
    vprintf Condensation: "Total PermCond (deg %o) time: %o\n",
	Degree(GG), Cputime(TIME);

    return F, CM;
end intrinsic;

TENSOR_INPUT_TOO_BIG_DIM := 300;
TENSOR_INPUT_TOO_BIG_DIM := 1000;
TENSOR_INPUT_TOO_BIG_DIM := 1000000;

function TensorCondHard(
    M1, M2:
	GG := Group(M1),
	Group := GG,
	UseClasses := assigned GG`Classes,
	SearchDim := Round(Dimension(M1)*Dimension(M2)/TENSOR_SEARCH_DENOM),
	NumGens := default_ngens(GG, BaseRing(M1)),
	H := 0,
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	Process := false
)
    if Dimension(M1) eq 1 then
	return [<M2, 1>];
    end if;
    if Dimension(M2) eq 1 then
	return [<M1, 1>];
    end if;

    if Max(Dimension(M1), Dimension(M2)) ge TENSOR_INPUT_TOO_BIG_DIM then
	return [];
    end if;

    if H cmpeq 0 then
	H := find_subgroup(
	    GG, BaseRing(M1), dim_func_tensor(M1, M2), SearchDim, UseClasses
	);
    end if;

    CM, sinfo, uncond, spin := tensor_setup(
	M1, M2, H, NumGens, Group: SeriesFunc := GetSeriesFunc(Process)
    );
    if CM cmpeq 0 then
	return [];
    end if;
    return do_cond(CM, sinfo, uncond, spin, SplitLimit: Process := Process);
end function;

intrinsic TensorCond(
    M1, M2:
	GG := Group(M1),
	Group := GG,
	UseClasses := assigned GG`Classes,
	SearchDim := Round(Dimension(M1)*Dimension(M2)/TENSOR_SEARCH_DENOM),
	H := 0,
	NumGens := default_ngens(GG, BaseRing(M1)),
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	Process := false
) -> []
{Tensor condensation of modules M1 and M2}
    if Dimension(M1) eq 1 then
	return [<M2, 1>];
    end if;
    if Dimension(M2) eq 1 then
	return [<M1, 1>];
    end if;

    if Max(Dimension(M1), Dimension(M2)) ge TENSOR_INPUT_TOO_BIG_DIM then
	return [];
    end if;

    vprintf Condensation: "TensorCond (dim %o, %o)\n",
	Dimension(M1), Dimension(M2);
    TIME := Cputime();

    if H cmpeq 0 then
	H := find_subgroup(
	    GG, BaseRing(M1), dim_func_tensor(M1, M2), SearchDim, UseClasses
	);
        vprint Condensation: "Condensation subgroup:", H: Minimal;
    end if;

    CM, sinfo, uncond, spin := tensor_setup(
	M1, M2, H, NumGens, Group: SeriesFunc := GetSeriesFunc(Process)
    );
    if CM cmpeq 0 then
	return [];
    end if;
    F, CM := do_cond(CM, sinfo, uncond, spin, SplitLimit: Process := Process);

    check_mults(F, Dimension(M1)*Dimension(M2));
    vprintf Condensation: "Total TensorCond (dim %o, %o) time: %o\n",
	Dimension(M1), Dimension(M2), Cputime(TIME);

    return F, CM;
end intrinsic;

intrinsic IndCond(
    G::Grp, MH::ModGrp:
	GG := G,
	UseClasses := assigned GG`Classes,
	SearchDim := Round(
	    Dimension(MH)*Index(G, Group(MH))/INDUCTION_SEARCH_DENOM
	),
	S := 0,
	NumGens := default_ngens(GG, BaseRing(MH)),
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	Process := false
) -> []
{Induction condensation of HM induced to G (with automatic search for
subgroup S by default)}

    // S is condensation subgroup

    H := Group(MH);
    ind := Index(G, H);
    vprintf Condensation: "IndCond (dim %o, index %o)\n", Dimension(MH), ind;
    TIME := Cputime();

    if S cmpeq 0 then
	S := find_subgroup(
	    GG, BaseRing(MH), dim_func_ind(G, MH), SearchDim, UseClasses
	);
        vprint Condensation: "Condensation subgroup:", S;
    end if;

    CM, sinfo, uncond, spin := ind_setup(
	G, MH, S, NumGens, GG: SeriesFunc := GetSeriesFunc(Process)
    );
    if CM cmpeq 0 then
	return [];
    end if;
    F, CM := do_cond(CM, sinfo, uncond, spin, SplitLimit: Process := Process);

    check_mults(F, Dimension(MH)*ind);
    vprintf Condensation: "Total IndCond (dim %o, index %o) time: %o\n",
	Dimension(MH), ind, Cputime(TIME);

    return F, CM;
end intrinsic;

/*******************************************************************************
			    Fast condensation
*******************************************************************************/

function do_cond_fast(CM, sinfo, uncond, spin, SplitLimit, ExtraLimit)

    T, CF, D := Explode(sinfo);

    CWM := ConstituentsWithMultiplicities(CM);
    C := [t[1]: t in CWM];
    vprint Condensation: "Constituent dimensions and mults:",
	[<Dimension(t[1]), t[2]>: t in CWM];
    want := { 1 .. #C };
    pos := [];
    k := 0;
    while k lt #CF do
	k +:= 1;
	M := CF[k];
	d := Dimension(M);
	if #want eq 0 then
	    if d gt ExtraLimit then
		k -:= 1;
		break;
	    else
		vprintf Condensation: "Include extra module of dim %o\n", d;
	    end if;
	end if;
	for i := 1 to #C do
	    if IsIsomorphic(M, C[i]) then
		vprintf Condensation:
		    "Found constituent %o (dim %o, mult %o) at factor %o\n",
		    i, Dimension(M), CWM[i, 2], k;
		pos[k] := i;
		Exclude(~want, i);
		break;
	    end if;
	end for;
    end while;

    vprint Condensation: "Reduced length:", k;
    vprint Condensation: "pos:", pos;
    D := D[1 .. k];
    T := RowSubmatrix(T, 1, &+D);

    vprintf Condensation:
    "Uncondense composition series (number of rows: %o)\n", Nrows(T);
    vtime Condensation:
	//U := Uncondense(H, T);
	U := uncond(T);

    vprint Condensation: "Get uncondensed factors";
    vtime Condensation:
	//F := SeriesFactors(U, D, G: Group := Group);
	F := spin(U, D);

    if USE_DELTA gt 0 then
	return F;
    end if;

    OF := F;
    vprint Condensation: "First factor dims:", [Dimension(M): M in F];
    P := [[]: i in [1 .. #C]];
    for i := 1 to k do
	M := F[i];
	Append(~P[pos[i]], M);
    end for;

    //"P:", P;

    FF := [];
    BF := [];
    vprint Condensation: "Check consistency";
    vtime Condensation:
	for i := 1 to #C do
	    L := P[i];
	    vprintf Condensation:
		"Constituent %o uncondensed dims: %o\n",
		i, [Dimension(M): M in L];
	    consistent := true;
	    M := L[1];
	    for j := 2 to #L do
		if not IsIsomorphic(L[j], M) then
		    consistent := false;
		    break;
		end if;
	    end for;

	    if consistent then
		if Dimension(M) le SplitLimit then
		    L := Constituents(M);
		else
		    L := [M];
		end if;
		if #L eq 1 then
		    Append(~FF, <M, CWM[i, 2]>);
		    L := [];
		else
		    vprint Condensation: "Reducible";
		end if;
	    else
		vprint Condensation: "Inconsistent";
	    end if;

	    if #L gt 0 then
		for M in &cat[Constituents(M): M in L | Dimension(M) gt 0] do
		    seen := false;
		    for N in BF do
			if IsIsomorphic(M, N) then
			    seen := true;
			    break;
			end if;
		    end for;
		    if not seen then
			Append(~BF, M);
		    end if;
		end for;
	    end if;
	end for;

    FF cat:= [<M, 0>: M in BF];
    Sort(~FF, func<t1, t2 | Dimension(t1[1]) - Dimension(t2[1])>);

    //Sort(~BF, func<M1, M2 | Dimension(M1) - Dimension(M2)>);

    /*
    F := [<F[i], mult[i]>: i in [1 .. #mult] | IsDefined(mult, i)];
    Sort(~F, func<t1, t2 | Dimension(t1[1]) - Dimension(t2[1])>);
    */

    return FF;
    return FF, CM, OF;
end function;

function PermCondFast(
    G, K:
	Group := G,
	UseClasses := assigned G`Classes,
	SearchDim := Round(Degree(G)/PERM_SEARCH_DENOM_FAST),
	H := find_subgroup(G, K, dim_func_perm, SearchDim, UseClasses),
	NumGens := default_ngens(G, K),
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	ExtraLimit := 3
)
    CM, sinfo, uncond, spin := perm_setup(G, K, H, NumGens, Group);
    return do_cond_fast(CM, sinfo, uncond, spin, SplitLimit, ExtraLimit);
end function;

function TensorCondFast(
    M1, M2:
	GG := Group(M1),
	Group := GG,
	UseClasses := assigned GG`Classes,
	SearchDim := Round(
	    Dimension(M1)*Dimension(M2)/TENSOR_SEARCH_DENOM_FAST
	),
	H := find_subgroup(
	    GG, BaseRing(M1), dim_func_tensor(M1, M2), SearchDim, UseClasses
	),
	NumGens := default_ngens(GG, BaseRing(M1)),
	SplitLimit := DEFAULT_SPLIT_LIMIT,
	ExtraLimit := 3
)
    CM, sinfo, uncond, spin := tensor_setup(M1, M2, H, NumGens, Group);
    if CM cmpeq 0 then
	return [];
    end if;
    return do_cond_fast(CM, sinfo, uncond, spin, SplitLimit, ExtraLimit);
end function;

/******************************************************************************/
