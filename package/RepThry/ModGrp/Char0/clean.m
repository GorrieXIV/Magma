freeze;

/*
Cleaning a rep.
AKS, 2001-2009.
*/

/*******************************************************************************
				Defines
*******************************************************************************/

EASY_CLEAN_DIM := 50;
EASY_CLEAN_DIM := 500;
EASY_CLEAN_NORM := 10^7;
EASY_CLEAN_DIM := 100;

// Nicify changed to Clean below
EASY_CLEAN_DIM := 1000;

FORM_TOLERANCE := 3;
CLEAN_CHECK := false;

Z := IntegerRing();
Q := RationalField();
is_Z := func<R | R cmpeq Z>;

/*******************************************************************************
				Aux matrix
*******************************************************************************/

function Diag(X)
    return [X[i][i]: i in [1 .. Min(Nrows(X), Ncols(X))]];
end function;
 
/*******************************************************************************
				Nicify/Clean
*******************************************************************************/

mod_to_matg := func<M | MatrixGroup(M: Check := false)>;

function log_norms(X)
    m := Nrows(X);
    return [
        n eq 0 select 0 else Ilog2(n) + 1 where
            n is Abs(Norm(X[i])): i in [1 .. m]
    ];
end function;

function nicify_L(L)
    function cost(L)
	return &+[&+log_norms(x): x in L];
    end function;

    C := cost(L);
    n := Ncols(L[1]);
    T := MatrixRing(Z, n) ! 1;

    vprintf ZMeataxe: "Nicify; degree %o\n", n;

// If F does not have rank equal to max rank of inputs, then randomize
// until so...
    while true do
	vprintf ZMeataxe: "Current cost: %o\n", C;
	F := &+[GramMatrix(x): x in L];
	//printf "F diagonal abs sum: %o\n", &+[Abs(F[i, i]): i in [1 .. n]];
	vtime ZMeataxe: LF, TF := LLLGram(
	    F: Delta := 0.999, Check := false, Proof := false
	);
	TFI := TF^-1;
	LL := [TF*g*TFI: g in L];
	CC := cost(LL);
	if CC ge C then
	    vprintf ZMeataxe: "Non-decreasing cost %o; stop\n", CC;
	    break;
	end if;

	L := LL;
	T := TF * T;
	C := CC;
    end while;

    return L, T;
end function;

function Nicify(M)
    L := [ActionGenerator(M, i): i in [1 .. Nagens(M)]];
    LL, T := nicify_L(L);
    if not IsOne(T) then
	if Type(M) eq ModGrp then
	    C := GModule(Group(M), LL);
	else
	    C := RModule(LL);
	end if;
	if assigned M`Character then
	    C`Character := M`Character;
	end if;
    else
	C := M;
    end if;
    return C, T;
end function;

function CleanG(G)
    Z := IntegerRing();
    if BaseRing(G) cmpeq RationalField() then
        G := IntegralGroup(G);
    end if;
    F := PositiveDefiniteForm(G);
"LLL";
time 
    FL, U := LLLGram(F: Delta := 0.999, Check := false, Proof := false);
    UI := U^-1;
    Q := [U*Matrix(G.i)*UI: i in [1 .. Ngens(G)]];
"Seysen";
SetVerbose("LLL", 0);
time FL, U := SeysenGram(FL);
UI := U^-1;
    Q := [U*Matrix(Q[i])*UI: i in [1 .. Ngens(G)]];
    H := MatrixGroup<Degree(G), Z | Q>;
    return H;
end function;

function clean_gens(L)
    n := Nrows(L[1]);
    NID := [i: i in [1 .. #L] | not IsOne(L[i])];
    if #NID eq 0 then
	return L;
    end if;

    VERB := GetVerbose("MCPoly");
    SetVerbose("MCPoly", 0);

    vprint Clean: "Clean gens";
    vprint Clean, 2: "IN:", L: Magma;

    G := MatrixGroup<n, Z | L>;
    if false then
	"Get form"; vtime Clean:
	    fl, F := PositiveDefiniteForm(L, FORM_TOLERANCE);
	assert fl;
    else
	vprint Clean: "Get form";
	vtime Clean:
	    F := PositiveDefiniteForm(G);
    end if;

    vprint Clean, 2: "F:", F: Magma;
    vprint Clean: "F diag:", Diag(F);
    vprint Clean: "Do LLL";
    vtime Clean:
	FL, TF := LLLGram(F: Delta := 0.999, Check := false, Proof := false);

    //vprint Clean, 2: "FL:", FL: Magma;
    //vprint Clean: "FL diag:", Diag(FL);

    vprint Clean: "Do Seysen";
    vtime Clean:
	FS, TS := SeysenGram(FL);

    U := TS*TF;

    vprint Clean: "Do inverse";
    vtime Clean:
	UI := U^-1;

    if CLEAN_CHECK then
	vprint Clean: "Test UI prod";
	if not IsOne(U*UI) then
	    "BAD INVERSE!!!!!!!!!!!";
	    "U := ";
	    U: Magma;
	    ";";
	    "UI := ";
	    UI: Magma;
	    ";";
	    assert false;
	end if;
    end if;
 
    vprint Clean: "Multiply matrices";
    vtime Clean:
	Q := [U*Matrix(L[i])*UI: i in [1 .. #L]];

    if CLEAN_CHECK then
	vprint Clean: "DO ASSERT TRACES";
	assert &and[Trace(Q[i]) eq Trace(L[i]): i in [1 .. #L]];
    end if;

    /*
    for i := 1 to #Q do
	L[NID[i]] := Q[i];
    end for;
    */

    vprint Clean, 2: "OUT:", L: Magma;

    SetVerbose("MCPoly", VERB);

    return Q;
end function;

function Clean(M)
    L := [ActionGenerator(M, i): i in [1 .. Nagens(M)]];
    L := clean_gens(L);
// #Group(M);
// Ngens($1);
// #L;
    C := GModule(Group(M), L);
    if assigned M`Character then
	C`Character := M`Character;
    end if;
    return C;
end function;

function Norms(X)
    m := Nrows(X);
    return [InnerProduct(X[i], X[i]): i in [1 .. m]];
end function;

ModuleMaxNorm := func<M |
    Max([Max(Norms(ActionGenerator(M, i))) + 0: i in [1 .. Nagens(M)]])>;

intrinsic EasyClean(M::ModRng) -> ModRng
{Attempt to clean M via easy method}
    d := Dimension(M);
    A := Action(M);
    m := Max([Max(Norms(A.i)): i in [1 .. Ngens(A)]]);
    if d le EASY_CLEAN_DIM then
    //if m le EASY_CLEAN_NORM then
	vprintf ZReps: "Cleaning module of dimension %o (max norm %o)\n", d, m;
	vtime ZReps:
	    M := Clean(M);
	    //M := Nicify(M);
//"Clean M:"; M: Maximal;
    end if;
    return M;
end intrinsic;
