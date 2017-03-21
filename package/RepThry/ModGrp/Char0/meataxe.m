freeze;

/*
Integral Meataxe.
AKS, 2001-2009.
*/

/*******************************************************************************
			    Direct parameters
*******************************************************************************/

USE_NEW_MEATAXE := 1 eq 1;
NEW_MEATAXE_MODULE_MIN := 2;

/*******************************************************************************
				Verbose
*******************************************************************************/

declare attributes ModRng: dyn_traces_info, get_traces, want_ind;
declare attributes ModRng: IsIrreducible, SchurIndex;
declare attributes Grp: MeataxeSkipCharacterTable;

import "char.m": char_is_multiple;

/*******************************************************************************
				Defines
*******************************************************************************/

K_PRIME := 11863279;
K_PRIME_2 := PreviousPrime(K_PRIME);

Z := IntegerRing();
Q := RationalField();
is_Z := func<R | R cmpeq Z>;

AddAttribute(ModGrp, "Character");
AddAttribute(ModRng, "Character");

FMP := func<X | FactoredMinimalPolynomial(X: Proof := false)>;

/*******************************************************************************
				Aux matrix
*******************************************************************************/

function Diag(X)
    return [X[i][i]: i in [1 .. Min(Nrows(X), Ncols(X))]];
end function;
 
function random_comb(L, range)
    return &+[Random(range)*L[i]: i in [1 .. #L]];
end function;

/*******************************************************************************
                            Possible characters
*******************************************************************************/

procedure get_split_degs(degs_mults, ~split_degs, ~split_degs_index)
    split_degs := [];
    split_degs_index := [];
    for i := 1 to #degs_mults do
        t := degs_mults[i];
        d := t[1];
        split_degs cat:= [d: j in [1 .. t[2]]];
        split_degs_index cat:= [i: j in [1 .. t[2]]];
    end for;
end procedure;

procedure get_split_degs_char(SplitChars, ~split_degs, ~split_degs_index)
    dm := [<Degree(t[1]), t[2]>: t in SplitChars];
    get_split_degs(dm, ~split_degs, ~split_degs_index);
end procedure;

function get_possible_chars(
    SplitChars, split_degs, split_degs_index, d: Max := 0
)
    kn := KnapsackSolutions(split_degs, d: Max := Max);
//"kn:", kn;
    possible := { &+[SplitChars[split_degs_index[i], 1]: i in s]: s in kn };
//possible;
    return possible;
end function;

function get_possible_chars_irr_chars(M, rats)
    d := Dimension(M);
    possible := {};
    for c in rats do
        dc := Z!Degree(c);
        if IsDivisibleBy(d, dc) then
            Include(~possible, (d div dc)*c);
        end if;
    end for;
    return possible;
end function;

function get_irr_char_mult(Mc, rats)
    d := Z!Degree(Mc);
    for c in rats do
        dc := Z!Degree(c);
        if IsDivisibleBy(d, dc) and Mc eq (d div dc)*c then
            return c, d div dc;
        end if;
    end for;
    return 0, 0;
end function;

/*******************************************************************************
				Endo dims
*******************************************************************************/

// For p >= Dimension(M) + 2 in group case, p does not divide |G|

get_prime := func<M |
    Type(M) eq ModGrp select NextPrime(Dimension(M) + 2) else 11863279
>;

function endo_centre_dim(M)
    p := get_prime(M);
    Mp := ChangeRing(M, GF(p));
    return &+[Dimension(CentreOfEndomorphismRing(c)): c in Constituents(Mp)];
end function;

function endo_dim_and_centre_dim(M)
    p := get_prime(M);
    M := ChangeRing(M, GF(p));
    C := ConstituentsWithMultiplicities(M);
    e := 0;
    z := 0;
    for t in C do
	E := EndomorphismRing(t[1]);
	e +:= Dimension(E) * t[2]^2;
	z +:= Dimension(Centre(E));
    end for;
    return e, z;
end function;

/******************************************************************************/
/******************************************************************************/
/******************************************************************************/
/******************************************************************************/

/*******************************************************************************
				Mark Irreducible
*******************************************************************************/

procedure MarkIrreducible(M, si)
    if si ne 0 then
	if assigned M`IsIrreducible then
	    assert M`IsIrreducible;
	end if;
	M`IsIrreducible := true;
	if si gt 0 then
	    M`SchurIndex := si;
	end if;
    end if;
end procedure;

procedure MarkIrreducibleSeq(Q, S)
    assert #S eq #Q;
    for i := 1 to #Q do
	MarkIrreducible(Q[i], S[i]);
    end for;
end procedure;

procedure MarkReducible(M)
    if assigned M`IsIrreducible then
	assert not M`IsIrreducible;
    end if;
    M`IsIrreducible := false;
end procedure;

/*******************************************************************************
				New chop
*******************************************************************************/

procedure sort_seq(~S)
    Sort(~S, func<x, y | Dimension(x) - Dimension(y)>);
end procedure;

function pspaces(X)
    vprint ZMeataxe: "Get partial primary invariant spaces";
    vtime ZMeataxe: S, L := PartialPrimaryInvariantSpaces(X);

    T := Cputime();
    n := Ncols(X);
    i := 1;
    while true do
	d := &+[Dimension(x): x in S];
	vprintf ZMeataxe: "Current dimension sum %o; need %o\n", d, n;

	if d eq n then
	    break;
	end if;

	t := L[i];
	vprintf ZMeataxe: "i: %o, factor: %o\n", i, t;
	vtime ZMeataxe: K := Kernel(Evaluate(t[1], X)^t[2]);
	dd := Dimension(K) - Dimension(S[i]);
	assert dd ge 0;
	d +:= dd;

	S[i] := K;
	L[i, 2] := ExactQuotient(Dimension(K), Degree(t[1]));

	i +:= 1;
    end while;
    assert &+[Dimension(x): x in S] eq n;

    vprint ZMeataxe: "Kernel fixing time:", Cputime(T);

    return S, L;
end function;

function get_partition(X, imap)
    S := [{imap[c]: c in Support(X[i])}: i in [1..Nrows(X)]];
    P := [];
    for i := 1 to #S do
        s := S[i];
	assert #s gt 0;
        p := 1;
        n := 0;
        while p le #P and #s gt 0 do
            if P[p] meet s ne {} then
                if n eq 0 then
                    n := p;
                    p +:= 1;
                else
                    P[n] join:= P[p];
                    Remove(~P, p);
                end if;
                s diff:= P[n];
            else
                p +:= 1;
            end if;
        end while;
        if n eq 0 then
            Append(~P, s);
        else
            P[n] join:= s;
        end if;
    end for;
    return P, S;
end function;

function nchop(M: WantSubmodules := false)
    range := 3;
    nag := Nagens(M);
    ML := [ActionGenerator(M, i): i in [1 .. nag]];
    X := &+[Random({-range .. range} diff {0})*g : g in ML];

    vprint ZMeataxe: "Get primary invariant spaces";
    T := Cputime();
    IndentPush();
    S, L := pspaces(X);
    IndentPop();
    vprint ZMeataxe: "Primary invariant spaces time:", Cputime(T);
    vprint ZMeataxe: "Dimensions:", [Dimension(s): s in S];

    vprint ZMeataxe: "Get modular submodules";
    K := GF(K_PRIME);
    MK := ChangeRing(M, K);

    vtime ZMeataxe: SK := [sub<MK | ChangeRing(s, K)>: s in S];
    vprint ZMeataxe: "Dimensions:", [Dimension(s): s in SK];

    BK := <Morphism(s, MK): s in SK>;
    b := #BK;

    J := VerticalJoin(BK);
    vprintf ZMeataxe:
	"Dimension sum: %o (full dimension %o)\n", Nrows(J), Dimension(M);
    vprint ZMeataxe: "Get modular relations";
    vtime ZMeataxe: KJ := Kernel(J);
    vprint ZMeataxe: "Nullity:", Dimension(KJ);

    imap := [];
    m := 1;
    for i := 1 to b do
	for j := 1 to Nrows(BK[i]) do
	    imap[m] := i;
	    m +:= 1;
	end for;
    end for;
    assert #imap eq Nrows(J);

    KJB := BasisMatrix(KJ);
    P := get_partition(KJB, imap);

    vprint ZMeataxe: "Partition:", P;
    U := { 1 .. b } diff &join P;
    vprint ZMeataxe: "Single indices:", U;

    P cat:= [{i}: i in U];
    vprint ZMeataxe: "New partition:", P;

    vprint ZMeataxe: "Get submodules";
    SS := [];
    for pi := 1 to #P do
	p := P[pi];
	W := VerticalJoin(<BasisMatrix(S[i]): i in p>);
	vprintf ZMeataxe: "Submodule %o; input dimension %o\n", pi, Nrows(W);
	if not WantSubmodules then
	    vtime ZMeataxe: s := SpinAction(W, ML);
	    vprint ZMeataxe: "Spin rank", Dimension(s);
	else
	    vtime ZMeataxe: sb := Spin(W, ML);
	    vprint ZMeataxe: "Spin rank", Nrows(sb);
	    vprint ZMeataxe: "Make submodule";
	    vtime ZMeataxe: s := ImageWithBasis(sb, M: Check := false);
	end if;
	Append(~SS, s);
    end for;

    sort_seq(~SS);
    return SS;

end function;

/*******************************************************************************
				Modular test
*******************************************************************************/

function modular_test(M)
/*
Return whether is proven irreducible by modular test.
*/

    TRIES := 5;
    TRIES := 3;
    p := K_PRIME;
    vprintf ZMeataxe: "Modular test (%o tries)\n", TRIES;
    f := false;
    vtime ZMeataxe:
	for i := 1 to TRIES do
	    K := GF(p);
	    MK := ChangeRing(M, K);
	    f := IsIrreducible(MK);
	    if f then
		break;
	    end if;
	    p := PreviousPrime(p);
	end for;
    return f;
end function;

/*******************************************************************************
			    Coprime basis
*******************************************************************************/

function coprime_basis(S)

    procedure incl(~C, f, m)
	for i := 1 to #C do
	    if f eq 1 then
		break;
	    end if;
	    g := C[i, 1];
	    c := GCD(f, g);
	    if c eq g then
		repeat
		    C[i, 2] +:= m;
		    f := ExactQuotient(f, g);
		until f mod g ne 0;
	    elif c ne 1 then
		C[i, 1] := c;
		mm := C[i, 2];
		C[i, 2] := mm + m;
		incl(~C, f div c, m);
		incl(~C, g div c, mm);
		return;
	    end if;
	end for;
	if f ne 1 then
	    Append(~C, <f, m>);
	end if;
    end procedure;

    C := [];
    for f in S do
	for t in SquarefreeFactorization(f) do
	    incl(~C, t[1], t[2]);
	end for;
    end for;
    return C;
end function;


/*******************************************************************************
			    Split by matrix
*******************************************************************************/

function split_by_matrix(M, r, mf, WantSubmodules)
//"r:", r;
//"mf:", mf;

    if false then
	vprint ZMeataxe: "Get kernels (eval method)";
	vtime ZMeataxe:
	    N := <KernelMatrix(t[1]^t[2], r): t in mf>;
    else
	vprint ZMeataxe: "Get kernels";
	vtime ZMeataxe:
	    N := <KernelMatrix(Evaluate(t[1]^t[2], r)): t in mf>;
    end if;
    vprint ZMeataxe: "Kernel dimensions:", [Nrows(S): S in N];

    A := Action(M);
    L := [A.i: i in [1 .. Ngens(A)]];
    Q := [];

    for k := 1 to #N do
	vprint ZMeataxe: "Make rep", k;

	SL := [];
	B := Saturation(N[k]);
	vprint ZMeataxe: "Do LLL on dim", Nrows(B);
	vtime ZMeataxe: B := LLL(B);

	if not WantSubmodules and Type(M) eq ModGrp then
	    vtime ZMeataxe:
		for i := 1 to #L do
		    SL[i] := Solution(B, B*L[i]);
		end for;

	    S := EasyClean(GModule(Group(M), SL));
	else
	    S := ImageWithBasis(B, M: Check := false);
	end if;
	Append(~Q, S);
    end for;

    return Q;
end function;

/*******************************************************************************
			    New decompose by endo
*******************************************************************************/

function split_by_basis(M, B, WantSubmodules: MaxIndex := #B)
// Return splitting of M by element of B if possible

    best_L := 0;
    best_X := 0;

    for i := 1 to Min(#B, MaxIndex) do
	X := B[i];
	L := FMP(X);
	if #L gt 1 and (best_L cmpeq 0 or #L gt #best_L) then
	    best_L := L;
	    best_X := X;
	    vprintf ZMeataxe:
		"New best number of factors for basis elt %o (of %o): %o\n",
		i, #B, #L;
	end if;
    end for;

    if best_L cmpeq 0 then
	return [M];
    end if;

    IndentPush();
    Q := split_by_matrix(M, best_X, best_L, WantSubmodules);
    IndentPop();
    vprint ZMeataxe: "Decomposition:", Q;
    return Q;

end function;

function split_by_endo(M, WantSubmodules: KnownHomog := false)
// Return splitting of M and whether contents of result proven indecomposable

    d := Dimension(M);

    vprintf ZMeataxe: "Get endomorphism ring for module of dim %o\n", d;
    vtime ZMeataxe: E := EndomorphismRing(M);

    e := Dimension(E);
    vprintf ZMeataxe: "Endomorphism ring has dimension %o\n", e;

    if e eq 1 then
	vprint ZMeataxe: "Endo trivial so module indecomposable";
	return [M], true;
    end if;

    if KnownHomog and IsCommutative(E) then
	vprint ZMeataxe: "Endo commutative so module indecomposable";
	return [M], true;
    end if;

    B := Basis(E);
    return split_by_basis(M, B, WantSubmodules), false;

end function;

/*******************************************************************************
			    Norm Equation test
*******************************************************************************/

function norm_eqn_test(M, E, C, WantSubmodules)
    if Dimension(C) ne 1 then
	vprint ZMeataxe: "Norm equation test inapplicable (center dim not 1)";
	return false, [M], [0];
    end if;
return false, [M], [0];

    vprint ZMeataxe: "Norm equation test";
    Z := IntegerRing();
    deg := Dimension(M);
    e := E.2;
    t := Trace(e);
    g := GCD(deg, t);
    e := (deg div g)*e - t div g;
//"e:", e;
    assert Trace(e) eq 0;
    d := e^2;
    assert IsScalar(d);
    d := d[1,1];
//"d:", d;
    if IsSquare(d) then
	e := e - Isqrt(d);
	assert not IsZero(e);
	//Q := split_by_matrix(M, e, [<PolynomialRing(Z).1, 1>], WantSubmodules);
	Q := split_by_matrix(M, e, FactoredMinimalPolynomial(e), WantSubmodules);
	return true, Q, [1, 1];
    end if;

    assert Dimension(E) eq 4;
    L := [E.i: i in [1..4]];
    vprint ZMeataxe: "Form products and kernel";
    vtime ZMeataxe:
	F := [x*e + e*x: x in L];
    FF := Matrix(deg^2, &cat[Eltseq(x): x in F]);
    vtime ZMeataxe:
	K := Kernel(FF);
    assert Dimension(K) gt 0;
//K;
    vprint ZMeataxe: "Get Galois automorphism";
    v := K.1;
    vtime ZMeataxe:
	f := &+[v[i]*L[i]: i in [1..4]];
    assert f ne 0 and e*f eq -f*e;
    vprint ZMeataxe: "d:", d;
    vprint ZMeataxe: "f:", f;
    K := QuadraticField(d);
    y2 := f^2;
    assert IsScalar(y2);
    y2 := y2[1,1];
    vprintf ZMeataxe: "Solve NormEquation(%o, %o)\n", K, y2;
    vtime ZMeataxe:
	l, r := NormEquation(K, y2);
    if not l then
	vprint ZMeataxe: "No solution; proven irreducible";
	return true, [M], [2];
    end if;
vprint ZMeataxe, 2: "r:", r;
    a, b := Explode(Eltseq(r[1]));
    denom := LCM(Denominator(a), Denominator(b));
    s := f*(Z!(denom*a) + Z!(denom*b)*e) - denom*y2;
    assert not IsZero(s);
    fmp := FactoredMinimalPolynomial(s);

vprint ZMeataxe, 2: "s:", s;
vprint ZMeataxe, 2: "s mp:", fmp;

    if #fmp ne 2 then
	vprint ZMeataxe: "Norm equation method FAILS to split!";
	return false, [M], [0];
    end if;

    Q := split_by_matrix(M, s, fmp, WantSubmodules);
    return true, Q, [1, 1];
end function;

/*******************************************************************************
			    Symmetric Forms test
*******************************************************************************/

function get_group_prime(G)
    o := #G;
    p := 2;
    while o mod p eq 0 do
	p := NextPrime(p);
    end while;
    return p;
end function;

function num_sym_forms(M)
    G := Group(M);
    p := get_group_prime(G);

    vprint ZMeataxe: "Group prime:", p;

    K := GF(p);
    M := ChangeRing(M, K);
    CM := ConstituentsWithMultiplicities(M);
    sym := 0;
    anti := 0;
    for T in CM do
        C, m := Explode(T);
        D := Dual(C);
        forms := Basis(GHom(C, D));
        d := Dimension(C);
        M := MatrixRing(K, d);
        syms := Rank(
            Matrix(
		K, #forms, d^2, &cat[Eltseq(M!f + Transpose(M!f)): f in forms]
	    )
        );
        antis := Rank(
            Matrix(
		K, #forms, d^2, &cat[Eltseq(M!f - Transpose(M!f)): f in forms]
	    )
        );
        if syms gt 0 and antis eq 0 then
            // constituent is of orthogonal type
            sym +:= (m^2+m)/2 * syms;
            anti +:= (m^2-m)/2 * syms;
        elif syms eq 0 and antis gt 0 then
            // constituent is of symplectic type
            sym +:= (m^2-m)/2 * antis;
            anti +:= (m^2+m)/2 * antis;
        elif syms gt 0 and antis gt 0 then
            // constituent is of unitary type and selfdual
            sym +:= m^2 * syms;
            anti +:= m^2 * antis;
        else
            // constituent is of unitary type but not selfdual (fixes no form)
            e := Dimension(EndomorphismRing(C));
            sym +:= m^2 * e/2;  // other half comes from dual
            anti +:= m^2 * e/2;
        end if;
    end for;

    return sym, anti;
end function;

function sym_forms_test(M, e, c)
    if Type(M) ne ModGrp then
	return false, _;
    end if;

    z := c;
    assert e mod z eq 0;
    q := e div z;
    p := Isqrt(q);
    if q eq p^2 and IsPrime(p) then
	vprintf ZMeataxe: "Use NumberOfSymmetricForms test (prime %o)\n", p;
	vtime ZMeataxe: nsf := num_sym_forms(M);
	vprintf ZMeataxe: "Number of Symmetric forms: %o\n", nsf;
	if nsf eq (z*p*(p - 1)) div 2 then
	    vprintf ZMeataxe:
		"Proven irreducible (Schur index %o) by symmetric forms test\n",
		p;
	    return true, p;
	end if;
    end if;
    vprint ZMeataxe: "Fail symmetric forms test";
    return false, _;
end function;

/*******************************************************************************
				Decompose by Centre
*******************************************************************************/

function try_basis(B)
    vprint ZMeataxe: "Try direct basis";
    vtime ZMeataxe:
    for i := 1 to #B do
	X := B[i];
	fmp := FMP(X);
	if #fmp gt 1 then
	    vprintf ZMeataxe: "Split found with basis element %o\n", i;
	    return X, fmp;
	end if;
    end for;
    return 0, 0;
end function;

function try_basis_sum(B)
    vprint ZMeataxe: "Try basis sum";
    vtime ZMeataxe:
    for i := 1 to #B do
	for j := 1 to i - 1 do
	    X := B[i] + B[j];
	    fmp := FMP(X);
	    if #fmp gt 1 then
		vprintf ZMeataxe: "Split found with basis sum %o, %o\n", i, j;
		return X, fmp;
	    end if;
	end for;
    end for;
    return 0, 0;
end function;

function try_basis_product(B)
    vprint ZMeataxe: "Try basis product";
    vtime ZMeataxe:
    for i := 1 to #B do
	for j := 1 to i - 1 do
	    X := B[i] * B[j];
	    fmp := FMP(X);
	    if #fmp gt 1 then
		vprintf ZMeataxe:
		    "Split found with basis product %o, %o\n", i, j;
		return X, fmp;
	    end if;
	end for;
    end for;
    return 0, 0;
end function;

function try_random_products_lll(B, k, CB)
    n := #B;
    nr := Round(n/4);
nr:=100;
nr:=5;
    vprintf ZMeataxe: "Try %o random basis products (%o times)\n", nr, k;
    for c := 1 to k do
c;
	//time P := [Random(B)*Random(B): i in [1 .. nr]] cat B;
	if 0 eq 1 then
	    P := [];
	    for r := 1 to 6 do
		X := Random(B)*Random(B);
		for Y in CB do
		    Append(~P, X*Y);
		end for;
	    end for;
	    P cat:= B;
	else
	    //time P := [Random(B)*Random(B): i in [1 .. nr]] cat CB cat B;
	    time P := [Random(B)*Random(B): i in [1 .. nr]] cat B;
	end if;
	time P := LLL(P);
	for j := 1 to n do
	    X := P[j];
	    fmp := FMP(X);
//fmp[1,1];
	    if #fmp gt 1 then
		vprintf ZMeataxe:
		    "Split found with random product element %o (try %o)\n",
		    j, c;
		return X, fmp;
	    end if;
	end for;
	/*
	P := P[1 .. n];
	rr := RegularRepresentation(P);
	rr := LLL(rr);
	for j := 1 to n do
	    X := rr[j];
	    fmp := FMP(X);
"rr", j, fmp[1,1];
	    if #fmp gt 1 then
		vprintf ZMeataxe:
		    "Split found with random product element %o (try %o)\n",
		    j, c;
		error "FOUND";
		return X, fmp;
	    end if;
	end for;
	*/
    end for;
    return 0, 0;
end function;

function try_random_products_lll(B, k, CB)
    n := #B;
    nr := Round(n/4);

    T := Cputime();
    rr := RegularRepresentation(B);

nr:=100;
nr:=20;
    vprintf ZMeataxe: "Try %o random basis products (%o times)\n", nr, k;
    for c := 1 to k do
	P := [Random(rr)*Random(rr): i in [1 .. nr]] ; //cat rr;
	P := LLL(P);
	for j := 1 to #P do
	    X := P[j];
	    fmp := FMP(X);
	    if #fmp gt 1 then
		s := Solution(Matrix(rr), Vector(Eltseq(X)));
		Y := &+[s[i]*B[i]: i in [1 .. #B]];
		assert FMP(Y) eq fmp;
		vprintf ZMeataxe:
	"Split found with random product element %o (try %o); time %o\n",
		    j, c, Cputime(T);
		vprintf ZMeataxe: "Solution vector: %o\n", s;
		return Y, fmp;
	    end if;
	end for;
    end for;
    vprintf ZMeataxe: "No split found; time %o\n", Cputime(T);
    return 0, 0;
end function;

function split_homog(M, E, WantSubmodules)
    d := Dimension(M);
    e := Dimension(E);
    //e := Ngens(E);

    vprint ZMeataxe: "Split by centre";
//M: Magma;
    vprint ZMeataxe: M;
    vprint ZMeataxe: "Module dim:", d;
    vprint ZMeataxe: "Endo has dim", e;
    vprint ZMeataxe: "Get dim of centre of Endo";
    vtime ZMeataxe:
	if /*true or*/ Type(M) eq ModGrp then
	    c := endo_centre_dim(M);
	else
	    if IsCommutative(E) then
		c := e;
	    else
		/*
		if Dimension(E)*d^2 ge 50*50^2 then
		    vprint ZMeataxe: "Too big; give up";
		    return [M], [0];
		end if;
		*/
		c := Dimension(Centre(E));
	    end if;
	end if;
    vprint ZMeataxe: "Centre of Endo has dim", c;

    if c eq e then
	vprint ZMeataxe: "Endo abelian so module indecomposable";
	MarkIrreducible(M, 1);
	return [M], [1];
    end if;

    l, p := sym_forms_test(M, e, c);
    if l then
	MarkIrreducible(M, p);
	return [M], [p];
    end if;

    z := c;
    if e mod z ne 0 then
	"BAD ENDO CENTRE!!!!!!!!";
	"e:", e;
	"z:", z;
	printf "M := %m;\n", M;
	error "";
    end if;

    q := e div z;

    if q eq 4 then
	vprint ZMeataxe: "Get centre of Endo of dim", e;
	vtime ZMeataxe:
	    C := Centre(E);

	l, Q, S := norm_eqn_test(M, E, C, WantSubmodules);
	if l then
	    MarkIrreducibleSeq(Q, S);
	    return Q, S;
	end if;
    end if;

    if 1 eq 1 and Type(M) eq ModGrp then
	G := Group(M);
	l, L := RepsSmallGet(G);
	if l then
	    S := L[1];
	    vprint ZMeataxe: "Found module in DB:", S;
	    H := AHomOverCentralizingField(S, M);
	    Hd := Dimension(H);
	    vprint ZMeataxe: "Number of homs:", Hd;
	    if Hd gt 0 then
		si := 1;
		HB := [LLL(h: Proof := false): h in LLL(Basis(H))];
		L := [ImageWithBasis(h, M: Check := false): h in HB];
		for S in L do MarkIrreducible(S, si); end for;
		Q := [si: i in [1 .. #L]];
		return L, Q;
	    end if;
	end if;
    end if;

    vprint ZMeataxe: "Get maximal order basis";
    IndentPush();
    vtime ZMeataxe: OB, denom, split, si, multiplicity := MaximalOrderBasis(E);
    IndentPop();

    if not split then
	vprintf ZMeataxe: "Endo ring proven simple (Schur index %o)\n", si;
	MarkIrreducible(M, si);
	return [M], [si];
    end if;

    vprintf ZMeataxe: "Should split: multiplicity %o, Schur index %o\n",
	multiplicity, si;

    is_gmodule := Type(M) eq ModGrp;
    if denom eq 1 or is_gmodule then
	ztry := 1;
	ztry := 2;
    else
	ztry := 2;
    end if;

    X := 0;
    for stry := 1 to 2 do
	vprintf ZMeataxe: "Try to find split element (try %o)\n", stry;
	if stry eq ztry then
	    vprint ZMeataxe: "Use integral endo basis";
	    EB := LLL(Basis(E));
	    X, fmp := try_basis(EB);
	    if X cmpne 0 then break; end if;
	    //X, fmp := try_basis_sum(EB);
	    //if X cmpne 0 then break; end if;
	else
	    vprintf ZMeataxe: "Use maximal order basis (denom %o)\n", denom;
	    /*
	    if stry gt 2 then
		vprint ZMeataxe: "Get new maximal order basis";
		IndentPush();
		vtime ZMeataxe: OB, denom, split, si := MaximalOrderBasis(E);
		IndentPop();
	    end if;
	    */
	    X, fmp := try_basis(OB);
	    if X cmpne 0 then break; end if;

	if 1 eq 1 then
	    X, fmp := try_basis_product(OB);
	    if X cmpne 0 then break; end if;
	    X, fmp := try_basis_sum(OB);
	    if X cmpne 0 then break; end if;
	end if;

if 1 eq 1 then
X, fmp := try_random_products_lll(OB, 100, LLL(Basis(Centre(E))));
if X cmpne 0 then break; end if;
end if;

if 1 eq 1 and q eq 4 then
    X := SplitViaConic(E);
    fmp := FMP(X);
    if #fmp gt 1 then break; end if;
    if X cmpne 0 then break; end if;
end if;
	end if;
    end for;

    if X cmpne 0 then
	vprint ZMeataxe: "Split element:", X;
	vprint ZMeataxe: "Factored minimal polynomial:", fmp;
	assert #fmp gt 1;
	mf := [<t[1], 1>: t in fmp];
	Q := split_by_matrix(M, X, fmp, WantSubmodules);
	if #Q eq multiplicity then
	    vprint ZMeataxe: "Correct multiplicity found";
	    S := [si: i in [1 .. #Q]];
	    MarkIrreducibleSeq(Q, S);
	    return Q, S;
	end if;

	vprint ZMeataxe: "Got Q:", Q;
	vprintf ZMeataxe: "Multiplicity %o found, need %o\n", #Q, multiplicity;

	md, mi := Min([Dimension(x): x in Q]);

	if md * multiplicity eq Dimension(M) then
	    vprint ZMeataxe: "Use min only";
	    Q := [Q[mi]];
	    S := [si: i in [1 .. #Q]];
	    MarkIrreducibleSeq(Q, S);
	    return Q, S;
	end if;
	
	M := Q[mi];
	vprint ZMeataxe: "Recurse on:", M;
	vprint ZMeataxe: "Get endo";
	vtime ZMeataxe: E := EndomorphismRing(M);
	return split_homog(M, E, WantSubmodules);
    end if;

    vprintf ZMeataxe: "FAIL SPLITTING (dim %o, centre dim %o)\n",
	Dimension(M), c;
    return [M], [0];

    c := d le 10 select 50 else 10;
    c := 1000;
    c := 10;
c := 5;
    for i := 1 to c do

	vprintf ZMeataxe: "Try to find split element (try %o)\n", i;
	IndentPush();
	s, B, d, should_split := FindSplitElement(E: DistinctFactors);
	IndentPop();

	if s ne 0 then
	    mf := FactoredMinimalPolynomial(s);
	    vprintf ZMeataxe: "Found element with min poly split %o\n", mf;
	    if #mf gt 1 or mf[1, 2] gt 1 then
		mf := [<t[1], 1>: t in mf];
		Q := split_by_matrix(M, s, mf, WantSubmodules);
		// use MarkIrreducibleSeq
		return Q, [1: i in [1 .. #Q]];
	    else
		/*
		"M:", M: Magma;
		"BAD s:", s;
		"mf:", mf;
		error "Send this to Allan";
		*/
		error "Send this to Allan";
		;
	    end if;
	end if;
    end for;

return [M], [0];

    vprintf ZMeataxe: "M := %m;\n\n", M;
error "fail";
    vprint ZMeataxe: E, c: Magma;

    return [M], [0];
end function;

/*******************************************************************************
				Decompose by LLL
*******************************************************************************/

function basis_LLL(L: Saturate := false)
    // Apply LLL to basis (sequence) L of matrices

    if #L eq 0 then
	return L;
    end if;
    m := Nrows(L[1]);
    n := Ncols(L[1]);
    d := #L;
    B := Matrix(d, m*n, &cat[Eltseq(x): x in L]);
    if Saturate then
	B := NewSaturation(B);
    end if;

    lll_block := d;
    //vprintf ZMeataxe: "Get LLL block (%o) of basis (dim %o)\n", lll_block, d;
    //vtime ZMeataxe: L := GramSchmidtReduce(B, Min(lll_block, Nrows(B)));

    vtime ZMeataxe: B := LLL(B: Delta := 0.999, Proof := false);

    U := Generic(Parent(L[1]));
    return [U | Eltseq(B[i]): i in [1 .. d]];
end function;

function split_LLL_endo(M, WantSubmodules)
    vprintf ZMeataxe: "Decompose module of dimension %o by LLL endo\n",
	Dimension(M);

    n := Dimension(M);
    E := EndomorphismRing(M);
    e := Dimension(E);
    B := Matrix(e, n^2, &cat[Eltseq(x): x in Basis(E)]);

    lll_block := 20;
lll_block := e;
    vprintf ZMeataxe: "Get LLL block (%o) of endo basis (dim %o)\n",
	lll_block, e;
    //vtime ZMeataxe: L := GramSchmidtReduce(B, Min(lll_block, Nrows(B)));
vtime ZMeataxe: L := LLL(B: Delta := 0.999, Proof := false);

    GE := Generic(E);
    //for i := 1 to Min(e, 5) do
    for i := 1 to e do
	A := GE!Eltseq(L[i]);
	if not IsOne(A) then
	    fmp := FMP(A);
	    if #fmp gt 1 then
		Q := split_by_matrix(M, A, fmp, WantSubmodules);
		vprint ZMeataxe: "Decomposition:", Q;
		return Q;
	    end if;
	end if;
    end for;

    return [M];
end function;

/*******************************************************************************
			Character decomposition
*******************************************************************************/

function get_char_decomp(M, IrrChars)
// Pass 0 for IrrChars by default

    G := Group(M);

    if not assigned G`RationalCharacterTable then
	vprint ZMeataxe: "Get rational character table";
	vtime ZMeataxe: CT, CTI := RationalCharacterTable(G);
    else
	CT, CTI := RationalCharacterTable(G);
    end if;

    if IrrChars cmpeq 0 then
	IrrChars := CT;
    end if;

    vprint ZMeataxe: "Get module character";
    vtime ZMeataxe: c := Char(M: IrrChars := IrrChars);

    D := RationalCharacterDecomposition(c);
    DI := [i: i in [1 .. #D] | D[i] gt 0];
    vprintf ZMeataxe: "Character index decomposition: %o\n",
	[<i, D[i]>: i in DI];
    vprintf ZMeataxe: "Character degree decomposition: %o\n",
	[<Degree(CT[i]), D[i]>: i in DI];
    //IrrChars := [CT[i]: i in DI];

    irred := false;
    si := 0;

    if #DI eq 1 then
	i := DI[1];
	m := D[i];
	if m eq 1 then
	    si := 1;
	else
	    si := RationalCharacterSchurIndex(G, i);
	end if;
	if m eq si then
	    vprintf ZMeataxe:
		"M irreducible by character test (Schur index %o)\n", si;
	    MarkIrreducible(M, si);
	    irred := true;
	end if;
    end if;

    return c, D, DI, irred, si;

end function;

/*******************************************************************************
				Main split
*******************************************************************************/

intrinsic IntegralDecomposition(
    M::ModRng:
    Depth := 0, ME := 0,
    HomogIrredDim := 0,		// if = d > 0, then is homog, dim d is irred.
    IrrChars := 0,
    SeenChars := {},
    WantChars := {},
    SplitChars := [],
    WantDTraces := [],
    SplitDTraces := [],
    WantDDims := [],
    SplitDDims := [],
    DynTraces := false,
    IrreducibilityTest := false,
    WantSubmodules := true	// whether want actual submodules of M
) -> {}
{Decompose integral module M}

    IRRED_TEST_RED := [-1, -1];
    OM := M;
    is_gmodule := Type(M) eq ModGrp;
    dim := Dimension(M);

    if dim eq 1 then
	MarkIrreducible(M, 1);
	return [M], [1];
    end if;

    if #SplitDTraces gt 0 then
	// Get rid of modules mapping to zero.
	SplitDTraces := [t: t in SplitDTraces | t[1, 1] ne 0];
	dm := [<t[1, 1], t[2]>: t in SplitDTraces];
	get_split_degs(dm, ~split_degs, ~split_degs_index);
    elif #SplitChars gt 0 then
	get_split_degs_char(SplitChars, ~split_degs, ~split_degs_index);
    else
	split_degs := [];
	split_degs_index := [];
    end if;

    want_degs := [Degree(x): x in WantChars];
    if #WantChars gt 0 then
	min_want_deg := Min(want_degs);
    else
	min_want_deg := 0;
    end if;
    WantDDims := [Z | x: x in WantDDims];

    vprint ZMeataxe: "*******";
    vprint ZMeataxe: "Decompose M of dimension", Dimension(M);
//M: Magma;
    vprint ZMeataxe: "Depth:", Depth;
    vprint ZMeataxe: "Decomposition degrees:", split_degs;
    if #SplitDTraces gt 0 then
	vprint ZMeataxe: "SplitDTraces:", SplitDTraces;
	vprint ZMeataxe: "WantDTraces:", WantDTraces;
	vprint ZMeataxe: "SplitDDims:", SplitDDims;
	vprint ZMeataxe: "WantDDims:", WantDDims;
    end if;
    if #want_degs gt 0 then
	vprint ZMeataxe: "Want degrees:", want_degs;
	vprint ZMeataxe: "Min want degree:", min_want_deg;
    end if;

    if HomogIrredDim gt 0 then
	vprint ZMeataxe: "Homog irred degree:", HomogIrredDim;
	if dim eq HomogIrredDim then
	    vprint ZMeataxe: "Proven irreducible";
	    MarkIrreducible(M, 1);
	    return [M], [1];
	end if;
	assert dim mod HomogIrredDim eq 0;
    end if;

    //"WantDTraces:", WantDTraces; "SplitDTraces:", SplitDTraces;

    IndentPush();

    if Dimension(M) lt min_want_deg then
	vprint ZMeataxe: "Module too small for wanted degrees";
	IndentPop();
	return [], [];
    end if;

    if forall{i: i in [1 .. Nagens(M)] | IsDiagonal(ActionGenerator(M, i))} then
	vprint ZMeataxe: "Trivial diagonal action: complete split into linears";
	IndentPop();

	Q := [];
	for i := 1 to dim do
	    v := M!0;
	    v[i] := 1;
	    Append(~Q, sub<M | v>);
	end for;
	S := [1: i in [1 .. dim]];
	MarkIrreducibleSeq(Q, S);
	return Q, S;
    end if;

    function ignore_seen_test(c)
	dc := Z!Degree(c);
	for s in SeenChars do
	    l, q := char_is_multiple(c, s);
	    if l then
		vprintf ZMeataxe:
		    "Character is %o times a seen character so ignore\n", q;
		return true;
	    end if;
	end for;
	return false;
    end function;

    endo_dim := 0;
    G := 0;
    Mchar := 0;

    if Type(M) eq ModGrp then
	G := Group(M);
	if
	    (
		not assigned G`MeataxeSkipCharacterTable or
		not G`MeataxeSkipCharacterTable
	    ) and
	    (#G le 10^6 or #KnownIrreducibles(G) gt 0)
	then

	    Mchar, Mchar_D, Mchar_DI, irred, si := get_char_decomp(M, 0);

	    if ignore_seen_test(Mchar) then
		IndentPop();
		return [], [];
	    end if;

	    CT, CTI := RationalCharacterTable(G);
	    IrrChars := [CT[i]: i in Mchar_DI];

	    if #WantChars gt 0 then
		WantChars_I := [Index(CT, c): c in WantChars];
		vprint ZMeataxe: "WantChars_I indices:", WantChars_I;
		assert 0 notin WantChars_I;
		if #(Set(WantChars_I) meet Set(Mchar_DI)) eq 0 then
		    vprint ZMeataxe: "No intersection with wanted chars";
		    IndentPop();
		    return [], [];
		end if;
	    end if;

	    if irred then
		IndentPop();
		return [M], [si];
	    end if;

	    if IrreducibilityTest then
		IndentPop();
		return IRRED_TEST_RED, [];
	    end if;

	    Mchar_deg_decomp := [<Degree(CT[i]), Mchar_D[i]>: i in Mchar_DI];

CHAR_GET_ENDO_DIM := false;
CHAR_GET_ENDO_DIM := true;

	    if CHAR_GET_ENDO_DIM then
		CCT := CharacterTable(G);
		vprint ZMeataxe: "Get endo dim via characters";
		vtime ZMeataxe: endo_dim := &+[
		    DegreeOfCharacterField(CCT[CTI[i, 1]])*Mchar_D[i]^2:
			i in Mchar_DI
		];
		vprint ZMeataxe: "Endo dim:", endo_dim;
	    end if;
	end if;
    end if;

    if Depth ge 1 and HomogIrredDim eq 0 and Mchar cmpeq 0 then
	if modular_test(M) then
	    vprint ZMeataxe: "M irreducible by modular test";
	    IndentPop();
	    MarkIrreducible(M, 1);
	    return [M], [1];
	else
	    vprint ZMeataxe: "Fail modular test";
	end if;
    end if;

    nag := Nagens(M);

    /*********************
    Wanted trace handling.
    *********************/

    split_seq := []; // obs
    split_ind := []; // obs
    split_seqm := [];
    split_seqm_ind := [];
    split_seqm_bounds := [];
    want_module := [];
    want_ind := [];
    want_count := [];
    want_ind_seen := {};
    do_want_dt := #WantDTraces gt 0 or DynTraces;

    if DynTraces then
	if assigned M`want_ind then;
	    want_ind := M`want_ind;
	end if;
	vprint ZMeataxe: "Dynamic wanted indices:", want_ind;
    else
	for ti := 1 to #SplitDTraces do
	    t := SplitDTraces[ti];
	    tr, e := Explode(t);
if tr[1] eq 0 then continue; end if;
	    tr := ChangeUniverse(tr, Z);

	    Append(~split_seqm, tr);
	    Append(~split_seqm_ind, ti);
	    Append(~split_seqm_bounds, e);

	    for c := 1 to e do
		Append(~split_seq, tr);
		Append(~split_ind, ti);
	    end for;
	end for;

	SplitDTracesFlat := [t[1]: t in SplitDTraces];
	want_ind := [Index(SplitDTracesFlat, w): w in WantDTraces];
	if 0 in want_ind then
	    "BAD WantDTraces:", WantDTraces;
	    "SplitDTraces:", SplitDTraces;
	    "WantDTraces:", WantDTraces;
	    error "DIE";
	end if;

	if do_want_dt then
	    vprint ZMeataxe, 2: "SplitDTraces:", SplitDTraces;
	    vprint ZMeataxe, 2: "WantDTraces:", WantDTraces;

	    //vprint ZMeataxe, 2: "split_seq:", split_seq;
	    //vprint ZMeataxe, 2: "split_ind:", split_ind;
	    //vprint ZMeataxe, 2: "want_ind:", want_ind;
	end if;
    end if;

    want_ind_set := Set(want_ind);
    trace_ind := [];
    SC_traces := [];
    modules_to_split := [];

NEW_KNAP := 1 eq 1;

    procedure want_dtraces_search(
	S, ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
	~trace_ind, ~SC_traces: IsHomog := false
    )
	traces := [Z | Trace(ActionGenerator(S, j)): j in [1 .. nag]];
	d := Dimension(S);

	function solve_knapsack(SS, V, SS_ind)
	    vprintf ZMeataxe, 2:
		"Solve dim-traces system (split length: %o)\n", #SS;
	    vprint ZMeataxe, 2: "V:", V;
	    vprint ZMeataxe, 2: "SS:", SS;
	    vprint ZMeataxe, 2: "SS_ind:", SS_ind;
	    vprint ZMeataxe, 2: "IsHomog:", IsHomog;

	    if IsHomog then
		l := #V;
		kn := [];
		for i := 1 to #SS do
		    if i gt 1 and SS_ind[i] eq SS_ind[i - 1] then
			continue;
		    end if;
		    S := SS[i];
		    q := V[1] div S[1];
		    if forall{j: j in [1 .. l] | V[j] eq q * S[j]} then
			k := SS_ind[i];
			if NEW_KNAP then
			    Append(~kn, [<k, q>]);
			else
			    Append(~kn, [k: c in [1 .. q]]);
			end if;
		    end if;
		end for;

		/*
		vprint ZMeataxe, 2: "kn:", kn;
		vtime ZMeataxe, 2:
		    kn2 := MultiKnapsackSolutions(SS, V: Max := 2);
		vprint ZMeataxe, 2: "first #kn2:", #kn2;
		kn2 := Sort(Setseq({ [SS_ind[j]: j in s]: s in kn2}));
		assert Set(kn) subset Set(kn2);
		*/
	    else
		if NEW_KNAP then
		    vtime ZMeataxe, 2:
			kn := MultiKnapsackSolutions(
			    SS, V: Multiples /*, Max := 2*/
			);
		    vprint ZMeataxe, 2: "first #kn:", #kn;
		else
		    vtime ZMeataxe, 2:
			kn := MultiKnapsackSolutions(SS, V /*: Max := 2*/ );
		    vprint ZMeataxe, 2: "first #kn:", #kn;
		    kn := Sort(Setseq({ [SS_ind[j]: j in s]: s in kn}));
		end if;
	    end if;

	    vprint ZMeataxe: "kn:", kn;
	    return kn;
	end function;

	if DynTraces then
	    get_traces := M`get_traces;
	    trace_ind_set := Set(trace_ind);
	    itry := [i: i in [1 .. nag] | i notin trace_ind_set];
	    itry1 := [i: i in itry | traces[i] ne 0];
	    itry2 := [i: i in itry | traces[i] eq 0];
	    itry := itry1 cat itry2;

	    SC := SplitChars; // zero mappings removed?  Matches SplitDDims
	    SC := [t[1]: t in SplitChars];

	    first := true;
	    while true do

		if first then
		    vprint ZMeataxe: "First try";
		    vprint ZMeataxe: "Current trace_ind:", trace_ind;
		    vprint ZMeataxe: "Current SC_traces:", SC_traces;
		    first := false;
		elif #itry gt 0 then
		    gi := itry[1];
		    itry := itry[2 .. #itry];
		    Append(~trace_ind, gi);
		    T := get_traces(gi, SC);
		    Append(~SC_traces, T);

		    vprint ZMeataxe: "Use ind", gi;
		    vprint ZMeataxe: "new trace_ind:", trace_ind;
		    vprint ZMeataxe: "new SC_traces:", SC_traces;
		end if;

		if #trace_ind lt Min(2, #trace_ind - 1) then
		    continue;
		end if;

		OMC := OM;
		OMC`dyn_traces_info := <trace_ind, SC_traces>;

		V := [Z | d];
		V cat:= [Z | traces[i]: i in trace_ind];

		SS := [];
		SS_ind := [];
		SS_bound := [];
		for i := 1 to #SC do
		    di := SplitDDims[i];
		    if di eq 0 or di gt d then
			continue;
		    end if;
		    q := [Z | SplitDDims[i]];
		    q cat:= [Z | SC_traces[j, i]: j in [1 .. #SC_traces]];
		    if NEW_KNAP then
			Append(~SS, q);
			Append(~SS_ind, i);
			Append(~SS_bound, SplitChars[i, 2]);
		    else
			for j := 1 to SplitChars[i, 2] do
			    Append(~SS, q);
			    Append(~SS_ind, i);
			end for;
		    end if;
		end for;

/*
"SS:", SS;
"SS_ind:", SS_ind;
"SS_bound:", SS_bound;
"V:", V;
*/
		kn := solve_knapsack(SS, V, SS_ind);
//"Got kn:", kn;
		if NEW_KNAP then
		    kni := { t[1]: t in s, s in kn };
		else
		    kni := { i: i in s, s in kn };
		end if;
		if
		    #kn eq 1 or #trace_ind eq nag or kni meet want_ind_set eq {}
		then
		    break;
		end if;
	    end while;
	else
	    V := [Z | d] cat traces;
	    if NEW_KNAP then
//"split_seqm_bounds:", split_seqm_bounds;
		kn := solve_knapsack(
		    split_seqm, V, split_seqm_ind
		    // split_seqm_bounds
		);
		kni := { t[1]: t in s, s in kn };
	    else
		kn := solve_knapsack(split_seq, V, split_ind);
		kni := { i: i in s, s in kn };
	    end if;
	end if;

	m := kni meet want_ind_set;
	if m eq {} then
	    vprintf ZMeataxe: "No intersection with wanted indices %o\n",
		want_ind_set;
	    return;
	end if;

	Append(~modules_to_split, S);

	if #kn ne 1 then
	    vprint ZMeataxe: "Trace Knapsack NOT UNIQUE!!!";
	    return;
	end if;

	vprint ZMeataxe: "Unique solution (indices):", kn[1];
	s := kn[1];
	if #Set(s) eq 1 then
	    if NEW_KNAP then
		i := s[1, 1];
		c := s[1, 2];
	    else
		i := s[1];
		c := #s;
	    end if;
	    if i in want_ind and i notin want_ind_seen then
		Append(~want_module, S);
		Append(~want_count, c);
		Include(~want_ind_seen, i);
		vprintf ZMeataxe: "Got wanted index %o, count %o\n", i, c;
	    end if;
	end if;
    end procedure;

    procedure want_dtraces_search_split(
	S, ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
	~trace_ind, ~SC_traces, ~finished: KnownIsHomog := false
    )
	finished := false;

	if not do_want_dt then
	    return;
	end if;

	if not KnownIsHomog then
	    SL, indec := split_by_endo(S, WantSubmodules);
	    T := [];
	    T_traces := {};
	    for S in SL do
		traces := [
		    Trace(ActionGenerator(S, j)): j in [1 .. nag]
		];
		if traces notin T_traces then
		    Include(~T_traces, traces);
		    Append(~T, S);
		end if;
	    end for;
	    SL := T;
	    vprint ZMeataxe: "Decomposition reduced to:", SL;

	    for S in SL do
		vprint ZMeataxe: "Try", S;
		if indec then
		    is_homog := true;
		else
		    vprint ZMeataxe: "Get endo";
		    vtime ZMeataxe: SE := EndomorphismRing(S);
		    SE_d := Dimension(SE);
		    vprint ZMeataxe: "Endo dim is", SE_d;
		    if
			Dimension(SE) eq 1 or
			SE_d le 10 and IsCommutative(SE)
		    then
			is_homog := true;
		    else
			vprint ZMeataxe: "Get centre";
			vtime ZMeataxe:
			    SEC := CentreOfEndomorphismRing(S);
			SEC_d := Dimension(SEC);
			vprint ZMeataxe: "Centre dim is", SEC_d;
			if
			    SEC_d in {1, SE_d} or
			    forall{x: x in Basis(SEC) |
				IsIrreducible(MinimalPolynomial(x))}
			then
			    vprint ZMeataxe: "Homogeneous via centre";
			    is_homog := true;
			else
			    vprint ZMeataxe: "INHOMOGENEOUS via centre";
			    is_homog := false;
			end if;
		    end if;
		end if;

		want_dtraces_search(
		    S, ~want_module, ~want_count, ~want_ind_seen,
		    ~modules_to_split, ~trace_ind, ~SC_traces:
			IsHomog := is_homog
		);
		finished := #want_module eq #want_ind;
		if finished then
		    break;
		end if;
	    end for;
	else
	    // Old direct method
	    want_dtraces_search(
		S, ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
		~trace_ind, ~SC_traces: IsHomog := KnownIsHomog
	    );
	    finished := #want_module eq #want_ind;
	end if;

    end procedure;

    procedure check_want_dt(want_module, want_count, ~ret_S, ~ret_C)

	assert do_want_dt;
	ret_S := 0;
	ret_C := 0;

	vprint ZMeataxe: "want_module:", want_module;
	vprint ZMeataxe: "want_count:", want_count;

	if #want_module ne #want_ind then
	    vprint ZMeataxe: "MISSED getting all that were wanted";
	    return;
	end if;

	if #want_module eq #want_ind and Set(want_count) eq {1} then
	    vprint ZMeataxe: "GOT ALL WITH COUNT 1";
	    IndentPop();
	    MarkIrreducibleSeq(want_module, want_count);
	    ret_S := want_module;
	    ret_C := want_count;
	    return;
	end if;

	vprint ZMeataxe: "COUNT > 1";

	if #want_module ne #want_ind then
	    return;
	end if;

	vprint ZMeataxe: "Right number of wanted; recurse on these";
	SS := [];
	BB := [];
	for i := 1 to #want_module do
	    Mi := want_module[i];
	    if want_count[i] eq 1 then
		S := [Mi];
		B := [1];
	    else
		d := ExactQuotient(Dimension(Mi), want_count[i]);
		S, B := IntegralDecomposition(
		    Mi: Depth := 1, HomogIrredDim := d
		);
	    end if;
	    SS cat:= S;
	    BB cat:= B;
	end for;
	IndentPop();
	ret_S := SS;
	ret_C := BB;

    end procedure;

    /**************************************
    Get endo dim and decide on main method.
    **************************************/

    /*
    if USE_NEW_MEATAXE then
	vprint ZMeataxe: "Get Endo and centre dim";
	vtime ZMeataxe:
	    e, c := endo_dim_and_centre_dim(M);
	vprintf ZMeataxe: "Endo dim: %o, centre dim: %o\n", e, c;
    end if;
    */

    is_perm_module := IsPermutationModule(M);

    if endo_dim gt 0 and USE_NEW_MEATAXE then
	if is_perm_module then
	    use_meataxe := endo_dim gt 200;
	else
	    use_meataxe := endo_dim gt 10;
	end if;
    else
	use_meataxe := USE_NEW_MEATAXE;
    end if;

    if
	use_meataxe and
	/* do_want_dt and */
	Depth le 0 and
	dim ge NEW_MEATAXE_MODULE_MIN
	//and not is_perm_module
    then
	vprint ZMeataxe: "Use new chop";
	ZEIT := Cputime();

	range := 3;
	ML := [ActionGenerator(M, i): i in [1 .. nag]];

	if 1 eq 0 then
	    X := random_comb(ML, [-2,-1, 1,2]);
	    for c := 1 to 2 do
		X := X * random_comb(ML, [-2,-1, 1,2]);
		X := X + random_comb(ML, [-2,-1, 1,2]);
	    end for;
	else
	    X := &+[Random({-range .. range} diff {0})*g: g in ML];
	end if;

	X := IntegralMatrix(X);

	T := Cputime();
	CF := 0;

NEW_KERNEL := 1 eq 1 and Dimension(M) lt 500;

	if NEW_KERNEL then
	    vprint ZMeataxe: "Get factored min poly and space";
	    IndentPush();
	    vtime ZMeataxe: L, CF, space, IF := MCSplit(X);
	    IndentPop();
//mp := &*[t[1]^t[2]: t in L];
//assert mp eq IF[1];
	    mp := IF[1];
	    SZ := sub<RSpace(Z, Ncols(X))|>;
	    PS := [SZ: t in L];
	    vprint ZMeataxe: "Min poly degree:", Degree(mp);
	    vprint ZMeataxe: "Min poly factor degrees:",
		{* Degree(t[1])^^t[2]: t in L *};
	    vprint ZMeataxe: "Char poly factor degrees:",
		{* Degree(t[1])^^t[2]: t in CF *};
	elif 0 eq 1 then
	    vprint ZMeataxe: "Get factored min poly";
	    IndentPush();
	    vtime ZMeataxe: L := FactoredMinimalPolynomial(X: Proof := false);
	    IndentPop();
	    SZ := sub<RSpace(Z, Ncols(X))|>;
	    PS := [SZ: t in L];
	    vprint ZMeataxe: "Min poly factor degrees:",
		{* Degree(t[1])^^t[2]: t in L *};
	else
	    vprint ZMeataxe: "Get partial primary invariant spaces";
	    IndentPush();
	    vtime ZMeataxe: PS, L := PartialPrimaryInvariantSpaces(X);
	    IndentPop();
	    vprint ZMeataxe: "Partial dimensions:", [Dimension(s): s in PS];
	    vprint ZMeataxe: "Partial degrees:", [<Degree(t[1]), t[2]>: t in L];
	end if;

	// want_dims := {t[1]: t in WantDTraces};
	want_dims := Set(WantDDims);
	cmp := function(t0, t1)
	    d0 := Dimension(t0[1]);
	    if d0 eq 0 then d0 := Degree(t0[2, 1])*t0[2, 2]; end if;
	    d1 := Dimension(t1[1]);
	    if d1 eq 0 then d1 := Degree(t1[2, 1])*t1[2, 2]; end if;
	    if d0 in want_dims and d1 notin want_dims then
		return -1;
	    end if;
	    if d0 notin want_dims and d1 in want_dims then
		return 1;
	    end if;
	    div0 := exists{d: d in want_dims | IsDivisibleBy(d, d0)};
	    div1 := exists{d: d in want_dims | IsDivisibleBy(d, d1)};
	    if div0 and not div1 then
		return -1;
	    end if;
	    if not div0 and div1 then
		return 1;
	    end if;
	    if div0 and div1 then
		return d1 - d0;
	    end if;
	    return d0 - d1;
	end function;
	PS_L := [<PS[i], L[i]>: i in [1 .. #PS]];
	if do_want_dt then
	    Sort(~PS_L, cmp);
	end if;
	PS := [* PS_L[i, 1]: i in [1 .. #PS_L] *];
	L := [PS_L[i, 2]: i in [1 .. #PS_L]];
	/*
	vprint ZMeataxe: "Resorted partial dimensions:",
	    [Dimension(s): s in PS];
	*/
	vprint ZMeataxe: "Resorted partial degrees:",
	    [Degree(t[1])*t[2]: t in L];

	new_M := [];

	T := Cputime();
	n := Ncols(X);
	//K := GF(K_PRIME)
	//MK := ChangeRing(M, K);
	for i := 1 to #L do

	    if #L eq 1 then
		vprint ZMeataxe: "No split";
		Append(~new_M, M);
		break;
	    end if;

	    t := L[i];
	    dims := [
		ISA(Type(x), Mtrx) select Nrows(x) else Dimension(x): x in PS
	    ];
	    d := &+dims;

	    vprintf ZMeataxe: "i: %o, dim sum %o (of %o)\n", i, d, n;
	    if Degree(t[1]) gt 20 then
		vprintf ZMeataxe: "Factor: <[degree %o], %o>",
		    Degree(t[1]), t[2];
	    else
		vprintf ZMeataxe: "Factor: %o", t;
	    end if;

	    if CF cmpne 0 then
		cf_nullity := Degree(CF[i, 1])*CF[i, 2];
		vprintf ZMeataxe: " (CF nullity %o)\n", cf_nullity;
	    else
		cf_nullity := 0;
		"";
	    end if;

	    IndentPush();

USE_AHOM := true and NEW_KERNEL;
USE_AHOM := false and NEW_KERNEL;

	    if d lt n then
		vprint ZMeataxe, 2: "Get kernel";

		N := 0;
		f := t[1]^t[2];
		if NEW_KERNEL and Degree(f) ge 2 then
		    if USE_AHOM or #IF eq 1 or GCD(f, IF[2]) eq 1 then
			fq := ExactQuotient(mp, f);
			fq := Vector(Eltseq(fq));
			vprint ZMeataxe: "Get vector";
			vtime ZMeataxe:
			    w := fq*RowSubmatrix(space, 1, Ncols(fq));
			N := ZeroMatrix(Z, Degree(f), dim);
			N[1] := w;
			vprint ZMeataxe: "Get basis of space";
			vtime ZMeataxe:
			    for i := 2 to Nrows(N) do
				N[i] := N[i - 1]*X;
			    end for;
			vprint ZMeataxe: "Echelonize over Q";
			vtime ZMeataxe:
			    N := EchelonForm(Matrix(RationalField(), N));
			vprint ZMeataxe: "Saturate";
			vtime ZMeataxe: N := Saturation(N);
//assert RowSpace(N) eq Kernel(Evaluate(t[1], X)^t[2]);
		    else
			vprint ZMeataxe: "Factor is repeated; use direct";
		    end if;
		end if;

		if N cmpeq 0 then
		    vprint ZMeataxe: "Get direct kernel of evaluation";
		    vtime ZMeataxe: N := Kernel(Evaluate(t[1], X)^t[2]);
		    N := BasisMatrix(N);
		end if;

		dd := Nrows(N) - Dimension(PS[i]);
		assert dd ge 0;
		d +:= dd;
		PS[i] := N;
		L[i, 2] := ExactQuotient(Nrows(N), Degree(t[1]));
	    else
		N := PS[i];
		N := BasisMatrix(N);
	    end if;

	    vprintf ZMeataxe: "Kernel dim %o; do spin\n", Nrows(N);

//N := Matrix(LLL(N: Sort)[1]);

	    verb := GetVerbose("ZMeataxe");
	    SetVerbose("ZMeataxe", 0);
	    zeit := Cputime();
	    spin := Spin(N, ML);
	    SetVerbose("ZMeataxe", verb);
	    vprintf ZMeataxe:
		"Spin rank %o, time %o\n", Nrows(spin), Cputime(zeit);

	    if IrreducibilityTest and Nrows(spin) lt dim then
		vprint ZMeataxe: "Found proper submodule; reducible";
		IndentPop();
		IndentPop();
		return IRRED_TEST_RED, [];
	    end if;

	    vprint ZMeataxe: "Make submodule";
	    vtime ZMeataxe: S := ImageWithBasis(spin, M: Check := false);

	    want_dtraces_search_split(
		S, ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
		~trace_ind, ~SC_traces, ~finished
	    );

	    if finished then
		IndentPop();
		vprint ZMeataxe: "All wanted got; break";
		break;
	    end if;

	    if Mchar cmpne 0 then
		Schar, Schar_D, Schar_DI, irred, si := get_char_decomp(
		    S, IrrChars
		);
		if #WantChars gt 0 then
		    sm := Set(WantChars_I) meet Set(Schar_DI);
		    vprint ZMeataxe: "Intersection with wanted chars:", sm;
		    if #sm eq 0 then
			vprint ZMeataxe: "No intersection with wanted chars";
			IndentPop();
			continue;
		    end if;
		    if #Mchar_DI gt 1 and #WantChars_I eq 1 then
			IndentPop();
			vprint ZMeataxe: "Recurse to get wanted";
			SB, SS := IntegralDecomposition(
			    S: Depth := 0, IrrChars := IrrChars,
				WantChars := WantChars
			);
			IndentPop();
			return SB, SS;
		    end if;
		end if;
	    end if;

	    Sd := Dimension(S);
	    if Sd lt Dimension(M) then
		if USE_AHOM and Sd lt cf_nullity and cf_nullity mod Sd eq 0 then
		    vprint ZMeataxe: "Get homs into M ";
//S; M; Nagens(S), Nagens(M); EndomorphismRing(S); CentreOfEndomorphismRing(S);
		    vtime ZMeataxe:
			H := AHomOverCentralizingField(S, M);
		    vprint ZMeataxe: "Number of homs:", Dimension(H);
		    for h in LLL(Basis(H)) do
			S := ImageWithBasis(h, M: Check := false);
			Append(~new_M, S);
		    end for;
		else
		    Append(~new_M, S);
		end if;
	    end if;

	    IndentPop();
	end for;

	//assert &+[Dimension(x): x in S] eq n;

	vprint ZMeataxe: "Chop time:", Cputime(ZEIT);

	if do_want_dt then

	    check_want_dt(want_module, want_count, ~ret_S, ~ret_C);
	    if ret_S cmpne 0 then
		return ret_S, ret_C;
	    end if;

	end if;

	if #new_M gt 1 then

	    vprint ZMeataxe: "Got split:", [Dimension(S): S in new_M];

	    d := Dimension(M);
	    dim_sum := &+[Dimension(S): S in new_M];
	    if
		dim_sum eq d and
		Rank(VerticalJoin(<Morphism(S, M): S in new_M>)) eq d
	    then
		vprint ZMeataxe: "Full split was found";

		if do_want_dt then
		    vprint ZMeataxe: "modules_to_split:", modules_to_split;
		    if #modules_to_split eq 0 then
			vprint ZMeataxe: "Set to modules_to_split split";
			modules_to_split := new_M;
		    end if;
		else
		    vprint ZMeataxe: "Recurse on all";
		    SS := [];
		    BB := [];
		    for i := 1 to #new_M do
			S := new_M[i];
			vprintf ZMeataxe: "Decompose dim %o (mod %o of %o)\n",
			    Dimension(S), i, #new_M;

			if IrrChars cmpne 0 then
			    vprint ZMeataxe: "First get character";
			    vtime ZMeataxe:
				_ := Char(S: IrrChars := IrrChars);
			end if;

			S, B := IntegralDecomposition(
			    S: Depth := 0, HomogIrredDim := HomogIrredDim
			);
			SS cat:= S;
			BB cat:= B;
		    end for;
		    IndentPop();
		    return SS, BB;
		end if;
	    else
		vprintf ZMeataxe: "Full split not found (dim sum %o)\n",
		    dim_sum;
	    end if;
	end if;

    end if;

NEW := false;
NEW := true;
if NEW then

    // if Depth le 1 then

    // want_module := []; want_count := [];

    if #modules_to_split gt 0 then
	S := modules_to_split;
	modules_to_split := [];
    elif is_perm_module then
	vprint ZMeataxe: "Get endomorphism ring (of perm module) first";
	vtime ZMeataxe:
	    E := EndomorphismRing(M);
	e := Dimension(E);
	vprint ZMeataxe: "Endo has dim", e;
	vprint ZMeataxe: "Split via (perm) endo basis";
	IndentPush();
	S := split_by_basis(M, Basis(E), WantSubmodules: MaxIndex := 50);
	IndentPop();
    else
	S := [M];
    end if;

    if IrreducibilityTest and #S gt 1 then
	vprint ZMeataxe: "Proper split; reducible";
	IndentPop();
	return IRRED_TEST_RED, [];
    end if;

    if true then
	// Split by centre first

	SS := [];
	finished := false;

	while #S gt 0 do

	    U := S[#S];
	    Prune(~S);

	    d := Dimension(U);
	    vprintf ZMeataxe: "Split module of dim %o via endo centre\n", d;
	    IndentPush();

	    vprint ZMeataxe: "Get centre of endomorphism ring";
	    vtime ZMeataxe:
		EC := CentreOfEndomorphismRing(U);
	    ec := Dimension(EC);
	    vprint ZMeataxe: "Centre of endo has dim", ec;

	    if ec eq 1 then
		L := [U];
	    else
		L := split_by_basis(U, Basis(EC), WantSubmodules);
	    end if;

	    if #L gt 1 then
		if IrreducibilityTest then
		    vprint ZMeataxe: "Proper split; reducible";
		    IndentPop(2);
		    return IRRED_TEST_RED, [];
		end if;
		S cat:= L;
	    else
		vprint ZMeataxe: "No split by endo centre so homogeneous";
		want_dtraces_search_split(
		    U, ~want_module, ~want_count, ~want_ind_seen,
		    ~modules_to_split, ~trace_ind, ~SC_traces, ~finished
		);
		if finished then
		    vprint ZMeataxe: "All wanted got; break";
		    IndentPop();
		    break;
		end if;
		Append(~SS, U);
	    end if;
	    IndentPop();

	end while;

	if do_want_dt then
	    check_want_dt(want_module, want_count, ~ret_S, ~ret_C);
	    if ret_S cmpne 0 then
		IndentPop();
		vprint ZMeataxe: "Final split (via traces):", ret_S, ret_C;
		return ret_S, ret_C;
	    end if;
	end if;

	S := SS;
    end if;

    vprint ZMeataxe: "Homogeneous split:", S;

    U := 0;
    FM := [];
    FSI := [];

    HS := [[x]: x in S];

    while #HS gt 0 do

	// vprint ZMeataxe: "Now HS:", HS;

	S := HS[#HS];
	Prune(~HS);

	if #S eq 0 then
	    continue;
	end if;

	sort_seq(~S);

	if 1 eq 1 and #S gt 1 then
	    // Since homogeneous, if one submodule smaller than others,
	    // try AHom split.

	    U := S[1];
	    SS := [U];
	    d := Dimension(U);

	    for i := 2 to #S do
		W := S[i];
		Wd := Dimension(W);
//"here:", Wd, d;
		if Wd gt d and Wd mod d eq 0 then
		    vprintf ZMeataxe: "Try AHom(%o, %o)\n", d, Wd;
		    vtime ZMeataxe: H := AHomOverCentralizingField(U, W);
		    Hd := Dimension(H);
		    vprintf ZMeataxe: "Hom over centre has dim %o\n", Hd;
assert Hd eq Wd div d;
		    B := LLL(Basis(H));
		    BL := [ImageWithBasis(LLL(x), W: Check := false): x in B];
		    SS cat:= BL;
		else
		    Append(~SS, W);
		end if;
	    end for;

	    S := SS;
	    sort_seq(~S);
	    S := Reverse(S);
	    U := S[#S];
	    Prune(~S);
	    ES := S;
	else
	    U := S[1];
	    ES := [];
	end if;

	d := Dimension(U);
	if d le 1 then
	    Append(~FM, U);
	    Append(~FSI, 1);
	    Append(~HS, ES);
	    continue;
	end if;

	vprintf ZMeataxe: "Split module of dim %o via endo\n", d;
	IndentPush();

	vprint ZMeataxe: "Get endomorphism ring";
	vtime ZMeataxe:
	    E := EndomorphismRing(U);
	e := Dimension(E);
	vprint ZMeataxe: "Endo has dim", e;

	if e eq 1 or IsCommutative(E) then
	    vprint ZMeataxe:
		"Endo trivial or commutative so module indecomposable";
	    MarkIrreducible(U, 1);
	    Append(~FM, U);
	    Append(~FSI, 1);
	    Append(~HS, ES);
	    IndentPop();
	    continue;
	end if;

	L := split_by_basis(U, Basis(E), WantSubmodules);

	if #L gt 1 then
	    if IrreducibilityTest then
		vprint ZMeataxe: "Proper split; reducible";
		IndentPop(2);
		return IRRED_TEST_RED, [];
	    end if;
	    Append(~HS, L cat ES);
	    IndentPop();
	    continue;
	end if;

	vprint ZMeataxe: "No split by endo; try LLL endo";
	//IndentPush();
	L := split_LLL_endo(U, WantSubmodules);
	//IndentPop();

	if #L gt 1 then
	    if IrreducibilityTest then
		vprint ZMeataxe: "Proper split; reducible";
		IndentPop(2);
		return IRRED_TEST_RED, [];
	    end if;
	    Append(~HS, L cat ES);
	    IndentPop();
	    continue;
	end if;

	vprint ZMeataxe: "No split by LLL endo; use homog split";
	L, SI := split_homog(U, E, WantSubmodules);
	if IrreducibilityTest and #L gt 1 then
	    vprint ZMeataxe: "Proper split; reducible";
	    IndentPop(2);
	    return IRRED_TEST_RED, [];
	end if;
	FM cat:= L;
	FSI cat:= SI;

	want_dtraces_search_split(
	    L[1], ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
	    ~trace_ind, ~SC_traces, ~finished: KnownIsHomog
	);
	IndentPop();

	if finished then
	    vprint ZMeataxe: "All wanted got; break";
	    break;
	end if;

	Append(~HS, ES);

    end while;

    IndentPop();
    U := 0;

    if do_want_dt then
	check_want_dt(want_module, want_count, ~ret_S, ~ret_C);
	if ret_S cmpne 0 then
	    IndentPop();
	    vprint ZMeataxe: "Final split (via traces):", ret_S, ret_C;
	    return ret_S, ret_C;
	end if;
    end if;

    vprint ZMeataxe: "Final split:", FM, FSI;
    return FM, FSI;

end if;

    vprint ZMeataxe: "Get Endo and centre DIM";
    vtime ZMeataxe:
	e, c := endo_dim_and_centre_dim(M);

    vprint ZMeataxe: "Endo has dim", e;
    vprint ZMeataxe: "Centre of Endo has dim", c;
    if e eq 1 then
	vprint ZMeataxe: "Endo trivial so module indecomposable";
	IndentPop();
	MarkIrreducible(M, 1);
	return [M], [1];
    end if;

    if Depth ge 1 then
	if 1 eq 1 and c eq 1 then
	    l, p := sym_forms_test(M, e, c);
	    if l then
		IndentPop();
		MarkIrreducible(M, p);
		return [M], [p];
	    end if;
	end if;
    end if;

// Sep 15: turned off
    if
false and
	e gt 20 and Depth le 1 and not is_perm_module and HomogIrredDim eq 0 
	/*and c eq 1*/
    then
	vprint ZMeataxe:
	    "Homogeneous and big endo; try Meataxe for irreducible";

	range := 3;
	ML := [ActionGenerator(M, i): i in [1 .. nag]];
	best_dim := 10^10;
	best_S := 0;

	verb := GetVerbose("ZMeataxe");

	for i := 1 to 5 do
	    vprintf ZMeataxe: "Try %o\n", i;
	    X := &+[Random({-range .. range} diff {0})*g: g in ML];
	    vprint ZMeataxe: "Get factored min poly";
	    vtime ZMeataxe: L := FactoredMinimalPolynomial(X: Proof := false);

	    for t in L do
		vprint ZMeataxe: "Get kernel for factor:", t;
		vtime ZMeataxe:
		    N := LLL(KernelMatrix(Evaluate(t[1], X)): Proof := false);
		vprintf ZMeataxe: "Kernel dim: %o; spin one vector\n", Nrows(N);
		v := N[1];

		SetVerbose("ZMeataxe", 0);
		vtime ZMeataxe: S := SpinAction(v, ML);
		SetVerbose("ZMeataxe", verb);

		d := Dimension(S);
		vprintf ZMeataxe: "Spin dimension: %o\n", d;
		if d lt best_dim then
		    best_dim := d;
		    best_S := S;
		    vprintf ZMeataxe: "NEW BEST\n";
		    if best_dim le 3 then
			break;
		    end if;
		end if;
	    end for;
	end for;

	if best_dim lt Dimension(M) then
	    vprint ZMeataxe: "Decompose", best_S;
	    IndentPush();
	    vtime ZMeataxe: S, SI := IntegralDecomposition(
		best_S: HomogIrredDim := HomogIrredDim
	    );
	    IndentPop();
	    si := SI[1];
	else
	    si := 0;
	    best_S := 0;
	end if;

	if si gt 0 then
	    U := S[1];
	    vprintf ZMeataxe: "Get homs from dim %o submodule\n", Dimension(U);
	    vtime ZMeataxe: H := GHomOverCentralizingField(U, M);
	    vprint ZMeataxe: "Got", H;

	    dd := Dimension(H)*Dimension(U);
	    if dd eq Dimension(M) then
		HB := Basis(H);
		vprintf ZMeataxe: "Apply LLL to basis of dim %o\n", #HB;
		vtime ZMeataxe: HB := basis_LLL(HB);

		I := [
		    ImageWithBasis(LLL(h: Proof := false), M: Check := false):
			h in HB
		];
		vprintf ZMeataxe: "Good result with %o submodule(s)\n", #I;
		IndentPop();
		S := [si: i in [1 .. #I]];
		MarkIrreducibleSeq(I, S);
		return I, S;
	    end if;

	    vprintf ZMeataxe: "Wrong dim %o\n", dd;
	else
	    vprint ZMeataxe: "SI 0, so fail";
	    vprint ZMeataxe: "best_S:", best_S: Magma;
	end if;
    end if;

    if ME cmpeq 0 then
	vprint ZMeataxe: "Get Endo";
//M: Magma;
	vtime ZMeataxe:
	    E := EndomorphismRing(M);
    else
	vprint ZMeataxe: "Already got Endo";
	E := ME;
    end if;

    vprint ZMeataxe: E;

    d := Dimension(E);
    if d eq 1 then
	vprint ZMeataxe: "Endo trivial so M indecomposable";
	IndentPop();
	MarkIrreducible(M, 1);
	return [M], [1];
    end if;

    L := Basis(E);

/*
"USE CENTRE Basis";
L := Basis(CentreOfEndomorphismRing(M));
"dim:", #L;
*/

    // procedure split_by_basis(

    d := #L;
    COUNT := 3;
    GCOUNT := 0;
    GCOUNT := d;
    //GCOUNT := Min(GCOUNT, 5);
    RANGE := 1;
    BEST_COUNT_MAX := 10;

    best_count := 0;
    bestn := 0;

    if is_perm_module then
	GCOUNT := 0;
	COUNT := 5;
    end if;

    for i := 1 to GCOUNT + COUNT do
	vprint ZMeataxe, 2: "ELT", i;
	if i le GCOUNT then
	    vprint ZMeataxe, 2: "Use gen", i;
	    //r := BasisElement(E, i);
	    r := L[i];
	else
	    vprint ZMeataxe, 2: "Use random";
	    r := random_comb(L, [-RANGE .. RANGE]);
	end if;

	if IsOne(r) then
	    continue;
	end if;

	vtime ZMeataxe, 2: 
	    mf := FactoredMinimalPolynomial(r: Proof := false);

	vprint ZMeataxe, 2: "Number of factors:", #mf;
	if #mf gt bestn then
	    vprintf ZMeataxe: "New best: elt %o, number factors: %o\n", i, #mf;
	    bestn := #mf;
	    bestr := r;
	    bestmf := mf;
	    if #mf eq #split_degs then
		vprint ZMeataxe:
		    "Number of modular factors now equals split cardinality";
		break;
	    end if;
	elif #mf eq bestn and bestn gt 1 then
	    best_count +:= 1;
	    if best_count eq BEST_COUNT_MAX then
		vprint ZMeataxe: "Best count now hit";
		break;
	    end if;
	end if;
    end for;

    r := bestr;
    mf := bestmf;
    vprint ZMeataxe: "Best number of factors:", bestn;
    vprint ZMeataxe: "Min poly split:", [<Degree(t[1]), t[2]>: t in mf];
    if GetVerbose("ZMeataxe") ge 2 then
	if #Sprint(mf) le 100 then
	    vprint ZMeataxe, 2: "Best factors:", mf;
	end if;
    end if;

//"r:", r;
//"mf:", mf;

    if bestn eq 1 and bestmf[1, 2] eq 1 then

	IndentPop();
	vprint ZMeataxe: "r is 1";

	Q := split_LLL_endo(M, WantSubmodules);
	if #Q gt 1 then
	    vprint ZMeataxe: "Got LLL Decomposition:", Q;
	    SS := [];
	    BB := [];
	    IndentPush();
	    for x in Q do
		S, B := IntegralDecomposition(
		    x: Depth := 1,
		    HomogIrredDim := HomogIrredDim,
		    SeenChars := SeenChars,
		    WantChars := WantChars,
		    SplitChars := SplitChars,
		    WantSubmodules := WantSubmodules
		);
		SS cat:= S;
		BB cat:= B;
	    end for;
	    IndentPop();
	    return SS, BB;
	end if;

	vprint ZMeataxe: "Use split_homog";
	return split_homog(M, E, WantSubmodules);

    end if;

    if bestn eq 1 then
	vprintf ZMeataxe, 2:
	    "Single factor; change multiplicity from %o to 1\n", bestmf[1, 2];
	bestmf[1, 2] := 1;
    end if;

    if #WantDTraces gt 0 then
	for ti := 1 to #bestmf do
	    t := bestmf[ti];
	    vprintf ZMeataxe: "Get kernel %o for (degree %o)^%o\n",
		ti, Degree(t[1]), t[2];
	    vtime ZMeataxe: N := Kernel(Evaluate(t[1]^t[2], r));
	    vprintf ZMeataxe: "Dimension: %o\n", Dimension(N);
	    B := BasisMatrix(N);
	    vprint ZMeataxe: "Do LLLBlock on dim", Nrows(B);
	    vtime ZMeataxe:
		 B := LLLBlock(B);
	    S := ImageWithBasis(B, M: Check := false);

	    want_dtraces_search(
		S, ~want_module, ~want_count, ~want_ind_seen, ~modules_to_split,
		~trace_ind, ~SC_traces
	    );
	    if #want_module eq #want_ind then
		vprint ZMeataxe: "All wanted got; break";
		break;
	    end if;
	end for;

	vprint ZMeataxe: "want_module:", want_module;
	vprint ZMeataxe: "want_count:", want_count;

	if #want_module ne #want_ind then
	    vprint ZMeataxe: "MISSED ALL WANTED";
	end if;

	if #want_module eq #want_ind and Set(want_count) eq {1} then
	    vprint ZMeataxe: "GOT ALL WITH COUNT 1";
	    IndentPop();
	    MarkIrreducibleSeq(want_module, want_count);
	    return want_module, want_count;
	end if;

	vprint ZMeataxe: "COUNT > 1";

	if #want_module eq #want_ind then
	    vprint ZMeataxe: "Right number of wanted; recurse on these";
	    SS := [];
	    BB := [];
	    for i := 1 to #want_module do
		S, B := IntegralDecomposition(
		    want_module[i]: Depth := 1, HomogIrredDim := HomogIrredDim
		);
		SS cat:= S;
		BB cat:= B;
	    end for;
	    IndentPop();
	    return SS, BB;
	end if;

    end if;

    mod_chars_test := false;
    mod_chars_test := true;
    mod_chars_test := mod_chars_test and #WantChars ne 0;

    use_knapsack := true;
    vprint ZMeataxe: "Get Kernels";

    if mod_chars_test then
	A := Action(M);
	L := [A.i: i in [1 .. nag]];

	PRIME := PreviousPrime(K_PRIME_2);
	K := GF(PRIME);
	rK := Matrix(K, r);
	NK := [**];
	for t in bestmf do
	    vprint ZMeataxe: "Get modular kernel for degree", Degree(t[1]);
	    vtime ZMeataxe:
		NN := Kernel(Evaluate(PolynomialRing(K)!t[1]^t[2], r));
	    Append(~NK, NN);
	end for;

	dims := [Dimension(x): x in NK];
	vprint ZMeataxe: "Modular kernel dims:", dims;

	/*
	SHOULD DO MORE: even if not perfect split, then with knapsack
	on degs for each dim, can eliminate several submodules (and
	find the ones we want).
	*/

	if split_degs eq Sort(dims) then
	    vprint ZMeataxe: "MATCHES GIVEN SPLIT!";
	    want_degs := {Degree(x): x in WantChars};
	    indices := [i: i in [1 .. #NK] | Dimension(NK[i]) in want_degs];
	    dims := [Dimension(NK[i]): i in indices];
	    vprint ZMeataxe: "Reduced modular kernel dims:", dims;
	else
	    indices := [1 .. #NK];
	end if;

	seen_degs := {Degree(s): s in SeenChars};
	//"seen_degs:", seen_degs;

	N := [**];
	chars := [];
	c := 0;

	for i in indices do
	    NN := NK[i];
	    t := bestmf[i];
	    skip := false;
	    delete c;

	    possible := get_possible_chars(
		SplitChars, split_degs, split_degs_index, Dimension(NN)
	    );

	    assert #possible ge 1;
	    if #possible eq 1 then
		vprintf ZMeataxe:
		"%o: unique knapsack solution gives character for dim %o\n",
		    i, Dimension(NN);
		c := Rep(possible);
	    else
		vprintf ZMeataxe:
		"%o: %o knapsack solutions; get modular submodule of dim %o\n",
		    i, #possible, Dimension(NN);
		B := BasisMatrix(NN);
		if not assigned LK then
		    LK := [Matrix(K, X): X in L];
		end if;
		vtime ZMeataxe:
		    SL := [Solution(B, B*X): X in LK];
		SK := GModule(Group(M), SL);
		IndentPush();
		c := Char(SK: SymRange, Possible := possible);
		IndentPop();
	    end if;

	    if not ignore_seen_test(c) then
		vprint ZMeataxe: "Keep; get integral kernel for degree",
		    Degree(t[1]);
		vtime ZMeataxe:
		    NN := Kernel(Evaluate(t[1]^t[2], r));
		Append(~N, NN);
		chars[#N] := c;

		// THINK: if got all want chars now then stop!
	    end if;
	end for;
    else
	vtime ZMeataxe:
	    N := [Kernel(Evaluate(t[1]^t[2], r)): t in bestmf];
	chars := [];
    end if;

    vprint ZMeataxe: "Kernel dimensions:", [Dimension(S): S in N];

    Q := [];

    for k := 1 to #N do
	vprint ZMeataxe: "Make rep", k;
	SL := [];
	B := BasisMatrix(N[k]);
	vprint ZMeataxe: "Do LLL on dim", Nrows(B);
	vtime ZMeataxe:
	     B := LLLBlock(B);
// "LLL B:", B; "Real LLL:", LLL(B);

	vprint ZMeataxe: "Form image";
	if not WantSubmodules and Type(M) eq ModGrp then
	    vtime ZMeataxe:
		SL := [Solution(B, B*X): X in L];
		/*
		for i := 1 to #L do
		    SL[i] := Solution(B, B*L[i]);
		end for;
		*/

	    S := GModule(Group(M), SL: Check := false);
	else
	    vtime ZMeataxe:
		//S := sub<M | [B[i]: i in [1..Nrows(B)]]>;
		S := ImageWithBasis(B, M: Check := false);
	end if;

	if IsDefined(chars, k) then
	    vprint ZMeataxe: "Include character";
	    S`Character := chars[k];
	end if;

	Append(~Q, S);
    end for;

    vprint ZMeataxe: "Final kernel dimensions:", [Dimension(S): S in N];

    vprint ZMeataxe: "Recurse to prove on each";
    SS := [];
    BB := [];
    for x in Q do
	S, B := IntegralDecomposition(
	    x: Depth := 1,
	    HomogIrredDim := HomogIrredDim,
	    SeenChars := SeenChars,
	    WantChars := WantChars,
	    SplitChars := SplitChars,
	    WantSubmodules := WantSubmodules
	);
	SS cat:= S;
	BB cat:= B;
    end for;
    IndentPop();
    return SS, BB;

end intrinsic;
