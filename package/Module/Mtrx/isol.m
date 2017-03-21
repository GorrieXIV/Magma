freeze;

/*******************************************************************************
				Debug
*******************************************************************************/

CHECK_UnimodularExtension := true;
CHECK_UnimodularExtension := false;

/*******************************************************************************
				Auxiliary
*******************************************************************************/

Z := IntegerRing();

function Pivots(X)
    // Pivot columns of X
    E := EchelonForm(X);
    P := [];
    for i := 1 to Nrows(E) do
        S := Support(E[i]);
        if #S gt 0 then
            Append(~P, Min(S));
        end if;
    end for;
    return P;
end function;

/*******************************************************************************
			Unimodular Extension
*******************************************************************************/

function unimodext_direct(X)

    r := Nrows(X);

    vprint Isolution: "Get Smith with right inverse"; vtime Isolution:
    S, U := SmithForm(X: RightInverse);

    c := Ncols(X);
    assert Nrows(U) eq c;
    U := RowSubmatrixRange(U, r + 1, c);
    return U;
    // J := VerticalJoin(X, U); return J;

end function;

function get_indep_rows(X, ED)

    m := Nrows(X);
    n := Ncols(X);
    rank := #ED;

    V := sub<RSpace(Z, n)|>;
    I := [];
    for i := 1 to m do
        Include(~V, X[i], ~new);
        if new then
            Append(~I, i);
            if #I ge rank and ElementaryDivisors(BasisMatrix(V)) eq ED then
                break;
            end if;
        end if;
    end for;

    return I;
end function;

intrinsic UnimodularExtension(X::Mtrx: IsHerm := false) -> Mtrx
{Given a basis matrix X with trivial elementary divisors, return a matrix
U such that the vertical join of X with U is unimodular}

    OX := 0;
    if CHECK_UnimodularExtension then
	OX := X;
    end if;

    //printf "UnimodularExtensionX := %m\n;", X;

    require BaseRing(X) cmpeq Z: "Matrix must be integral";
    // Don't bother to check ED

    nr := Nrows(X);
    nc := Ncols(X);

    if nr eq 0 then
	return MatrixRing(Z, nc)!1;
    end if;

//return unimodext_direct(X);
    if 1 eq 1 and not IsHerm then
	vprintf Isolution:
	    "UnimodularExtension (%o by %o): get Hermite\n",
	    Nrows(X), Ncols(X);
	vtime Isolution: X := HermiteForm(X);
    end if;
    vprint Isolution: "First X Diagonal:", Diagonal(X);

//"UNI MOD EXT:"; X: Magma;

    if false and exists{i: i in [1 .. nr - 1] | X[i, i] ne 1 } then
	return unimodext_direct(X);
    end if;
    
    ED := [1: i in [1 .. nr]];

    if nr ge 20 then
	min_end_nr := 3;
    else
	min_end_nr := 1;
    end if;

    perm0 := Sym(nc) ! 1;
    first := true;
    while true do
        b := 1;
        while b lt nr and X[b, b] eq 1 do
            b +:= 1;
        end while;

        vprint Isolution: "Got b:", b;
//first := false;
        if not first or nr - b le min_end_nr then
            break;
        end if;

        first := false;
        vprint Isolution: "Use col basis";

        if ED cmpeq 0 then
	    vprint Isolution: "Get ED";
            time ED := ElementaryDivisors(X);
        end if;

        I := get_indep_rows(Transpose(X), ED);
        IS := Set(I);
        II := [i: i in [1 .. nc] | i notin I];

        vprint Isolution: "Got I:", I;
	if CHECK_UnimodularExtension then
	    XI := ColumnSubmatrix(X, I);
	    "XI:", XI;
	    XIED := EDMS(XI);
	    "XI ED:", XIED;
	    assert XIED eq {* 1^^Nrows(XI) *};
	end if;

        I cat:= II;

        perm0 := Sym(nc) ! I;

        X := ColumnSubmatrix(X, I);
        vprint Isolution: "Get Herm again"; vtime Isolution:
            X := HermiteForm(X);

	// Now first #I cols of X have trivial ED

        vprint Isolution: "X Diagonal:", Diagonal(X);
        //perm0 := perm0^-1;

	if CHECK_UnimodularExtension then
	    assert X^perm0 eq OX;
	end if;
    end while;

    /*
    Now work on rows b to end.

    Seems best to use ~50 when big integers, but not too big for LLL
    in Hermite.
    */

//Support(X[nr]); X;
    k := 10;
    k := 50;

//k := 3; "HACK k", k;

    if b eq nr then
	c := nr;
	lastg := 0;
	goodc := [];
	while lastg ne 1 do
	    g := GCD(lastg, X[nr, c]);
	    if g ne lastg then
		Append(~goodc, c);
		lastg := g;
	    end if;
	    c +:= 1;
	end while;

	goodcs := Set(goodc);
	perm := Sym(nc) !
	    ([1 .. nr - 1] cat goodc cat [j: j in [nr .. nc] | j notin goodcs]);

	vprint Isolution: "goodc:", goodc;

	if not IsIdentity(perm) then
	    X := X^(perm^-1);
	end if;
    else
	perm := 1;
    end if;

    while true do
	k := Min(k, nc - b + 1);
	if b eq nr then
	    Q := [X[nr, j]: j in [nr .. nr + k - 1]];
	    if GCD(Q) eq 1 then
		break;
	    end if;
	else
	    Y := Submatrix(X, b, b, nr - b + 1, k);
	    vprint Isolution: "Y:", Parent(Y);
	    ED := ElementaryDivisors(Y);
	    if #ED eq Nrows(Y) and ED[#ED] eq 1 then
		vprint Isolution: "Good Y:", Y;
		break;
	    end if;
	end if;
	k +:= 10;
    end while;

    vprint Isolution: "Use k:", k;
    if b eq nr then
	vprint Isolution: "Q:", Q;
	C := ColumnMatrix(Q);
    else
	C := Transpose(Y);
    end if;

    //"C:"; Parent(C); LogNorms(C); C: Magma;

    vprint Isolution: "Get column Hermite of C"; vtime Isolution:
    CH, U := HermiteForm(C: Optimize);

    //"CH:", CH; "U:", U;
    vprint Isolution: "First U LogNorms:", LogNorms(U);

    e := Ncols(C);
    assert Determinant(RowSubmatrix(CH, 1, e)) in {1, -1};

    vprint Isolution: "Invert U"; vtime Isolution:
    U := U^-1;
    U := Transpose(U);
    U := RowSubmatrixRange(U, e + 1, Nrows(U));

    vprint Isolution: "HermiteForm of U:"; vtime Isolution:
    U := HermiteForm(U);

    vprint Isolution: "LLL of U:"; vtime Isolution:
    U := QuickLLL(U);

    assert Nrows(U) eq k - e;
    assert Ncols(U) eq k;

    V := ZeroMatrix(Z, nc - nr, nc);
//Parent(V);
    InsertBlock(~V, U, 1, b);
    for j := b + k to nc do
	V[j - b - e + 1, j] := 1;
    end for;

    if perm cmpne 1 then
	perm := perm0*perm;
    else
	perm := perm0;
    end if;
    //perm := perm0^-1*perm;
    if perm cmpne 1 and not IsIdentity(perm) then
	V := V^perm;
    end if;

    if CHECK_UnimodularExtension then
	"CHECK UnimodularExtension";
	J := VerticalJoin(OX, V);
	Parent(J);
	ED := EDMS(J);
	"J EDMS:", ED;
	assert ED eq {* 1^^nc *};
    end if;

    return V;

end intrinsic;

/*******************************************************************************
			Lattice Basis Matrix
*******************************************************************************/

intrinsic LatticeBasisMatrix(X::Mtrx: ED := 0, Inc := 0) ->
    Mtrx, Mtrx, SeqEnum, Mtrx
{Return a basis matrix B of the lattice spanned by the rows of X, with
transformation T so that T*X = B, the list of indices for the rows of
X that are actually used, and the matrix of those rows from X
(set E to elementary divisors of X if known)}

    require BaseRing(X) cmpeq Z: "Matrix must be integral";

    if ED cmpeq 0 then
        vprint Isolution: "Get ElementaryDivisors"; vtime Isolution:
        E := ElementaryDivisors(X);
    else
        E := ED;
    end if;

    rank := #E;
    EP := &*E;

    USE_KER := true;

    vprintf Isolution: "LatticeBasisMatrix: %o by %o\n", Nrows(X), Ncols(X);
    vprint Isolution: "Input ED:", {* x: x in E *};
    vprint Isolution: "Input rank:", rank;

    m := Nrows(X);
    if rank eq m then
	return X, MatrixRing(Z, m)!1, 0, [1 .. m], X, [1 .. m];
	//return U*Y, U, N, Ypp, Y, pp;
    end if;

    d := E[#E];
    p := 1;
    repeat
	p := NextPrime(p);
    until d mod p ne 0;
    vprint Isolution: "Get pivots mod", p; vtime Isolution:
    piv := Pivots(Matrix(GF(p), Transpose(X)));
    pivs := Set(piv);
    // Remove repeated rows?
    pp := piv cat [i: i in [1 .. m] | i notin pivs];

    last_EY := 0; e := 0;
last_l := rank;
    e := 1;
    e := 5;
    e := 10;

e := 20;
e := 30;

    if Inc gt 0 then
	e := Inc;
    end if;

    vprint Isolution: "Use Inc:", e;

    ecount := 0;
    step := 0;

    if USE_KER then
	det := 0;

        DELAY := true; // has bugs
DELAY := false;
        if DELAY then
            last_l := rank;
        else
            Ypp := pp[1 .. rank];

            Y := RowSubmatrix(X, Ypp);

            vprint Isolution: "Get determinant of initial sublattice";
            //vtime Isolution: det := Determinant(Y);
            vtime Isolution: det := &*ElementaryDivisors(Y);
            vprint Isolution: "Initial quotient:", det/EP;

            /*
            "Det Fact:", Factorization(det);
            "EP fact:", Factorization(EP);
            "Init quot fact:", Factorization(Z!(det/EP));
            */

            last_l := #Ypp;
            Ldet := det;
        end if;

        first := DELAY;

	while first or Ldet ne EP do
	    step +:= 1;

	    l := Min(last_l + e, #pp);
	    ecount +:= e;
	    Ypp := pp[1 .. l];
//Ypp;
	    Y := RowSubmatrix(X, Reverse(Ypp));
	    vprint Isolution: "\n*** STEP", step;
	    vprintf Isolution: "rank: %o, last_l: %o, l: %o\n", rank, last_l, l;

            if first then
                vprint Isolution: "Get determinant of initial sublattice";
                //vtime Isolution: det := Determinant(Y);
                vtime Isolution: det := &*ElementaryDivisors(Y);
vprint Isolution: "Got:", det;
                Ldet := det;
            end if;

	    vprintf Isolution: "Quotient: %o\n", Ldet/EP;

	    vprint Isolution: "Get kernel";
	    vtime Isolution: k := EchelonForm(KernelMatrix(Y));
	    kr := Nrows(k);
	    assert kr eq Nrows(Y) - rank;
	    sk := ColumnSubmatrix(k, 1, kr);
	    //sk := ReverseColumns(sk);
	    sk := EchelonForm(sk);
	    //"sk:", sk;
	    skd := Diagonal(sk);

	    skd := Reverse(skd);
	    vprint Isolution: "Fixed sk Diag:", skd;

	    // "New &*skd fact:", Factorization(&*skd);
            if not first then
                Ldet := ExactQuotient(det, &*skd);
            end if;

	    ind := [i: i in [1 .. #skd] | skd[i] ne 1];
	    vprint Isolution: "ind:", ind;

	    if false and #ind eq 1 and Ldet eq EP then
                MIN := 20;
		i := ind[1];
		ind := [i: i in [1 .. Min(MIN, #skd)]];
		Include(~ind, i);
		Sort(~ind);
		vprint Isolution: "EXTEND ind:", ind;
	    end if;

	    keep := [1 .. rank] cat [rank + i: i in ind] cat
		[rank + kr + 1 .. #pp];
	    pp := pp[keep];
	    last_l := rank + #ind;
	    Ypp := pp[1 .. last_l];
	    Y := RowSubmatrix(X, Ypp);

	    /*
	    vprintf Isolution:
		"Get ElementaryDivisors for %o + %o rows\n",
		rank, Nrows(Y) - rank;

	    vtime Isolution: EY := ElementaryDivisors(Y);
	    vprint Isolution: "EY:", {* x: x in EY *};
	    EPY := &*EY;
	    vprint Isolution: "E quotient:", EPY/EP;
	    if EY eq E then
		break;
	    end if;
	    last_EY := EY;
	    */

            first := false;

	end while;
    else
	while true do
	    step +:= 1;

	    l := Min(last_l + e, #pp);
	    ecount +:= e;
	    Ypp := pp[1 .. l];
	    Y := RowSubmatrix(X, Ypp);
//Ypp;
	    vprint Isolution: "\n*** STEP", step;
	    vprintf Isolution: "rank: %o, last_l: %o, l: %o\n", rank, last_l, l;

	    if USE_KER then
		vprint Isolution: "Get kernel";
		vtime Isolution: k := KernelMatrix(ReverseRows(Y));
		kr := Nrows(k);
		assert kr eq Nrows(Y) - rank;
		sk := ColumnSubmatrix(k, 1, kr);
		//sk := ReverseColumns(sk);
		sk := EchelonForm(sk);
		//"sk:", sk;
		skd := Diagonal(sk);

		skd := Reverse(skd);
		vprint Isolution: "Fixed sk Diag:", skd;

		ind := [i: i in [1 .. #skd] | skd[i] ne 1];
		vprint Isolution: "ind:", ind;
		keep := [1 .. rank] cat [rank + i: i in ind] cat
		    [rank + kr + 1 .. #pp];
		pp := pp[keep];
		last_l := rank + #ind;
		Ypp := pp[1 .. last_l];
		Y := RowSubmatrix(X, Ypp);

		// KP := &*skd; "KP quot:", EP/KP;
	    end if;

	    vprintf Isolution:
		"Get ElementaryDivisors for %o + %o rows\n",
		rank, Nrows(Y) - rank;

	    vtime Isolution: EY := ElementaryDivisors(Y);
	    vprint Isolution: "EY:", {* x: x in EY *};
	    EPY := &*EY;
	    vprint Isolution: "E quotient:", EPY/EP;
	    if EY eq E then
		break;
	    end if;

	    if USE_KER then
		;
	    elif last_EY cmpne 0 and EY eq last_EY then
		vprint Isolution: "No change; remove extra row indices";
		//pp := pp[1 .. l - e] cat pp[l + 1 .. #pp];
//last_l, l;
assert l gt last_l;
		pp := pp[1 .. last_l] cat pp[l + 1 .. #pp];
	    else
		//e +:= 10;
		last_l := l;
	    end if;
	    last_EY := EY;
    //assert ElementaryDivisors(RowSubmatrix(X, pp)) eq E;
	end while;
    end if;

    vprintf Isolution: "Final number of extra rows: %o\n", Nrows(Y) - rank;

    vprint Isolution: "Get kernel"; vtime Isolution:
    N := KernelMatrix(Y);

//N;

    vprint Isolution: "Kernel dim:", Nrows(N);
    if 1 eq 1 then
	vprint Isolution: "Get Echelon of kernel"; vtime Isolution:
	N := EchelonForm(N);
    else
	vprint Isolution: "Get LLL of kernel"; vtime Isolution:
	//N := QuickLLL(N);
	N := LLL(N: Proof := false);
    end if;

    vprint Isolution: "LLL Kernel log norms:", LogNorms(N);

    U := UnimodularExtension(N);
    //delete N;

//"First U:", U;
    //U := QuickLLL(U);
//"Next U:", U;

    return U*Y, U, N, Ypp, Y, pp;

end intrinsic;

intrinsic NHerm(X::Mtrx: e := 1) -> Mtrx
{Internal; assumes rank eq Ncols(X)?}

//SetVerbose("Isolution",1);
//"NHerm"; X: Magma;

    n := Ncols(X);
    m := Nrows(X);
    s := n - e;

    vprintf Isolution: "NHerm: %o by %o\n", m, n;

    S := ColumnSubmatrix(X, 1, s);
    vprint Isolution: "Get initial ED";
    vtime Isolution: SED := ElementaryDivisors(S);

    B, U, N, Ypp, Y := LatticeBasisMatrix(S: ED := SED);
    pp := Ypp cat [i: i in [1 .. m] | i notin Ypps] where Ypps := Set(Ypp);
    X := RowSubmatrix(X, pp);

    k := #Ypp;
    assert k ge s;
    d := k - s;

    C := Submatrix(X, 1, s + 1, k, e);
    UC := U*C;
    NC := N*C;

    //"UC:", Parent(UC); UC;
    //"NC:", Parent(NC); NC;

// Add case below where max ED is 1!!!

    M := SED[#SED];

    if M eq 1 then
        P := B;
        delete B, S;
        SH := MatrixRing(Z, Ncols(P))!1;
    else
        M := 2*M;
        R := IntegerRing(M);
        S := Matrix(R, S);

        PACKED_LIMIT := 16;

        Sd := Density(S);
        if Sd le 0.1 and M le PACKED_LIMIT then
            S := SparseMatrix(S);
            vprintf Isolution:
                "Get Hermite of S (sparse density %.4o) mod %o\n",
                Sd, M;
            vtime Isolution: Echelonize(~S);
            S := SparseMatrix(Z, S);
            S := Matrix(S);
            SH := S;
        else
            //S: Magma;
            vprint Isolution: "Get Hermite S mod", M; vtime Isolution:
            //S := EchelonForm(S);
            S := EchRec(S);
            SH := Matrix(Z, EchelonForm(S));
        end if;
        delete S;

        RemoveZeroRows(~SH);

        vprint Isolution: "Get PseudoInverse of SH"; vtime Isolution:
        PI, den := PseudoInverse(Matrix(SH));

        vprint Isolution: "Get product of B and PI"; vtime Isolution:
        P := (B*PI) div den;
        delete PI, B;

    end if;

    vprint Isolution: "Get solution column W"; vtime Isolution:
    W := Transpose(Solution(Transpose(P), Transpose(UC)));
    delete P;

    // "SH:", SH; "W:", W;

    NC := HermiteForm(NC);
    if e eq 1 and Nrows(NC) gt 0 then
	M := NC[1, 1];
	if M ne 0 then
	    vprint Isolution: "Mod W by bottom entry", M;
	    for i := 1 to Nrows(W) do
		W[i, 1] := W[i, 1] mod M;
	    end for;
	end if;
    end if;

    InsertBlock(~X, SH, 1, 1);
    InsertBlock(~X, W, 1, s + 1);
    for i := s + 1 to k do
	X[i] := 0;
    end for;
    InsertBlock(~X, NC, s + 1, s + 1);

    vprint Isolution: "Final classical Hermite"; vtime Isolution:
    X := HermiteForm(X: Al := "Classical", InitialSort := false);

    return X;

end intrinsic;

intrinsic SingleSolutionTest(X::Mtrx, W::Mtrx) -> Mtrx
{true and solution V with V*X=W, or false if no solution}

    require BaseRing(X) cmpeq Z and BaseRing(W) cmpeq Z:
	"Matrices must be integral";

    n := Ncols(X);
    require Ncols(W) eq n: "RHS must have the same number of columns";

    B, U, N, Ypp, Y := LatticeBasisMatrix(X);
    vprint Isolution: "Get solution for B"; vtime Isolution:
    l, S := IsConsistent(B, W);
    if not l then
	return false, _;
    end if;

    m := Nrows(X);
    r := Nrows(S);
    s := Ncols(S);
// "S:", S; "B:", B; "U:", U; "Ypp:", Ypp; "s:", s; "Y:", Y;

    S *:= U;
    delete U;
// "New S:", S;
// "New S*Y:", S*Y;

    if Type(W) eq ModTupRngElt then
	V := RSpace(Z, m)!0;
	for j := 1 to Ncols(S) do
	    //V[Ypp[j]] := S[j];
	    V[j] := S[Ypp[j]];
	end for;
    else
	V := RMatrixSpace(Z, r, m)!0;
	for i := 1 to r do
	    for j := 1 to Ncols(S) do
		V[i, Ypp[j]] := S[i, j];
	    end for;
	end for;
    end if;

    return true, V;

end intrinsic;

/*******************************************************************************
			Unimodular Extension
*******************************************************************************/

intrinsic NHerm2(X::Mtrx: e := 1, k := 10) -> Mtrx
{Internal; assumes rank eq Ncols(X)?}

    n := Ncols(X);
    r := Nrows(X);
    ok := r - n;
    k := Min(k, ok);

    S := Submatrix(X, 1,1, n+k, n-e);

    printf "S: %o by %o\n", Nrows(S), Ncols(S);

    "Get kernel";
    time ker := KernelMatrix(S);

    Parent(ker);
    "LogNorms:", LogNorms(ker);

    SC := Submatrix(X, 1,n-e+1, n+k,e);
    R := ker*SC;
    RH := HermiteForm(R);
    RemoveZeroRows(~RH);
    "Bottom right Hermite:", RH;

    "Get UnimodularExtension";
    time U := UnimodularExtension(ker);

    "Get US";
    time US := U*S;
    Parent(US);

    assert Nrows(US) eq Ncols(US);

    //SetVerbose("Determinant",1);
    "Get US ED";
    time ED := EDMS(US);
    "ED:", ED;
    M := Max(ED);
    "M:", M;

    if M eq 1 then
        P := US;
        H := MatrixRing(Z, Ncols(US))!1; // Put direct into result!
    else
        printf "Get Herm of US (%o by %o) mod M\n", Nrows(US), Ncols(US);

        time H := EchRec(Matrix(IntegerRing(M), US));
        H := Matrix(Z, H);
        RemoveZeroRows(~H);

        vprint Isolution: "Get PseudoInverse of SH"; vtime Isolution:
            PI, den := PseudoInverse(Matrix(H));
        vprint Isolution: "Get product of US and PI"; vtime Isolution:
            P := (US*PI) div den;
        delete PI, US;
    end if;

    RHED := EDMS(RH);
    "RHED:", RHED;
    RHM := Max(RHED);
    "RHM:", RHM;

    UC := U*SC;

    P := Transpose(P);
    UC := Transpose(UC);

    vprint Isolution: "Get solution column W"; vtime Isolution:
    if true then
        R := IntegerRing(RHM);
        P := Matrix(R, P);
        UC := Matrix(R, UC);
        W := Transpose(Solution(P, UC));
        W := Matrix(Z, W);
    else
        W := Transpose(Solution(P, UC));
    end if;
    delete P, UC;

    return H, W, RH;

end intrinsic;
