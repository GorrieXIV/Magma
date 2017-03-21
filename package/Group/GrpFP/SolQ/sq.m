freeze;

/* 
 * The Verbose_ modes are organized as bitmap flags, so one can 
 * combine print options by adding the given values.
 * Names, Values and Meanings:
 *
 * MSQ_TraceFunc:  (0 - 2)
 *     Give messages about the current function called.
 *     0:  No messages (Default)
 *     1:  Important functions
 *     2:  almost all (except some tiny and trivial functions
 *
 * MSQ_Collector (0 - 1)
 *    If 1, the timing for the setup of the collector is printed.
 *
 * MSQ_RepsCalc (0 - 3)
 *     1:  timing for calculating representations/modules on each level
 *     2:  some statistics on each level
 *
 * MSQ_RepsCheck   (0 - 3)
 *     1:  Timing information for checking extensions of modules
 *     2:  Statistics of the number of modules to be checked.
 *
 * MSQ_PrimeSearch (0 - 15)
 *     Information about different part in the algorithm for determine
 *     the relevant primes.
 *     1:  Timings and statistics about the calculation of rational
 *         representations (in combination with MSQ_RepsCalc).
 *     2:  Timings of the transformation into integral representations.
 *     4:  Calculation of the relevant primes determination step
 *     8:  Printing of new relevant primes
 *
 * MSQ_Messages (0 - 1)
 *     Given information about the size of the soluble quotients
 *     calculated so far.
 */ 

// Default levels of Print statements
SetVerbose("MSQ_PrimeSearch" , 0);
SetVerbose("MSQ_RepsCalc"    , 0);
SetVerbose("MSQ_RepsCheck"   , 0);
SetVerbose("MSQ_Collector"   , 0);
SetVerbose("MSQ_TraceFunc"   , 0);
SetVerbose("MSQ_Messages"    , 0);

/* 
 * Definitions of variables giving different strategies.
 * These are optional arguments of the main function MSQ.
 *
 * MSQ_CollectorModus :
 *     defines the setup modus for the symbolic collector:
 *     0:  complete precalculation of the tables
 *     1:  Partial precalculations, depending on the size of the tables,
 *     2:  Dynamic setup during normalisation (default)
 *
 * MSQ_ModulCalcModus :
 *     defines how the modules for nonsplit extensions are determined
 *     CAUTION: a change of this parameter can lead to wrong results if
 *               a series other than the SAG is chosen.
 *     0:   Calculate and check all modules (default)
 *     1:   Take constituents of tensor products, plus further
 *          candidates (faster, but need some checks)
 *     2:   Restrict to constituents tensor products.
 *          (better only for big quotients.)
 *          
 * MSQ_PrimeSearchModus :
 *     Defines the strategy of finding new relevant primes
 *
 *     0:   No prime search. (Default, if not explicitly requested)
 *     1:   Prime search after SQ calculation and quit.
 *          (suitable for checking the maximality of an SQ of known
 *           order/prime divisors)
 *     2:   Prime search after SQ calculation; continue if new primes
 *          occure.
 *     3:   Prime search end beginning of a new nilpotent section.
 *          (Default for explicite primesearch request)
 *     4:   Prime search at beginning of e new layer in the LCS
 *     5:   Prime search after each extension of the SQ.
 */

/*
 * A collection of help functions to set/read theses variables.
 */

MSQVerboseIsSet := function(NN, i)
// checks whether the i-th bit is set in A

A := GetVerbose(NN);
if A lt i then
	return false;
else
	A := A mod (2*i);
	if A lt i then
		return false;
	else
		return true;
	end if;
end if;

end function;
	
MSQ_TraceFunction := procedure(A, l);
// print message if MSQ_TraceFunc has given value

v := GetVerbose("MSQ_TraceFunc");
if v ge l then
	x := v mod (2*l);
	if x ge l then
		if l eq 1 then 
			print "   Enter:", A;
		else
			print "     Enter:", A;
		end if;
	end if;
end if;

end procedure;

MSQsetVerboseForOption := procedure(~pr)
case pr:
    when -1:
        pr := 0;
    when 0:
        SetVerbose("MSQ_PrimeSearch", 0);
        SetVerbose("MSQ_RepsCalc"   , 0);
        SetVerbose("MSQ_RepsCheck"  , 0);
        SetVerbose("MSQ_Collector"  , 0);
        SetVerbose("MSQ_TraceFunc"  , 0);
		SetVerbose("MSQ_Messages"   , 0);
    when 1:
        if not IsVerbose("MSQ_PrimeSearch") then
			SetVerbose("MSQ_PrimeSearch", 8); end if;
		if not IsVerbose("MSQ_Messages") then
			SetVerbose("MSQ_Messages"   , 1); end if;
    when 2:
        if not IsVerbose("MSQ_PrimeSearch") then
			SetVerbose("MSQ_PrimeSearch", 10); end if;
        if not IsVerbose("MSQ_RepsCalc") then
			SetVerbose("MSQ_RepsCalc"   , 1); end if;
        if not IsVerbose("MSQ_RepsCheck") then
			SetVerbose("MSQ_RepsCheck"  , 1); end if;
        if not IsVerbose("MSQ_Collector") then
			SetVerbose("MSQ_Collector"  , 1); end if;
		if not IsVerbose("MSQ_Messages") then
			SetVerbose("MSQ_Messages"   , 1); end if;
    when 3:
        if not IsVerbose("MSQ_PrimeSearch") then
			SetVerbose("MSQ_PrimeSearch", 11); end if;
        if not IsVerbose("MSQ_RepsCalc") then
			SetVerbose("MSQ_RepsCalc"   , 2); end if;
        if not IsVerbose("MSQ_RepsCheck") then
			SetVerbose("MSQ_RepsCheck"  , 2); end if;
        if not IsVerbose("MSQ_Collector") then
			SetVerbose("MSQ_Collector"  , 1); end if;
		if not IsVerbose("MSQ_Messages") then
			SetVerbose("MSQ_Messages"   , 1); end if;
    when 4:
        if not IsVerbose("MSQ_PrimeSearch") then
			SetVerbose("MSQ_PrimeSearch", 15); end if;
        if not IsVerbose("MSQ_RepsCalc") then
			SetVerbose("MSQ_RepsCalc"   , 3); end if;
        if not IsVerbose("MSQ_RepsCheck") then
			SetVerbose("MSQ_RepsCheck"  , 3); end if;
        if not IsVerbose("MSQ_Collector") then
			SetVerbose("MSQ_Collector"  , 1); end if;
		if not IsVerbose("MSQ_Messages") then
			SetVerbose("MSQ_Messages"   , 1); end if;
        if not IsVerbose("MSQ_TraceFunc") then
			SetVerbose("MSQ_TraceFunc"  , 1); end if;
    when 5:
        if not IsVerbose("MSQ_PrimeSearch") then
			SetVerbose("MSQ_PrimeSearch", 15); end if;
        if not IsVerbose("MSQ_RepsCalc") then
			SetVerbose("MSQ_RepsCalc"   , 3); end if;
        if not IsVerbose("MSQ_RepsCheck") then
			SetVerbose("MSQ_RepsCheck"  , 3); end if;
        if not IsVerbose("MSQ_Collector") then
			SetVerbose("MSQ_Collector"  , 1); end if;
		if not IsVerbose("MSQ_Messages") then
			SetVerbose("MSQ_Messages"   , 1); end if;
        if not IsVerbose("MSQ_TraceFunc") then
			SetVerbose("MSQ_TraceFunc"  , 2); end if;
end case;
end procedure;

MSQGetCollectorModus := function( MSQ_CollectorModus  );

if MSQ_CollectorModus eq 0 then
	return "Complete";
elif MSQ_CollectorModus eq 1 then
	return "Partial";
else
	return "Dynamic";
end if;
end function;

MSQGetRepsOption := function(flag)
// return the value for the optional arg 'Print' in the calculation of 
// Reps/Moduls

if flag eq true then  // rational representation calculation
	if MSQVerboseIsSet("MSQ_PrimeSearch", 1) then
		if MSQVerboseIsSet("MSQ_RepsCalc", 1) then
			if MSQVerboseIsSet("MSQ_RepsCalc", 2) then
				return 11;
			else
				return 7;
			end if;
		else
			if MSQVerboseIsSet("MSQ_RepsCalc", 2) then
				return 8;
			else
				return 4;
			end if;
		end if;
	else
		return 2*GetVerbose("MSQ_RepsCalc");
	end if;

else             // finite modules calculation
	return 2*GetVerbose("MSQ_RepsCalc");
end if;
end function;

Message_MSQ_return_comment := function(flag)
case flag:
when 0:
   	comm :=	"Soluble quotient stops when no extension with this specification was found.";
when 1:
   	comm := "Soluble quotient with this specification successfully completed.";
when 2:
   	comm :=	"Soluble quotient terminates when hitting a given bound.";

when 3:
   	comm :=	"Soluble quotient terminates when free abelian section found.";
end case;

return comm;
end function;

/* 
 * Help function for various situations
 */

find_nontrivial_length := function(weights, MSQ_PrimeSearchModus);

MSQ_TraceFunction("find_nontrivial_length", 2);

if #weights eq 0 then
	return 0;
end if;

nt := 0;
if MSQ_PrimeSearchModus le 2 then
	for lw in weights do /* nilpotent section */
		for lwl in lw do /* sequence of head/layers */
			for lwi in lwl do /* sequence of prime plus dimension */
				for i := 2 to #lwi do /* add up the dimensions */
					nt +:= Dimension(lwi[i]);
				end for;
			end for;
		end for;
	end for;
else
	lw := weights[#weights]; /* last nilpotent section */
	if MSQ_PrimeSearchModus eq 3 then
		for lwl in lw do /* sequence of head/layers */
			for lwi in lwl do /* sequence of prime plus dimension */
				for i := 2 to #lwi do /* add up the dimensions */
					nt +:= Dimension(lwi[i]);
				end for;
			end for;
		end for;
	else
		lwl := lw[#lw]; /* last head/layer */
		if MSQ_PrimeSearchModus eq 4 then
			for lwi in lwl do /* sequence of prime plus dimension */
				for i := 2 to #lwi do /* add up the dimensions */
					nt +:= Dimension(lwi[i]);
				end for;
			end for;
		elif MSQ_PrimeSearchModus eq 5 then
			lwi:= lwl[#lwl];         /* last module in layer   */
			nt := Dimension(lwi[#lwi]);
		end if;
	end if;
end if;

return nt;
end function;

/*******************************************************************************
			    ElementaryPrimeDivisors
*******************************************************************************/

/*
Allan, December 2000.
Most of this is being placed in C; but this can stay as is for moment.
*/

function lllblock(X, k)
    m := Nrows(X);
    if m eq 0 then
	return X;
    end if;

    n := Ncols(X);
    if k lt m then
	r := m div k;
	k := m div r + 1;
    end if;

    Q := [1 .. m by k];

    for i := 1 to #Q do
	r := Q[i];
	l := Min(k, m - r + 1);
	//printf "LLL BLOCK %o/%o, row: %o, number of rows: %o\n", i, #Q, r, l;
	XX := Submatrix(X, r, 1, l, n);
	XX := LLL(XX: Delta := 0.99999);
	InsertBlock(~X, XX, r, 1);
    end for;

    return X;
end function;

function get_det(W)
    L := lllblock(W, 50);
    return Abs(Determinant(L));
end function;

function random_subset(T, k)
    assert k le #T;
    //T := { 1 .. n };
    S := {};
    for i := 1 to k do
	x := Random(T);
	Exclude(~T, x);
	Include(~S, x);
    end for;
    return S;
end function;

function get_submat(X)
    n := Ncols(X);
    r := Nrows(X);
    if r eq n then
	return X;
    end if;
    assert r gt n;

    K := GF(11863279);

    Z := IntegerRing();
    Y := Matrix(Z, n, []);
    i := 1;
    while Nrows(Y) lt n do
	if i gt r then
	    return X;
	end if;
	d := n - Nrows(Y) + 20;
	l := Min(d, r - i + 1);
	//printf "Get submat n: %o, i: %o, d: %o, l: %o, nY: %o\n",
	//n, i, d, l, Nrows(Y);
	S := VerticalJoin(Y, RowSubmatrix(X, i, l));
	//"S:", Nrows(S);
	i +:= l;
	N := EchelonForm(KernelMatrix(Matrix(K, S)));
	C := { 1 .. Nrows(S) } diff {Min(Support(N[i])): i in [1 .. Nrows(N)]};
	//"#C:", #C;
	S := [S[i]: i in C];
	Y := RMatrixSpace(Z, #S, n) ! S;
	//Y := VerticalJoin(Y, S);
    end while;

    return Y;
end function;

// Given matrix X over Z and sequence ignore_primes of primes to ignore
ElementaryPrimeDivisors := function(X, ignore_primes)

"Entering ElementaryPrimeDivisors sq.m";
    MSQ_TraceFunction("ElementaryPrimeDivisors", 2);

    Z := Integers();
    r := Nrows(X);
    c := Ncols(X);
     
    dump := GetVerbose("User1") ge 1;

    if dump then
        FILE := "sq_dump";
        FILE := "~allan/mjunk/sq_dump";

	"*****";
        printf "ElementaryPrimeDivisors of %o by %o\n", Nrows(X), Ncols(X);
        "Ignore primes:", ignore_primes;

        "Dumping to", FILE;
        PrintFile(FILE, Sprintf("X := %m;\n", X));

	ds := GetVerbose("Smith");
	SetVerbose("Smith", 1);

        ZEIT := Cputime();
        T := Cputime();
    end if;

    S, s := SmithForm(X: Partial);

    if dump then
	SetVerbose("Smith", ds);
    end if;

    ss := Nrows(S);
    while ss gt s and IsZero(S[ss]) do
	ss -:= 1;
    end while;

    U := RowSubmatrixRange(S, s+1, ss);
    V := ColumnSubmatrixRange(U, s+1, Ncols(U));

    if dump then
        "Smith time:", Cputime(T);
	printf "Reduced dense matrix is %o by %o\n", Nrows(V), Ncols(V);
        T := Cputime();
    end if;

    if Ncols(V) gt Nrows(V) then
	if dump then
	    "Doesn't have full column rank";
	end if;
	return [0];
	//V := Transpose(V);
    end if;

    if dump then
	dv := GetVerbose("Determinant");
	SetVerbose("Determinant", 1);
    end if;

    BOUND := 10^6;

    ignore := &*ChangeUniverse(ignore_primes, Z);

    MULTI := 5;
    SUM := 10;

    step := 0;
    D := 0;
    repeat
	if true then

	    step +:= 1;
	    if step eq 1 then
		step := 2;
	    end if;

	    Vc := Ncols(V);

	    nz := [i: i in [1 .. Nrows(V)] | not IsZero(V[i])];
	    z := Nrows(V) - #nz;
	    if z gt 100 or z ge Nrows(V) div 4 then
		V := [V[i]: i in nz];
		V := RMatrixSpace(IntegerRing(), #V, Vc) ! V;
	    end if;

	    if true then
		rows := Nrows(V);
		VS := RSpace(Z, Vc);
		W := Matrix(
		    [
			&+[
			    VS | V[i]:
				i in random_subset({1 .. rows}, Min(SUM, rows))
			]: c in [1 .. MULTI - 1]
		    ]
		);
		W := VerticalJoin(get_submat(V), W);
	    else
		rows := Min(2 * Ncols(V), Nrows(V));
		R := random_subset({1 .. Nrows(V)}, rows);
		R := {i: i in R | V[i] ne 0};
		W := RMatrixSpace(IntegerRing(), #R, Ncols(V)) ! [V[i]: i in R];
	    end if;

	    L := lllblock(W, Nrows(W) le 100 select 20 else 50);

	    procedure chop(~L)
		z := Nrows(L);
		while z ge 1 and IsZero(L[z]) do
		    z -:= 1;
		end while;
		if z lt Nrows(L) then
		    L := RowSubmatrix(L, 1, z);
		end if;
	    end procedure;

	    chop(~L);

	    rows := Min(Ncols(L) - 1 + MULTI, Nrows(L));

	    if rows lt Ncols(L) then
		L := LLL(V: Delta := 0.999);
		chop(~L);
		if Nrows(L) lt Ncols(L) then
		    d := 0;
		else
		    assert Nrows(L) eq Ncols(L);
		    d := Determinant(L);
		end if;
	    else
		if Ncols(L) eq 0 then
		    d := 1;
		else
		    d := GCD(Determinant(L, MULTI));
		end if;

		if d eq 0 then
		    if dump then
			"Check full Hermite";
			hv := GetVerbose("Hermite");
			SetVerbose("Hermite", 1);
		    end if;
		    H := HermiteForm(V);
		    if dump then
			SetVerbose("Hermite", hv);
		    end if;
		    d := &*[H[i, i]: i in [1 .. Ncols(H)]];
		end if;
	    end if;

	    if dump then
		"New determinant:", d;
	    end if;

	    if d eq 0 then
		SetVerbose("Determinant", dv);
		if dump then
		    "Not full rank";
		    "*****";
		end if;
		return [0];
	    end if;
	else
	    while true do
		step +:= 1;
		if dump then
		    "STEP", step;
		end if;

		R := random_subset({1 .. Nrows(V)}, Ncols(V));
		W := MatrixRing(IntegerRing(), Ncols(V)) ! [V[i]: i in R];
		d := get_det(W);
		if dump then
		    "New determinant:", d;
		end if;

		if d ne 0 then
		    break;
		end if;

		if step eq 1 then
		    if dump then
			"Try again";
		    end if;
		    continue;
		end if;

		if dump then
		    "Check full rank";
		end if;

		if step eq 3 and Rank(X) lt c then
		    SetVerbose("Determinant", dv);
		    if dump then
			"Not full rank";
			"*****";
		    end if;
		    return [0];
		end if;
	    end while;
	end if;

	while true do
	    g := GCD(d, ignore);
	    if g eq 1 then
		break;
	    end if;
	    d := d div g;
	end while;

	D := GCD(D, d);
	if D eq 1 then
	    if dump then
		"Now trivial";
	    end if;
	    P := [];
	    break;
	end if;
	P, C := TrialDivision(D, BOUND: Proof := false);
	if dump then
	    "Current factorization:", P, C;
	end if;
    until #C eq 0 and (step gt 1 or P[#P, 1] le 255 and #P le 10);

    SP := &join{Set(PrimeBasis(S[i, i])): i in [1 .. s]};
    P := {t[1]: t in P};

    P := Sort([x: x in SP join P | x notin ignore_primes]);
    if dump then
	SetVerbose("Determinant", dv);
        "Determinants time:", Cputime(T);
	"Possible primes list:", P;
	T := Cputime();
    end if;

    L := [];
    for p in P do
	if dump then
	    "Prime:", p;
	end if;
	assert p notin ignore_primes;
	///////// USE S, not X!!!!!!!!!
	rank := Rank(RMatrixSpace(GF(p), r, c) ! X);
	if dump then
	    printf "Modular rank: %o/%o\n", rank, c;
	end if;
	if rank lt c then
	    Append(~L, p);
	end if;
    end for;

    if dump then
	"Total modular ranks time:", Cputime(T);
	"Final primes:", L;
	"Total ElementaryPrimeDivisors time:", Cputime(ZEIT);
	"*****";
    end if;

    return L;
end function;

/*******************************************************************************
			    IntegralRepresentation
*******************************************************************************/

IntegralRepresentation := function (DD)
    MSQ_TraceFunction("IntegralRepresentation", 2);

    t := Cputime();
    Q := Rationals();
    Z := Integers();
    G := Domain(DD);
    ng := NPCgens(G);
    GLM := Codomain(DD);
    d := Degree(GLM);

    Mats := [DD(G.i) : i in {1 .. ng}];

    if false then
	/*
	if forall{M: M in Mats | CanChangeUniverse(Eltseq(M), Z)} then
	    return DD, 0;
	end if;
	*/

	GZ := IntegralGroup(Mats);
     
	/*
	"GLM:", GLM;
	"GZ:", GZ;
	"G:", G;
	Parent(GZ.1);
	"Im:", [GLM!GZ.i: i in [1 .. Ngens(GZ)]];
	*/

	DDO := hom< G -> GLM | GZ >;

	if MSQVerboseIsSet("MSQ_PrimeSearch", 4) then
		print "   Transform to integral representation:", Cputime(t);
	end if;

	return DDO, 1;
	
    end if;
     
    LS := StandardLattice(d);
    RS := RSpace(Q, d);
    AM := MatrixRing(Z, d);
     
    dump := GetVerbose("User1") gt 10^10;
    if dump then
	"Mats:", Mats;
	"dom:", G;
	"codom:", GLM;
    end if;
     
    IntMat := [CanChangeUniverse(Eltseq(M), Z) : M in Mats];
    flag := false in IntMat;
    DDO := DD;
    tries := 0;
     
    while flag do
	flag := false;
	tries +:= 1;
	MatR := [Mats[i] : i in {1..#Mats} | IntMat[i] eq false];
	    ST := [Eltseq(M[i]): i in {1..Nrows(M)}, M in MatR];
	    S := [t : t in ST | CanChangeUniverse(t, Z) eq false];
	// S := [Eltseq((RS!l)*M) : l in Basis(LS), M in MatR];
	LL := ext<LS| S>;
	    BB := Basis(LL); 
	    BBT := [(RS!bb) : bb in BB | bb notin LS];
	T := {l*M : l in BBT, M in Mats};
	LLe := ext<LL| T>;
     
	if LLe eq LL then
	    BM := LLL(BasisMatrix(LL));
	    BMi := BM^-1;
	    Mats := [BM*M*BMi : M in Mats];
	    DDO := hom< G -> GLM | Mats > ;
	else
	    BM := LLL(BasisMatrix(LLe));
	    BMi := BM^-1;
	    Mats := [BM*M*BMi : M in Mats];
	    IntMat := [CanChangeUniverse(Eltseq(M), Z) : M in Mats];
	    flag := false in IntMat;
	    if flag eq false then
		DDO := hom< G -> GLM | Mats > ;
		if dump then
		    "Good Mats:", Mats;
		end if;
	    end if;
	end if;
    end while;
     
    if MSQVerboseIsSet("MSQ_PrimeSearch", 4) then
	    print "   Transform to integral representation:", Cputime(t);
    end if;
     
    return DDO, tries;
end function;
 
Coboundmats := function(FG, DD, epi)
    MSQ_TraceFunction("Coboundmats", 2);
     
    dump := GetVerbose("User1") gt 0;

    t := Cputime();
    Q := Rationals();
    Z := Integers();
    G := Domain(DD);
    k := Ngens(FG);
    g := Codomain(DD);
    d := Degree(g);
     
    UM := RMatrixSpace(Z, d, d*k);
     
    BQ := [];
    TM := [Transpose(DD(epi(FG.i))) : i in {1..k}];
    for i := 1 to d do
	for j := 1 to k do
	    tt := Eltseq(TM[j][i]);
	    tt[i] -:= 1;
	    Append(~BQ, tt);
	end for;
    end for;
    B := &cat BQ;
     
    U := UM ! B;

    if dump then
	printf "Smith form of %o by %o\n", Nrows(U), Ncols(U);
	ZEIT := Cputime();

	/*
	HERM_FILE := "~allan/mjunk/herm_dump";
	"Dumping to", HERM_FILE;
	PrintFile(HERM_FILE, Sprintf("X := %m;\n", U));
	*/
    end if;

    if true then
	// This is now the BEST way!

	D, Bi, D_rank := SmithForm(U: RightInverse);

	if dump then
	    "Smith time:", Cputime(ZEIT);
	end if;
    else
	D := HermiteForm(U);

	if dump then
	    "Hermite time:", Cputime(ZEIT);
	    printf "Smith form of %o by %o\n", Nrows(U), Ncols(U);
	    ZEIT := Cputime();
	end if;

	D, A, B := SmithForm(D);
	D_rank := Rank(D);
	 
	if dump then
	    "Smith time:", Cputime(ZEIT);
	    printf "##### Get inverse of dim %o; only want rows [%o .. %o]\n",
		Nrows(B), D_rank+1, Nrows(B);
	    ZEIT := Cputime();
	end if;

	Bi := B^-1;

	if dump then
	    "Inverse time:", Cputime(ZEIT);
	end if;
    end if;

    if dump then
	v := Bi[D_rank + 1];
	"Sample inverse row:", {v[j]: j in [1..Ncols(v)]};
    end if;

    if dump then
	"Reduce lattice";
	ZEIT := Cputime();
    end if;

    if true then
	A := RowSubmatrixRange(Bi, D_rank + 1, Nrows(Bi));
	if Nrows(A) gt 0 then
	    LB := LLLBlock(A);
	    rank := Nrows(LB);
	else
	    rank := 0;
	    LB := A;
	end if;
    else
	Bz := [Bi[i] : i in {D_rank+1..Nrows(Bi)}];
	A := &cat[Eltseq(b): b in Bz];
	L := Lattice(d*k, A);
	LB := Basis(L);
	rank := #LB;
    end if;

    if dump then
	"Lattice reduction time:", Cputime(ZEIT);
    end if;
     
    CR := RMatrixSpace(Integers(), d, rank);

    Cobounds := [];
    for i := 1 to k do
	LBS := Submatrix(LB, 1, d*(i-1) + 1, rank, d);
	M := Transpose(LBS);
	Append(~Cobounds, M);
    end for;

    AM := MatrixAlgebra(Integers(), d);
    DDG := [AM ! DD(epi(FG.i)) : i in {1..k}];

    if dump then
	"Compute inverses of dimensions", [Nrows(X): X in DDG];
	ZEIT := Cputime();
    end if;

    function myinv(X)
	S, P, Q := SmithForm(X);
	return Q*P;		// assumes S == 1
    end function;

    DDGi := [myinv(DDG[i]) : i in [1..k]];

    if dump then
	"Inverses time:", Cputime(ZEIT);
    end if;

    CoboundInvs := [-1*DDGi[i] * Cobounds[i]: i in {1..k}];
     
    if MSQVerboseIsSet("MSQ_PrimeSearch", 2) then
	    print "   Setup of the coboundary matrices took:", Cputime(t);
    end if;
    return DDG, DDGi, Cobounds, CoboundInvs, 1;
end function;

RelationsImage := function(r, DDG, DDGi, Cobounds, CoboundInvs)
    MSQ_TraceFunction("RelationsImage", 2);
     
    if Eltseq(r[2]) eq [] then
	El := Eltseq(r[1]);
    else
	El := Eltseq(r[1] * r[2]^-1);
    end if;
     
    if El[1] gt 0 then
	A := DDG[El[1]];
	C := Cobounds[El[1]];
    else
	A := DDGi[-El[1]];
	C := CoboundInvs[-El[1]];
    end if;
     
    for j := 2 to #El do
	e := El[j];
	if e gt 0 then
	    C := C + A*Cobounds[e];
	    A := A*DDG[e];
	else
	    e := -e;
	    C := C + A*CoboundInvs[e];
	    A := A*DDGi[e];
	end if;
    end for;
     
    return C;
 
end function;

FirstCohomPrimes := function (FG, DDQ, epi, PP_known)
MSQ_TraceFunction("FirstCohomPrimes", 1);
 
t := Cputime();
DD := IntegralRepresentation(DDQ);
 
R := Relations(FG);
Z := Integers();
 
DDG, DDGi, Cobounds, CoboundInvs, LIndex := Coboundmats(FG, DD, epi);
 
/*
RC := [];
for r in R do
    RC cat:= Eltseq(RelationsImage(r,DDG,DDGi, Cobounds, CoboundInvs));
end for;
*/
RC := &cat[Eltseq(RelationsImage(r,DDG,DDGi, Cobounds, CoboundInvs)): r in R];

U := RMatrixSpace(Integers(),#R*Nrows(Cobounds[1]), Ncols(Cobounds[1]));
M := U!RC;
PD := ElementaryPrimeDivisors (M, PP_known);
return PD;
 
end function;
 
MSQfindprimes := function(epi, nt)
MSQ_TraceFunction("MSQfindprimes", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * nt : Number of generators on which the rep must not be completely
 *      trivial.
 */

FG := Domain(epi);
 G := Codomain(epi);
 R := Rationals();

if #G eq 1 then
	AI := AbelianQuotientInvariants(FG);
	if 0 in AI then
		return {0};
	end if;
	P := {};
	for q in AI do
		P join:= {p : p in PrimeDivisors(q)};
	end for;
	return P;
end if;

t := Cputime();

if nt ne 0 then
	D := AbsolutelyIrreducibleRepresentationsSchur(G, R, nt : GaloisAction:="Yes",Process:=true,
		Print := MSQGetRepsOption(true));
	F := [* D[1] *];
	E := Remove(D, 1);
	AbsolutelyIrreducibleRepresentationsDelete(~F);
	D := IrreducibleRepresentations(G, R, E :
		Print := MSQGetRepsOption(true)); 
	AbsolutelyIrreducibleRepresentationsDelete(~E);
else
	D := IrreducibleRepresentations(G, R: Print := MSQGetRepsOption(true));
end if;
if MSQVerboseIsSet("MSQ_PrimeSearch", 1) then
	dD := [];
	for i := 1 to #D do
		Append(~dD, Degree(Codomain(D[i])));
	end for;
	print "   Needed", Cputime(t) ,"sec to calculate",
		#D, "rational representations with degrees:";
	print "    ", dD;
end if;

PP_known := {p: p in PCPrimes(G)};
PP := {};
for delta in D do
	t := Cputime();
	S := FirstCohomPrimes(FG, delta, epi, PP_known);
	if S eq [0] then
	//print D, Type(D), delta;
	//AbsolutelyIrreducibleRepresentationsDelete(~D);
		return {0};
	end if;

	if MSQVerboseIsSet("MSQ_PrimeSearch", 2) then
		print "   ", Cputime(t) ,"sec to check", delta;
		if #S ne 0 then
			vprint MSQ_PrimeSearch,8: "   Occuring primes:", S;
		end if;
	elif #S ne 0 then
		vprint MSQ_PrimeSearch,8: "   Occuring primes for :", 
			delta, S;
	end if;

	PP := PP join Seqset(S);

end for;
AbsolutelyIrreducibleRepresentationsDelete(~D);

return PP;
end function;

find_weight_right := function(wseq, limit, offset)
 
if limit eq 0 then
    for k := 2 to #wseq do
        offset +:= Dimension(wseq[k]);
    end for;
    return [offset];
end if;
 
mw := [offset];
pp := wseq[1];
d := 0;
for i := 2 to #wseq do
    if pp^(d+Dimension(wseq[i])) gt limit then
        if d eq 0 then
            Append(~mw, mw[#mw] + Dimension(wseq[i]));
        else
            Append(~mw, mw[#mw] + d);
            d := Dimension(wseq[i]);
        end if;
    else
        d +:= Dimension(wseq[i]);
    end if;
end for;
if d ne 0 then
    Append(~mw, mw[#mw] + d);
end if;
Remove(~mw, 1);
 
return mw;
 
end function;

find_my_weights := function(weights, limit)
MSQ_TraceFunction("find_my_weights", 2);
 
if #weights eq 0 then
    return [];
end if;
 
outq := [];
for i := 1 to #weights do
    NS := weights[i];
    for j := 1 to #NS do
        layer := NS[j];
        for k := 1 to #layer do
            p_layer := layer[k];
            if &+[Integers() | #q: q in outq] eq 0 then
                pd := find_weight_right(p_layer, limit, 0);
            else
		l := #outq;
		repeat
		    last := outq[l];
		    l -:= 1;
		until #last gt 0;
                pd := find_weight_right(p_layer, limit, last[#last]);
            end if;
            Append(~outq, pd);
        end for;
    end for;
end for;
out := &cat outq;
 
/*
out := [];
for i := 1 to #weights do
    NS := weights[i];
    for j := 1 to #NS do
        layer := NS[j];
        for k := 1 to #layer do
            p_layer := layer[k];
            if out eq [] then
                pd := find_weight_right(p_layer, limit, 0);
            else
                pd := find_weight_right(p_layer, limit, out[#out]);
            end if;
            out cat:= pd;
        end for;
    end for;
end for;
*/
 
return out;
end function;
 
RepsListDelete := function(DL)
 
for ip := 1 to #DL do
    D := DL[ip];
    if #D ne 0 then
        AbsolutelyIrreducibleRepresentationsDelete(~D);
    end if;
end for;
 
return true;
end function;
 
RepsListFind := function(DL, p)
 
for ip := 1 to #DL do
    D := DL[ip];
    if #D ne 0 then
        delta := D[1];
        if p eq Characteristic(CoefficientRing(delta[2])) then
            return true, D;
        end if;
    end if;
end for;
 
return false, _;
end function;
 
ModuleListe := function(G, primes, ng, agsflag, ags_last_prime)
MSQ_TraceFunction("ModuleListe", 2);
 
/*
 * create the list of representations interesting for relevant primes.
 * the reps are ordered s.t. those which are nontrivial on the last
 * nilpotent section appear first, their number is stored in DLnum.
 * the lists are modified s.t. the handle is still a module over its
 * splitting field whils the explicit module is given over GF(p).
 * (this part might be obsolete soon)
 */
 
NewPrimes := [];
np := #primes;
DL := [* *];
DLnum := [];

for ip := 1 to np do
    if ags_last_prime eq primes[ip,1] then
        Append(~NewPrimes, primes[ip]);
        Append(~DL, [* *]);
        Append(~DLnum, 0);
        continue;
    end if;
	DLstat := []; /* sequence for statistics */
    R := GF(primes[ip,1]);
    e := primes[ip,2];
    NWi := [ primes[ip,1] ];
    if agsflag eq true and ng ne 0 then
        D := AbsolutelyIrreducibleModulesSchur(G, R, ng : 
                GaloisAction:="Yes",Process := true, MaxDimension := e,
				Print := MSQGetRepsOption(false));
        F := [* D[1] *];
        E := Remove(D, 1);
        D := AbsolutelyIrreducibleModulesSchur(G, R, E : 
                GaloisAction:="Yes",Process := true, MaxDimension := e,
				Print := MSQGetRepsOption(false));
        AbsolutelyIrreducibleRepresentationsDelete(~E);
        Append(~DLnum, #D);
        E := AbsolutelyIrreducibleModulesSchur(G, R, F : 
                GaloisAction:="Yes",Process := true, MaxDimension := e,
				Print := MSQGetRepsOption(false));
        AbsolutelyIrreducibleRepresentationsDelete(~F);
        D cat:= E;
    else
        D := AbsolutelyIrreducibleModulesSchur(G, R : GaloisAction := "Yes", 
                          Process := true, MaxDimension := e,
						  Print := MSQGetRepsOption(false));
        Append(~DLnum, #D);
    end if;
	// get the corresponding Fp-moduls
    DD := IrreducibleModules(G, R, D: Print := MSQGetRepsOption(false)); 
    for i := 1 to #D do
		Append(~DLstat, <Dimension(D[i,2]), 
							Degree(CoefficientRing(D[i,2]))>);
        D[i,2] := DD[i];
    end for;
    if e eq 0 then
        Append(~NewPrimes, primes[ip]);
    end if;
    Append(~DL, D);
	vprint MSQ_RepsCalc, 2: "   ",#DLstat,"modules in characteristic",
		primes[ip,1], "<dim, degree(R)>:\n", "   ", DLstat;
end for;
 
return NewPrimes, DL, DLnum;
end function;
 

MSQallsplit := function(epi, primes, weights, primesearch, agsflag,
		MSQ_PrimeSearchModus, MSQ_ModulCalcModus, MSQ_CollectorModus);

MSQ_TraceFunction("MSQallsplit", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * Primes: sequence of tuples <p_i, e_i>, where e_i is 0 or an
 *         upper bound for the extension size.
 * weights: Sequences describing the ags structure of G.
 * primesearch : gives the upper exponent for new primes, and known primes.
 * agsflag: function is called in ags-context, i.e. we can exclude
 * some modules from the list.
 */

FG := Domain(epi);
 G := Codomain(epi);

if #G eq 1 and MSQ_PrimeSearchModus ge 3 then
	nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
	new_primes := MSQfindprimes(epi, nt);
	if 0 in new_primes then
		return 3, epi, primes, weights, primesearch, [* *];
	end if;
	new_primes := new_primes diff primesearch[2];
	if #new_primes ne 0 then
		if #new_primes ne 0 then
			if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
				print "+++ New primes have been found:", new_primes;
			end if;
			for p in new_primes do
				Append(~primes, <p, primesearch[1]>);
			end for;
			primesearch[2] join:= new_primes;
		end if;
	end if;
else
	new_primes := {};
end if;

np := #primes;
if np eq 1 then
	R := GF(primes[1,1]);
else
	R := Integers();
end if;

t := Cputime();
if #weights eq 0 then
	// VS := MSQLettersplit(G, R: Setup := MSQGetCollectorModus(MSQ_CollectorModus  ));
	VS := MSQLettersplit(G, R: Setup := "Complete");
else
	mw := find_my_weights(weights, 65);
	// VS := MSQLettersplit(G, R, mw: Setup := MSQGetCollectorModus(MSQ_CollectorModus  ));
	VS := MSQLettersplit(G, R, mw: Setup := "Complete");
	lw := weights[#weights]; /* last nilpotent section */
end if;

vprint MSQ_Collector: "   Symbolic collector setup:", Cputime(t), "sec";

NW := [];   /* Sequence for the new weights */
NewPrimes := []; /* sequence of the remaining primes */

nt := 0;
nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);

if agsflag eq true and nt ne 0 and #lw[1] eq 1 then
	ags_last_prime := lw[1,1,1];
	// last nilpotent section was p-group, so this p need no check
else
	ags_last_prime := -1;
end if;

NewPrimes, DL, DLnum := ModuleListe(G,primes,nt,agsflag,ags_last_prime);

for ip := 1 to np do
	D := DL[ip];
	if #D eq 0 then
		continue;
	end if;

	e := primes[ip,2];

	vprint MSQ_RepsCheck,2: "   Check split extensions for",
				#D, "modules for prime", primes[ip,1];

	NWi := [* primes[ip,1] *];

    for dn := #D to 1 by -1 do
        delta := D[dn];
		/* check that delta is nontrivial on last nilpotent section */
		B := Basis(delta[2]);
		Fp_dim := #B * Degree(CoefficientRing(delta[2]));
		if e gt 0 and e lt Fp_dim then
			continue;
		end if;

		t := Cputime();
		dd, new_epi := MSQsplit(VS, epi, delta);
		ndd := Integers()!(dd / Fp_dim);

		if MSQVerboseIsSet("MSQ_RepsCheck",1) then
			if ndd eq 0 then
				print "   Needed", Cputime(t) ,"sec to check ",delta[2];
			else
				print "   Needed", Cputime(t) ,"sec to check ",delta[2],
					"found multiplicity", ndd;
			end if;
		elif ndd ne 0 then
			vprint MSQ_Messages: 
				"   found multiplicity", ndd, "for module", delta[2];
		end if;

		if dd ne 0 then /* step was successfull */
            for i := 1 to ndd do
                Append(~NWi, delta[2] );
            end for;
			epi := new_epi;
			if e gt 0 then
				e -:= dd;
				if e le 0 then
					break;
				end if;
			end if;

			if MSQ_PrimeSearchModus eq 5 then
				new_primes join:= MSQfindprimes(epi, dd);
				if 0 in new_primes then
					if e gt 0 then
						Append(~NewPrimes, <primes[ip,1], e>);
					end if;
					if #NWi gt 1 then
						Append(~NW, NWi);
						Append(~weights, [NW]);
					end if;
					return 3, epi, NewPrimes, weights, primesearch, DL;
				end if;
			end if;

		end if;
	end for;
	if e gt 0 then
		Append(~NewPrimes, <primes[ip,1], e>);
	end if;
	if #NWi gt 1 then
		Append(~NW, NWi);
	end if;
end for;
ttt := LetterVarDelete(VS);

if #NW gt 0 then
	Append(~weights, [NW]);
	if MSQ_PrimeSearchModus eq 4 then
		nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
		new_primes join:= MSQfindprimes(epi,nt);
		if 0 in new_primes then
			return 3, epi, NewPrimes, weights, primesearch, DL;
		end if;
	end if;
	if MSQ_PrimeSearchModus gt 3 then
		new_primes := new_primes diff primesearch[2];
		if #new_primes ne 0 then
			if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
				print " New primes has been found:", new_primes;
			end if;
			for p in new_primes do
				Append(~NewPrimes, <p, primesearch[1]>);
			end for;
			primesearch[2] join:= new_primes;
		end if;
	end if;

	return 1, epi, NewPrimes, weights, primesearch, DL;
else	
	return 0, epi, NewPrimes, weights, primesearch, DL;
end if;

end function;

checktrivial := function(G, weights, primerest)
MSQ_TraceFunction("checktrivial", 2);
 
/*
 * returns a sequence of pairs [i,i] or [i,j] for which one can
 * require that the tail at the relation G.i^p resp. G.i^G.j
 * is trivial.
 */

PO := PCPrimes(G);
T1 := [];
 
/* First step: take all pairs of generators where both indices do not
 * occur in PO
 */
Ind := {i : i in [1..#PO] | PO[i] notin primerest};
if #Ind eq 0 then
    T1 := [];
else
    T1 := [[a,b] : a in Ind, b in Ind | a ge b];
end if;
 
NS := weights[#weights]; /* last section, count gens belonging to it */
ng := 0;
nd := 0;
ld := [0];  /* dimension of the layers */
for NSL in NS do /* loop on the layers in the descending series */
    for NSLP in NSL do /* loop over the primes in layers */
        for i := 2 to #NSLP do /* loop over module dimensions */
            ng +:= Dimension(NSLP[i]);
        end for;
    end for;
    Append(~ld, ng-nd);
    nd := ng;
end for;
 
Ind := {#PO- ng+1..#PO};
ldw := [0 : i in {1..#PO- ng}];
wt := 1;
for i := 2 to #ld do
    ttt := [wt : j in {1..ld[i]}];
    ldw := ldw cat ttt;
    wt +:= 1;
end for;
 
/* Second step: look at the actual nilpotent section, take all pairs of
 * generators with different indices.
 * i.e. use the fact that a nilpotent group is the direct product of
 * p-groups.
 */
 
T2 := [[a,b] : a in Ind, b in Ind | a ge b and PO[a] ne PO[b]];
 
/* Third step: look at each p-group in the nilpotent section and
 * use the weights given by the lower descending series.
 * collect those pairs where the sum of the weights is bigger then
 * the expected weight of the new layer.
 */
T3 := [[a,b] : a in Ind, b in Ind | a gt b and PO[a] eq PO[b] and
                                    ldw[a]+ldw[b] gt wt ];
 
/*
 * fourth step: only need reps which are trivial on the last nilpotent
 * section, add this to the group operation.
 */
if #weights gt 1 then
    a := #PO+1;
    T4 := [[a,b] : b in {a-ng..a-1}];
else
    T4 := [];
end if;
TC := T1 cat T2 cat T3 cat T4;
return TC, ng;
end function;
 
elemabel_layer := function(G, weights, split_flag)
MSQ_TraceFunction("elemabel_layer", 2);
 
/*
 * returns a sequence of pairs [i,j] or [i,j] (as above) in order
 * to require that the module together with the last layer is still
 * elementary abelian.
 */
 
PO := PCPrimes(G);
 
NS := weights[#weights]; /* last section, count gens belonging to it */
ng := 0;
nd := 0;
ld := [0];  /* dimension of the layers */
for NSL in NS do /* loop on the layers in the descending series */
    for NSLP in NSL do /* loop over the primes in layers */
        for i := 2 to #NSLP do /* loop over module dimensions */
            ng +:= Dimension(NSLP[i]);
        end for;
    end for;
    Append(~ld, ng-nd);
    nd := ng;
end for;
 
Ind := {#PO- ld[#ld]+1..#PO};
   
T1 := [[a,b] : a in Ind, b in Ind | a ge b ];
if split_flag eq false then
    T2 := [];
else
    /* force the extension to split with the quotient with the last
       nilpotent section. */
    Ind := {1 .. #PO-ng};
    T2 := [[a,b] : a in Ind, b in Ind | a ge b ];
end if;
 
return T1 cat T2;
end function;


MSQallnonsplit := function(epi, primes, weights, primesearch, firstflag,
		DL,MSQ_PrimeSearchModus,MSQ_ModulCalcModus,MSQ_CollectorModus)

MSQ_TraceFunction("MSQallnonsplit", 1);

/* epi: epimorphism FG --> G, FG and G are read from it.
 * Primes: sequence of tuples <p_i, e_i>, where e_i is 0 or an
 *         upper bound for the extension size.
 * weights: Sequences describing the ags structure of G.
 * firstflag: if true, only extension are checked which are elementary
 *            abelian with the last layer.
 */

FG := Domain(epi);
 G := Codomain(epi);

np := #primes;

nnf := #weights;
if nnf le 0 then
	return 0, _,_,_,_;
end if;

lastsection := weights[nnf];               /* last nilpotent section */
lastlayer   := lastsection[#lastsection];  /* head or layer */
primerest   := {l[1] : l in lastlayer};    /* remaining primes for this sec */
if #primerest eq 1 then
	R := GF(Setseq(primerest)[1]);
else
	R := Integers();
end if;
new_primes := {};

trivseq, ng := checktrivial(G, weights, primerest);
if firstflag eq true then
    if #lastsection eq 1 then
        trivelemseq := elemabel_layer(G, weights, true);
    else
        trivelemseq := elemabel_layer(G, weights, false);
    end if;
    trivseq cat:= trivelemseq;
end if;

t := Cputime();
mw := find_my_weights(weights, 65);
VS := MSQLetternonsplit(G, R, trivseq, mw: 
		Setup := "Complete");
		// Setup := MSQGetCollectorModus(MSQ_CollectorModus));
vprint MSQ_Collector: 
		"   Symbolic collector setup:", Cputime(t), "sec";

NL := [];        /* Sequence for the new layer */
NewPrimes := []; /* sequence of the remaining primes */

for ip := 1 to np do
	pp := primes[ip,1];
	if pp notin primerest then
		Append(~NewPrimes, primes[ip]);
		continue;
	end if;

    flag, D := RepsListFind (DL, pp);
	vprint MSQ_RepsCheck, 2:
		"   Check nonsplit extensions for",#D, "modules for prime", pp;

	R := GF(pp);
	e := primes[ip,2];
	old_e := e;
	NWi := [* pp *];

	for delta in D do
		dB := #Basis(delta[2]) * Degree(CoefficientRing(delta[2]));
		if e gt 0 and e lt dB then
			continue;
		end if;

		t := Cputime();
		dd, new_epi := MSQnonsplit(VS, epi, delta);
		ndd := Integers()!(dd / dB);

		if MSQVerboseIsSet("MSQ_RepsCheck",1) then
			if ndd ne 0 and IsVerbose("MSQ_Messages") then
				print "   Needed", Cputime(t) ,"sec to check ", delta[2],
					"    found multiplicity", ndd;
			else
				print "   Needed", Cputime(t) ,"sec to check ", delta[2];
			end if;
		else
			if ndd ne 0 then
				vprint MSQ_Messages: 
					"   found multiplicity",ndd,"for module",delta[2];
			end if;
		end if;

		if dd ne 0 then /* step was successfull */
            for i := 1 to ndd do
                Append(~NWi, delta[2]);
            end for;
			epi := new_epi;
			new_epi := 0;
			if e gt 0 then
				e -:= dd;
				if e le 0 then
					break;
				end if;
			end if;
			if MSQ_PrimeSearchModus eq 5 then
				new_primes join:= MSQfindprimes(epi,dd);
				if 0 in new_primes then
					if old_e eq 0 then
						Append(~NewPrimes, <pp, old_e>);
					elif e gt 0 then
						Append(~NewPrimes, <pp, e>);
					end if;
					if #NWi gt 1 then
						Append(~NL, NWi);
						if firstflag eq true then
							k := #weights[nnf];
							weights[nnf,k] cat:= NL;
						else
							Append(~weights[nnf], NL);
						end if;
					end if;
					return 3, epi, NewPrimes, weights, primesearch;
				end if;
			end if;
		end if;
	end for;
	if old_e eq 0 then
		Append(~NewPrimes, <pp, old_e>);
	elif e gt 0 then
		Append(~NewPrimes, <pp, e>);
	end if;
	if #NWi gt 1 then
		Append(~NL, NWi);
	end if;
end for;
ttt := LetterVarDelete(VS);

if #NL gt 0 then
    if firstflag eq true then
        k := #weights[nnf];
        weights[nnf,k] cat:= NL;
    else
        Append(~weights[nnf], NL);
    end if;
	if MSQ_PrimeSearchModus eq 4 then
		nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
		new_primes join:= MSQfindprimes(epi,nt);
		if 0 in new_primes then
			return 3, epi, NewPrimes, weights, primesearch;
		end if;
	end if;
	if MSQ_PrimeSearchModus gt 3 then
		new_primes := new_primes diff primesearch[2];
		if #new_primes ne 0 then
			if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
				print "    New primes has been found:", new_primes;
			end if;
			for p in new_primes do
				Append(~NewPrimes, <p, primesearch[1]>);
			end for;
		primesearch[2] join:= new_primes;
		end if;
	end if;
	return 1, epi, NewPrimes, weights, primesearch;
else	
	return 0, _ , _ , _,_;
end if;

end function;

FindTensorConstituents := function(LL, FL, DD, MSQ_ModulCalcModus )

MSQ_TraceFunction("FindTensorConstituents", 2);
 
if MSQ_ModulCalcModus eq 2 then // 'strict' module search
	CL := [* *];
else
	CL := LL;
end if;

for i := 1 to #LL do
    M := LL[i];
    CI := [];
    if #FL eq 0 then
        for j := i to #LL do
            N := LL[j];
            Append(~CI, TensorProduct(M, N));
        end for;
    else
        for j := 1 to #FL do
            N := FL[j];
            Append(~CI, TensorProduct(M, N));
        end for;
    end if;
    for M in CI do
        C := Constituents(M);
        for c in C do
            flag := false;
            for k := 1 to #CL do
                flag := IsIsomorphic(c, CL[k]);
                if flag eq true then
                    break;
                end if;
            end for;
            if flag eq false then
                Append(~CL, c);
            end if;
        end for;
    end for;
end for;
 
if #CL eq #DD then
    DDO := DD;
else
    DDO := [* *];
    for i := 1 to #DD do
        D := DD[i,2];
        for j := 1 to #CL do
            if IsIsomorphic(CL[j], D) then
                Append(~DDO, DD[i]);
                Remove(~CL, j);
                break;
            end if;
        end for;
    end for;
end if;
 
return DDO;
end function;

ExtractPossibleModules := function(weights, DL, MSQ_ModulCalcModus)
MSQ_TraceFunction("ExtractPossibleModules", 2);
 
/*
 * realization of Charles' idea: create a sublist of DL of modules 
 * which are constituents of the tensor products of modules in the 
 * first and the last layer of the nilpotent section.
 */
 
NS := weights[#weights];
LL := NS[#NS]; /* last layer == bottom */
FL := NS[  1]; /* first layer == head */
t := Cputime();
 
DLout := [* *];
 
primes := {l[1] : l in LL}; // Primes still relevant
for p in primes do // main loop
    ff, DT := RepsListFind(DL, p);
    if #DT eq 1 or MSQ_ModulCalcModus eq 0 then
        Append(~DLout, DT);
        continue;
    end if;
    LLmodules := [* *];
    for ll in LL do
        if ll[1] ne p then
            continue;
        end if;
        for i := 2 to #ll do
            M := ll[i];
            flag := true;
            for j := 1 to #LLmodules do
                if IsIsomorphic(M, LLmodules[j]) then
                    flag := false;
                    break;
                end if;
            end for;
            if flag eq true then
                Append(~LLmodules, M);
            end if;
        end for;
    end for;
    FLmodules := [* *];
    if #NS ne 1 then
        for ll in FL do
            if ll[1] ne p then
                continue;
            end if;
            for i := 2 to #ll do
                M := ll[i];
                flag := true;
                for j := 1 to #FLmodules do
                    if IsIsomorphic(M, FLmodules[j]) then
                        flag := false;
                        break;
                    end if;
                end for;
                if flag eq true then
                    Append(~FLmodules, M);
                end if;
            end for;
        end for;
    end if;
    DLP := FindTensorConstituents(LLmodules, FLmodules, DT, MSQ_ModulCalcModus);
       vprint MSQ_RepsCalc: "   Compare:", #DLP, "Modules out of",
			#DT, "are candidates," , Cputime(t), "secs to check";
    Append(~DLout, DLP);
end for;
 
return DLout;
end function;

MSQnilpotent := function(epi,primes,weights,primesearch,
	MSQ_PrimeSearchModus, MSQ_ModulCalcModus, MSQ_CollectorModus : 
	LCSbound := 0)
MSQ_TraceFunction("MSQnilpotent", 1);

flag, epit, primest, weightst, primesearcht, DL := 
	MSQallsplit(epi,primes,weights, primesearch, true,
	MSQ_PrimeSearchModus, MSQ_ModulCalcModus, MSQ_CollectorModus  );

if flag eq 0 then
	ttt := RepsListDelete(DL);
	return 0, _, _, _, _;
elif flag eq 3 then
	ttt := RepsListDelete(DL);
	return 3, epit, [], weightst, primesearch;
elif primest eq [] then
	ttt := RepsListDelete(DL);
	vprint MSQ_Messages: ">>>Found soluble quotient of size", 
		#Codomain(epit);
	return 1, epit, primest, weightst, primesearch;
elif LCSbound eq 1 then
	ttt := RepsListDelete(DL);
	vprint MSQ_Messages: 
		"<<<Algorithm reached limit given for LDS length."; 
	return 2, epit, [], weightst, primesearch;
end if;

vprint MSQ_Messages: ">>>Found soluble quotient of size", 
	#Codomain(epit);

while flag eq 1 do
	epi := epit;
	primes := primest;
	weights := weightst;
	primesearch := primesearcht;
    DLT := ExtractPossibleModules(weights, DL, MSQ_ModulCalcModus);

	flag, epit, primest, weightst, primesearcht := 
		MSQallnonsplit(epi, primes, weights, primesearch, false, DLT,
		MSQ_PrimeSearchModus, MSQ_ModulCalcModus, MSQ_CollectorModus);
	if flag ne 0 then
		vprint MSQ_Messages: 
			">>>Found soluble quotient of size", #Codomain(epit);
		if flag eq 3 then
			ttt := RepsListDelete(DL);
			return 3, epit, primest, weightst, primesearch;
		elif primest eq [] then
			ttt := RepsListDelete(DL);
			return 1, epit, primest, weightst, primesearch;
		elif LCSbound eq #weightst[#weightst]  then
			vprint MSQ_Messages: 
				"<<<Algorithm reached limit given for LDS length."; 
			ttt := RepsListDelete(DL);
			return 2, epit, primest, weightst, primesearch;
		end if;
	end if;
end while;

tt := RepsListDelete(DL);
if MSQ_PrimeSearchModus eq 3 then
	nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
	new_primes := MSQfindprimes(epi, nt);
	if 0 in new_primes then
		return 3, epi, primes, weights, primesearch;
	end if;
	new_primes := new_primes diff primesearch[2];
	if #new_primes ne 0 then
		if MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
			print "+++ New primes have been found:", new_primes;
		end if;
		for p in new_primes do
			Append(~primes, <p, primesearch[1]>);
		end for;
		primesearch[2] join:= new_primes;
	end if;
end if;
return 1, epi, primes, weights, primesearch;

end function;

MSQall_ags := function(epi,T,weights, MSQ_PrimeSearchModus, 
		MSQ_ModulCalcModus, MSQ_CollectorModus: 
		NilpotencyClass:=0, LCSlimit:=0)

MSQ_TraceFunction("MSQall_ags", 1);

/* calculating the quotient using a ags system.
 * The first entry in primesearch gives a limit on the exponent for new primes,
 * the second entry is the set of known primes.
 */
if Type(LCSlimit) eq RngIntElt then
	bound := LCSlimit;
elif Type(LCSlimit) eq SeqEnum and #LCSlimit gt 0 then
	bound := LCSlimit[1];
else
	print"MSQ Error: Wrong argument type for parameter LCSlimit";
	return 0, _, _, _;
end if;

Null_T := {t : t in T | t[1] eq 0};
if #Null_T gt 1 then
	print "MSQ Error: specification of primes is not unique:", Null_T;
	return 0,_,_,_;
elif #Null_T eq 0 then
	primes := T;
	first_primes := primes;
	primesearch := <0, {Integers() | t[1]: t in T}>;
else
	primes := [t : t in T | t[1] ne 0];
	first_primes := {t[1] : t in primes};
	a := Random(Null_T); // just to get the elt.
	primesearch := <a[2], {Integers() | t[1]: t in primes}>;
end if;

flag := 1;
epit := epi;
primest := primes;
weightst := weights;
primesearcht := primesearch;

while flag eq 1 do

	epi := epit;
	primes := primest;
	weights := weightst;
	primesearch := primesearcht;

	lw := #weights;
	if Type(LCSlimit) eq RngIntElt then
		bound := LCSlimit;
	elif #LCSlimit gt lw then
		bound := LCSlimit[lw+1];
	else
		bound := 0;
	end if;
	flag,epit,primest,weightst, primesearcht := 
		MSQnilpotent(epi, primes, weights, primesearch, 
			MSQ_PrimeSearchModus, MSQ_ModulCalcModus  ,
			MSQ_CollectorModus  : LCSbound := bound);

	case flag:
	when 0:
		if MSQ_PrimeSearchModus in {1,2} then
			nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
			new_primes := MSQfindprimes(epi,nt);
			if 0 in new_primes then
				print "<<<Found free abelian module in final primesearch.";
				new_primes := new_primes diff primesearch[2];
				if #new_primes ne 0 then
					print "+++Found new relevant primes in final primesearch:",
						new_primes;
					for p in new_primes do
						Append(~primes, <p, primesearch[1]>);
					end for;
				end if;
				return 3, epi, primes, weights;
			end if;
			new_primes := new_primes diff primesearch[2];
			if #new_primes ne 0 then
				print"+++New primes found in the final prime search:", 
						new_primes;
				for p in new_primes do
					Append(~primes, <p, primesearch[1]>);
				end for;
				primesearch[2] join:= new_primes;
				if MSQ_PrimeSearchModus eq 1 then
					return 1, epi, primes, weights;
				else
					flag := 1;
					epit := epi;
					primest := primes;
					weightst := weights;
					primesearcht := primesearch;
				end if;
			else
						return 1, epi, primes, weights;
			end if;
		else
			return 1, epi, primes, weights;
		end if;
	when 1:
		vprint MSQ_Messages:
			">>> Nilpotent section completed, size of Quotient:", 
				#Codomain(epit);
		if NilpotencyClass gt 0 and #weightst ge NilpotencyClass then
			vprint MSQ_Messages:
				"<<<Algorithm reached limit given on Nilpotency Class";
			return 2, epit, primest, weightst;
		elif bound eq #weightst[#weightst]  then
			return 2, epit, [], weightst;
		end if;

		if primest eq [] and Null_T eq {} then
			if MSQ_PrimeSearchModus in {1,2} then
				nt := find_nontrivial_length(weights, MSQ_PrimeSearchModus);
				new_primes := MSQfindprimes(epi, nt);
				if 0 in new_primes then
					if IsVerbose("MSQ_Messages") or
						MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
						print "<<<Found free abelian module in the final prime search.";
						end if;
					new_primes := new_primes diff primesearch[2];
					if #new_primes ne 1 then
						if IsVerbose("MSQ_Messages") or
							MSQVerboseIsSet("MSQ_PrimeSearch", 8)
							then
						print "+++New primes found in the final prime search:", 
							new_primes;
						end if;
					end if;
					for p in new_primes do
						Append(~primest, <p, primesearch[1]>);
					end for;
					return 3, epit, primest, weightst;
				end if;
				new_primes := new_primes diff primesearch[2];
				if #new_primes ne 0 then
					if IsVerbose("MSQ_Messages") or
						MSQVerboseIsSet("MSQ_PrimeSearch", 8) then
						print "+++New primes found in the final prime search:", 
							new_primes;
					end if;
					for p in new_primes do
						Append(~primest, <p, primesearch[1]>);
					end for;
					primesearch[2] join:= new_primes;
					if MSQ_PrimeSearchModus eq 1 then
						return 1, epit, primest, weightst;
					end if;
				end if;
			else
						return 1, epit, primest, weightst;
			end if;
		end if;

	when 2:
		return 2, epit, primest, weightst;
	when 3:
		return 3, epit, primest, weightst;
	end case;
end while;
 
end function;

MSQ_inner := function(FG, LL: NilpotencyClass := 0, LCSlimit := 0, 
	Print := -1, MSQ_PrimeSearchModus := 0, MSQ_ModulCalcModus := 0,
	MSQ_CollectorModus := 0)

MSQsetVerboseForOption(~Print);

weights := [];
G := PCGroup(CyclicGroup(1));
epit := hom< FG -> G | [Id(G): g in Generators(FG)]>;

if Type(LL) ne List then
	L := LL;
else 
	L := LL[1];
end if;

if Type(L) eq RngIntElt then
	if L eq 0 then
		T := [<0,0>];
		if MSQ_PrimeSearchModus eq 0 then
			MSQ_PrimeSearchModus := 3;
		end if;
		if Type(LL) ne List then
			NpClass := NilpotencyClass; 
		elif #LL eq 1 then
			NpClass := NilpotencyClass; 
		else
			NpClass := 1;
		end if;
	else
		T := Factorization(L);
		NpClass := NilpotencyClass; 
	end if;
elif Type(L) eq SetEnum then
		T := [<l, 0> : l in L];
		NpClass := NilpotencyClass; 
		if 0 in L and MSQ_PrimeSearchModus eq 0 then
			MSQ_PrimeSearchModus := 3;
		end if;
elif Type(L) eq SeqEnum or Type(L) eq RngIntEltFact then
	T := L;
	NpClass := NilpotencyClass; 
	if <0,0> in L and MSQ_PrimeSearchModus eq 0 then
		MSQ_PrimeSearchModus := 3;
	end if;
end if;

flag, epi, primes, weights := MSQall_ags(epit, T, weights, 
			MSQ_PrimeSearchModus,MSQ_ModulCalcModus, MSQ_CollectorModus:
			NilpotencyClass := NpClass, LCSlimit := LCSlimit);

comm := Message_MSQ_return_comment(flag);

if flag ne 1 or Type(LL) ne List or #LL eq 1 then
   return Codomain(epi), epi, weights, comm;
end if;

for i := 2 to #LL do
	L := LL[i];
	if Type(L) eq RngIntElt then
		if L eq 0 then
			T := [<0,0>];
			if MSQ_PrimeSearchModus eq 0 then
				MSQ_PrimeSearchModus := 3;
			end if;
			if i eq #LL then
				NpClass := NilpotencyClass; 
			else
				NpClass := #weights+1;
			end if;
		else
			T := Factorization(L);
			NpClass := NilpotencyClass; 
		end if;
	elif Type(L) eq SetEnum then
		T := [<l, 0> : l in L];
		if i eq #LL then
			NpClass := NilpotencyClass; 
		else
			NpClass := #weights+1;
		end if;
		if 0 in L and MSQ_PrimeSearchModus eq 0 then
			MSQ_PrimeSearchModus := 3;
		end if;
	elif Type(L) eq SeqEnum or Type(L) eq RngIntEltFact then
		T := L;
		if i eq #LL then
			NpClass := NilpotencyClass; 
		else
			NpClass := #weights+1;
		end if;
		if <0,0> in L and MSQ_PrimeSearchModus eq 0 then
			MSQ_PrimeSearchModus := 3;
		end if;
	end if;

	flag, epi, primes, weights := MSQall_ags(epi, T, weights,
		MSQ_PrimeSearchModus, MSQ_ModulCalcModus, MSQ_CollectorModus: 
		NilpotencyClass := NpClass, LCSlimit := LCSlimit); 
	if i lt #LL and flag eq false then 
		vprint MSQ_Messages: 
			"MSQ Warning: Specification in", i,
			"-th step does not lead to bigger quotient.";
	end if;
end for;

comm := Message_MSQ_return_comment(flag);

return Codomain(epi), epi, weights, comm;
end function;

MSQ_check := function(epi)
 
FG := Domain(epi);
R := {r[1] * r[2]^-1: r in Relations(FG)};
S := {epi(r) : r in R};
 
if #S ne 1 then
    return false;
end if;
 
G := Codomain(epi);
GS := sub< G | {epi(f) : f in Generators(FG)}>;
 
if GS ne G then
    return false;
else
    return true;
end if;
 
end function;

/*
These SolubleQuotient functions are completely duplicated below as
SolvableQuotient -- if you change one, fix the other.
*/
 
intrinsic SolubleQuotient(F::GrpFP : NilpotencyClass := 0, LCSlimit := 0, 
	Print := -1, MSQ_PrimeSearchModus := 0, MSQ_ModulCalcModus := 0,
	MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute largest possible soluble quotient of F.  }

    return MSQ_inner(F, 0 : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;

intrinsic SolubleQuotient(F::GrpFP, n::RngIntElt : NilpotencyClass := 0,
        LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F with order n. If n is 0, then compute
largest possible soluble quotient.  }

    return MSQ_inner(F, n : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;
 
intrinsic SolubleQuotient(F::GrpFP, P::SetEnum : NilpotencyClass := 0,
        LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. P is a set of primes and the algorithm
calculates the largest quotient such that the order has prime divisors
only in P.  }

    return MSQ_inner(F, P : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;
 
/*

intrinsic SolubleQuotient(F::GrpFP, S::SeqEnum : NilpotencyClass := 0,
	LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

    return MSQ_inner(F, S : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;

*/
 
intrinsic SolvableQuotient(F::GrpFP : NilpotencyClass := 0, LCSlimit := 0, 
	Print := -1, MSQ_PrimeSearchModus := 0, MSQ_ModulCalcModus := 0,
	MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute largest possible soluble quotient of F.  }
    return MSQ_inner(F, 0 : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;

intrinsic SolvableQuotient(F::GrpFP, n::RngIntElt : NilpotencyClass := 0,
	LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F with order n. If n is 0, then compute
largest possible soluble quotient.  }

    return MSQ_inner(F, n : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;
 
intrinsic SolvableQuotient(F::GrpFP, P::SetEnum : NilpotencyClass := 0,
	LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. P is a set of primes and the algorithm
calculates the largest quotient such that the order has prime divisors
only in P.  }

    return MSQ_inner(F, P : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;
 
intrinsic SolvableQuotient(F::GrpFP, S::SeqEnum : NilpotencyClass := 0,
	LCSlimit := 0, Print := -1, MSQ_PrimeSearchModus := 0,
	MSQ_ModulCalcModus := 0, MSQ_CollectorModus := 0)
        -> GrpPC, Map, SeqEnum, MonStgElt
{ Compute a soluble quotient of F. S is a sequence of tuples <p, e>, with p
a prime  or 0 and e a non-negative integer. The order of the quotient will be
a divisor of &* [ p^e : <p, e> in S] if all p's and e's are positive. See
handbook for further details. }

    return MSQ_inner(F, S : NilpotencyClass := NilpotencyClass, 
	LCSlimit := LCSlimit, Print := Print, 
	MSQ_PrimeSearchModus := MSQ_PrimeSearchModus, 
	MSQ_ModulCalcModus := MSQ_ModulCalcModus,
	MSQ_CollectorModus := MSQ_CollectorModus); 

end intrinsic;
