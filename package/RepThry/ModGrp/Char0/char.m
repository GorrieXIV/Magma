freeze;

/*******************************************************************************
				Verbose
*******************************************************************************/

declare verbose ZRepsKnapsack, 2;

/*******************************************************************************
				Defines
*******************************************************************************/

declare attributes ModRng: Character;
declare attributes ModGrp: Character;

Z := IntegerRing();
Q := RationalField();

/*******************************************************************************
				Knapsack
*******************************************************************************/

/*
function OldMultiKnapsackSolutions(QQ, S)
    vprint ZRepsKnapsack, 2: "Knap QQ:", QQ;
    vprint ZRepsKnapsack, 2: "Knap S:", S;

    time0 := Cputime();

    n := #QQ;
    k := #QQ[1];

    for j := 1 to k do
	if S[j] ge 0 and forall{i: i in [1 .. n] | QQ[i, j] ge 0} then
	    while n gt 0 and QQ[n, j] gt S[j] do
		//"Prune", QQ[n];
		Prune(~QQ);
		n -:= 1;
	    end while;
	end if;
    end for;

    //vprint ZRepsKnapsack, 2: "Prune QQ to:", QQ;

if 0 eq 1 then
    for j := 1 to k do
	if S[k] ge 0 and forall{i: i in [1 .. n] | QQ[i, j] ge 0} then
	    while n gt 1 and
		QQ[n] eq QQ[n - 1] and
		QQ[n, j] gt S[j]
		2*QQ[n, j] gt S[j]
	    do
		//"Prune", QQ[n];
		Prune(~QQ);
		n -:= 1;
	    end while;
	end if;
    end for;
"Again QQ:", QQ;
end if;

    if #QQ eq 0 then
	return [];
    end if;

    X := RMatrixSpace(IntegerRing(), n + 1, n + k + 1) ! 0;
    for i := 1 to n do
        X[i][i] := 2; 
        for j := 1 to k do 
            X[i][n + j] := n * QQ[i, j];
        end for;
        X[n + 1][i] := 1;
    end for; 
    for j := 1 to k do
        X[n + 1][n + j] := n * S[j];
    end for;
    X[n + 1][n + k + 1] := 1;
    L := Lattice(X);

    M := n + 1;
//"L:", L;
//"M:", M;
    S := ShortVectors(L, M, M);
//"#S:", #S;
    sol := [
        [i: i in [1 .. n] | v[i] ne v[n + k + 1]]: t in S |
            forall{i: i in [1 .. n] cat [n + k + 1] | Abs(v[i]) eq 1} and
            forall{i: i in [n + 1 .. n + k] | v[i] eq 0}
                where v is t[1]
    ];

    Sort(~sol, func<x, y | #x - #y>);

    vprint ZRepsKnapsack, 2: "Knap sol:", sol;
    vprint ZRepsKnapsack, 2: "Knap sol time:", Cputime(time0);

    return sol;
end function;
*/

function do_knap(X, count, n, S, Max)
    R := [];
    while n gt 0 do
/*
"do_knap n:", n;
"do_knap S:", S;
"do_knap R:", R;
*/
	d := S[1];
	if d eq 0 then
	    if IsZero(S) then
		Append(~R, []);
		// if Max gt 0 and #R ge Max then return R; end if;
	    end if;
	    return R;
	end if;
	while n gt 0 and X[n, 1] gt d do
	    n -:= 1;
	end while;
	while n gt 0 and X[n, 1] eq d do
	    if X[n] eq S then
		Append(~R, [<n, 1>]);
		if Max gt 0 and #R ge Max then return R; end if;
	    end if;
	    n -:= 1;
	end while;
	if n eq 0 then
	    break;
	end if;
	T := X[n];
	e := T[1];
	m := Min(d div e, count[n]);
// "m:", m;
	if n eq 1 then
	    if m*T eq S then
		Append(~R, [<1, m>]);
	    end if;
	    break;
	end if;
	    
	n1 := n - 1;
	SS := S;
	for j := 1 to m do
	    SS -:= T;
// IndentPush();
	    RR := do_knap(X, count, n1, SS, Max);
// IndentPop();
	    for r in RR do
		Append(~R, Append(r, <n, j>));
		if Max gt 0 and #R ge Max then return R; end if;
	    end for;
	end for;
	n -:= 1;
    end while;
// "do_knap final R:", R;
    return R;
end function;

/*
function NewMultiKnapsackSolutions(QQ, S: Max := 0, SingleRep := false)

    card := #Set(QQ);
    I := {@ @};
    ind := [{Z|}: i in [1 .. card]];

    for qi := 1 to #QQ do
	q := QQ[qi];
	Include(~I, q);
	i := Index(I, q);
	Include(~ind[i], qi);
    end for;

    count := [Min(#ind[i], Floor(S[1]/I[i, 1])): i in [1 .. card]];
*/

function NewMultiKnapsackSolutions(
    S, I, ind, count: Max := 0, SingleRep := false, Multiples := false
)

// "NewMultiKnapsackSolutions I:", I; "ind:", ind;
// "S:", S; "count:", count;

    X := Matrix(Z, [v: v in I]);
    RR := do_knap(X, count, #I, Vector(Z, S), Max);

//"RR:", RR;
    if Multiples then
	Sort(~RR, func<x, y | #x - #y>);
	return RR;
    end if;

    R := [];
    for v in RR do
	CO := [];
	//for j in Support(v) do
	//c := v[j];
	for t in v do
	    j, c := Explode(t);
	    assert c le #ind[j];
	    Append(~CO, Subsets(ind[j], c));
	end for;
	C := CartesianProduct(CO);
//C;
	for t in C do
//"t:", t;
	    Append(~R, Sort(Setseq(&join{s: s in t})));
	    if SingleRep then
		break;
	    end if;
	    if Max gt 0 and #R eq Max then
		break t;
	    end if;
	end for;
    end for;
    Sort(~R, func<x, y | #x - #y>);
    return R;
end function;

function MultiKnapsackSolutionsMultiplesPos(
    QQ, S: Max := 0, MultiplesBounds := 0
)

    k := #QQ;
    if MultiplesBounds cmpne 0 then
	assert #MultiplesBounds eq k;
    end if;

    while k gt 0 and QQ[k, 1] gt S[1] do
	Prune(~QQ);
	if MultiplesBounds cmpne 0 then Prune(~MultiplesBounds); end if;
	k -:= 1;
    end while;

    X := Matrix(Z, Append(QQ, S));

    row_map := [i: i in [1 .. k]];

    function nneg_with_bounds(X)
	k := Nrows(X) - 1;
	X := Transpose(X);
	v := X[1];
	assert Min(Eltseq(v)) gt 0;
	for i := 2 to Nrows(X) do
	    while Min(Eltseq(X[i])) lt 0 do
		X[i] := X[i] + v;
	    end while;
	end for;
	X := Transpose(X);

	nc := Ncols(X);
	v := X[k + 1];
	bounds := [
	    Min([v[j] div X[i, j]: j in [1 .. nc] | X[i, j] ne 0]):
		i in [1 .. k]
	];

	return X, bounds;
    end function;

    procedure remove_dead_rows(~X, ~bounds, ~row_map, ~reduced)

	reduced := 0 in bounds;
	if not reduced then
	    return;
	end if;

	vprint ZRepsKnapsack, 2: "Remove zero rows";

	assert Nrows(X) eq #bounds + 1;
	v := X[Nrows(X)];

	XQ := [];
	nbounds := [];
	k := 0;
	for i := 1 to #bounds do
	    b := bounds[i];
	    if b gt 0 then
		k +:= 1;
		row_map[k] := row_map[i];
		Append(~XQ, X[i]);
		Append(~nbounds, b);
	    end if;
	end for;
	X := Matrix(XQ);
	assert Nrows(X) eq k;
	X := VerticalJoin(X, v);
	bounds := nbounds;

	vprint ZRepsKnapsack, 2: "reduced matrix:", X;
	vprint ZRepsKnapsack, 2: "reduced bounds:", bounds;

	X := Transpose(X);
	C := [];
	seen := {};
	for v in Rows(X) do
	    if v ne 0 and v notin seen then
		g := GCD(Eltseq(v));
		w := Vector([x div g: x in Eltseq(v)]);
		Append(~C, w);
		Include(~seen, w);
	    end if;
	end for;
	X := Matrix(C);
	X := Transpose(X);

	vprint ZRepsKnapsack, 2: "matrix with col redundance removed:", X;
    end procedure;

    k := Nrows(X) - 1;
    X, bounds := nneg_with_bounds(X);
    assert Nrows(X) eq k + 1;
    v := X[k + 1];

    vprint ZRepsKnapsack, 2: "Knap nneg X:", X;
    vprint ZRepsKnapsack, 2: "first bounds:", bounds;

    if MultiplesBounds cmpne 0 then
	assert #MultiplesBounds eq k;
	bounds := [Min(bounds[j], MultiplesBounds[j]): j in [1 .. #bounds]];
	vprint ZRepsKnapsack, 2: "reduced bounds:", bounds;
    end if;

    remove_dead_rows(~X, ~bounds, ~row_map, ~reduced);

    while true do

	vprint ZRepsKnapsack, 2: "NEW U LOOP";

	U := Transpose(HermiteForm(Saturation(Transpose(X))));
	vprint ZRepsKnapsack, 2: "Knap U:", U;

	extra_cols := [];
	if true /*Nrows(X) ge NCols(X) + 5*/ then
	    UT := Transpose(U);
	    V := Parent(UT[1]);
	    nc := Ncols(UT);
	    h := Nrows(UT);
	    l := h - 5;
	    if l lt 1 then l := 1; end if;
	    for S in Subsets({ l .. h }) do
		v := &+[V | UT[i]: i in S];
		// S, v;
		if v[nc] gt 0 and forall{j: j in [1 .. nc] | v[j] ge 0} then
		    Append(~extra_cols, v);
		    vprint ZRepsKnapsack, 2: "GOOD nneg vec:", S, v;
		    t := v[nc];
		    for j := 1 to nc - 1 do
			x := v[j];
			if x ne 0 then
			    q := t div x;
			    bounds[j] := Min(bounds[j], q);
			end if;
		    end for;
		    vprint ZRepsKnapsack, 2: "new bounds:", bounds;
		end if;
	    end for;
	end if;

	EU := HorizontalJoin(ColumnSubmatrix(X, 1, 1), U);
	EU, Ubounds := nneg_with_bounds(EU);
	vprint ZRepsKnapsack, 2: "nneg EU:", EU;
	vprint ZRepsKnapsack, 2: "Ubounds:", Ubounds;
	bounds := [Min(bounds[j], Ubounds[j]): j in [1 .. #bounds]];
	vprint ZRepsKnapsack, 2: "new bounds:", bounds;

	remove_dead_rows(~X, ~bounds, ~row_map, ~reduced);
	if reduced then
	    continue;
	end if;

	L := Transpose(LLL(Saturation(Transpose(X)): Sort));
	vprint ZRepsKnapsack, 2: "Knap LLL L:", L;
	EL := HorizontalJoin(ColumnSubmatrix(X, 1, 1), L);
	EL, Lbounds := nneg_with_bounds(EL);
	vprint ZRepsKnapsack, 2: "nneg EL:", EL;
	vprint ZRepsKnapsack, 2: "Lbounds:", Lbounds;
	bounds := [Min(bounds[j], Lbounds[j]): j in [1 .. #bounds]];
	vprint ZRepsKnapsack, 2: "new bounds:", bounds;

	remove_dead_rows(~X, ~bounds, ~row_map, ~reduced);
	if reduced then
	    continue;
	end if;

	break;

    end while;

/*
    Y := //ReverseColumns(
	Transpose(ReverseColumns(
	    HermiteForm(Saturation(ReverseColumns(Transpose((X)))))))
    //)
    ;
    vprint ZRepsKnapsack, 2: "Y:", Y;

    Y2 := ColumnSubmatrix(Y, 2, Ncols(Y) - 1);
    Y2 := Transpose(HermiteForm(Saturation(Transpose(Y2))));
    vprint ZRepsKnapsack, 2: "Y2 (remove first col):", Y2;

    Y2L := Transpose(LLL(Transpose(Y2)));
    vprint ZRepsKnapsack, 2: "Y2 LLL (remove first col):", Y2L;
*/

    //X := HorizontalJoin(ColumnSubmatrix(X, 1, 1), U);
X := ColumnSubmatrix(X, 1, 1);
if #extra_cols gt 0 then
X := HorizontalJoin(X, Transpose(Matrix(extra_cols)));
end if;
    X := HorizontalJoin(X, U);
    vprint ZRepsKnapsack, 2: "Knap X:", X;

    n := Ncols(X);

    // Find all columns which have non-negative entries only.

    nr := Nrows(X);
    nneg_cols := {};
    for j := 1 to n do
	if forall{i: i in [1 .. nr] | X[i, j] ge 0} then
	    Include(~nneg_cols, j);
	end if;
    end for;
    assert 1 in nneg_cols;
    Exclude(~nneg_cols, 1);

    vprint ZRepsKnapsack, 2: "nneg_cols:", nneg_cols;
    vprint ZRepsKnapsack, 2: "bounds:", bounds;

    k := Nrows(X) - 1;
    v := X[k + 1];
    X := RowSubmatrix(X, 1, k);

    lastzc := 0;
    zero_col := [];
    for r := 1 to k do
	zc := n + 1;
	// Force monotonic increasing:
	while zc gt lastzc and X[r, zc - 1] eq 0 do
	    zc -:= 1;
	end while;
	Append(~zero_col, zc);
	lastzc := zc;
    end for;
    vprint ZRepsKnapsack, 2: "zero_col:", zero_col;

    Q := Rows(X);

    function do_knap(v, r)

//printf "v: %o, r: %o\n", v, r;

	R := [];
	d := v[1];
	if d eq 0 then
	    if IsZero(v) then
		vprint ZRepsKnapsack, 2: "SOLUTION";
		Append(~R, []);
		// if Max gt 0 and #R ge Max then return R; end if;
	    end if;
	    return R;
	end if;

	vnzc := n;
	while v[vnzc] eq 0 do
	    vnzc -:= 1;
	end while;
//"vnzc:", vnzc;

	while r gt 0 do

	    w := Q[r];
	    e := w[1];
	    b := bounds[r];
	    if b eq 0 or e gt d then
		r -:= 1;
		continue;
	    end if;

	    zc := zero_col[r];
//"r:", r; "zc:", zc; "w:", w;
	    if vnzc ge zc then
		// r -:= 1; continue; // No assumption
		break; // Assumes monotonic increasing zero_col
	    end if;

	    m := d div e;
//printf "b: %o, quotient: %o\n", b, m;
	    m := Min(m, b);

	    if m gt 0 then
		if r eq 1 then
		    if m*w eq v then
			vprint ZRepsKnapsack, 2: "SOLUTION";
			Append(~R, [<1, m>]);
			if Max gt 0 and #R ge Max then return R; end if;
		    end if;
		    break;
		end if;

		for j in nneg_cols do
		    ej := w[j];
		    if ej ne 0 then
//assert ej gt 0;
			dj := v[j];
			q := dj div ej;
			if q lt m then
//printf "j: %o, ej: %o, dj: %o, q: %o\n", j, ej, dj, q;
			    m := q;
			    if m eq 0 then
				break;
			    end if;
			end if;
		    end if;
		end for;
		    
		assert m ge 0;
		r1 := r - 1;
		vv := v;
		for j := 1 to m do
		    vv -:= w;
//IndentPush();
		    RR := do_knap(vv, r1);
//IndentPop();
		    for t in RR do
			Append(~R, Append(t, <r, j>));
			if Max gt 0 and #R ge Max then return R; end if;
		    end for;
		end for;
	    end if;
	    r -:= 1;
	end while;

	return R;

    end function;

    R := do_knap(v, k);

//"Final R:", R;
//R; row_map;

    R := [[<row_map[t[1]], t[2]>: t in s]: s in R];
    return R;

end function;

intrinsic MultiKnapsackSolutions(
    QQ::[], S::[]: Max := 0, SingleRep := false, Multiples := false,
    MultiplesBounds := 0
) -> []
{Knapsack solutions to S written as non-negative combination of elements
of QQ}

    vprint ZRepsKnapsack, 2: "*****";
    vprint ZRepsKnapsack, 2: "Knap QQ:", QQ;
    vprint ZRepsKnapsack, 2: "Knap S:", S;
    time0 := Cputime();

    if #QQ eq 0 then
	return [];
    end if;

    if 0 eq 1 then
	X := Transpose(Matrix(Z, Append(QQ, S)));
	X := Transpose(HermiteForm(X));
	"X:", X;

	X := Transpose(Matrix(Z, Append(Reverse(QQ), S)));
	X := Transpose(HermiteForm(X));
	"rev X:", X;

	X := Transpose(Matrix(Z, Append(QQ, S)));
	X := Transpose(LLL(X));
	"LLL X:", X;
    end if;

    n := #QQ;
    k := #QQ[1];

    pos1 := S[1] gt 0 and forall{i: i in [1 .. n] | QQ[i, 1] gt 0};

    if pos1 and Multiples then
	return MultiKnapsackSolutionsMultiplesPos(
	    QQ, S: Max := Max, MultiplesBounds := MultiplesBounds
	);
    end if;

    for j := 1 to k do
	if S[j] ge 0 and forall{i: i in [1 .. n] | QQ[i, j] ge 0} then
	    while n gt 0 and QQ[n, j] gt S[j] do
		//"Prune", QQ[n];
		Prune(~QQ);
		n -:= 1;
	    end while;
	end if;
    end for;

    vprint ZRepsKnapsack, 2: "Prune QQ to:", QQ;

    if #QQ eq 0 then
	return [];
    end if;

    R := [];

    if pos1 then
	d := S[1];
	while n gt 0 and QQ[n, 1] eq d do
	    if QQ[n] eq S then
		if Multiples then
		    Append(~R, [<n, 1>]);
		else
		    Append(~R, [n]);
		end if;
	    end if;
	    Prune(~QQ);
	    n -:= 1;
	end while;

	vprint ZRepsKnapsack, 2: "Extra prune QQ to:", QQ;
	if #QQ eq 0 then
	    return R;
	end if;

	T := QQ[n];
	assert T[1] lt d;
    end if;

    card := #Set(QQ);
    if 1 eq 1 and Multiples then
	I := {@ v: v in QQ @};
	assert #I eq #QQ;
	ind := [{i}: i in [1 .. card]];

	if pos1 then
	    count := [Floor(S[1]/I[i, 1]): i in [1 .. card]];
	else
	    count := [inf: I in ind] where inf := Infinity();
	end if;

	RR := NewMultiKnapsackSolutions(
	    S, I, ind, count: Max := Max, SingleRep := SingleRep,
	    Multiples := Multiples
	);
	R := RR cat R;
	vprint ZRepsKnapsack, 2: "Knap sol:", R;
	vprint ZRepsKnapsack, 2: "Knap sol time:", Cputime(time0);
	return R;
    else
	I := {@ @};
	ind := [{Z|}: i in [1 .. card]];

	for qi := 1 to #QQ do
	    q := QQ[qi];
	    Include(~I, q);
	    i := Index(I, q);
	    Include(~ind[i], qi);
	end for;

	if pos1 then
	    count := [Min(#ind[i], Floor(S[1]/I[i, 1])): i in [1 .. card]];
	else
	    count := [#I: I in ind];
	end if;
    end if;

    vprint ZRepsKnapsack, 2: "Count seq:", count;

    A := Matrix(Z, [v: v in I]);
    V := Vector(Z, S);
//Parent(A);
//Parent(V);

    vprint ZRepsKnapsack, 2: "A:", A;
    vprint ZRepsKnapsack, 2: "V:", V;

    l, U, K := IsConsistent(A, V);
    if not l then
	return R;
    end if;

    vprint ZRepsKnapsack, 2: "U:", U;
    vprint ZRepsKnapsack, 2: "K:", K;

    norm := Norm(Vector(count));

    // Use enum method if big dim and S[1] not too big
    if
	Multiples or
	pos1 and Dimension(K) ge 10 and S[1] le 2*QQ[#QQ, 1]
    then
	/*
	R := NewMultiKnapsackSolutions(
	    QQ, S: Max := Max, SingleRep := SingleRep
	);
	*/
	R := NewMultiKnapsackSolutions(
	    S, I, ind, count: Max := Max, SingleRep := SingleRep,
	    Multiples := Multiples
	);
	vprint ZRepsKnapsack, 2: "Knap sol:", R;
	vprint ZRepsKnapsack, 2: "Knap sol time:", Cputime(time0);
	return R;
    end if;

    if Dimension(K) eq 0 then
	L := 0;
    else
	L := Lattice(K);
    end if;

    vprint ZRepsKnapsack, 2: "L:", L;
    vprint ZRepsKnapsack, 2: "norm:", norm;

    r := #I;
    //CV := L cmpeq 0 select [<Parent(U)!0, 1>] else CloseVectors(L, U, norm);
    CV := L cmpeq 0 select 0 else CloseVectorsProcess(L, U, norm);

//    for t in CV do
//	v := U - t[1];

    cvcount := 0;
    while true do
	cvcount +:= 1;

	if L cmpeq 0 then
	    SV := Parent(U)!0;
	    svn := 0;
	else
	    SV, svn := NextVector(CV);
	    if svn lt 0 then
		break;
	    end if;
	end if;
	v := U - SV;

/*
"SV", SV;
"svn", svn;
"got v", v;
"#R:", #R;
*/
	if forall{j: j in [1 .. r] | v[j] ge 0 and v[j] le count[j]} then
	    CO := [];
	    for j in Support(v) do
		c := v[j];
		assert c le #ind[j];
		Append(~CO, Subsets(ind[j], c));
	    end for;
	    C := CartesianProduct(CO);
//C;
	    for t in C do
//"t:", t;
		Append(~R, Sort(Setseq(&join{s: s in t})));
		if SingleRep then
		    break;
		end if;
		if Max gt 0 and #R eq Max then
		    break t;
		end if;
	    end for;
	end if;

	if L cmpeq 0 then
	    break;
	end if;
    //end for;
    end while;

    vprint ZRepsKnapsack, 2: "#Close vectors enumerated:", cvcount;

    //Sort(~R);
    Sort(~R, func<x, y | #x - #y>);

    vprint ZRepsKnapsack, 2: "Knap sol:", R;
    vprint ZRepsKnapsack, 2: "Knap sol time:", Cputime(time0);

    return R;
end intrinsic;

intrinsic KnapsackSolutions(Q, s: Max := 0) -> []
{}

    return MultiKnapsackSolutions([[x]: x in Q], [s]: Max := Max);

    n := #Q;
    X := RMatrixSpace(IntegerRing(), n + 1, n + 2) ! 0;
    for i := 1 to n do
        X[i][i] := 2;
        X[i][n + 1] := n * Q[i];
        X[n + 1][i] := 1;
    end for;
    X[n + 1][n + 1] := n * s;
    X[n + 1][n + 2] := 1;
    L := Lattice(X);

    n := Rank(L) - 1;
    M := n + 1;
    S := ShortVectors(L, M, M);
    return [
        [i: i in [1 .. n] | v[i] ne v[n + 2]]: t in S |
            forall{i: i in [1 .. n] cat [n + 2] | Abs(v[i]) eq 1} and
                v[n + 1] eq 0 where v is t[1]
    ];
end intrinsic;

function WeightedMultiKnapsackSolutions(QQ, S: Max := 0)
    // Assumes pos1 (1st coord is positive)
    assert S[1] gt 0 and forall{Q: Q in QQ | Q[1] gt 0};
    S := ChangeUniverse(S, Z);
    d := S[1];
    NQQ := [];
    NI := [];
    for i := 1 to #QQ do
	Q := ChangeUniverse(QQ[i], Z);
	q := d div Q[1];
	for j := 1 to q do
	    Append(~NQQ, Q);
	    Append(~NI, i);
	end for;
    end for;

"NQQ:", NQQ; "NI:", NI;

    kn := MultiKnapsackSolutions(NQQ, S: Max := Max);
"first kn:", kn;
    kn := [[NI[i]: i in s]: s in kn];
"new kn:", kn;
    return kn;
end function;

/*******************************************************************************
				Get character
*******************************************************************************/

/*
function num_fixed_pts(g)
    e := Eltseq(g);
    return #[i: i in [1 .. Degree(Parent(g))] | e[i] eq i];
end function;
*/


function div_char(c, d)
    n := #c;
    assert forall{i: i in [1 .. n] | Z!c[i] mod d eq 0};
    c := Parent(c)![ExactQuotient(Z!c[i], d): i in [1 .. n]];
    return c;
end function;

// From Bill:
num_fixed_pts := func<g|Degree(Parent(g)) - Degree(g)>;

function PermCharRep(f)
    // f: G -> H; Perm char of H w.r.t. G's classes
    return [num_fixed_pts(f(t[3])): t in Classes(Domain(f))];
end function;

function PermChar(G)
    return [num_fixed_pts(t[3]): t in Classes(G)];
end function;

function sym_range(T)
    p := #Universe(T);
    T := [Z ! x: x in T];
    p2 := p div 2;
    T := [x ge p2 select x - p else x: x in T];
    return T;
end function;

intrinsic Char(
    m::ModGrp: SymRange := false, Possible := {}, IrrChars := [],
    PossiblyNone := false
) -> AlgChtrElt
{Character of module m}

/*
Return character of module m.
If PossiblyNone, then allows case of PossiblyNone; 0 returned if none.
*/
    if assigned m`Character then
	return m`Character;
    end if;

    assert not PossiblyNone or #IrrChars eq 0;

    vprintf ZMeataxe: "Get character for dim %o\n", Dimension(m);
//"MOD"; m: Magma;
//"Possible:", Possible;
//"IrrChars:", IrrChars;

    vprintf ZMeataxe: "#Possible given: %o\n", #Possible;
    if PossiblyNone then
	vprint ZMeataxe: "Possibly none";
    end if;

    G := Group(m);

    if #Possible eq 1 then
	vprint ZMeataxe: "    Only one possible!";
	m`Character := CharacterRing(G) ! Rep(Possible);
	return m`Character;
    end if;

    om := m;
    Z := IntegerRing();
    C := Classes(G);
    f := ClassMap(G);

    vprintf ZMeataxe: "Number of classes: %o\n", #C;
    if #Possible gt 0 then
	vprintf ZMeataxe: "%o possible character(s) given\n", #Possible;
    end if;

    if #IrrChars gt 0 then
	vprintf ZMeataxe: "%o irreducible character(s) given\n", #IrrChars;
    end if;

    if IsPermutationModule(m) then
	vprint ZMeataxe: "Permutation module; use perm rep";
	ng := Type(G) eq GrpPC select NPCgens(G) else Ngens(G);
	d := Dimension(m);
	assert Nagens(m) eq ng;
	S := Sym(d);
	PG := [S |
	    [Min(Support(X[i])): i in [1 .. d]] where
		X := ActionGenerator(m, k):
		k in [1 .. ng]
	];
	P := sub<S | PG>;
	Pf := hom<G -> P | [PG[i]: i in [1 .. ng]]>;
	c := CharacterRing(G) ! PermCharRep(Pf);
	m`Character := CharacterRing(G) ! c;
	return c;
    end if;

    TIME := Cputime();

    function traces(m)
	K := BaseRing(m);
	dim := Dimension(m);
	k := #C;

	if #IrrChars gt 0 then
	    possible := [];		// not used
	else
	    possible := [[K | c[i]: i in [1 .. k]]: c in Possible];
	end if;

	procedure try_knap(~possible, T)
	    if #IrrChars eq 0 then
		return;
	    end if;

	    n := #C;
	    cols := [j: j in [1 .. n] | IsDefined(T, j)];

	    S := [T[j]: j in cols];
	    QQ := [[c[j]: j in cols]: c in IrrChars];
	    //kn := MultiKnapsackSolutions(QQ, S: Max := 2);

	    // "QQ:", QQ; "S:", S;
	    //kn := WeightedMultiKnapsackSolutions(QQ, S: Max := 2);

	    if 1 eq 1 then
		kn := MultiKnapsackSolutions(
		    QQ, S: Multiples, SingleRep, Max := 2
		);
	    else
		kn := [];
	    end if;

	    vprintf ZMeataxe, 2: "kn: %o\n", [Sprint(x): x in kn];

	    if #kn eq 1 then
		vprint ZMeataxe, 2: "Unique!";
		//possible := [&+[IrrChars[i]: i in kn[1]]];
		possible := [&+[t[2]*IrrChars[t[1]]: t in kn[1]]];
	    end if;

	end procedure;

	// T used in IrrMat case; otherwise v gives new coord i
	procedure reduce_possible(~possible, i, v, T: TryKnap)
	    if TryKnap then
		try_knap(~possible, T);
	    end if;

	    for p in possible do
		if p[i] ne v then
		    possible := [p: p in possible | p[i] eq v];
		    vprintf ZMeataxe: "Number possible reduced to %o\n",
			#possible;
		    assert PossiblyNone or #possible gt 0;
		    return;
		end if;
	    end for;
	end procedure;

	procedure inc(~T, g, TraceFunc, ~possible, nprod: TryKnap)
	    i := f(g);
	    if IsDefined(T, i) then return; end if;

	    T[i] := TraceFunc();
//printf "Get for %o: %o\n", i, T[i];

	    reduce_possible(~possible, i, T[i], T: TryKnap := TryKnap);
	    if #possible eq 1 or PossiblyNone and #possible eq 0 then
		vprintf ZMeataxe:
	    "%o trace(s) needed to distinguish character, %o product(s)\n",
			#[i: i in [1 .. k] | IsDefined(T, i)], nprod;
	    end if;
	end procedure;

	count := k div 2;
	count := k;
	if dim ge 60 then
	    count := 2*k;
	    count := 3*k;
	end if;
	nprod := 0;

	T := [K | Dimension(m)];

	ng := Ngens(G);
	Lg := [G.i: i in [1 .. ng]];
	Lm := [ActionGenerator(m, i): i in [1 .. ng]];
	roots := 0;

	if 1 eq 1 and Type(K) in {FldNum, FldCyc, FldQuad} then

	    Kdeg := Degree(K);
	    Kdeg1 := Kdeg - 1;
	    f := DefiningPolynomial(K);
	    p := Floor(2^23.5);
	    while true do
		p := PreviousPrime(p);
		F := GF(p);
		roots := Roots(f, F);
		if #roots eq Kdeg then
		    break;
		end if;
	    end while;

	    roots := [t[1]: t in roots];
	    Rpows := [[r^j: j in [0 .. Kdeg1]]: r in roots];

	    Krange := [1 .. Kdeg];
	    Zx := PolynomialRing(Z);
	    mat_images := function(X)
		im := [ZeroMatrix(F, dim, dim): r in roots];
		for i, j in [1 .. dim] do
		    x := X[i, j];
		    d := Denominator(x);
		    /*
		    x := Eltseq(d*x);
		    d := (F!d)^-1;
		    for ri := 1 to Kdeg do
			rp := Rpows[ri];
			im[ri, i, j] := d*&+[x[k]*rp[k]: k in Krange];
		    end for;
		    */
		    x := Zx!Eltseq(d*x);
		    d := (F!d)^-1;
		    for ri := 1 to Kdeg do
			im[ri, i, j] := d*Evaluate(x, roots[ri]);
		    end for;
		end for;
		return im;
	    end function;

	    vprint ZMeataxe: "Set up images";
	    vtime ZMeataxe:
		Lm := [mat_images(x): x in Lm];

	    OLm := Lm;

	    function interp_traces(T)
		//I := [Matrix(1, 1, x): x in T];
//"Given T:", T;
		//I := EntriesInterpolationExpansion(roots, [I]);
		//return K!Eltseq(I);
		f := Interpolation(roots, T);
		e := [];
		for j := 0 to Degree(f) do
		    l, x := RationalReconstruction(Coefficient(f, j));
		    assert l;
		    Append(~e, x);
		end for;
// "f:", f; "e:", e;
		e cat:= [0: i in [#e + 1 .. #roots]];
		return K!e;
	    end function;

	    MultFunc := func<X, Y | [X[i]*Y[i]: i in [1 .. #X]]>;
	    TraceFunc := func<X |
		func<| interp_traces([Trace(x): x in X])>>;
	    TraceOfProductFunc := func<X, Y |
		func<|
		    interp_traces([TraceOfProduct(X[i], Y[i]): i in [1 .. #X]])
		>
	    >;

	else

	    MultFunc := func<X, Y | X*Y>;
	    TraceFunc := func<X | func<| Trace(X)>>;
	    TraceOfProductFunc := func<X, Y | func<| TraceOfProduct(X, Y)>>;

	end if;

	stop_cond := func<PossiblyNone, possible |
	    PossiblyNone and #possible eq 0 or #possible eq 1>;
	stop_ret := func<possible | #possible eq 0 select 0 else possible[1]>;

	procedure do_seq_product(~T, ~possible, np, Lg, Lm, k)
	    n := #Lg;
	    assert #Lm eq n and k le n;
	    g := Lg[k];
	    m := Lm[k];
	    if stop_cond(PossiblyNone, possible) then return; end if;
	    for i := 1 to n do
		if i eq k then continue; end if;
//vprint ZMeataxe: "Trace of product", k, i;
		inc(~T, g*Lg[i], TraceOfProductFunc(m, Lm[i]), ~possible, np);
		if #possible le 1 then return; end if;
//vprint ZMeataxe: "Trace of product", i, k;
		inc(~T, Lg[i]*g, TraceOfProductFunc(Lm[i], m), ~possible, np);
		if #possible le 1 then return; end if;
	    end for;
//vprint ZMeataxe: "Trace of square", k;
	    inc(~T, g^2, TraceOfProductFunc(m, m), ~possible, np);
	    if #possible le 1 then return; end if;
	end procedure;

	for i := 1 to ng do
	    Append(~Lg, G.i);
	    Append(~Lm, Lm[i]);
//vprint ZMeataxe: "Trace of input", i;
	    inc(
		~T, Lg[i], TraceFunc(Lm[i]), ~possible, nprod:
		    TryKnap := i eq ng
	    );
	    do_seq_product(~T, ~possible, nprod, Lg, Lm, #Lg);
	    if stop_cond(PossiblyNone, possible) then
		return stop_ret(possible);
	    end if;
	end for;

	for i := 1 to 3 do
	    r := Random(1, ng);
	    Append(~Lg, Lg[#Lg] * G.r);
	    Append(~Lm, MultFunc(Lm[#Lm], Lm[r]));
	    nprod +:= 1;
//vprint ZMeataxe: "Trace of random setup prod", i;
	    inc(~T, Lg[#Lg], TraceFunc(Lm[#Lm]), ~possible, nprod);
	    do_seq_product(~T, ~possible, nprod, Lg, Lm, #Lg);
	    if stop_cond(PossiblyNone, possible) then
		return stop_ret(possible);
	    end if;
	end for;

	vprintf ZMeataxe: "Try %o random elements\n", count;

	vtime ZMeataxe:
	    while count gt 0 do
		r := Random(1, #Lg);
		s := Random(1, #Lg);
		g := Lg[r] * Lg[s];
		nprod +:= 1;
		if IsIdentity(g) then
		    continue;
		end if;

		X := MultFunc(Lm[r], Lm[s]);
//vprint ZMeataxe: "Trace of random prod", r, s;
		inc(~T, g, TraceFunc(X), ~possible, nprod);
		do_seq_product(~T, ~possible, nprod, Lg, Lm, r);
		if stop_cond(PossiblyNone, possible) then
		    return stop_ret(possible);
		end if;
		Lg[r] := g;
		Lm[r] := X;
		count -:= 1;

		f := #[i: i in [1 .. k] | IsDefined(T, i)];
		if f eq k then
		    break;
		end if;
	    end while;

	//possible;
	//"T:", T;

	f := #[i: i in [1 .. k] | IsDefined(T, i)];
	vprintf ZMeataxe: "%o trace(s) found\n", f;

	if f eq k then
	    return T;
	end if;

	vprintf ZMeataxe: "Need %o other trace(s)\n", k - f;

	vprint ZMeataxe: "Get rep map"; vtime ZMeataxe:
	if roots cmpne 0 then
	    //MK := [GModule(G, L): L in OLm];
	    MK := [
		GModule(G, [OLm[j, i]: j in [1 .. ng]]: Check := false):
		i in [1 .. #roots]
	    ];
	    r := [Representation(m): m in MK];
//MK, r;
	else
	    r := Representation(m);
	end if;

	vprintf ZMeataxe: "Get %o other trace(s)\n", k - f;
	vtime ZMeataxe:
	    for i := 1 to k do
		if IsDefined(T, i) then continue; end if;

		g := C[i, 3];
		if roots cmpne 0 then
		    t := interp_traces([Trace(f(g)): f in r]);
		else
		    t := Trace(r(g));
		end if;
		T[i] := t;

		reduce_possible(~possible, i, T[i], T);
		if not (#possible eq 1 or PossiblyNone and #possible eq 0) then
		    continue;
		end if;
		vprintf ZMeataxe:
		    "%o trace(s) needed to distinguish character\n",
			#[i: i in [1 .. k] | IsDefined(T, i)];
		if PossiblyNone and #possible eq 0 then
		    return 0;
		end if;
		if #possible eq 1 then
		    return possible[1];
		end if;
	    end for;

	return T;
    end function;

    CR := CharacterRing(G);
    if BaseRing(m) cmpne Z or #IrrChars gt 0 then
	T := traces(m);
	if T cmpeq 0 then
	    vprint ZMeataxe: "None possible";
	    vprint ZMeataxe: "Total character computation time:", Cputime(TIME);
	    return 0;
	end if;
	if Characteristic(BaseRing(m)) gt 0 then
	    return T;
	end if;
	if SymRange then
	    T := CR!sym_range(T);
	else
	    //"Got T:", T;
	    c := CharacterFromTraces(CR, Eltseq(T));
	end if;
    else
	//PRIME := NextPrime(Max(2*Dimension(m) + 2, 65537));

	PRIME := PreviousPrime(2^23);
	K := GF(PRIME);
	m := ChangeRing(m, K);
	T := traces(m);
	if T cmpeq 0 then
	    vprint ZMeataxe: "None possible";
	    vprint ZMeataxe: "Total character computation time:", Cputime(TIME);
	    return 0;
	end if;
	c := CR!sym_range(T);
    end if;

    vprint ZMeataxe: "Total character computation time:", Cputime(TIME);

    om`Character := c;
    return c; // T;
end intrinsic;

/*******************************************************************************
                                Aux
*******************************************************************************/

function char_is_multiple(c, s)
    // Return whether c is multiple of s
    dc := Z!Degree(c);
    ds := Z!Degree(s);
    if ds gt 0 and IsDivisibleBy(dc, ds) and c eq (dc div ds)*s then
        return true, dc div ds;
    else
        return false, _;
    end if;
end function;

