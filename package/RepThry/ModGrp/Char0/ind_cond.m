freeze;

Z := IntegerRing();

NO_UCB := true;
NEW_set_up_action := true;
NEW_set_up_action := false;

/*******************************************************************************
			    New GBP
*******************************************************************************/

intrinsic NewGBP(G::GrpMat, n::RngIntElt) -> []
{Up to n new good base points}

    T := Cputime();
    GBP := [**];
    L := [];
    while true do
	r := Random(G);
	r := Matrix(r) - 1;
	ker := KernelMatrix(r);
	k := Nrows(ker);
	printf "%o: ker dim: %o, time: %o\n", #L + 1, k, Cputime(T);

	if k eq 0 then
	    continue;
	end if;

	for Bi := 1 to #L do
	    B := L[Bi];
	    P := ker*B;
	    ker2 := KernelMatrix(P);
	    if Nrows(ker2) gt 0 then
		I := ker2*ker;
		I := EchelonForm(I);
		RemoveZeroRows(~I);
		printf "Found intersection %o with space %o; dim: %o\n",
		    #GBP + 1, Bi, Nrows(I);
		skip := false;
		for i := 1 to #GBP do
		    if Nrows(GBP[i]) eq Nrows(I) and GBP[i] eq I then
			"Repeat; skip";
			skip := true;
			break;
		    end if;
		end for;
		if skip then continue; end if;
		Append(~GBP, I);
		if #GBP eq n then
		    return GBP;
		end if;
	    end if;
	end for;
	Append(~L, r);

    end while;

end intrinsic;

/*******************************************************************************
			    Subgroup sum
*******************************************************************************/

function SubgroupSum(r, G)
// Return sum of r(x), for all x in G
    //"Subgroup sum, size:", #G;
//"Soluble:";
vtime ZReps:
    if IsSoluble(G) then
	PC, PCf := PCGroup(G);
	gim := [r(PC.i@@PCf): i in [1 .. NPCGenerators(PC)]];
	pr := PCPrimes(PC);
	s := 1;
	for i := #pr to 1 by -1 do
	    im :=1;
	    ns :=im;
	    for j :=1 to pr[i]-1 do 
		im := im*gim[i];
		ns := ns + im;
	    end for;
	    s := s*ns;
	end for;
//assert s eq os;
	if s cmpeq 1 then
	    s := r(1);
	end if;
	return s;
    end if;
    vtime ZReps: os := &+[r(x): x in G];
    return os;
end function;

/*******************************************************************************
			    Induction setup
*******************************************************************************/

intrinsic InternalInductionCondensationSetup(
    G::Grp, HM::ModGrp, K::Grp: CondensedDimOnly := false
) -> Rec
{Set up condensation for Induction(HM, G) via subgroup K}

    R := BaseRing(HM);
    F := FieldOfFractions(R);

    H := Group(HM);
//HM: Magma;

    Hrep := Representation(HM);

    U, Uf := Transversal(G, H);
    if Type(G) eq GrpPerm then
	DC := DoubleCosetRepresentatives(G, H, K);
    else
	/*
	If g is an elt of G, then g permutes the elements of transversal T
	by the permutation g@f. The double cosets are not contiguous in T.
	*/

	f, I := CosetAction(G, H);
	T := [x@@f where _, x:=IsConjugate(I, 1, o): o in [1..Degree(I)]];
	orbs := Orbits(K@f); // the K-orbits, which are the double cosets
	DC := [T[o[1]]: o in orbs];
	delete orbs;
    end if;

    TI := [[g*t: t in Transversal(K, H^g meet K)]: g in DC];
    T := &cat TI;

    vprint ZReps: "TI lengths:", [#x: x in TI];

    vprint ZReps: "Get HI";
    vtime ZReps: HI := [H meet K^(g^-1): g in DC];
    vprint ZReps: "HI sizes:", {* #x: x in HI *};
    vprint ZReps: "HI IsCyclic:", {* IsCyclic(x): x in HI *};
    //vprint ZReps: "HI CF:", [CompositionFactors(x): x in HI];
    //vprint ZReps: "HI PC:", [PCGroup(x): x in HI]: Magma;
    //vprint ZReps: "HI:", HI: Magma;
    delete DC;

    if CondensedDimOnly then
	return &+[Rank(&+[Hrep(x): x in Hi]): Hi in HI];
    end if;

    Hd := Dimension(HM);
    Td := Index(G, H);

    base := [&+[Z|#TI[j]: j in [1 .. i - 1]]: i in [1 .. #TI]];
    TUI := [Index(U, Uf(t)): t in T];
    Uim := Eltseq((Sym(Td)!TUI)^-1);

    function Timap(g)
	i := Index(U, Uf(g));
	return Uim[i];
    end function;

    function set_up_action(g)
	Amats := [];
	Aind := [];
//hset := {};
	for i := 1 to Td do
	    t := T[i];
	    tg := t*g;
	    tdashi := Timap(tg);
	    tdash := T[tdashi];
	    h := tg*tdash^-1;
//printf "i: %o, t: %o, h: %o\n", i, t, h;
	    //assert h in H;
	    M := Matrix(R, Hrep(h));
//Include(~hset, h);
	    Append(~Amats, M);
	    Append(~Aind, tdashi);
	end for;
//printf "#hset: %o out of %o\n", #hset, Td;
//Sort([Hash(x): x in hset]);
	return Amats, Aind;
    end function;

    function new_set_up_action(mat, g, pos)
	Amats := [];
	Aind := {@@};
	for i in pos do
	    t := T[i];
	    tg := t*g;
	    tdashi := Timap(tg);
	    tdash := T[tdashi];
	    h := tg*tdash^-1;
//printf "i: %o, t: %o, h: %o\n", i, t, h;
	    //assert h in H;
	    //M := Matrix(R, Hrep(<mat, h>));
	    M := Representation(HM, <mat, h>);
/*
"mat:", mat;
"hr:", Hrep(h);
"prod:", mat*Hrep(h);
"bad M:", M;
assert M eq mat*Hrep(h);
*/
	    M := Matrix(R, M);
	    Append(~Amats, M);
	    //Append(~Aind, tdashi);
	    Include(~Aind, tdashi);
	end for;
	return Amats, Aind;
    end function;

    function action2(w, Amats, Aind)
	assert Ncols(w) eq Hd*Td;
	X := RMatrixSpace(R, Td, Hd) ! Eltseq(w);
	Y := RMatrixSpace(R, Td, Hd) ! 0;
	for i := 1 to Td do
	    u := X[i]*Amats[i];
	    Y[Aind[i]] := u;
	end for;
	return Generic(Parent(w))!Eltseq(Y);
    end function;

    function action(w, g)
	assert Ncols(w) eq Hd*Td;

	X := RMatrixSpace(F, Td, Hd) ! Eltseq(w);
	Y := RMatrixSpace(F, Td, Hd) ! 0;
	for i := 1 to Td do
	    t := T[i];
	    tg := t*g;
	    tdashi := Timap(tg);
	    tdash := T[tdashi];
	    h := tg*tdash^-1;
	    assert h in H;
	    u := X[i]*Matrix(F, Hrep(h));
	    Y[tdashi] := u;
	end for;

	return Generic(Parent(w))!Eltseq(Y);
    end function;

//NO_UCB := false;
    if NO_UCB then
	vprint ZReps: "NEW";

	vprint ZReps: "Get EI";
	//vtime ZReps: EI := [Matrix(R, &+[Hrep(x): x in Hi]): Hi in HI];
	vtime ZReps: EI := [Matrix(R, SubgroupSum(Hrep, Hi)): Hi in HI];
	vprint ZReps: "Get im";
	vtime ZReps: im := <BasisMatrix(Rowspace(Matrix(R, ei))): ei in EI>;
	cdim := &+[Z | Nrows(im[i]): i in [1 .. #im]];
	VGe := RSpace(R, cdim);

	//"im:", im;
	vprint ZReps: "cdim:", cdim;

	blen := Hd;
	nb := Td;
vprint ZReps: "blen:", blen;
vprint ZReps: "nb:", nb;
	UCB := 0;

	im := <Matrix(R, X): X in im>;
	TI_lens := [#x: x in TI];

	function get_ege(g)

	    MS := GetMS();
	    SetMS(false);

	    r := [];
// "Set up action", g; time
	    if NEW_set_up_action then
		;
	    else
		Amats, Aind := set_up_action(g);
	    end if;

//Amats; Aind;
// Parent(Amats);

	    W := ZeroMatrix(R, cdim, cdim);
	    p := 1;
	    row := 1;

// "Do loop", cdim, cdim;
//"#im:", #im; <Parent(x): x in im>;
//time
	    for i := 1 to #im do
		dcl := #TI[i];
		X := im[i];
		r := Nrows(X);
		// X at block positions [p .. p + dcl - 1]

		// Get action of g
		pos := [p .. p + dcl - 1];
//Parent(X); Parent(Amats[1]);
//printf "i: %o, im r: %o, pos: %o\n", i, r, pos; "X:", X;
		if NEW_set_up_action then
		    XM, XP := new_set_up_action(X, g, pos);
		else
		    XM := [X*Amats[i]: i in pos];
		    XP := {@ Aind[i]: i in pos @};
		end if;

// "XM:", XM; "XP:", XP;
		// Multiply by e back into condensed module

/*
TI: seq of seq of elts of G (only use len of TI[j])
XP: indexed set of integers
XM: seq of matrices
im: seq of matrices
*/

NO_TEST_C := true;

		if NO_TEST_C then
		    InternalInductionCond(<TI_lens, XP, XM, im, EI>, ~W, row);
		else
OW := W;

		zero := Universe(XM)!0;
		b := 1;
		col := 1;
		for j := 1 to #TI do
		    TIj := TI[j];
		    nextb := b + #TIj;
		    v := zero;
		    for k := b to nextb - 1 do
			ind := Index(XP, k);
			if ind gt 0 then
//printf "j: %o, k: %o, ind: %o\n", j, k, ind;
			    v +:= XM[ind];
			end if;
		    end for;
		    if v ne 0 then
// Parent(v); Parent(EI[j]); EI[j];
			v := v*EI[j];
			vc := Solution(im[j], v);
			//vc := vc * #HI[j];
//"p:", p; "b:", b;
//"row:", row; "col:", col;
			InsertBlock(~W, vc, row, col);
		    end if;
		    b := nextb;
		    col +:= Nrows(im[j]);
		end for;

		    InternalInductionCond(<TI_lens, XP, XM, im, EI>, ~OW, row);
		    if OW ne W then
			"W:", W;
			"OW:", OW;
			"row:", row;
			"Tuple:", <TI_lens, XP, XM, im, EI>;
			error "DIE";
		    end if;
		end if;

		p +:= dcl;
		row +:= r;
	    end for;
	    assert row eq cdim + 1;
// p,nb;
	    assert p eq nb + 1;

	    if IsField(R) then
		W := (1 / #K) * W;
	    end if;

	    SetMS(MS);

	    return W;
	end function;

	function uncond(V)

	    //U := ZeroMatrix(R, Nrows(V), 0);
	    F := BaseRing(V);
	    U := ZeroMatrix(F, Nrows(V), 0);
	    col := 1;
// Parent(V);
	    for i := 1 to #im do
		X := im[i];
		r := Nrows(X);
//"i:", i; "col:", col; "r:", r;
//"X:", X;
		S := ColumnSubmatrix(V, col, r);
//"S:", S;
		S := S*Matrix(F, X);
//"new S:", S;
		col +:= r;
		/*
		for j := 1 to #TI[i] do
		    InsertBlock(~U, S, 1, col);
		end for;
		*/
		J := HorizontalJoin([S: j in [1 .. #TI[i]]]);
//"U:", U; "J:", J;
		U := HorizontalJoin(U, J);
	    end for;

	    return U;
	    /*
	    for i := 1 to #im do
		J := HorizontalJoin([im[i]: j in [1 .. #TI[i]]]);
		UCB := DiagonalJoin(UCB, J);
		Append(~impos, p);
		p +:= #TI[i] * Ncols(im[i]);
		assert Ncols(UCB) eq p-1;
	    end for;
	    */
	end function;
    else

	vtime ZReps: EI := [1/#Hi * Matrix(F, &+[Hrep(x): x in Hi]): Hi in HI];
	vtime ZReps: im := <BasisMatrix(Rowspace(Matrix(F, ei))): ei in EI>;
	cdim := &+[Z | Nrows(im[i]): i in [1 .. #im]];
	VGe := RSpace(R, cdim);

	//"im:", im;
	vprint ZReps: "cdim:", cdim;

	UCB := ZeroMatrix(F, 0, 0);
	impos := [];
	p := 1;

	vprint ZReps: "Make UCB:";
	vtime ZReps: for i := 1 to #im do
	    J := HorizontalJoin([im[i]: j in [1 .. #TI[i]]]);
	    UCB := DiagonalJoin(UCB, J);
	    Append(~impos, p);
	    p +:= #TI[i] * Ncols(im[i]);
    /*
    "im[i]:", im[i];
    "J:", J;
    "UCB:", UCB;
    i, p, Ncols(UCB);
    */
	    assert Ncols(UCB) eq p-1;
	end for;

	vprint ZReps: "impos:", impos;
	vprint ZReps: "UCB:", Parent(UCB);

	function mult_by_e(v)
	    assert Ncols(v) eq Hd*Td;

	    X := RMatrixSpace(F, Td, Hd) ! Eltseq(v);
	    w := <>;
	    b := 0;
	    for i := 1 to #TI do
		TIi := TI[i];
		ei := EI[i];
		v := &+[X[b + j]: j in [1 .. #TIi]];
		if IsZero(v) then
		    vc := RSpace(F, Nrows(im[i])) ! 0;
		else
		    v := v*ei;
		    vc := Solution(im[i], v);
		    vc := vc * #HI[i];
		end if;
		Append(~w, vc);
		/*
		for j := 1 to #TIi do
		    Append(~w, vc);
		end for;
		*/
		b +:= #TIi;
	    end for;

	    "First w:", w;

	    w := Vector([F | x: x in Eltseq(u), u in w]);

F;
#K;
	    if IsField(F) then
		w := (1 / #K) * w;
	    end if;

	    return w;
	end function;

	function get_ege(g)
	    r := [];
	    Amats, Aind := set_up_action(g);
    //Amats; Aind;
	    for i := 1 to cdim do
		u := UCB[i];
		// u := action(u, g);
		u := action2(u, Amats, Aind);
		u := mult_by_e(u);
		Append(~r, u);
	    end for;
	    return Matrix(F, cdim, cdim, r);
	end function;

	function uncond(v)
	    return v * Matrix(BaseRing(v), UCB);
	end function;
    end if;

    function set_up_action_seqs(L)
	MQ:=[];
	IQ:=[];
	for g in L do
	    q, p := set_up_action(g);
	    Append(~MQ, q);
	    Append(~IQ, p);
	end for;
	return MQ, IQ;
    end function;

    fmt := recformat<get_ege, uncond, set_up_action, set_up_action_seqs>;
    r := rec<fmt |
	get_ege := get_ege, uncond := uncond,
	set_up_action := set_up_action,
	set_up_action_seqs := set_up_action_seqs
    >;

    return r, action;

end intrinsic;

/*

time W := BasisMatrix(Rowspace(VerticalJoin(W,
    Matrix([action(w, G.i): w in Rows(W), i in [1..Ngens(G)]]))));

time repeat OW := W; W := BasisMatrix(Rowspace(VerticalJoin(W,
    Matrix([action(w, G.i): w in Rows(W), i in [1..Ngens(G)]])))); Parent(W);
    until W cmpeq OW;

S:=LLL(Saturation(BasisMatrix(Rowspace(W))));

time M:=GModule(G, [Solution(S, Matrix([action(w, G.i): w in Rows(S)])):
    i in [1..Ngens(G)]]);

*/

intrinsic IndCond(
    G::Grp, HM::ModGrp, K::Grp: Single := false, Nrgens := 20
) -> []
{Induction condensation of HM induced to G, using subgroup K}

    vtime ZReps: info := InternalInductionCondensationSetup(G, HM, K);

    uncond := info`uncond;
    set_up_action := info`set_up_action;

    MQ:=[];
    IQ:=[];
    vprint ZReps: "Set up action";
    vtime ZReps: for i in [1 .. Ngens(G)] do
	q, p := set_up_action(G.i);
	Append(~MQ, q);
	Append(~IQ, p);
    end for;

    L := [info`get_ege(Random(G)): i in [1 .. Nrgens]];
    CM := RModule(L);

    R := BaseRing(HM);
    char0 := Characteristic(R) eq 0;

    if Single and char0 then
	a:=Action(CM);
	a;
	t:=&+[a.i: i in [1..5]];
	vtime ZReps: L:=FactoredMinimalPolynomial(t: Proof:=false);
	vtime ZReps: k:=KernelMatrix(Evaluate(L[1,1], t)); Parent(k);

	W := uncond(k);
	vtime ZReps: S, M:=InductionSpin(W, MQ, IQ: Group := G);
	return [M];
    end if;
    
    vprint ZReps: "CM:", CM;

    verb := GetVerbose("ZMeataxe");

    vprint ZReps: "Decompose";
    vtime ZReps: if char0 then
	D := IntegralDecomposition(CM);
    else
	D := IndecomposableSummands(CM);
	//D := MinimalSubmodules(CM);

	SetVerbose("ZMeataxe", 0);
    end if;

    vprint ZReps: "Remove redundant";
    DD := [];
    for S in D do
	keep := true;
	for T in DD do
	    if Dimension(T) eq Dimension(S) and Dimension(GHom(S, T)) gt 0 then
		keep := false;
		break;
	    end if;
	end for;
	if keep then
	    Append(~DD, S);
	end if;
    end for;
    D := DD;

    vprint ZReps: "Got Decomposition:", D;


    L := [];
    for S in D do
	k := Morphism(S, CM);
	if char0 then
// k; Parent(k);
	    k := LLL(Saturation(k));
	    W := uncond(k);
	    W := LLL(Saturation(W));
	else
// "Spin", Parent(k);
	    W := uncond(k);
	end if;
	IndentPush();
	vtime ZReps: _, M := InductionSpin(W, MQ, IQ: Group := G);
	M;
	IndentPop();
	Append(~L, M);
    end for;

    SetVerbose("ZMeataxe", verb);

    return L;

end intrinsic;
