freeze;

/*******************************************************************************
			    Direct parameters
*******************************************************************************/

MIN_SPIN_VERBOSE := 100;

USE_WANT_TRACES := true;
CHAR_KNAP_LIMIT := 20;
DYN_TRACES_K_ORDER := 20;

/*******************************************************************************
				Imports
*******************************************************************************/

import "reps.m": filter_subgroups_repetition, sort_subgroup_seq;
import "meataxe.m": get_split_degs_char, get_possible_chars_irr_chars,
    get_possible_chars;

/*******************************************************************************
				Verbose
*******************************************************************************/

declare attributes ModRng: dyn_traces_info, get_traces, want_ind;
declare attributes ModRng: tcond_info;

/*******************************************************************************
				Subgroups defs
*******************************************************************************/

SUBGROUPS_DEFAULT := "default";
SUBGROUPS_NEVER := false;
SUBGROUPS_ALWAYS := true;
SUBGROUPS_DONE := "done";

SUBGROUPS_TRY_ALL_DIM := 100;
SUBGROUPS_MAX_ORDER_COUNT := 10;

/*******************************************************************************
				Defines
*******************************************************************************/

Z := IntegerRing();
Q := RationalField();
is_Z := func<R | R cmpeq Z>;

gngens := func<G | Type(G) eq GrpPC select NPCgens(G) else Ngens(G)>;

/*******************************************************************************
				Perm tensor
*******************************************************************************/

function perm_tensor_rep(G, f1, f2)
    assert Domain(f1) cmpeq G;
    assert Domain(f2) cmpeq G;
    P1 := Codomain(f1);
    P2 := Codomain(f2);
    d1 := Degree(P1);
    d2 := Degree(P2);
    dt := d1 * d2;
    St := Sym(dt);

    function ft(g)
	g1 := f1(g);
	g2 := f2(g);

	e := [];
	for i := 1 to d1 do
	    ii := i^g1;
	    b := (ii - 1)*d2;
	    for j := 1 to d2 do
		jj := j^g2;
		Append(~e, b + jj);
	    end for;
	end for;

	return St ! e;
    end function;

    Gt := sub<St | [ft(G.i): i in [1 .. Ngens(G)]]>;
    return Gt, hom<G -> Gt | g :-> ft(g)>;
end function;

/******************************************************************************/
/******************************************************************************/
/******************************************************************************/
/******************************************************************************/

/******************************************************************************/
/******************************************************************************/

/*******************************************************************************
				    Perm cond
*******************************************************************************/

function pcond_image(O, g, F)
    r := #O;

    Z_case := is_Z(F);
    if Z_case then
	lcm := LCM([#o: o in O]);
	scale := [lcm div #O[j]: j in [1 .. r]];
    else
	lcm := 1;
	scale := [F!#O[j]^-1: j in [1 .. r]];
    end if;

    O := [Set(x): x in O];

    Q := [F| ];
    for i := 1 to r do
	Oig := O[i]^g;
	for j := 1 to r do
	    /*
	    if Z_case then
		//x := #(Oig meet O[j]) * (lcm div #O[j]);
		x := IntersectionCardinality(Oig, O[j]) * (lcm div #O[j]);
	    else
		x := F!IntersectionCardinality(Oig, O[j]) / #O[j];
	    end if;
	    Append(~Q, x);
	    */
	    Append(~Q, IntersectionCardinality(Oig, O[j]) * scale[j]);
	end for;
    end for;

    /*
    if Z_case then
	g := GCD(Q);
	if g ne 1 then
	    Q := [x div g: x in g];
	end if;
    end if;
    */

    return MatrixRing(F, r)!Q, lcm;
end function;

function pcond_images(K, O, G, F, n)
    R := {};
    while #R lt n do
	repeat
	    g := Random(G);
	until g notin K;
	Include(~R, g);
    end while;
    return [pcond_image(O, g, F): g in R];
end function;

function pcond(K, G, F, n)
    O := Orbits(K);
    I := pcond_images(K, O, G, F, n);
    M := RModule(I);

    return M;
end function;

/******************************************************************************/
/******************************************************************************/

/*******************************************************************************
				Z/Q funcs for tcond
*******************************************************************************/

toQ := func<X | ChangeRing(X, Q)>;

function clear_nd(X)
    if BaseRing(X) cmpne Q then
	return X, 1;
    end if;
    denom := LCM([Z | Denominator(x): x in Eltseq(X)]);
//"Common denom:", denom;
    if denom ne 1 then
	X := denom*X;
    end if;
    numer := GCD([Z | Numerator(x): x in Eltseq(X)]);
//"Common numer:", numer;
    if numer gt 1 then
	X := X/numer;
    else
	numer := 1;
    end if;
    return Matrix(Z, X), denom/numer;
end function;

/*******************************************************************************
				Iso/constituents
*******************************************************************************/

function is_iso(M, N)
// Only for irreds
    if BaseRing(M) cmpeq Z then
	if Dimension(M) eq Dimension(N) then
	    H := AHom(M, N);
	    if Dimension(H) gt 0 then
		return true, H.1;
	    end if;
	end if;
	return false, _;
    end if;
    return IsIsomorphic(M, N);
end function;

/*******************************************************************************
				Decomp
*******************************************************************************/

function decomp_S(M)
    if BaseRing(M) cmpeq Z then

	G := Group(M);
	G`MeataxeSkipCharacterTable := true;

	L, LSI := IntegralDecomposition(M: WantSubmodules);
//"M:", M: Magma;
//"L:", L;
//"LSI:", LSI;
	assert 0 notin LSI;

	Sort(~L, func<x, y | Dimension(x) - Dimension(y)>);
	C := [];
	B := <>;
	S := [];
	for s in L do
//"Now", C, B, S;
	    seen := false;
	    for i := 1 to #C do
		l, T := is_iso(s, C[i]);
		if l then
//"i:", i;
//"T:", T;
//Determinant(T);
//T:=1;
		    Append(~B[i], toQ(T)^-1 * toQ(Morphism(s, M)));
		    Append(~S[i], s);
		    seen := true;
		    break;
		end if;
	    end for;
	    if not seen then
		Append(~C, s);
		Append(~B, [toQ(Morphism(s, M))]);
		Append(~S, [s]);
	    end if;
	end for;
	S := &cat S;
	C := [<C[i], #B[i]>: i in [1 .. #C]];
	B := <X: X in b, b in B>;
	T := VerticalJoin(B);
	return S, T, C;
    end if;

    C := ConstituentsWithMultiplicities(M);

    B := <b: b in Basis(GHomOverCentralizingField(t[1], M)), t in C>;
    T := VerticalJoin(B);
    S := [ImageWithBasis(b, M): b in B];

    return S, T, C;
end function;

/*******************************************************************************
				Tensor cond
*******************************************************************************/

function tcond_images(M, N, H, G_list)
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

    vprint Condensation: "TENSOR Condensation";
    vprint Condensation: M, N;
    //M: Magma;
    //N: Magma;

    MH := Restriction(M, H);
    NN := 0;

    if 1 eq 0 and Ngens(H) eq 1 then
// This is now WRONG!!! ???  Must handle Dual(N component)
	assert Nagens(MH) eq 1;

	MX := ActionGenerator(MH, 1);
	_, MT, MF := PrimaryRationalForm(lift(MX));
	MTI := lift(MT)^-1;
	MM := lift(M)^MTI;

vprint Condensation: "****";
vprint Condensation: "Single Gen case", M, N, MF;

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

    elif 0 eq 1 then

MS := 0;
NS := 0;
	CH := RationalCharacterTable(H);

	vprint Condensation: "Get MH char", MH;
	vtime Condensation: MHc := Character(MH);
	Mdec := RationalCharacterDecomposition(MHc);
	vprint Condensation: "M Decomposition:", Mdec;

	if M cmpne N then
	    vprint Condensation: "Get NH";
	    vtime Condensation: NH := Restriction(N, H);

	    vprint Condensation: "Get NH char", NH;
	    vtime Condensation: NHc := Character(NH);

	    Ndec := RationalCharacterDecomposition(NHc);
	    vprint Condensation: "N Decomposition:", Ndec;
	else
	    NH := MH;
	    Ndec := Mdec;
	end if;

	want := [i: i in [1 .. #CH] | Mdec[i] gt 0 or Ndec[i] gt 0];
	//want := [i: i in [1 .. #CH] | Mdec[i] gt 0];
	vprint Condensation: "Want indices:", want;

	vprint Condensation: "H chief factors:", ChiefFactors(H);

	/// "Hack H Skip"; H`MeataxeSkipCharacterTable := true;

	vprint Condensation: "Get H reps:";
	IndentPush();
	vtime Condensation: RH := InternalIrreducibleIntegralModules(
	    H: Characters := CH[want]
	);
	IndentPop();

	vprint Condensation: "Got RH:", RH;

	OC := [RH[i, 1]: i in want];

	CCM := [RH[i, 1]: i in want | Mdec[i] gt 0];
	CCN := [RH[i, 1]: i in want | Mdec[i] eq 0];
	CC := CCM cat CCN;
	C := CCM;

	vprint Condensation: "M C:", C;
	vprint Condensation: "Extra N C:", CCN;

	MC := [];
	NC := <>;
	MT := <>;
	NT := <>;
	Ni := 1;
	Np := 1;

time
	for i := 1 to #CC do
	    ci := CC[i];
"i:", i;
IndentPush();
"ci:", ci;
"Get M U"; time
	    U := GHomOverCentralizingField(ci, MH);
"U:", U;
	    ei := Dimension(U);
	    cd := Dimension(ci);

	    if ei gt 0 then

		Append(~MC, <ImageWithBasis(U.1, MH), ei>);
		Append(~MCI, [Mi .. Mi + ei - 1]);
		Append(~Mpos, Mp);
		for h in Basis(U) do
		    Append(~MT, Matrix(h));
		end for;

		Mi +:= ei;
		Mp +:= ei * cd;
	    end if;

"Get N U"; time
	    U := GHomOverCentralizingField(Dual(ci), NH);
U;
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
IndentPop();

	end for;

	"MC:", MC;
	"MCI:", MCI;
	"Mpos:", Mpos;

	"NC:", NC;
	"NCI:", NCI;
	"Npos:", Npos;

	if #MT eq 0 then
	    MT := Matrix(R, 0, Dimension(MH), []);
	else
	    //"join", <Nrows(x): x in MT>; time
	    MT := VerticalJoin(MT);
	end if;
	//"First MT:", MT;

	assert Nrows(MT) eq Dimension(MH);
	MTI := lift(MT)^-1;
	MM := lift(M)^MTI;

	if #NT eq 0 then
	    NT := Matrix(R, 0, Dimension(NH), []);
	else
	    //"join", <Nrows(x): x in NT>; time
	    NT := VerticalJoin(NT);
	end if;
	// "First NT:", NT;

	assert Nrows(NT) le Dimension(NH);
	NTI := lift(NT)^-1;
	NN := lift(N)^NTI;

    else
	MS, MT, MC := decomp_S(MH);

	vprint Condensation: "MH decomp:", MC;

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

//"GHom"; time
		U := GHomOverCentralizingField(Dual(ci), NH);
//printf "i: %o, ci: %o, U: %o\n", i, ci, U;
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
		//"join", <Nrows(x): x in NT>; time
		NT := VerticalJoin(NT);
	    end if;
	    // "First NT:", NT;

	    assert Nrows(NT) le Dimension(NH);
	    if Nrows(NT) lt Dimension(NH) then
		_, _, NHC := decomp_S(NH);
                for cjt in NHC do
		    cj := cjt[1];
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

/*
"MM:", MM: Maximal;
"C:", C: Maximal;

"MC:", MC: Maximal;
"MCI:", MCI;
"Mpos:", Mpos;

"NC:", NC: Maximal;
"NCI:", NCI;
"Npos:", Npos;
"C:", C;
*/

    Q := <>;
    P := <>;

"Setup P, Q"; time
    for i := 1 to #C do
	ci := C[i];
	if i le Min(#MCI, #NCI) and #MCI[i] gt 0 and #NCI[i] gt 0 then
	//if #MCI[i] gt 0 and #NCI[i] gt 0 then
	    //Ms := MS[MCI[i, 1]];
	    //Ns := NS[NCI[i, 1]];
	    Ms := MC[i, 1];
	    Ns := NC[i, 1];
//"Ms:", Ms;
//"Ns:", Ns;
	    Mrep := Representation(Ms);
	    Nrep := Representation(Ns);
	    // E := &+[TensorProduct(Mrep(h), Nrep(h)): h in H];
	    E := 0;
	    for h in H do
		E +:= TensorProduct(Mrep(h), Nrep(h));
	    end for;
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

    //"P:", P;
    //"Q:", Q;

//"MM:", MM: Maximal;

    MCL := [#q: q in MCI];
    NCL := [#q: q in NCI];

    //d := &+[Z | MCL[i] * NCL[i] * Nrows(Q[i]): i in [1 .. #C]];
    d := &+[Z | MCL[i] * NCL[i] * Nrows(Q[i]): i in [1 .. Min(#MCL, #NCL)]];

//"d:", d;

    function get_images(MM, NN)
	MMrep := Representation(MM);
	NNrep := Representation(NN);

	F := BaseRing(MM);
	PF := <Matrix(F, x): x in P>;
	QF := <Matrix(F, x): x in Q>;

	L := [];

	for g in G_list do
	    //"Gen", g;
	    X := MatrixRing(K, d) ! 0;

	    Mg := MMrep(g);
	    Ng := NNrep(g);

	    if 1 eq 1 then

		X := InternalTensorProductAction(
		    Mg, Ng, <C, MCL, NCL, Mpos, Npos, PF, QF>
		);
	    else

	    Xi := 1;
	    for i := 1 to #C do
		ci := C[i];
		cid := Dimension(ci);
		qi := QF[i];

		Mipos := Mpos[i];
		for mi in MCI[i] do

		    //Mgi := RowSubmatrix(Mg, Mipos, cid);

		    Nipos := Npos[i];
		    for ni in NCI[i] do

			//Ngi := RowSubmatrix(Ng, Nipos, cid);

			Xj := 1;
			for j := 1 to #C do
			    cj := C[j];
			    cjd := Dimension(cj);

			    pj := PF[j];
			    Mjpos := Mpos[j];
			    for mj in MCI[j] do
				Njpos := Npos[j];
				for nj in NCI[j] do

				    MB := Submatrix(Mg, Mipos, Mjpos, cid, cjd);
				    NB := Submatrix(Ng, Nipos, Njpos, cid, cjd);
				    B := TensorProduct(MB, NB);
				    BB := qi*B*pj;

				    InsertBlock(~X, BB, Xi, Xj);
				    Xj +:= Ncols(pj);

				    Njpos +:= cjd;
				end for; // for nj

				Mjpos +:= cjd;
			    end for; // for mj

			end for; // for j

			Xi +:= Nrows(qi);
			Nipos +:= cid;
		    end for; // for ni

		    Mipos +:= cid;
		end for; // for mi

	    end for; // for i
	    end if;

	    //"X:", X;

	    Append(~L, X);
	end for;
	return L;
    end function;

    if Type(K) eq FldRat then
	p := Floor(2^23.5);
	P := 1;
	sij := <1, 1>;
	pi := 0;
	while true do
	    pi +:= 1;
	    p := PreviousPrime(p);
	    F := GF(p);
	    vprintf Condensation: "Prime %o: %o\n", pi, p; vtime Condensation:
	    Lp := get_images(ChangeRing(MM, F), ChangeRing(NN, F));
	    Lp := [Matrix(Z, X): X in Lp];
	    // "Lp traces:", [Trace(x): x in Lp];
	    if P eq 1 then
		LP := Lp;
	    else
		LP := [CRT([LP[i], Lp[i]], [P, p]): i in [1 .. #LP]];
	    end if;
	    P *:= p;
	    db := Isqrt(P) div 1000;
	    if db eq 0 then continue; end if;
	    nb := db;
	    L := [];
	    for X in LP do
		// printf "Try RR; P: %o, nb: %o, db: %o\n", P, nb, db;
		Y, nsij := RationalReconstruction(
		    X, P, nb, db, RationalField(), sij
		);
		if Y cmpeq 0 and not IsZero(X) then
		    vprintf Condensation: "Fail RR (P %o)\n", P;
		    break;
		end if;
		Append(~L, Y);
	    end for;
	    delete Lp, Y;
	    if #L eq #LP then break; end if;
	    delete L;
	end while;
    else
	L := get_images(MM, NN);
    end if;

    LCM := [];
    if over_Z then
	OL := L;
	L := [];
	for Y in OL do
	    X, lcm := clear_nd(Y);
	    Append(~L, X);
	    Append(~LCM, lcm);
	end for;
    end if;

    info := <M, N, MT, NT, C, MCI, Mpos, NCI, Npos, Q, MM, NN>;
    return L, LCM, info;
end function;

function tuncond(info, V)

    R := BaseRing(V);

// "uncond V:", V;
// "uncond info:", info;

    M, N, MT, NT, C, MCI, Mpos, NCI, Npos, Q := Explode(info);

    K := FieldOfFractions(R);

    Md := Dimension(M);
    Nd := Dimension(N);

    U := RMatrixSpace(K, Nrows(V), Md*Nd) ! 0;

    for r := 1 to Nrows(V) do

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

		    v := Submatrix(V, r, Xi, 1, Nrows(qi));
		    v := Matrix(K, v) * Matrix(K, qi);

		    pos := 1;
		    for k := 1 to cid do
			//printf "Copy %o, len %o to %o\n", pos, cid, upos;
			InsertBlock(~U, Submatrix(v, 1, pos, 1, cid), r, upos);
			upos +:= Nd;
			pos +:= cid;
		    end for;

		    Xi +:= Nrows(qi);
		    Nipos +:= cid;
		end for; // for ni
		Mipos +:= cid;
	    end for; // for mi
	end for; // for i
    end for;

    U := clear_nd(U);

    //if BaseRing(T) cmpeq RationalField() then
    if K cmpeq RationalField() then
// DUMB: only do if some denom
	U := toQ(U);
	MT := toQ(MT);
	NT := toQ(NT);
    end if;

    U := TensorProductAction(U, Transpose(ChangeRing(MT, K)), ChangeRing(NT, K));
    U := clear_nd(U);

    return U;
end function;


/*******************************************************************************
				    Perm uncond
*******************************************************************************/

function puncond_basis_mat(B, P, K)

    B := Matrix(B);
    O := Orbits(K);
    r := #O;

    F := BaseRing(Parent(B));
    n := Degree(P);

    if is_Z(F) then
	vprint ZReps, 2: "Condensed basis norms:", Norms(B);
	vprint ZReps, 2: "LLL condensed basis";
//vprint ZReps: "Cond B:", B;
	vtime ZReps, 2: B := LLL(B);
//vprint ZReps: "Cond LLL B:", B;
	vprint ZReps, 2: "New condensed basis norms:", Norms(B);
    end if;

    d := Nrows(B);
    U := RMatrixSpace(F, d, n) ! 0;
    for i := 1 to d do
	for j := 1 to r do
	    x := B[i, j];
	    if x ne 0 then
		for k in O[j] do
		    U[i, k] := x;
		end for;
	    end if;
	end for;
    end for;

    return U;
end function;

function puncond_basis(S, M, G, K)
    // return puncond_basis_mat(Morphism(S, M), G, K);

    H := AHom(S, M);
    d := Dimension(H);
    vprintf ZReps: "Hom from submodule has dim %o\n", d;
    B := Basis(H);
    B := [puncond_basis_mat(x, G, K): x in B];
    vprint ZReps: "uncond norms:", [Norms(x): x in B];
    B := LLL(B: Proof := false, Sort);
    vprint ZReps: "LLL uncond norms:", [Norms(x): x in B];
    return B[1];
end function;

function puncond(S, M, G, K:
    mod_G := G, want_submod := 0, want_B := false, expect_dim := 0
)
    L := [G.i: i in [1..Ngens(G)]];
    if ISA(Type(S), Mtrx) then
	vprintf ZReps: "Get uncondensed basis of dimension %o\n", Nrows(S);
	vtime ZReps: U := puncond_basis_mat(S, G, K);
    else
	vprintf ZReps: "Get uncondensed basis of dimension %o\n", Dimension(S);
	vtime ZReps: U := puncond_basis(S, M, G, K);
    end if;
    if is_Z(BaseRing(S)) then
	vprint ZReps, 2: "Uncondensed norms:", Norms(U);
	vprint ZReps, 2: "LLL uncondensed basis";
//vprint ZReps, 1: "Uncondensed input:", U;
	vtime ZReps, 2: U := LLL(U);
	vprint ZReps, 1: "Uncondensed LLL norms:", Sort(Norms(U));

//vprint ZReps, 1: "Uncondensed LLL input:", U;

//U := Matrix(U[1]);
    end if;
    vprintf ZReps: "Perm spin uncondensed basis of dimension %o (degree %o)\n",
	Nrows(U), Ncols(U);
    if expect_dim gt 0 then
	vprintf ZReps: "Expecting spin dimension %o\n", expect_dim;
    end if;

    verb := GetVerbose("ZMeataxe");
    if expect_dim lt MIN_SPIN_VERBOSE then
	SetVerbose("ZMeataxe", 0);
    end if;

    B := 0;
    if want_submod cmpne 0 then
	vtime ZReps: B := Spin(U, L);
	vtime ZReps: M := sub<want_submod | RowSpace(B)>;
    else
want_B:=true;
	if want_B then
	    vtime ZReps: M, B := SpinAction(U, L);
	else
	    vtime ZReps: M := SpinAction(U, L);
	end if;
	M := GModule(mod_G, M: Check := false);
    end if;

    SetVerbose("ZMeataxe", verb);

    return M, B;
end function;

/*******************************************************************************
				Wrapper functions
*******************************************************************************/

condfmt := recformat<Image, CondensedModule, Uncondense, UncondenseSpin>;

function get_v(CM, v)
    if ISA(Type(v), ModRng) then
	return Morphism(v, CM);
    elif ISA(Type(v), ModRngElt) then
	return Matrix(CM ! v);
    end if;
    return Matrix(v);
end function;

intrinsic PermutationCondensation(G::Grp, f::Map, K::Grp, F::Rng) -> Rec
{Set up permutation condensation for group G, perm rep f: G->P (for perm
group P), w.r.t. condensation subgroup K, over ring R}

    require Domain(f) cmpeq G: "Domain of rep map is not G";

    p := Characteristic(F);
    require p eq 0 or GCD(#K, p) eq 1: "Order of group not coprime with #F";

    //O := Orbits(K);
    fK := f(K);
    O := Orbits(fK);

    function Image(g)
	return pcond_image(O, f(g), F);
    end function;

    P := Codomain(f);
    function CondensedModule(ng)
	L := [Image(Random(G)): i in [1 .. ng]];
	M := RModule(L);
	return M;
    end function;

    function Uncondense(CM, v)
	// return puncond_basis(get_v(CM, v), CM, P, fK);
	return puncond_basis_mat(get_v(CM, v), P, fK);
    end function;

    function UncondenseSpin(CM, v)
	return puncond(get_v(CM, v), CM, P, fK: mod_G := G);
    end function;

    R := rec<condfmt |
	Image := Image, CondensedModule := CondensedModule,
	Uncondense := Uncondense, UncondenseSpin := UncondenseSpin
    >;
    return R;

end intrinsic;

intrinsic TensorCondensation(M1::ModGrp, M2::ModGrp, K::Grp) -> Rec
{Set up tensor condensation for M1, M2, w.r.t. condensation subgroup K}

    G := Group(M1);
    F := BaseRing(M1);
    p := Characteristic(F);

    require Group(M2) cmpeq G: "Different groups";
    require p eq 0 or GCD(#K, p) eq 1: "Order of group not coprime with #F";

    d1 := Dimension(M1);
    d2 := Dimension(M2);

    function Image(g)
	error "Individual image not supported at moment";
	return 0;
    end function;

    function CondensedModule(ng)
	L := [Random(G): i in [1 .. ng]];
	I, I_lcm, info := tcond_images(M1, M2, K, L);
	CM := RModule(I);
	CM`tcond_info := info;
	return CM;
    end function;

    function Uncondense(CM, v)
	info := CM`tcond_info;
	v := get_v(CM, v);
	w := tuncond(info, v);
	return w;
    end function;

    function UncondenseSpin(CM, v)
	w := Uncondense(CM, v);
	if is_Z(BaseRing(v)) then
	    w := Saturation(w);
	    w := LLL(w: Delta := 0.999, Proof := false);
	end if;
	R := SpinAction(w, Transpose(M1), M2);
	R := GModule(G, R: Check := false);
	return R;
    end function;

    R := rec<condfmt |
	Image := Image, CondensedModule := CondensedModule,
	Uncondense := Uncondense, UncondenseSpin := UncondenseSpin
    >;
    return R;

end intrinsic;

intrinsic InductionCondensation(G::Grp, MH::ModGrp, K::Grp) -> Rec
{Set up condensation for Induction(MH, G) via subgroup K}

    require Group(MH) subset G: "H is not subgroup of G";
    require K subset G: "K is not subgroup of G";

    F := BaseRing(MH);
    p := Characteristic(F);
    require p eq 0 or GCD(#K, p) eq 1: "Order of K not coprime with #F";

    info, action := InternalInductionCondensationSetup(G, MH, K);

    function Image(g)
	return info`get_ege(g);
    end function;

    function CondensedModule(ng)
	L := [Image(Random(G)): i in [1 .. ng]];
	M := RModule(L);
	return M;
    end function;

    MQ, IQ := info`set_up_action_seqs([G.i: i in [1 .. Ngens(G)]]);

    function Uncondense(CM, v)
	v := get_v(CM, v);
	w := info`uncond(v);
	return w;
    end function;

USE_NEW_SPIN := true;
USE_NEW_SPIN := false;

    l, NewSpinAction := IsIntrinsic("NewSpinAction");
    USE_NEW_SPIN := USE_NEW_SPIN and l;

    function UncondenseSpin(CM, v: RankEstimate := 0)
	w := Uncondense(CM, v);
	if is_Z(BaseRing(v)) then
	    w := Saturation(w);
	    w := LLL(w: Delta := 0.999, Proof := false);
	end if;

	if USE_NEW_SPIN and RankEstimate gt 0 then
	    vprint Condensation:
		"Ind UncondenseSpin: try NewSpinAction with RankEstimate",
		RankEstimate;

	    L := NewSpinAction(w, <G, action>, RankEstimate);
	    if L cmpne 0 then
		return GModule(G, L: Check := false);
	    end if;

	    vprint Condensation:
		"Ind UncondenseSpin: fail NewSpinAction; use normal ind spin";
	end if;

	S, R := InductionSpin(w, MQ, IQ: Group := G, Saturate);
	return R;
    end function;

    R := rec<condfmt |
	Image := Image, CondensedModule := CondensedModule,
	Uncondense := Uncondense, UncondenseSpin := UncondenseSpin
    >;
    return R;

end intrinsic;

/*******************************************************************************
				Auto Character Cond
*******************************************************************************/

CCOND_PERM := 1;
CCOND_TENS := 2;
CCOND_IND := 3;

//forward char_decomp;

transversal_indices := func<K, g, f, cf | [cf(f(g*x)): x in K]>;

function cond_traces_Kg(Kg, C)
    n := #Kg;
    return [&+[c[i]: i in Kg]/n: c in C];
end function;

function cond_traces(K, g, C, f, cf)
    return cond_traces_Kg(transversal_indices(K, g, f, cf), C);
end function;

procedure ccond(
    CG, ccond_kind, M_char, info, ~AllSubgroups, ~G_subgroups, ~RQ, ~BQ:
	f := Coercion(CG, CG),		// f: (orig G) -> CG
	MaxCond := 100, MinCond := 1, CondTarget := 0,
	// MaxCond := 200, MinCond := 150,
	MaxUncond := 0,
	MaxTries := 0,
	NumRand := 10,
	HardGroup := false,
	IrrChars := {},
	SeenChars := {},
	WantChars := [],
	WantSchurIndices := [],
	SplitChars := [],
	SplitSchurIndices := [],
	FullWantChars := [],
	FullSplitChars := [],
	FullCharTable := 0,
	DynTraces := false,
	AllowDenoms := false,
	Blackbox := false
)
/*
CG: original external G which is used for classes and result modules.
G: group to condense (perm rep in perm case).
f: G -> CG.
*/

    perm := ccond_kind eq CCOND_PERM;
    tcond := ccond_kind eq CCOND_TENS;
    icond := ccond_kind eq CCOND_IND;

    if icond then
	HM, M_char := Explode(info);
	G := CG;

	vprint ZReps: "**** INDUCTION COND ****";

	H := Group(HM);
	index := Index(G, H);
	vprintf ZReps:
	    "#H: %o, index: %o, H rep dim: %o\n", #H, index, Dimension(HM);

	vprint ZReps: "H rep:", HM: Maximal;

	function make_full_rep()
	    IM := Induction(HM, G);
	    IM`Character := M_char;
	    return IM;
	end function;

    elif tcond then
	M1, M2 := Explode(info);
	G := CG;

	vprint ZReps: "**** TENSOR COND ****";

	d1 := Dimension(M1);
	d2 := Dimension(M2);
	vprintf ZReps: "Module dims: %o, %o, product: %o\n",
	    d1, d2, d1*d2;

	function make_full_rep()
	    TM := TensorProduct(M1, M2);
	    TM`Character := M_char;
	    return TM;
	end function;
    else
	/*
	G used for perm condensation.
	f: G -> CG; classes w.r.t. CG.
	*/

	G := info;

	vprint ZReps: "**** PERM COND ****";
	vprintf ZReps: "Perm rep degree: %o\n", Degree(G);

	function make_full_rep()
	    P := GModule(CG, G, Z);
	    P`Character := M_char;
	    return P;
	end function;
    end if;
    H := 0;

    vprint ZReps: "M_char:", M_char;

    split_count := &+[Z | t[2]: t in SplitChars];
    split_base_count := #SplitChars;

    vprint ZReps: "Want chars:", WantChars;
    vprint ZReps: "Want Schur indices:", WantSchurIndices;
    vprint ZReps: "Split Schur indices:", SplitSchurIndices;
    vprint ZReps: "Decomposition degrees:",
	[ <Degree(t[1]), t[2]>: t in SplitChars ];
    vprint ZReps: "Decomposition multiset:",
	{* Degree(t[1])^^t[2]: t in SplitChars *};
    vprint ZReps: "Decomposition base count:", split_base_count;
    vprint ZReps: "Decomposition count:", split_count;
    vprint ZReps: "SplitChars:", SplitChars;

    if Type(WantChars) ne SeqEnum then
	WantChars := [x: x in WantChars];
	assert FullWantChars eq 0;
    end if;

/*
pointless; already sorted, I think.
"first SplitChars:", SplitChars;
    Sort(~SplitChars, func<x, y | Degree(x[1]) - Degree(y[1])>);
"sorted SplitChars:", SplitChars;
*/
    SC := [t[1]: t in SplitChars];
    WantIndex := [Index(SC, c): c in WantChars];
    non_scaled_C := WantChars;

SCALE_BY_SI := true;

    if SCALE_BY_SI then
	assert #SplitSchurIndices eq #SplitChars;
	for i := 1 to #SplitSchurIndices do
	    t := SplitChars[i];
	    si := SplitSchurIndices[i];
	    q := ExactQuotient(t[2], si);
	    t[2] := q;
	    t[1] := si*t[1];
	    SplitChars[i] := t;
	end for;

	for i := 1 to #WantIndex do
	    assert SplitSchurIndices[WantIndex[i]] eq WantSchurIndices[i];
	    WantChars[i] := WantChars[i] * SplitSchurIndices[WantIndex[i]];
	end for;

	// "Scaled SplitChars:", SplitChars; "Scaled WantChars:", WantChars;

	SC := [t[1]: t in SplitChars];

    end if;

    C := WantChars;
    assert #Set(C) eq #C;
    want_chars := #C gt 0;

    num_rand := NumRand;
    F := Z;

    best_K := 0;
    best_dim := 0;
    best_D := [Z|];
    D := [];

    SEARCH_TIME := Cputime();

    classes := Classes(CG);
    cf := ClassMap(CG);

    SEARCH_STOP_CLASSES := 100;
    SEARCH_STOP := 100;
//SEARCH_STOP_CLASSES := 20;
//SEARCH_STOP := 20;

//"HEY!!!!!!!!!!!!!!"; SEARCH_STOP_CLASSES := 150; SEARCH_STOP := 150;

    if #G le 100000 then
	ORDER_LIMIT := 2000;
    else
	ORDER_LIMIT := 2000;
    end if;

    procedure try_subgroup(K, ~best_dim, ~best_K, ~best_D, ~new_best)

	new_best := false;
	if #K gt ORDER_LIMIT then
	    return;
	end if;

	if icond or tcond then
	    K1c := CharacterRing(K)!1;
	    td := Z!InnerProduct(Restriction(M_char, K), K1c);
	elif tcond then
	    SD := cond_traces(K, G!1, SC, f, cf);
	    SD := [<SD[i], SplitChars[i, 2]>: i in [1 .. #SD]];
	    td := &+[t[1]*t[2]: t in SD];
	else
	    if Ngens(K) eq 1 then
		td := &+[t[2]: t in CycleStructure(K.1)];
	    else
		td := #Orbits(K);
	    end if;
	end if;

// printf "#K: %o, td: %o\n", #K, td;

	if best_K cmpne 0 then
	    if CondTarget gt 0 then
		td_diff := Abs(td - CondTarget);
		best_diff := Abs(best_dim - CondTarget);
// printf "td: %o, diffs: %o, %o\n", td, td_diff, best_diff;
		if td_diff ge best_diff then
		    return;
		end if;
	    else
		if td ge best_dim or td lt MinCond then
		    return;
		end if;
	    end if;
	end if;

	if icond or tcond then
	    D := [Z | InnerProduct(Restriction(c, K), K1c): c in C];
	elif tcond then
	    D := [SD[i, 1]: i in WantIndex];
	else
	    D := cond_traces(K, G!1, C, f, cf);
	end if;

	vprintf ZReps, 2: "    Condensed dimension: %o, char dims: %o\n", td, D;
	if not forall{d: d in D | d ne 0} then
	    return;
	end if;

	best_K := K;
	best_D := D;
	best_dim := td;
	new_best := true;

	vprintf ZReps: "    NEW BEST: dim %o", td;
	if CondTarget gt 0 then
	    vprintf ZReps: " (distance %o)", Abs(td - CondTarget);
	end if;
	vprintf ZReps: ", order: %o, char dims: %o\n", #K, D;
    end procedure;

    function new_stop(dim, D)
	return dim le 200 and CondTarget eq 0 and #D gt 0 and Max(D) le 20;
    end function;

    stopped := false;

if 1 eq 1 then

    /* New maximal subgroups search */

    Md := Z!Degree(M_char);
    if Md ge 500000 then
	MaxCdim := 800;
	min_ord := Round(0.8 * Md/MaxCdim);
MaxCdim:=800;
    elif Md ge 200000 then
	MaxCdim := 300;
	min_ord := Round(0.8 * Md/MaxCdim);
MaxCdim:=400;
    else
	MaxCdim := 200;
	min_ord := Round(0.9 * Md/MaxCdim);
    end if;

    while min_ord gt 1 and #G mod min_ord ne 0 do
	min_ord -:= 1;
    end while;

    vprintf ZReps: "Md: %o, target max cdim: %o, min order: %o\n",
	Md, MaxCdim, min_ord;

    //range := 
    L := [G];
    while #L gt 0 do
	H := L[#L];
	acdim := Round(Md/#H);
	vprintf ZReps: "Queue len: %o, H order: %o, approx cdim: %o\n",
	    #L, #H, acdim;
	Prune(~L);

	try_subgroup(H, ~best_dim, ~best_K, ~best_D, ~new_best);
	if best_dim gt 0 and best_dim le MaxCdim then
	    vprint ZReps: "Break out with best dim", best_dim;
	    break;
	end if;

	IndentPush();
	vprint ZReps: "Get ms";
//"H:", H;
	vtime ZReps: ms := MaximalSubgroups(H);
	ms := [x`subgroup: x in ms];
	ms := [x: x in ms | #x ge min_ord];
	vprint ZReps: "New subgroup orders:", {* #x: x in ms *};
	IndentPop();
	L cat:= ms;
	Sort(~L, func<a, b | #b - #a>);
    end while;

else

    if Type(G) in {GrpPerm, GrpMat} then
	if Type(G) eq GrpMat then
	    H := Stabilizer(G, RSpace(G).1);
	else
	    H := Stabilizer(G, 1);
	end if;

	if 1 eq 1 and #H le 300 then
	    vprintf ZReps: "Try stabilizer of order %o\n", #H;
	    try_subgroup(H, ~best_dim, ~best_K, ~best_D, ~new_best);
	end if;
    end if;

    if
	AllSubgroups cmpne SUBGROUPS_ALWAYS and
	AllSubgroups cmpne SUBGROUPS_DONE
    then
	primes := PrimeBasis(#G);
	vprintf ZReps: "Search Sylow subgroups for primes %o\n", primes;
	count := 0;
	for p in primes do
	    Gp := Sylow(G, p);
	    while true do
		if best_dim gt 0 and best_dim le SEARCH_STOP_CLASSES then
//"NOW", best_dim, SEARCH_STOP_CLASSES;

		    vprintf ZReps: "Stop after %o Sylow tri(es)\n", count;
		    stopped := true;
		    break p;
		end if;
		count +:= 1;
		vprintf ZReps, 1: "Sylow try %o: order %o\n", count, #Gp;
		if 0 eq 1 and #Gp gt 300 then
		    vprint ZReps, 1: "Skip";
		else
		    try_subgroup(Gp, ~best_dim, ~best_K, ~best_D, ~new_best);
		end if;
		if IsPrime(#Gp) then
		    break;
		end if;
		Gp := MaximalSubgroups(Gp)[1]`subgroup;
	    end while;
	end for;
    end if;

    if
	AllSubgroups cmpne SUBGROUPS_ALWAYS and
	AllSubgroups cmpne SUBGROUPS_DONE
    then
	vprintf ZReps: "Search %o cyclic groups from classes\n", #classes;
	count := 0;
	for ci := #classes to 1 by -1 do
	    if best_dim gt 0 and best_dim le SEARCH_STOP_CLASSES then
		vprintf ZReps: "Stop after %o class(es)\n", count;
		stopped := true;
		break;
	    end if;
	    count +:= 1;
	    o, _, g := Explode(classes[ci]);
	    g := g @@ f;
	    vprintf ZReps, 2: "Class %o: order %o\n", ci, o;
	    try_subgroup(sub<G | g>, ~best_dim, ~best_K, ~best_D, ~new_best);
	end for;
    end if;

    if AllSubgroups cmpeq SUBGROUPS_DEFAULT then
	//get_all := best_dim ge SUBGROUPS_TRY_ALL_DIM;
	get_all := not HardGroup and /* not stopped */
	    not new_stop(best_dim, best_D) and
	    #G le 100000;
    elif AllSubgroups cmpeq SUBGROUPS_ALWAYS then
	get_all := true;
    elif AllSubgroups cmpeq SUBGROUPS_NEVER then
	get_all := false;
    else
	assert AllSubgroups cmpeq SUBGROUPS_DONE;
	get_all := false;
    end if;

    if get_all then
	vprint ZReps: "*** GET ALL subgroups of G";
	vtime ZReps: G_subgroups := [H`subgroup: H in Subgroups(CG)];
	vprintf ZReps: "Got %o subgroup(s)\n", #G_subgroups;
	G_subgroups := filter_subgroups_repetition(
	    G_subgroups, SUBGROUPS_MAX_ORDER_COUNT
	);
	vprintf ZReps: "Filtered to %o subgroup(s)\n", #G_subgroups;
	AllSubgroups := SUBGROUPS_DONE;
    end if;

    S := G_subgroups;
    S := Sort(S, func<G, H | #G - #H>);

    vprintf ZReps: "Try %o subgroup(s)\n", #S;
    ZEIT := Cputime();
    seen_orders := {};
    count := 0;
    count_nothing_new := 0;
    for H in S do
	if new_stop(best_dim, best_D) then
	    break;
	end if;

	count +:= 1;
	if count ge 100 and best_dim le SEARCH_STOP then
	    break;
	end if;

	/*
	if count_nothing_new ge 10 and #H ge 10*#best_K then
	    break;
	end if;
	*/

	if #H notin seen_orders then
	    vprintf ZReps, 2: "Order %o, %o\n", #H, Cputime(ZEIT);
	end if;
	Include(~seen_orders, #H);

	if #H gt ORDER_LIMIT then
	    continue;
	end if;

	//HH := perm select H else H @@ f;
	HH := perm select H @@ f else H;
	try_subgroup(HH, ~best_dim, ~best_K, ~best_D, ~new_best);
	if new_best then
	    count_nothing_new := 0;
	else
	    count_nothing_new +:= 1;
	end if;
    end for;

/*
	//if best_dim gt MaxCond then
	if best_dim gt Min(MaxCond, 300) then
	    FO := FactoredOrder(G);
	    loop := 0;
	    tries := 0;
	    repeat
		loop +:= 1;
		for i := 1 to #FO do
		    KK := SylowSubgroup(G, FO[i, 1]);
		    vprintf ZReps:
			"KK order: %o, best dim: %o\n", #KK, best_dim;
		    jrange := loop eq 1 select 1 else 5;
		    for j := 1 to jrange do
			tries +:= 1;
			if j eq 1 then
			    K := KK;
			else
			    K := sub<KK | [Random(KK): k in [1..2]]>;
			end if;

			try_subgroup(K, ~best_dim, ~best_K, ~best_D, ~new_best);

			if
			    not good and MaxTries gt 0 and tries ge MaxTries and
				best_dim gt MaxCond
			then
			    vprintf ZReps: "Give up: %o tries\n", tries;
			    vprint ZReps: "Search time: ", Cputime(SEARCH_TIME);
			    return [], [];
			end if;

			if FO[i, 1] eq 1 then
			    break;
			end if;
		    end for;
		end for;
	    until best_dim le MaxCond;
	end if;
    end if;
*/
end if;

    K := best_K;
    CD := best_D;
    no_split := #CD eq 1 and CD[1] eq best_dim and not Blackbox;

    vprint ZReps, 2: "****";
    vprint ZReps: "Search time:", Cputime(SEARCH_TIME);
    vprint ZReps: "Subgroup Order:", #K;
    vprint ZReps: "Condensed DIM:", best_dim;

    // K:=sub<G|>; best_dim := Degree(M_char);
    // if 0 eq 1 and #K eq 1 and Type(G) ne GrpPC then
    if 1 eq 1 and not Blackbox and #K eq 1 /*and Type(G) ne GrpPC*/ then
	assert best_dim eq Degree(M_char);
	vprint ZReps: "No condensation; set up full rep";
	vtime ZReps: M := make_full_rep();

	vprint ZReps: "Direct Meataxe";
	RQ, BQ := IntegralDecomposition(
	    M: WantChars := non_scaled_C
	    // , WantSubmodules := false??
	);
	return;
    end if;

    use_traces := false;
    use_traces := true;
    dyn_traces := DynTraces and #K gt DYN_TRACES_K_ORDER;
    if dyn_traces then
	use_traces := false;
    end if;

    num_rand := 15;
    if #G le 10000 then
	num_rand := 20;
	vprintf ZReps: "*** CHANGE num_rand to %o for small group order\n",
	    num_rand, #G;
    elif true and Max(WantSchurIndices) gt 1 then
	num_rand *:= 2;
	vprintf ZReps: "*** CHANGE num_rand to %o for SI\n", num_rand;
    end if;

    num_extra := 0;

    if split_count gt 40 then
	vprint ZReps: "Large split_count";
	num_rand := Max(num_rand, split_count div 3);
    end if;

    num_rand := Max(num_rand, 2*split_base_count);

    if 0 eq 1 and (best_dim le 40 /*or dyn_traces*/) then
	vprint ZReps: "Inc num_rand for small dim";
	num_rand := Max(num_rand, 30);
    end if;

    if no_split then
	num_rand := 1;
	vprint ZReps: "No split needed";
    end if;

    if tcond then
	num_rand *:= 2;
    end if;

    vprint ZReps: "Number of rand elts:", num_rand;

    if perm then
	O := Orbits(K);
    elif icond then
	icond_info := InternalInductionCondensationSetup(G, HM, K);
    end if;

//"G:", G;
//"K:", K;

    while true do

	SETUP_TIME := Cputime();

	if tcond then
	    R := {};
	    while #R lt num_rand do
		repeat
		    g := Random(G);
		until g notin K and g notin R;
		Include(~R, g);
	    end while;
	    R := Setseq(R);
	    I, I_lcm, info := tcond_images(M1, M2, K, R);
	else
	    seen := {};
	    I := [];
	    I_lcm := [];

	    R := [];
	    RR := {};
	    init_R := [];
	    if 0 eq 1 then
		init_R := Reverse([t[3]: t in Classes(G) | t[3] notin K]);
	    end if;

	    vprintf ZReps: "Get ege for %o rand element(s)\n", num_rand;

	    fail := 0;
	    t0count := 0;
	    vtime ZReps: while #R lt num_rand or #init_R gt 0 do
		repeat
		    if #init_R gt 0 then
			g := init_R[#init_R];
			Prune(~init_R);
		    //"init_R:", #init_R;
		    else
			g := Random(G);
		    end if;
		until g notin K and g notin RR;
		Include(~RR, g);
		if #RR + #K ge #G then
		    break;
		end if;
		if perm then
		    X, lcm := pcond_image(O, g, F);
		else
		    X := icond_info`get_ege(g);
		    lcm := #K;
		end if;
		if IsZero(X) then
		    vprint ZReps: "zero fail", fail;
		    fail +:= 1;
		    if fail ge 20*num_rand and #R gt 5 then
			break;
		    end if;
		    continue;
		end if;
//"non-zero", #R, Trace(X);
		if Trace(X) eq 0 then
		    t0count +:= 1;
		    if t0count le 5 then
			continue;
		    end if;
		end if;

		t := <X, lcm>;
		if t notin seen then
// "good g:", g; "Order:", Order(g); "Class:", ClassMap(G)(g);
		    Include(~seen, t);
		    Append(~R, g);
		    Append(~I, X);
		    Append(~I_lcm, lcm);
		    vprintf ZReps: "Got generator %o, trace %o\n", #R, Trace(X);
		else
		    fail +:= 1;
		    if fail ge 20*num_rand then
			break;
		    end if;
		end if;
	    end while;

	    vprintf ZReps:
		"Final num gens: %o, num fail: %o, t0count: %o\n",
		#R, fail, t0count;
	end if;
//I;
	traces := [Trace(x): x in I];
	vprint ZReps: "Matrix Traces:", traces;

	if false and #K gt 1 and Set(traces) eq {0} and num_rand lt 100 then
	    vprint ZReps: "Traces all zero; get more gens";
	    num_rand *:= 2;
	    vprint ZReps: "Move num_rand to", num_rand;
	    continue;
	end if;

	SETUP_TIME := Cputime(SETUP_TIME);
	vprint ZReps: "Condensed gens setup time:", SETUP_TIME;
	vprint ZReps: "Number of gens:", #R;

	for i := 1 to num_extra do
	    X := &+[Random({-2,-1,1,2})*Y: Y in I];
	    Append(~I, X);
"Extra", i, X;
	    Append(~I_lcm, I_lcm[1]);
	end for;

//"I_lcm:", I_lcm;

	if not want_chars or not use_traces /*or dyn_traces*/ then
	    break;
	end if;

	TT := Cputime();

	invert := func<T | [[T[i, j]: i in [1 .. #T]]: j in [1 .. #T[1]]]>;
	Kg := [transversal_indices(K, g, f, cf): g in R];

	get_traces := func<C |
	    invert(
		[[I_lcm[i]*t: t in cond_traces_Kg(Kg[i], C)]: i in [1..#I]]
	    )
	>;

	// "M_char traces:", get_traces([M_char]);

	ST := get_traces(SC);
	CT := [ST[i]: i in WantIndex];
	/*
	CT := get_traces(C);
	assert CT eq [ST[i]: i in WantIndex];
	*/

	vprint ZReps, 1: "Traces time:", Cputime(TT);

	OST := [<ST[i], SplitChars[i, 2]>: i in [1 .. #ST]];
	//vprint ZReps, 1: "CT:", CT;
	//vprint ZReps, 1: "OST:", OST;

	if #Set(CT) eq #CT then
	//if #Set(ST) eq #ST then
	    break;
	end if;

	vprint ZReps: "Condensed traces not distinct!", CT;
	vprint ZReps: "CT:", CT;
	vprint ZReps: "ST:", ST;

	//num_rand +:= 1;
	num_rand := num_rand + num_rand div 2;
	vprint ZReps: "Move num_rand to", num_rand;
    end while;

    TM := RModule(I);
//"Condensed module TM:"; TM: Magma;

    WantDTraces := [Z| ];
    SplitDTraces := [Z| ];
    SD := 0;

    no_split := false;
    if want_chars then
	/*
	CD := cond_traces(K, G!1, C, f, cf);
	CD := ChangeUniverse(CD, Z);
	assert CD eq best_D;
	*/
	vprint ZReps: "Desired condensed modules dimensions:", CD;

	if no_split then
	    ;
	elif dyn_traces then

	    AddAttribute(Type(K), "transversal_indices");
	    K`transversal_indices := [];

// vprint ZReps, 1: "OST:", OST;
// "get t C:", C;
	    function get_traces(gi, C)
		g := R[gi];
		TI := K`transversal_indices;
		if IsDefined(TI, gi) then
		    Kg := TI[gi];
		else
		    Kg := transversal_indices(K, g, f, cf);
		    TI[gi] := Kg;
		    KK := K;
		    KK`transversal_indices := TI;
		end if;
		T := cond_traces_Kg(Kg, C);
		s := I_lcm[gi];
		return [Z | s*x: x in T];
	    end function;

	    /*
	    infofmt := recformat<get_traces>;
	    dyn_traces_info := rec<infofmt |
		get_traces := get_traces
	    >;
	    */

	    TM`get_traces := get_traces;
	    TM`want_ind := WantIndex;
	    TM`dyn_traces_info := <[Z|], [Z|]>;

	    SD := cond_traces(K, G!1, SC, f, cf);
	    SD := ChangeUniverse(SD, Z);
	    vprint ZReps: "Decompose condensed modules dimensions:", SD;

	elif not use_traces then
	    vprint ZReps: "Skip full traces";
	else
	    SD := cond_traces(K, G!1, SC, f, cf);
	    SD := ChangeUniverse(SD, Z);
	    vprint ZReps: "Decompose condensed modules dimensions:", SD;

	    if USE_WANT_TRACES then
		WantDTraces := [[CD[i]] cat CT[i]: i in [1 .. #C]];
		SplitDTraces := [
		    <[SD[i]] cat OST[i, 1], OST[i, 2]>: i in [1 .. #SC]
		];

		Sort(~SplitDTraces, func<x, y | x[1, 1] - y[1, 1]>);
	    end if;
	end if;
    end if;

    //vprint ZReps: "WantDTraces:", WantDTraces;
    //vprint ZReps: "SplitDTraces:", SplitDTraces;

    if no_split then
	vprint ZReps: "No split needed";
	S := [TM];
    else
	vprint ZReps: "Splitting condensed module of dimension", Dimension(TM);
	IndentPush();
	SPLIT_TIME := Cputime();
// TM: Magma;
	S := IntegralDecomposition(
	    TM:
		WantDTraces := WantDTraces, SplitDTraces := SplitDTraces,
		WantDDims := CD, SplitDDims := SD,
		SplitChars := SplitChars,
		DynTraces := dyn_traces
	);
	SPLIT_TIME := Cputime(SPLIT_TIME);
	IndentPop();

	Sort(~S, func<x, y | Dimension(x) - Dimension(y)>);
	vprint ZReps: "Splitting time:", SPLIT_TIME;
    end if;

    vprint ZReps: "Condensed split dimensions:", [Dimension(x): x in S];
    //vprint ZReps: "Condensed split SI:", [si: si in SI];

//"TM Decompose:", S: Maximal;

    /*
    "S:", S;
    "CD:", CD;
    "Traces:",
	[[Trace(ActionGenerator(s, j)): j in [1 .. nag]]: s in S];
    */

    nag := Nagens(S[1]);
    ST := [[Trace(ActionGenerator(s, j)): j in [1 .. nag]]: s in S];
    vprint ZReps, 2: "GOT:";
    for i := 1 to #S do
/*
"i:", i;
S[i]: Maximal;
"e trace:", Trace(ActionGenerator(S[i], 1)*ActionGenerator(S[i], nag));
*/
	vprint ZReps, 2: Dimension(S[i]), ST[i];
    end for;

    if want_chars then
	vprint ZReps, 2: "CD:", CD;
	if use_traces then
	    vprint ZReps, 2: "OST:", OST;
	    vprint ZReps, 2: "ST:", ST;
	    vprint ZReps, 2: "CT:", CT;
	end if;

	/*
	if FullWantChars cmpne {} and 0 eq 1 then

	    DT := Cputime();

	    C_full_decomp := [char_decomp(FullCharTable, c): c in C];
	    "Full C decomp:", C_full_decomp;
	    "Full C traces:", [get_traces([t[1]: t in D]): D in C_full_decomp];

	    SC_full_decomp := [char_decomp(FullCharTable, c): c in SC];
	    "Full SC decomp:", SC_full_decomp;
	    "Full SC traces:",[get_traces([t[1]: t in D]): D in SC_full_decomp];

	    "Full C decomp:", FullWantChars;
	    "Full C traces:", [get_traces(D): D in FullWantChars];

	    "Full SC decomp:", FullSplitChars;
	    "Full SC traces:", [get_traces(D): D in FullSplitChars];

	    "FULL DECOMP TIME:", Cputime(DT);

	end if;
	*/
    end if;

    p := rep{p: p in [2 .. 2*#G] | GCD(p, #G) eq 1 and IsPrime(p)};
    F := GF(p);
    L := [G.i: i in [1..Ngens(G)]];

    if want_chars then
	RQ := [];
	BQ := [];

	get_split_degs_char(SplitChars, ~split_degs, ~split_degs_index);
	vprint ZReps: "G split degrees:", split_degs;

	if no_split then
	    dyn_traces := false;
	    use_traces := false;
	end if;

	if dyn_traces then
	    trace_ind, SC_traces := Explode(TM`dyn_traces_info);
	    QQ := [
		[Dimension(S[i])] cat [ST[i, j]: j in trace_ind]:
		    i in [1 .. #ST]
	    ];
	    vprint ZReps: "Dynamic trace_ind:", trace_ind;
	    delete TM`get_traces;
	    delete TM`want_ind;
	    delete TM`dyn_traces_info;
	    delete K`transversal_indices;
	elif use_traces then
	    QQ := [
		[Dimension(S[i])] cat [ST[i, j]: j in [1 .. nag]]:
		    i in [1 .. #ST]
	    ];
	else
	    QQ := [[Dimension(S[i])]: i in [1 .. #ST]];
	end if;

	if icond then
	    vprint ZReps: "Set up ind action for G gens";
	    vtime ZReps: icond_MQ, icond_IQ := icond_info`set_up_action_seqs(
		[G.i: i in [1 .. gngens(G)]]
	    );
	end if;

	vprint ZReps, 2: "Got dim and traces:", QQ;

	C := non_scaled_C;
	for i := 1 to #C do
	    Cd := Z!Degree(C[i]);
	    d := Z!CD[i];
	    //Sd := [s: s in S | Dimension(s) mod d eq 0];
	    //printf "# condensed modules: %o\n", #Sd;

	    vprintf ZReps: "Character %o: %o\n", i, C[i];
	    vprintf ZReps: "Condensed dim: %o\n", d;

	    if dyn_traces then
		ii := WantIndex[i];
		t := [T[ii]: T in SC_traces];
		tt := [d] cat t;
		vprintf ZReps, 2: "Want condensed traces: %o\n", t;
	    elif use_traces then
		t := CT[i];
		tt := [d] cat t;
		vprintf ZReps, 2: "Want condensed traces: %o\n", t;
	    else
		tt := [d];
	    end if;
	    vprint ZReps, 2: "tt:", tt;

	    founds := 0;
	    oschur := WantSchurIndices[i];
	    if SCALE_BY_SI then
		schur := 1;
	    else
		schur := oschur;
	    end if;
	    si := schur;

	    vprintf ZReps:
		"Get knapsack solutions (#submodules: %o, #values: %o)\n",
		#QQ, #QQ[1];

	    ttt := [si*x: x in tt];
	    vtime ZReps, 2:
		kn := MultiKnapsackSolutions(QQ, ttt);
	    vprintf ZReps: "# knapsack solutions: %o\n", #kn;

	    for k := 1 to #kn do
		vprintf ZReps: "Solution: %o\n", kn[k];

		s := &+[S[i]: i in kn[k]];
		/*
		Ts := [Trace(ActionGenerator(s, j)): j in [1 .. nag]];
		vprint ZReps, 2: "Ts:", Ts;
		*/

		q := ExactQuotient(Dimension(s), d);
		vprint ZReps, 2: "q:", q;

		if dyn_traces then
		    tlen := #trace_ind;
		elif use_traces then
		    tlen := nag;
		else
		    tlen := 0;
		end if;

		// if forall{j: j in [1 .. tlen] | Ts[j] eq q * t[j]}
		if true 
		then
		    vprintf ZReps: "Submodule of dimension %o matches\n",
			Dimension(s);

		    expect_dim := si*Cd;
		    mor := Morphism(s, TM);
//"Got morphism:", mor; Parent(mor);
		    IndentPush();
		    if tcond then
			mor := Morphism(s, TM);
			if Blackbox then
			    function uc(v)
				F := BaseRing(v);
				v := v*Matrix(F, mor);
				return tuncond(info, v);
			    end function;
			    function spin(v, limit)
				F := BaseRing(v);
				R := SpinAction(
				    v, Transpose(ChangeRing(M1, F)),
				    ChangeRing(M2, F): Limit := limit
				);
				MF := GModule(CG, R: Check := false);
				return MF;
			    end function;
			    // "Cd:", Cd; "si:", si;
			    RQ := <s, uc, spin, CG, Cd*oschur>;
			    BQ := 0;
			    return;
			end if;
			w := tuncond(info, mor);
			w := Saturation(w);
			w := LLL(w: Delta := 0.999, Proof := false);
			vprintf ZReps: "Tensor uncondense dimension %o\n",
			    Nrows(w);
			vprint ZReps: "Uncondensed norms:", Norms(w);
			vtime ZReps: R := SpinAction(w, Transpose(M1), M2);
			R := GModule(CG, R: Check := false);
			delete w;
		    elif icond then
			if Blackbox then
			    function uc(v)
				F := BaseRing(v);
//"Do uc in v:", v;
//"Do uc mor:", mor;
				v := v*Matrix(F, mor);
//"Do uc new v:", v;
				return icond_info`uncond(v);
			    end function;
			    function spin(
				v, limit:
				    Saturate, WantBasis := false,
				    ModularPrime := 0
				    //Reduced
			    )
				F := BaseRing(v);
				//v := uc(v);
				icond_MQ_F := [
				    [ChangeRing(x, F): x in q]: q in icond_MQ
				];
				if WantBasis then
				    B := InductionSpin(
					v, icond_MQ_F, icond_IQ:
					    Group := G, Limit := limit,
					    Saturate := Saturate,
					    ModularPrime := ModularPrime
					    //Reduced := Reduced
				    );
				    return B;
				else
				    _, MF := InductionSpin(
					v, icond_MQ_F, icond_IQ:
					    Group := G, Limit := limit,
					    Saturate := Saturate,
					    ModularPrime := ModularPrime
					    //Reduced := Reduced
				    );
				    return MF;
				end if;
			    end function;
			    // "Cd:", Cd; "si:", si;
			    RQ := <s, uc, spin, CG, Cd*oschur>;
			    BQ := 0;
			    return;
			end if;
			v := LLL(mor: Delta := 0.999, Proof := false);
			w := icond_info`uncond(v);
			w := Saturation(w);
			w := LLL(w: Delta := 0.999, Proof := false);
			vprintf ZReps: "Induction uncondense dim %o\n",
			    Nrows(w);
			vprint ZReps: "Uncondensed norms:", Norms(w);
			vtime ZReps:
			    _, R := InductionSpin(
				w, icond_MQ, icond_IQ: Group := G,
				Saturate := not AllowDenoms
			    );
			delete v, w;
		    else
			if Blackbox then
			    mor := Morphism(s, TM);
			    uc := func<B |
				puncond_basis_mat(
				    B*Matrix(BaseRing(B), mor), G, K
				)
			    >;
			    // "Cd:", Cd; "si:", si;
			    RQ := <s, uc, G, CG, Cd*oschur>;
			    BQ := 0;
			    return;
			end if;

			R := puncond(
			    s, TM, G, K:
				mod_G := CG, expect_dim := /* - */ expect_dim
			);
		    end if;
		    IndentPop();

		    assert not Blackbox;

		    dim := Dimension(R);
		    vprint ZReps:
			"Got uncondensed module of dimension", dim;

		    if dim mod Cd eq 0 then

			vprint ZReps:
			    "Try char test on products of irreducibles";
			rats := [t[1]: t in SplitChars];
			possible := get_possible_chars_irr_chars(R, rats);
			c := Char(R: Possible := possible, PossiblyNone);

			if c cmpeq 0 then
			    vprint ZReps:
				"Products of irreducibles failed";
			    if #split_degs gt CHAR_KNAP_LIMIT then
				rats := [t[1]: t in SplitChars];
				possible := {};
				vprintf ZReps:
				    "Use %o IRREDUCIBLE character(s)\n",
				    #rats;
			    else
				possible := get_possible_chars(
				    SplitChars,
				    split_degs, split_degs_index, dim
				);
				assert #possible ge 1;
				rats := [];
				vprintf ZReps:
				    "%o possible character(s)\n", #possible;
			    end if;
/*
"possible:", possible;
"actual char:", Char(R);
delete R`Character;
*/

			    c := Char(
				R: Possible := possible, IrrChars := rats
			    );
			end if;

			q := ExactQuotient(dim, Cd);
			if c eq q*C[i] then
			    vprint ZReps: "Good character!";
			    Append(~RQ, R);
			    Append(~BQ, q);
			    founds := s;
			    break;
			else
			    vprint ZReps: "NON-MATCHED character!";
			    vprint ZReps: "Wanted:", C[i];
			    vprint ZReps: "Got:", c;
			    //error "....";
			end if;
		    else
			vprint ZReps: "BAD dimension!!!";
		    end if;
		end if;
	    end for;

	    if founds cmpeq 0 then
		vprint ZReps: "BAD character (not found)";
		vprint ZReps: "Wanted:", C[i];
		vprint ZReps: "Traces:", t;

		// error "BAD character (Tell Allan about this)";
	    end if;
	end for;
    else
	RQ := [];
	BQ := <>;

	if true then
	    // puncond to non-iso modules????
	    "Remove isomorphic duplicates";

	    SI := [];
	    for i := 1 to #S do
		s := S[i];
		st := ST[i];
		skip := false;
		for j in SI do
		    if st eq ST[j] then
			H := AHom(S[i], S[j]);
			if Dimension(H) gt 0 then
			    printf "Module %o isomorphic to module %o\n", i, j;
			    skip := true;
			end if;
		    end if;
		end for;
		if not skip then
		    Append(~SI, i);
		end if;
	    end for;

	    S := [S[i]: i in SI];
	    ST := [ST[i]: i in SI];

	    "Reduced list:";
	    for i := 1 to #S do
		Dimension(S[i]), ST[i];
	    end for;

	    for i := 1 to #S do
		S[i]: Maximal;
	    end for;
	end if;

	for s in S do
	    "Uncondense dim", Dimension(s);
	    IndentPush();
	    U := puncond_basis(s, TM, G, K);
	    IndentPop();
	    if MaxUncond gt 0 then
		UF := ChangeRing(U, F);
		"Get modular spin";
		time B := Spin(UF, L);
		bd := Nrows(B);
		"Modular rank:", bd;
		if bd gt MaxUncond then
		    "Skip";
		    continue;
		end if;
	    end if;

	    "LLL basis";
	    time UU := LLL(U: Proof := false);

	    "Spin uncondensed";
	    IndentPush();
	    R, B := SpinAction(UU, L);
	    IndentPop();

	    R := GModule(CG, R);
	    Append(~RQ, R);
	    Append(~BQ, B);
	end for;
    end if;

    //return RQ, BQ;
end procedure;
