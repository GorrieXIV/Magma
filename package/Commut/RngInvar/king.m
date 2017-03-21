freeze;

/*
Fundamental Invariants using algorithm from:

    Simon King.
    Minimal generating sets of non-modular invariant rings of finite groups.
    arXiv:math/0703035, 14 pages, 2007.

AKS, July 2008.
*/

/*******************************************************************************
			    Debug
*******************************************************************************/

DUMP := true;
DUMP := false;
DO_PRIM_TEST := true;

/*******************************************************************************
			       Stuff
*******************************************************************************/

get_degs := func<B | [TotalDegree(f): f in B]>;

function my_rey(m, G)
    if Type(G) eq GrpPerm then
	return &+(m^G);
    else
	return ReynoldsOperator(m, G);
    end if;
end function;

function deg_summary(B)
    degs := get_degs(B);
    return [#[j: j in degs | j eq d]: d in [1 .. Max(degs cat [0])]];
end function;

function hilb_basis(B)
    I := Ideal(B);
    MarkGroebner(I);
    return HilbertSeries(I);
end function;

/*******************************************************************************
			       Primary test
*******************************************************************************/

function primary_test(R, L: PartialGB := 0)
    P := Universe(L);
    n := Rank(P);
    if #L ne n then
	return false;
    end if;
    H := HilbertSeries(R);
    t := Parent(H).1;
    N := &*[1-t^TotalDegree(f): f in L] * H;
    if not IsOne(Denominator(N)) then
	vprint Invariants: "Fail denom test";
	return false;
    end if;

    if PartialGB cmpne 0 then
	I := Ideal(PartialGB);
    else
	I := Ideal(L);
    end if;

    return IsZeroDimensional(I);

end function;

/*******************************************************************************
			Main King algorithm
*******************************************************************************/

intrinsic FundamentalInvariantsKing(
    IR::RngInvar: UsePrim := false, MaxDegree := 0, GB := false
) -> SeqEnum
{Fundamental invariants using King algorithm}

    require not IsModular(IR): "Invariant Ring must be non-modular";

    vprint Invariants: "Fundamental Invariants via King algorithm";

    grp := Group(IR);
    dmax := #grp;
    grp_is_monomial := Type(grp) eq GrpPerm or
	forall{g: g in Generators(grp) | IsMonomial(g)};
//grp_is_monomial:=true;
    vprint Invariants: "Group is monomial:", grp_is_monomial;

    P := PolynomialRing(IR);

    if UsePrim then
	vprint Invariants: "Get Primaries";
	vtime Invariants: prim := PrimaryInvariants(IR);
	I := EasyIdeal(PrimaryIdeal(IR));
	CP := Generic(I);
	S := ChangeUniverse(prim, CP);
	assert HasGrevlexOrder(I);
	G := GroebnerBasis(I);

	H<t> := HilbertSeries(IR);
	H_numer := Numerator(&*[1 - t^TotalDegree(f): f in prim] * H);

	vprint Invariants: "Hilbert series:", H;
	vprint Invariants: "Hilbert series numer:", H_numer;

	numer_bound := Degree(H_numer);
	if numer_bound eq 0 then
	    vprint Invariants: "Numerator bound is trivial";
	    return prim;
	end if;

	if MaxDegree gt 0 then
	    dmax := Min(dmax, MaxDegree);
	else
	    // dmax := Max([TotalDegree(f): f in MonomialBasis(CP/I)]);
	    dm := 0;
	    for d := 1 to Min(dmax, numer_bound) do
		mons := MonomialsOfDegree(CP, d, G);
		vprintf Invariants: "#reduced mons of deg %o: %o\n", d, #mons;
		if #mons gt 0 then
		    dm := d;
		end if;
	    end for;
	    assert dm gt 0;
	    dmax := Min(dmax, dm);
	end if;

	dmax := Min(dmax, numer_bound);
	G_max_deg := Max(get_degs(G));
    else
	CP := Generic(ChangeOrder(P, "grevlex"));
	S := [CP | ];
	I := Ideal(S);
	G := S;
	H_numer := 0;

	if MaxDegree gt 0 then
	    dmax := Min(dmax, MaxDegree);
	end if;
	G_max_deg := -2;
    end if;

    dmax_bound := dmax;

    OG := Set(G);
    OG := G;
    tried_prim_test := false;

    vprint Invariants: "Diag test";
    diag := 0;
    Rdiag := 0;
    vtime Invariants: if Type(grp) eq GrpMat and #grp lt 100000 then
	diag := sub<grp | >;
	for x in grp do
	    if IsDiagonal(x) and x notin diag then
		diag := sub<grp | diag, x>;
		vprint Invariants: "new #diag:", #diag;
	    end if;
	end for;
	vprint Invariants: "final #diag:", #diag;
	if #diag eq 1 then
	    diag := 0;
	else
	    vprint Invariants: "Diagonal subgroup of order", #diag;
	    Rdiag := InvariantRing(diag);
	end if;
    end if;

/*
    "Get Mol";
    vtime Invariants: mol<t> := MolienSeries(grp);
    denom := Denominator(mol);
    numer := Numerator(mol);
    "Molien series function:", mol;
    mols<t> := PowerSeriesRing(IntegerRing())!mol;
    "Molien series:", mols;
    "Molien numer:", numer;
*/

    d := 0;
    while true do

	if dmax gt 0 and d ge dmax then
	    vprint Invariants: "\nd reached dmax now";
	    // return ChangeUniverse(S, P);
	    break;
	end if;

	d +:= 1;

	vprintf Invariants: "\n****\nd: %o, dmax: %o, G_max_deg: %o\n",
	    d, dmax, G_max_deg;

	// MemProfile();

	ZEIT := Cputime();

	if DUMP then
	    "S:", S;
	    "G:", G;
	end if;

	vprint Invariants: "S deg summary:", deg_summary(S);
	vprint Invariants: "G deg summary:", deg_summary(G);

	if H_numer ne 0 then
	    vprint Invariants: "H_numer:", H_numer;
	    // vtime Invariants: "Current hilb series:", hilb_basis(G);
	end if;

	/*
	//"Molien numer:", numer;
	vprint Invariants: "Molien series:", mols;

	*/

	if G_max_deg eq d - 2 and MaxDegree eq 0 and (dmax eq 0 or d lt dmax)
	then
	    // I := Ideal(S);
	    I := Ideal(G);
	    vprint Invariants: "Get full GB";
	    IndentPush();
	    vtime Invariants: Groebner(I: DegreeStart := d);
	    IndentPop();
	    // assert I eq Ideal(S cat G);
	    if IsZeroDimensional(I) then
		dmax := Max([TotalDegree(f): f in MonomialBasis(CP/I)]);
		vprint Invariants: "New dmax:", dmax;
		dmax := Min(dmax, dmax_bound);
		vprint Invariants: "Adjusted dmax:", dmax;
		if d gt dmax then
		    vprint Invariants: "d exceeds dmax now";
		    vprint Invariants: "Step time:", Cputime(ZEIT);
		    // "Final degree summary:", deg_summary(S);
		    // "Max degree:", Max(get_degs(S)) + 0;
		    // return ChangeUniverse(S, P);
		    break;
		end if;
	    end if;
	    // "Get full GB";
	    IndentPush();
	    vtime Invariants: G := GroebnerBasis(I);
	    IndentPop();
	    G_max_deg := Max([TotalDegree(f): f in G]);
	elif G_max_deg eq d - 1 then

	    extra := [f: f in OG | TotalDegree(f) eq d];
	    vprintf Invariants:
		"Include %o poly(s) from orig GB for deg %o\n", #extra, d;
	    if #extra gt 0 then
		G := G cat extra;
		G := Sort(Setseq(Set(G)));
	    end if;
	    vprint Invariants: "Get deg", d, "GB";
	    IndentPush();
	    vtime Invariants: G := GroebnerBasis(G, d: DegreeStart := d);
	    IndentPop();
	    if false and #OG gt 0 then
		G := Sort(Setseq(Set(G) join OG));
		// "Add in original GB"; vtime Invariants:
		//G := ReduceGroebnerBasis(G cat OG);
	    end if;
	    if #G gt 0 then
		G_max_deg := Max([TotalDegree(f): f in G]);
	    end if;
	end if;

	if not(H_numer eq 0 or d le Degree(H_numer)) then
	    vprintf Invariants: "*** PAST NUMER BOUND %o!!!\n", Degree(H_numer);
	end if;

	if H_numer ne 0 then
	    c := Coefficient(H_numer, d);
	    if c eq 0 then
		vprintf Invariants: "Skip degree %o by Hilbert numer\n", d;
		continue;
	    end if;
	end if;

	vprintf Invariants: "Get mons of deg %o mod G\n", d;
	vtime Invariants: mons := MonomialsOfDegree(CP, d, G);
	vprint Invariants: #mons;

	/*
	LMI := Ideal([CP | LeadingMonomial(f): f in G]);
	vprint Invariants: "LMI:", deg_summary(Basis(LMI));

	vprint Invariants: "Get mons of deg", d; vtime Invariants:
	amons := MonomialsOfDegree(CP, d);
	vprint Invariants: #amons;

	vprint Invariants: "Exclude mons in LMI"; vtime Invariants:
	mons2 := [m: m in amons | m notin LMI];

	if Set(mons) ne Set(mons2) then
	    "BAD";
	    "d:", d;
	    "LMI:", LMI;
	    mons;
	    mons2;

	    error "";
	end if;
	*/

	if DUMP then mons; end if;

	vprint Invariants: "Apply Reynolds"; vtime Invariants:
	if Type(grp) eq GrpPerm then
	    B := ReynoldsOperator(mons, grp);
	elif 1 eq 1 and Rdiag cmpne 0 then
	    B := [];
	    // rmons := {};

	    if 1 eq 1 then
		rmons := {};
		for mi := 1 to #mons do
//"mi:", mi; "rmons:", rmons;
		    m := mons[mi];
		    if not IsInvariant(m, diag) then
			continue;
		    end if;
		    if m in rmons then
			continue;
		    end if;
		    vprintf Invariants: "Do mon %o of %o\n", mi, #mons;
		    if grp_is_monomial then
			Include(~rmons, m);
		    end if;
		    f := ReynoldsOperator(m, grp);
		    if f eq 0 then
			continue;
		    end if;
		    // "Len", Length(f);
		    Append(~B, f);
		    if grp_is_monomial then
			for fm in Monomials(f) do
			    Include(~rmons, fm);
			end for;
		    end if;
		end for;
//"d:", d, #B, #Set(B);
		delete rmons;
	    else
		vtime Invariants: "Get diag mons for deg", d;
		vtime Invariants: di := InvariantsOfDegree(Rdiag, d);
		dmons := {CP!m: m in Monomials(f), f in di};
		rmons := {};
		vprint Invariants: "Got", #dmons, "diag mons";
		for mi := 1 to #mons do
		    m := mons[mi];
		    if m notin dmons or m in rmons then
			continue;
		    end if;
		    // vprintf Invariants: "Do mon %o of %o\n", mi, #mons;
		    Include(~rmons, m);
		    f := ReynoldsOperator(m, grp);
		    if f eq 0 then
			continue;
		    end if;
		    // "Len", Length(f);
		    Append(~B, f);
		    if grp_is_monomial then
			for fm in Monomials(f) do
			    Include(~rmons, fm);
			end for;
		    end if;
		end for;
		delete rmons;
	    end if;

	    if grp_is_monomial then
		assert #B eq #Set(B);
	    else
		B := Setseq({Normalize(f): f in B});
	    end if;
	    Sort(~B);
	else
	    // B := [ReynoldsOperator(m, grp): m in mons];
	    B := {my_rey(m, grp): m in mons};
	    B := Setseq(B);
	    Sort(~B);
	end if;
	vprint Invariants: #B;
	if DUMP then "B:", B; end if;
	if DUMP then "G:", G; end if;

	if GetVerbose("Invariants") gt 0 then
	    verb := GetVerbose("Groebner");
	    SetVerbose("Groebner", 1);
	    vprint Invariants: "Get normal forms by G";
	    IndentPush();
	    vtime Invariants: NF := NormalForm(B, G);
	    IndentPop();
	    SetVerbose("Groebner", verb);
	else
	    NF := NormalForm(B, G);
	end if;
	if DUMP then "NF:", NF; end if;

	nc := 0;
	vprint Invariants: "Normal forms include loop"; vtime Invariants:
	for i := 1 to #NF do
	    f := NF[i];
	    if IsZero(f) then
		continue;
	    end if;

	    f := NormalForm(f, G);
	    // "new f", i, f;
	    if IsZero(f) then
		continue;
	    end if;

	    Append(~S, Normalize(B[i]));
	    Append(~G, Normalize(f));
	    G_max_deg := d;
	    nc +:= 1;
	end for;

	vprint Invariants: "Num new elements:", nc;

	n := Rank(P);
	if DO_PRIM_TEST and not tried_prim_test and #S ge n then
	    tried_prim_test := true;
	    L := S[1 .. n];
	    if #S eq n then
		PartialGB := G;
	    else
		PartialGB := 0;
	    end if;
	    pdegs := [TotalDegree(f): f in L];
	    vprint Invariants: "Try primary test for degs:", pdegs;
	    vtime Invariants: pt := primary_test(IR, L: PartialGB := PartialGB);
	    if pt then
		vprint Invariants: "*** Primary test succeeds";
		vprint Invariants: "Primary degs:", pdegs;
		H<t> := HilbertSeries(IR);
		H_numer := Numerator(&*[1 - t^TotalDegree(f): f in L] * H);
		vprint Invariants: "Got H_numer:", H_numer;
		numer_bound := Degree(H_numer);
		if dmax eq 0 then
		    dmax := numer_bound;
		else
		    dmax := Min(dmax, Degree(H_numer));
		end if;
	    end if;
	end if;

	vprint Invariants: "Step time:", Cputime(ZEIT);
    end while;

    vprint Invariants: "Final degree summary:", deg_summary(S);
    vprint Invariants: "Max degree:", Max(get_degs(S)) + 0;

    S := ChangeUniverse(S, P);
    S := [Normalize(f): f in S];

    cmp := function(f, g)
	d := Degree(f) - Degree(g);
	if d ne 0 then
	    return d;
	end if;
	if f lt g then
	    return 1;
	elif f gt g then
	    return -1;
	else
	    return 0;
	end if;
    end function;

    Sort(~S, cmp);

    if GB then
	return S, G;
    end if;
    return S;

end intrinsic;

/*******************************************************************************
				    Aux
*******************************************************************************/

intrinsic TransitiveGroupFundamentalInvariants(
    d::RngIntElt, i::RngIntElt: Char := -1
) -> []
{Fundamental invariants of TransitiveGroup(d, i)}

    G := TransitiveGroup(d, i);
    if Char lt 0 then
	p := rep{p: p in [2 .. #G] | IsPrime(p) and #G mod p ne 0};
	K := GF(p);
    elif Char eq 0 then
	K := RationalField();
    else
	K := GF(Char);
    end if;

    R := InvariantRing(G, K);
    return FundamentalInvariants(R), R;

end intrinsic;
