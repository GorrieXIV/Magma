freeze;

declare attributes RngInvar: relations;

intrinsic Relations(R::RngInvar: UseGroebner := false) -> []
{Algebraic relations for the invariant ring R};

    require Type(UseGroebner) eq BoolElt:
	"Parameter 'UseGroebner' must be a boolean";

    if assigned R`relations then
	return R`relations;
    end if;

    vprint Invariants: "INVARIANT RING RELATIONS";

    P := PolynomialRing(R);
    n := Rank(P);

    // Create algebra AP and expressions AR of secondaries
    AP, AR := Algebra(R);

    // Get primaries, irreducible secondaries, secondaries
    PL := PrimaryInvariants(R);
    SGL := IrreducibleSecondaryInvariants(R);
    SL := SecondaryInvariants(R);

    if UseGroebner then
	if false then
	    L := PL cat SGL;
	    V, f := VariableExtension(P, #L, false);
	    AssignNames(
		~V,
		[Sprint(P.i): i in [1 .. n]] cat 
		["f" cat Sprint(i): i in [1 .. #PL]] cat
		["h" cat Sprint(i): i in [1 .. #SGL]]
	    );
	    g := hom<V -> AP | [0: i in [1 .. n]] cat [AP.i: i in [1 .. #L]]>;
	else
	    L := SGL cat PL;
	    V, f := VariableExtension(P, #L, false);
	    AssignNames(
		~V,
		[Sprint(P.i): i in [1 .. n]] cat 
		["h" cat Sprint(i): i in [1 .. #SGL]] cat
		["f" cat Sprint(i): i in [1 .. #PL]]
	    );
	    g := hom<
		V -> AP |
		[0: i in [1 .. n]] cat
		[AP.(n + i): i in [1 .. #SGL]] cat
		[AP.i: i in [1 .. #PL]]
	    >;
	end if;
	LL := [f(L[i]) - V.(n + i): i in [1 .. #L]];
	I := ideal<V | LL>;
/*
return I;
*/
//print I;
	E := EliminationIdeal(I, n: Walk := false);
	S := g(Basis(E));
	R`relations := S;
	return S;
    end if;

    // Create module M
    M := Module(R);

    // Create hom h from t-variables algebra of module into algebra AP
    primv := func<i | AP.i>;
    secgv := func<i | AP.(n + i)>;
    h := hom<CoefficientRing(M) -> AP | [primv(i): i in [1 .. n]]>;

    // Initialize S to module syzgies
    S := [AP |
	&+[h(v[i])*AR[i]: i in [1 .. #SL]] where v is Eltseq(r):
	    r in Relations(M)
    ];

    if #SGL eq 0 then
	R`relations := S;
	return S;
    end if;

    // Compute parallel sequences of sequences
    // Q[d] has the actual polynomial products (in P) of degree d
    // prod[d] has the corresponding product expressions (in A)

    maxdeg := func<S | Maximum([WeightedDegree(f): f in S])>;
    Q := [[]: i in [0 .. maxdeg(SGL) + maxdeg(SL)]];
    prod := [{@ AP | @}: i in [0 .. maxdeg(SGL) + maxdeg(SL)]];

    seen := {};
    for i in [1 .. #SGL] do
	vprintf Invariants, 1: "Setup irred sec %o of %o\n", i, #SGL;
	for j in [1 .. #SL] do
	    p := SGL[i] * SL[j];
	    if not p in seen then
		Include(~seen, p);
		d := WeightedDegree(p);
		Append(~Q[d + 1], p);
		Include(~prod[d + 1], secgv(i) * AR[j]);
	    end if;
	end for;
    end for;

    // Create A-variables AR and indexed-set expressions for secondaries
    Avars := [AP.i: i in [1 .. Rank(AP)]];
    AR_ind := {@ f: f in AR @};

    // Loop over degrees d
    for d := 0 to #Q - 1 do
	Q_d := Q[d + 1];
	prod_d := prod[d + 1];
	if #Q_d eq 0 then
	    continue;
	end if;

	vprint Invariants, 1: "\nDEGREE:", d;
	vprint Invariants, 2: "Products:", prod_d;

	while #Q_d gt 0 do
	    // Test which products are derivable from current relations.
	    H := HomogeneousModuleTest(Avars, S, n, prod_d, AR_ind);

	    vprint Invariants, 2: "Redundancy result:", H;

	    // Update Q_d & prod_d to products and expressions which are useful.
	    Q_d := [Q_d[i]: i in [1 .. #H] | not H[i]];
	    prod_d := {@ prod_d[i]: i in [1 .. #H] | not H[i] @};

	    if #Q_d eq 0 then
		//vprint Invariants, 2: "All are now redundant";
		break;
	    end if;

	    // Write each product in Q_d in terms of the primaries and
	    // secondaries.  B should contain all true since we know
	    // the product lies in the module.
	    i := 1;
	    B, V := HomogeneousModuleTest(PL, SL, [Q_d[i]]);
	    assert B[i];

	    // Form new relation s and insert in S if non-zero.
	    s := &+[AR[k]*h(V[i][k]): k in [1 .. #SL]] - prod_d[i];
	    if not IsZero(s) then
		Append(~S, s);
		vprint Invariants, 2: "New relation:", s;
	    end if;

	    prod_d := {@ prod_d[i]: i in [2 .. #prod_d] @};
	    Q_d := [Q_d[i]: i in [2 .. #Q_d]];
	end while;
    end for;

    R`relations := S;
    return S;
end intrinsic;

intrinsic RelationIdeal(R::RngInvar) -> RngMPol
{The ideal of algebraic relations for the invariant ring R};
    return ideal<Algebra(R) | Relations(R)>;
end intrinsic;
