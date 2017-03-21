freeze;

/*******************************************************************************
			    Decomposition via MP
*******************************************************************************/

function zpd(I: Start := Rank(I))

    assert IsZeroDimensional(I);

    F := BaseRing(I);
    // assert Type(F) eq FldFunRat; D := IntegerRing(F);

    vprint Decomposition: "ZERO DIM PDECOMP (MIN POLY method)";
    vprint Decomposition: "I input basis len:", #Basis(I);
    E := I;

    dim := QuotientDimension(E);
    vprint Decomposition: "Quotient dimension:", dim;

    Q := Generic(E)/E;
    n := Rank(I);
    for i := Start to 1 by -1 do
	printf "*** i: %o, get min poly\n", i;
	time mp := MinimalPolynomial(Q.i);

	deg := Degree(mp);
	vprint Decomposition: "mp degree:", Degree(mp);

	"Factorize";
	time L := Factorization(mp);
	vprint Decomposition:
	    "Factorization pattern:", [<Degree(t[1]), t[2]>: t in L];

	full := deg eq dim;
	if full then
	    vprint Decomposition: "FULL deg found";
	end if;

	if full and #L eq 1 then
	    vprint Decomposition: "Primary";
	    if L[1, 2] eq 1 then
		return [E];
		return [E], [E];
	    else
		return [E];
		R := E + Ideal(L[1, 1]);
		return [E], [R];
	    end if;
	end if;

	if #L gt 1 then
	    vprint Decomposition: "Split by factorization";
	    D := [];
	    for j := 1 to #L do
		g := L[j, 1];
		printf "Factor %o: %o\n", j, g;
		eg := Evaluate(g, Generic(E).i);
		printf "    eg: %o\n", eg;
		J := E + Ideal(eg);
		if full then
		    Append(~D, J);
		else
		    IndentPush();
		    D cat:= zpd(J: Start := i - 1);
		    IndentPop();
		end if;
	    end for;
	    return D;
	end if;

    end for;

    vprint Decomposition: "Finish univ loop";
    return [E];

end function;

function split_by_fact(I, f, ev)

    "Factorize";
    time L := Factorization(f);
    vprint Decomposition:
	"Factorization pattern:", [<Degree(t[1]), t[2]>: t in L];

    if #L eq 1 and L[1, 2] eq 1 then
	vprint Decomposition: "Irreducible";
	return false, [I];
    end if;

    vprint Decomposition: "Split by factorization";
    D := [];
    for j := 1 to #L do
	g := L[j, 1];
	printf "Factor %o: %o\n", j, g;
	eg := ev(g);
	printf "    eg: %o\n", eg;
	J := I + Ideal(eg);
	Append(~D, J);
    end for;
    return true, D;
end function;

function zpd(I: Start := Rank(I))

    assert IsZeroDimensional(I);

    F := BaseRing(I);
    // assert Type(F) eq FldFunRat; D := IntegerRing(F);

    vprint Decomposition: "I input basis len:", #Basis(I);
    E := I;

    function try_mp(E, dim, elt)
	// Return full, split, [ideals]

	vprint Decomposition: "Get min poly of", elt;
	time mp := MinimalPolynomial(elt);

	deg := Degree(mp);
	vprint Decomposition: "mp degree:", Degree(mp);

	full := deg eq dim;
	if full then
	    vprint Decomposition: "FULL deg found";
	end if;

	split, D := split_by_fact(E, mp, func<g| Evaluate(g, Generic(E)!elt)>);
	return full, split, D;
    end function;

    if 1 eq 1 then
	"Initial basis factorization";
	IndentPush();
	T := [E];
	L := [];
	time while #T gt 0 do
	    "Now #T:", #T;
	    E := T[#T];
	    Prune(~T);
	    split := false;
	    for f in GroebnerBasis(E) do
		split, D := split_by_fact(E, f, func<f | f>);
		if split then break; end if;
	    end for;
	    if split then
		T cat:= D;
	    else
		Append(~L, <E, Start>);
	    end if;
	end while;
	IndentPop();
    else
	L := [<E, Start>];
    end if;

    final := [];
    while #L gt 0 do
	printf "**** Queue len: %o\n", #L;

	E, i := Explode(L[#L]);
	Prune(~L);

	"E length:", #Basis(E);

// E; [Factorization(f): f in Basis(E)];
	"i:", i;

	dim := QuotientDimension(E);
	vprint Decomposition: "Quotient dimension:", dim;

	Q := Generic(E)/E;
	while true do

	    if i ge 1 then
		elt := Q.i;
	    else
		//error "need rand elt";
		EB := BaseRing(E);
		if Characteristic(EB) eq 0 then
		    elt := &+[Random(-5, 5)*Q.i: i in [1 .. Rank(Q)]];
		elif Type(EB) eq FldFunRat then
		    EBB := BaseRing(EB);
		    elt := &+[
			Random(EBB)*EB.Random(1, Rank(EB))^Random(0,1)*Q.i:
			    i in [1 .. Rank(Q)]
		    ];
		else
		    elt := &+[Random(EB)*Q.i: i in [1 .. Rank(Q)]];
		end if;
	    end if;

	    vprintf Decomposition: "Try mp (full dim %o)\n", dim;
	    IndentPush();
	    full, split, D := try_mp(E, dim, elt);
	    IndentPop();

	    printf "full: %o, split: %o, #D: %o\n", full, split, #D;

	    if full then
		final cat:= D;
		break;
	    end if;

	    if i gt 0 then
		i -:= 1;
	    end if;

	    if split then
		//"Decomposition length:", #D;
		L cat:= [<J, i>: J in D];
		break;
	    end if;
	end while;
    end while;

    return final;

end function;

intrinsic InternalZPD(I::RngMPol) -> []
{Internal}

    vprint Decomposition: "Get Easy Ideal";
    vtime Decomposition: E := EasyIdeal(I);

    return zpd(E);
end intrinsic;

/*******************************************************************************
			    Decomposition via MP
*******************************************************************************/

function degrees(K)
    if Type(K) eq FldRat then
	return [1];
    else
	return [Degree(K)] cat degrees(BaseField(K));
    end if;
end function; 

function decompose_triangular(B, v, K, Khi, vars)
/*
Assumes min polys of all variables already done.
Also, all polys from variable v + 1 factored (K is field for such).
*/

    vprint Decomposition: "*** Variable", v;

    f := B[v];

    assert Domain(Khi) eq K;

    R := Universe(B);
    U := PolynomialRing(K); x := U.1;
    n := Rank(R);
    h := hom<R -> U |
	[0: i in [1 .. v - 1]] cat [x] cat
	[U!K!vars[i - v]: i in [v + 1 .. n]]>;
	// [K.(i - v): i in [v + 1 .. n]]>;

    g := h(f);

    if Degree(g) eq 1 then
	vprint Decomposition: "Linear";
	if v eq 1 then
	    return [Reduce(B)];
	end if;
	r := -Coefficient(g, 0);
	nvars := [r] cat vars;
	return decompose_triangular(B, v - 1, K, Khi, nvars);
    end if;

    vprint Decomposition, 2: "K:", K: Maximal;

    vprint Decomposition: "K degrees:", degrees(K);
    vprint Decomposition: "Polynomial degree:", Degree(g);

    /*
    "vars:", vars;
    "U:", U;
    "h im:", [h(R.i): i in [1 .. n]];
    "f:", f;
    "g:", g;
    "Parent(g):", Parent(g): Maximal;
    Degree(g);
    */

    vprint Decomposition: "Factor polynomial";
    vtime Decomposition: L := Factorization(g);

    vprint Decomposition: "Number of factors:", #L;
    vprint Decomposition: "Factor degrees:", [<Degree(t[1]), t[2]>: t in L];

    hi := hom<U -> R | Khi, R.v>;
    res := [];
    for ti := 1 to #L do
	t := L[ti];
	vprintf Decomposition: "Factor %o: %o\n", ti, t;
	IndentPush();
	ff := t[1];
	BB := B[1 .. v - 1] cat [hi(ff)] cat B[v + 1 .. n];
	if v gt 1 then
	    if Degree(ff) gt 1 then
		if Type(K) in {FldNum, FldCyc, FldQuad} then
		    KK := NumberField(t[1]: Check := false);
		else
		    //KK := ext<K | t[1]>;
		    KK := quo<U | t[1]>;
		end if;
		// "t[1]:", t[1];
		AssignNames(~KK, [Sprintf("w%o", v)]);
		// "KK:", KK: Maximal; Khi;
		KKhi := hom<KK -> R | Khi, R.v>;
		//"U1:", Universe([KK.1]); //"U2:", Universe(vars);
		nvars := [KK.1] cat vars;
	    else
		KK := K;
		KKhi := Khi;
		// "Universe:", Universe([(-Reductum(ff))]); Universe(vars);
		r := -Coefficient(ff, 0);
		nvars := [r] cat vars;
	    end if;
	    D := decompose_triangular(BB, v - 1, KK, KKhi, nvars);
	    res cat:= D;
	else
	    Append(~res, BB);
	end if;
	IndentPop();
    end for;

    return res;

end function;

intrinsic InternalZPDTriangular(I::RngMPol) -> []
{Internal}

    n := Rank(I);
    assert MonomialOrder(I) cmpeq <"lex">;
    B := GroebnerBasis(I);
    assert #B eq n;

    vprint Decomposition: "Decomposition of Triangular system by factorization";
    vprintf Decomposition, 2: "Triangular Ideal:\n %o\n", I;

    T := Cputime();

    K := BaseRing(I);
    D := decompose_triangular(B, n, K, Coercion(K, Generic(I)), []);
    D := [Ideal(B): B in D];

//"Res D:", D;
    for J in D do
	MarkGroebner(J);
    end for;

    vprintf Decomposition: "Final number of ideals: %o\n", #D;
    vprintf Decomposition:
	"Total Triangular Factorization Decomposition time: %o\n", Cputime(T);
    
    return D;
end intrinsic;
