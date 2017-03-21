freeze;

declare attributes Grp: BCI;

field_degree_poly := function(f)
    coeffs := Coefficients(f);
    K := sub<Universe(coeffs)|1>;
    deg := 1;
    coeffs := [a:a in coeffs|not IsZero(a)];
    for a in coeffs do
        deg := Lcm(deg, Degree(MinimalPolynomial(a, K)));
    end for;
    return deg;
end function;

reduce_field_poly_seq := function(Q)
    deg := 1;
    for f in Q do
        deg := Lcm(deg, field_degree_poly(f));
    end for;
    bigK := BaseRing(Universe(Q));
    if deg eq Degree(bigK) then
        return Q;
    end if;
    K := sub<bigK|deg>;
    P := PolynomialRing(K);
    return [P|f:f in Q];
end function;

function EltWithOrder(K, e)
    q1 := #K - 1;
    k := q1;
    P := PrimeBasis(e);
    M := [];
    for p in P do
	m := 0;
	while IsDivisibleBy(k, p) do
	    k div:= p;
	    m +:= 1;
	end while;
	assert m gt 0;
	Append(~M, m);
    end for;
    o := q1 div k;

    EM := [Valuation(e, p): p in P];

// "P:", P;
// "M:", M;
// "EM:", EM;
// "o:", o;

    h := 1;
    r := PrimitiveElement(K);
    r := r^k;
    fail := false;
    for i := 1 to #P do
	p := P[i];
	kk := o div p^M[i];
	s := r^kk;
	m := 0;
	while not IsOne(s) do
	    m +:= 1;
	    if m eq M[i] then
		break;
	    end if;
	    s := s^p;
	end while;

	if m lt EM[i] then
	    fail := true;
	    break;
	end if;

	h *:= p^(m - EM[i]);
    end for;
    assert not fail;

    r := r^h;
    return r;

end function;

roots_of_unity := function(p, Q)

    assert forall{o:o in Q|Gcd(p,o) eq 1};
    assert #Factorization(p) eq 1;

    e := Lcm(Q);
    fe := Factorization(e);
    ppows := {@ t[1]^t[2]: t in fe @};
    primes := {@ t[1]: t in fe @};
    pp_elts := [**];

    /* get elts with prime power orders */
    for q in ppows do
        ord := Modorder(p, q);
	if not ExistsConwayPolynomial(p, ord) then
	    printf "WARNING: no ConwayPolynomial(%m, %m) - Brauer characters not well defined\n", p, ord;
	end if;
        K := GF(p, ord);
        Append(~pp_elts, EltWithOrder(K, q));
    end for;

    /* build final answers */
    res := [* *];
    for o in Q do

	/* build o-th root of unity mod p */
        if o eq 1 then
	    /* really easy case */
            Append(~res, GF(p)!1);
            continue o;
        end if;

	/* the field it will live in */
	degK := Modorder(p, o);
	K := GF(p, degK);

	/* build prime power order bits of root of unity */
        fo := Factorization(o);
        temp := [* *]; /* storage for prime power order bits */
        for t in fo do
            po := t[1];
            eo := t[2];
            ind := Index(primes, po);
            assert fe[ind, 1] eq po;
            ee := fe[ind,2];
            zeta := pp_elts[ind];
	    z := zeta^(po^(ee-eo));
	    degzeta := Degree(Parent(pp_elts[ind]));
	    if degK mod Degree(Parent(pp_elts[ind])) ne 0 then
		z := GF(p, Modorder(p,po^eo)) ! z;
	    end if;
            Append(~temp, K!z);
        end for;

	/* is o a prime power? */
        if #temp eq 1 then 
            Append(~res, temp[1]);
            continue o;
        end if;

	/* build this one */
        r := K!1;
        for i := 1 to #fo do
            rt := temp[i];
            ppo := fo[i,1]^fo[i,2];
	    /* assert Order(rt) eq ppo; */
            r *:= rt ^ Modinv(o div ppo, ppo);
        end for;
        Append(~res, r);
    end for;

// conditions satisfied by elts of res 
// comment out checks as they take a bit of time!
// assert forall{i:i in [1..#Q]|Order(res[i]) eq Q[i]}; /* orders as required */
    /* next is compatibility of powers */
// assert forall{0:i,j in [1..#Q]|i ge j or
//	res[i]^(Q[i] div d) eq res[j]^(Q[j] div d) where d is Gcd(Q[i], Q[j])};

    return res;
end function;


InitBrauerCharacterInfo := procedure(~G, p, ~info, root_p, root_0, sparse)
    hasBCI := assigned G`BCI;
    if hasBCI then
	if exists(r){r: r in G`BCI|r`p eq p} then
	    info := r;
	    return;
	end if;
    end if;
    zeit := Cputime();
    // vprint IrrMods, 2: "Computing Brauer Character information";
    BCIF := recformat< pCls, lift_polys, lift_vals, lift_where, field, zeta,
		p, e, root_p >;
    cl := ClassesData(G);
    /* Get p-regular classes, skipping the identity */
    reg := {@i:i in [2..#cl]|not IsDivisibleBy(cl[i,1], p)@};
    e := Lcm([cl[i,1]: i in reg]);
    pm := PowerMap(G);
    // vprint IrrMods, 3: "Got power map after", Cputime(zeit), "seconds";
    info := rec<BCIF|
			p := p,
			e := e
	>;
    polys := [**];
    vals := [**];
    lift_where := [];
    reg_ords := {@ cl[i,1]: i in reg @};
    if IsZero(root_p) then
	roots := roots_of_unity(p, reg_ords);
    else
	assert IsOne(root_p^e);
	roots := [ root_p^(e div o) : o in reg_ords];
    end if;
    // vprint IrrMods, 3:"Found roots of unity mod", p, "after", Cputime(zeit), "seconds";
    if IsZero(root_0) then
	field := CyclotomicField(e: Sparse:=sparse);
	big_zeta := RootOfUnity(e, field);
    else
	big_zeta := root_0;
	field := Parent(big_zeta);
    end if;
    // vprint IrrMods, 2: "Will compute Brauer Characters in", field, "after", Cputime(zeit), "secs";
    done := {@ @};
    for i in reg do
        n := cl[i, 1];
        assert e mod n eq 0;
	/* subgroup of unit grp mod n that fixes this class */
        grp := {j:j in [1..n-1]|pm(i, j) eq i};
        ind := Index(done, <n, grp>);
        if ind gt 0 then
            lift_where[i] := ind;
            continue i;
        else
            Include(~done,  <n, grp>);
            lift_where[i] := #done;
        end if;
        z := roots[Index(reg_ords, n)]; /* n-th root of unity over GF(p) */
        zeta := big_zeta ^ (e div n); /* n-th root of unity in field */
	K := Parent(z);
        P := PolynomialRing(K); X := P.1;
        n_polys := [P|];
        n_vals := [];
        to_do := {0..n-1};
        while to_do ne {} do
            r := Rep(to_do);
	    /* the following powers of z will occur together as eigenvalues */
            powers := {(r*j) mod n : j in grp};
            to_do diff:= powers;
	    /* precompute corresp. polynomial factor */
            Append(~n_polys, &*[ X-z^j : j in powers]);
	    /* precompute corresp. brauer chtr values in all powers */
            Append(~n_vals, [&+[ zeta^(k*j) : j in powers]:k in [1..n-1]]);
        end while;
        Append(~polys, reduce_field_poly_seq(n_polys));
        Append(~vals, n_vals);
    end for;
    info`lift_polys := polys;
    info`lift_vals := vals;
    info`lift_where := lift_where;
    info`pCls := reg;
    info`field := field;
    info`zeta := big_zeta;
    if hasBCI then
	Append(~G`BCI, info);
    else
//i	G`BCI := [info];
    end if;
    // vprint IrrMods, 2: "Precomputation of Brauer Character data", Cputime(zeit), "seconds";
end procedure;

intrinsic BrauerCharacter (M::ModGrp : RootOfUnityCharp := 0, RootOfUnityChar0 := 0, Sparse := true) -> AlgChtrElt
{}
    zeit := Cputime();
    p := Characteristic(BaseRing(M));
    G := Group(M);
    ord := FactoredOrder(G);
    if #G eq 1 or (#ord eq 1 and ord[1,1] eq p) then
	return CharacterRing(G)!([Dimension(M)] cat [0:i in [1..#Classes(G) - 1]]);
    end if;
    InitBrauerCharacterInfo(~G, p, ~info, RootOfUnityCharp, RootOfUnityChar0, Sparse);
    K := info`field;
    chtr := [K|Dimension(M)];
    reg := info`pCls;
    polys := info`lift_polys;
    vals := info`lift_vals;
    lift_where := info`lift_where;
    len := #reg;
    cl := ClassesData(G);
    pm := PowerMap(G);
    rho := Representation(M);
    for i := len to 1 by -1 do
        c := reg[i];
	if IsDefined(chtr, c) then
	    continue i;
	end if;
        w := lift_where[c];
        i_polys := polys[w];
	d_i_polys := Degree(BaseRing(Universe(i_polys)));
        i_vals := vals[w];
        i_len := #i_polys;
	n := cl[c,1];
        val := [K| 0 : k in [1..n-1]];
        cp := CharacteristicPolynomial(ClassRepresentative(G, c)@rho);
	d_cp := Degree(BaseRing(Parent(cp)));
	d := Gcd(d_cp, d_i_polys);
	if d lt d_cp then
	    cp := PolynomialRing(GF(p, d))!cp;
	end if;
	if d lt d_i_polys then
	    cp := Universe(i_polys)!cp;
	end if;
        for j := 1 to i_len do
            f := i_polys[j];
	    i_vals_j := i_vals[j];
            repeat
                flag, quot := IsDivisibleBy(cp, f);
                if flag then
                    cp := quot;
		    for k := 1 to n-1 do
			val[k] +:= i_vals_j[k];
		    end for;
                else
                    continue j;
                end if;
            until false;
        end for;
	for k := 1 to n-1 do
	    ck := pm(c, k);
	    if IsDefined(chtr, ck) then 
		continue k;
	    end if;
	    chtr[ck] := val[k];
	end for;
    end for;
    for i := 1 to #cl do
	if cl[i,1] mod p eq 0 then chtr[i] := K!0; end if;
    end for;
    // vprint IrrMods, 2: "BrauerCharacter:", Cputime(zeit), "seconds";
    return CharacterRing(G)!Minimize(chtr);
end intrinsic;

