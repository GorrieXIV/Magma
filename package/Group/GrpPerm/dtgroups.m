freeze;

procedure dterror(g, t, d, q)
    if t ne 0 or d ne 0 or q ne 0 then
	error
	    "Error recognizing Group", g, "\n",
	    "Failed at type", t, "\n",
	    "q was determined to be", q, "\n",
	    "d was determined to be", d, "\n";
    else
	error "Error recognizing Group", g;
    end if;
end procedure;	// dterror(g, t, d, q)

function logthm(a, b)
/*
The integer b is some power of the integer a; return c
as the Exponent ie a^c == b.
*/
    if exists(i){i: i in [1 .. b] | a^i eq b} then
	return i;
    end if;
    error "Integer", b, "is not a power of integer", a;
end function;	// logthm(a, b)

function ispower(n, m);
/* ispower returns true if n is a power of m.  */
    e := Factorization(n);
    f := Factorization(m);
    return #e eq #f and forall{
	i: i in [1 .. #e] | e[i][1] eq f[i][1] and e[i][2] mod f[i][2] eq 0
    } where e is Factorization(n) where f is Factorization(m);
end function;	// ispower(n, m)

dttypes := [
    <"Sym(d); Alt(d)", "d">,
    <"PSL(d, q), d >= 3; A7 (d = 4, q = 2)", "(q^d - 1) / (q - 1)">,
    <"PSL(2, q)", "q + 1">,
    <"Sz(q), q = 2^(2*d+1), d >= 1", "q^2 + 1">,
    <"PSU(3, q), q > 2", "q^3 + 1">,
    <"R(q), q = 3^(2*d+1), d > 1; PGammaL(2, 8) (q = 3)", "q^3 + 1">,
    <"Sp(2*d, 2), d >= 3", "2^(d - 1) * (2^d +/- 1)">,
    <"Sporadic groups, 3-transitive", "various">,
    <"Sporadic groups, not 3-transitive", "various">,
    <"T.SL(d, q), d > 2, q = p^e > 2", "q^d">,
    <"T.Sp(d, q), q = p^e > 2", "q^d">,
    <"T.G(2, q), q = 2^e > 2", "q^6">,
    <"T.SL(d, 2); T.A7 (d = 4)", "2^d">,
    <"T.Sp(d, 2), d even; T.A6 (d = 4)", "2^d">,
    <"T.G(2, 2); T.PSU(3, 3)", "2^6">,
    <"T.SL(2, q), q = p^e > 3", "q^2">,
    <"G <= AGammaL(1, q), q = p^e > 4", "q">,
    <"Soluble exceptions (Huppert)", "various">,
    <"Insoluble exceptions (Hering)", "various">
];

sporadics := [
    <"M11", 11>,
    <"M12", 12>,
    <"M22", 22>,
    <"M23", 23>,
    <"M24", 24>
];

sporadics[7] := <"HS", 176>;
sporadics[14] := <"Co3", 276>;

procedure result(g, tup)
/* Output result of the 2-transitive Group analysis */
    mns := "minimal normal subgroup.";
    t, f, d, q, auto, exact := Explode(tup);
    n := Degree(g);
    desc := dttypes[t + 1][1];
    degree := dttypes[t + 1][2];
    printf "The group is of type %o which comprises %o\n", t, desc;
    if degree ne "various" then
	printf "The degree of this type is given by %o\n", degree;
    end if;
    if t in {9 .. 15} then
	print "The group is non-soluble and has a regular normal subgroup of order", n;
    end if;

    case t:
    when 0:
	assert n eq d;
	printf "The group is the %o group of degree %o\n",
	    f eq "Sym" select "symmetric" else "alternating", n;
    when 1:
	assert (f eq "A" and d ge 2) or (f eq "Alt" and d eq 7);
	if f eq "A" then
	    printf "The group has PSL(%o, %o) as a %o\n", d + 1, q, mns;
	else
	    print "The group is the alternating group A7 acting on 15 points";
	end if;
    when 2:
	assert f eq "A" and d eq 1;
	printf "The group has PSL(2, %o) as a %o\n", q, mns;
    when 3:
	assert f eq "2B" and d eq 2;
	assert ispow and IsOdd(exponent) and exponent ge 3
	    where ispow, exponent is IsPowerOf(q, 2);
	printf "The group has Sz(%o) as a %o\n", q, mns;
    when 4:
	assert f eq "2A" and d eq 2 and q ge 3;
	printf "The group has PSU(3, %o) as a %o\n", q, mns;
    when 5:
	assert  (f eq "2G" and d eq 2) or
		(f eq "A" and d eq 1 and q eq 8 and auto);
	if f eq "2G" then
	    assert ispow and IsOdd(exponent) and exponent ge 5
		where ispow, exponent is IsPowerOf(q, 3);
	    printf "The group has R(%o) as a %o\n", mns;
	else
	    printf "The group is PGammaL(2, 8) acting on 28 points. ";
	    printf "Its soluble residual is of index 3 and is PSL(2, 8),";
	    printf "which is not 2-transitive.\n";
	end if;
    when 6:
	assert f eq "C" and d ge 3 and q eq 2;
	printf "The group is Sp(%o, 2)\n", 2*d;
    when 7:
	assert  (f eq "Sporadic" and q eq 0 and IsDefined(sporadics, d)) or
		(f eq "A" and d eq 1 and q eq 8 and auto);
	if f eq "A" then
	    printf "The group is PSigmaL(2, 8) acting on 28 points.  Its soluble residual is of index 3 and is PSL(2, 8) which is not 2-transitive\n";
	else
	    printf "The group is%o the simple group %o",
	      auto select " the automorphism group of" else "", sporadics[d][1];
	    if n ne sporadics[d][2] then
		printf " on %o points", n;
	    end if;
	end if;
	printf "\n";
    when 8:
	assert  (f eq "Sporadic" and q eq 0 and IsDefined(sporadics, d)) or
		(f eq "A" and d eq 1 and q eq 11 and n eq 11);
	if f eq "Sporadic" then
	    printf "The group is%o the simple group %o",
	      auto select " the automorphism group of" else "", sporadics[d][1];
	    if n ne sporadics[d][2] then
		printf " on %o points", n;
	    end if;
	else
	    print "The group is PSL(2, 11) acting on 11 points.";
	end if;
    when 9:
	assert f eq "A" and d ge 2 and q gt 2;
	printf "The soluble residual is ASL(%o, %o)\n", d + 1, q;
    when 10:
	assert f eq "C" and q gt 2;
	printf "The group is ASp(%o, %o)\n", 2 * d, q;
    when 11:
	assert f eq "G" and d eq 2 and q gt 2;
	printf "The soluble residual is AG(2, %o)\n", q;
    when 12:
	assert (f eq "A" and q eq 2) or (f eq "Alt" and d eq 7);
	if f eq "A" then
	    printf "The soluble residual is ASL(%o, 2)\n", d + 1;
	else
	    print "The group is 2^4 . A7";
	end if;
    when 13:
	assert (f eq "C" and q eq 2) or (f eq "Alt" and d eq 6);
	if f eq "C" then
	    printf "The group is ASp(%o, 2)\n", 2 * d;
	else
	    print "The group is 2^4 . A6";
	end if;
    when 14:
	assert  (f eq "G" and d eq 2 and q eq 2) or
		(f eq "2A" and d eq 2 and q eq 3);
	if f eq "G" then
	    print "The soluble residual is AG(2, 2)";
	else
	    print "The group is 2^6 . PSU(3, 3)";
	end if;
    when 15:
	assert f eq "A" and d eq 1 and q gt 3;
	printf "The soluble residual is ASL(2, %o)\n", q;
    when 16:
	assert f eq "A" and d eq 0 and q gt 4;
	printf "The group is%o AG%oL(1, %o)\n",
	    exact select "" else " a subgroup of",
	    auto select "amma" else "", q;
    when 17:
	assert f eq "Huppert";
	print "The group is a Huppert exception";
    when 18:
	assert f eq "Hering";
	print "The group is a Hering exception";
    end case;
end procedure;	// result(g, tup)

function exceptions(g, norbits, lorbit)
/*
g is a 2-transitive Group containing a regular normal
Subgroup. The number of Orbits of the two point Stabilizer
is 'norbits', while the Length of the i-th is stored as
the i-th Component of the integer sequence 'lorbit'.

g is one of the following groups:-
soluble:
(a) a Subgroup of Aut( AGL( 1, q ) )
(b) a Huppert exception
non-soluble:
(a) T . SL( 2, q )
(b) one of the following Hering exceptions:
type IV, E1, E4

Returns whether it identified the group and the (t, d, q) identification tag.
*/
    n := Degree(g);
    gorder := FactoredOrder(g);
    e := Factorization(n);
    if #e ne 1 then return false, 0, 0, 0; end if;
    q := e[1][1];
    d := e[1][2];

    // Case : T . SL(2, q); AYL(1, 16)
    if n ge 16 and  #e eq 1 and e[1][2] mod 2 eq 0 then
	// test whether
	// (1) an initial subsequence of the lengths of the Orbits of gab
	//        sums to q; and
	// (2) all remaining Orbit lengths are divisible by q.
	q := e[1][1] ^ (e[1][2] div 2);
	q1 := 0;
	for i in {1..norbits} do
	    q1 +:= lorbit[i];
	    if q1 eq q then tsl1 := true; bl := i; break; end if;
	    if q1 gt q then tsl1 := false; bl := i; break; end if;
	end for;

	if tsl1 and bl + 1 le norbits then
	    tsl2 := true;
	    for j := bl + 1 to norbits do
		tsl2 := tsl2 and lorbit[j] mod q eq 0;
	    end for;
	    if tsl2 then
		// when n := 16, the Group could be either AYL(1, q)
		// or T . SL(2, 4).
		// when n gt 16, the Group must be T . SL(2, q)
		if n eq 16 and IsSolvable(g) then
			return true, <16, "A", 0, n, true, true>;
		end if;
		return true, <15, "A", 1, q, false, false>;
	    end if;
	end if;
    end if;

    // construct the derived series of g

    dseries := DerivedSeries( g );
    dlength := #dseries - 1;
    h := dseries[dlength + 1];

    // Case: g < AYL( 1, q )
    if h eq sub<g | Id(g)> then
	if dlength le 3 then
	    if dlength eq 2 then
		return true, <16, "A", 0, n, false, true>;
	    end if;
	    if gorder eq Factorization(n*(n - 1)*d) then
		return true, <16, "A", 0, n, true, true>;
	    end if;

	    // Subgroup of AYL(1, q)
	    return true, <16, "A", 0, n, true, false>;

	// Case : Huppert exceptions
	else
	    // Subcase : Degree 3^2
	    if n eq 3^2 then
		if gorder eq [<2, 4>, <3, 3>] then
		    return true, <17, "Huppert", 3, 2, false, false>;
		end if;
		if gorder eq [<2, 3>, <3, 3>] then
		    return true, <17, "Huppert", 3, 2, false, false>;
		end if;
	    end if;	// huppert 3^2

	    // Subcase : Degree 5^2
	    if n eq 5^2 then
		if gorder eq [<2, 5>, <3, 1>, <5, 2>] then
		    return true, <17, "Huppert", 5, 2, false, false>;
		end if;
		if gorder eq [<2, 4>, <3, 1>, <5, 2>] then
		    return true, <17, "Huppert", 5, 2, false, false>;
		end if;
		if gorder eq [<2, 3>, <3, 1>, <5, 2>] then
		    return true, <17, "Huppert", 5, 2, false, false>;
		end if;
	    end if;

	    // Subcase : Degree 7^2
	    if n eq 7^2 then
		if gorder eq [<2, 4>, <3, 2>, <7, 2>] then
		    return true, <17, "Huppert", 7, 2, false, false>;
		end if;
		if gorder eq [<2, 4>, <3, 1>, <7, 2>] then
		    return true, <17, "Huppert", 7, 2, false, false>;
		end if;
	    end if;	// huppert 7^2

	    // Subcase : Degree 11^2
	    if n eq 11^2 then
		if gorder eq [<2, 4>, <3, 1>, <5, 1>, <11, 2>] then
		    return true, <17, "Huppert", 11, 2, false, false>;
		end if;
		if gorder eq [<2, 3>, <3, 1>, <5, 1>, <11, 2>] then
		    return true, <17, "Huppert", 11, 2, false, false>;
		end if;
	    end if;	// huppert 11^2

	    // Subcase : Degree 23^2
	    if n eq 23^2 then
		if gorder eq [<2, 4>, <3, 1>, <11, 1>, <23, 2>] then
		    return true, <17, "Huppert", 23, 2, false, false>;
		end if;
	    end if;	// huppert 23^2

	    // Subcase : Degree 3^4
	    if n eq 3^4 then
		if gorder eq [<2, 7>, <3, 4>, <5, 1>] then
		    return true, <17, "Huppert", 3, 4, false, false>;
		end if;
		if gorder eq [<2, 6>, <3, 4>, <5, 1>] then
		    return true, <17, "Huppert", 3, 4, false, false>;
		end if;
		if gorder eq [<2, 5>, <3, 4>, <5, 1>] then
		    return true, <17, "Huppert", 3, 4, false, false>;
		end if;
	    end if;	// huppert 3^4

	    if n notin {3^2, 5^2, 7^2, 11^2, 23^2, 3^4} then
		error "Error detected in degree of a Huppert exception";
	    end if;
	end if;

    // Case : Hering exceptions not treated elsewhere
    else	// insoluble
	hbase := Base(h);
	a := hbase[1];
	haorder := FactoredOrder(Stabilizer(h, a));

	// Subcase type IV : E(32) . A5 acting on 3^4
	if n eq 3^4 then
	    if haorder eq [<2, 7>, <3, 1>, <5, 1>] then
		// return true, 19, 4, 2;
		return true, <18, "Hering", 0, 0, false, false>;
	    end if;
	end if;	// Degree 3^4

	// Subcase E1 : SL(2, 5) acting on 9^2, 11^2, 19^2, 29^2 or 59^2
	if n in {81, 121, 361, 841, 3481} and
		haorder eq [<2, 3>, <3, 1>, <5, 1>] then
	    // return true, 20, 2, q;
	    return true, <18, "Hering", 0, 0, false, false>;
	end if;

	// Subcase E4 : 3^6 . SL( 2, 13 )
	if n eq 3^6 then
	    if haorder eq [<2, 3>, <3, 1>, <7, 1>, <13, 1>] then
		// return true, 23, 6, 3;
		return true, <18, "Hering", 0, 0, false, false>;
	    end if;
	end if;	// Degree 3^6
    end if;	// insoluble exceptions
    return false, 0;
end function;	// exceptions(g, norbits, lorbit)

function sporadic(g)
/*
recognize various sporadic groups
*/
    n := Degree(g);
    gorder := FactoredOrder(g);

    // Cases : PSL(2, 11) on 11 points and M11
    if n eq 11 then
	if gorder eq [<2, 2>, <3, 1>, <5, 1>, <11, 1>] then
	    return true, <8, "A", 1, 11, false, false>;
	end if;
	if gorder eq [<2, 4>, <3, 2>, <5, 1>, <11, 1>] then
	    return true, <7, "Sporadic", 1, 0, false, false>;
	end if;
    end if;	// PSL(2, 11) and M11

    // Case : M11 on 12 points and M12
    if n eq 12 then
	if gorder eq [<2, 4>, <3, 2>, <5, 1>, <11, 1>] then
	    return true, <7, "Sporadic", 1, 0, false, false>;
	end if;
	if gorder eq [<2, 6>, <3, 3>, <5, 1>, <11, 1>] then
	    return true, <7, "Sporadic", 2, 0, false, false>;
	end if;
    end if;	// M11 on 12 points and M12

    // Cases : M22 and Aut(M22)
    if n eq 22 then
	if gorder eq [<2, 7>, <3, 2>, <5, 1>, <7, 1>, <11, 1>] then
	    return true, <7, "Sporadic", 3, 0, false, false>;
	end if;
	if gorder eq [<2, 8>, <3, 2>, <5, 1>, <7, 1>, <11, 1>] then
	    return true, <7, "Sporadic", 3, 0, true, false>;
	end if;
    end if;	// M22 and Aut(M22)

    // Case : M23
    if n eq 23 and gorder eq [<2, 7>, <3, 2>, <5, 1>, <7, 1>, <11, 1>, <23, 1>]
    then
	return true, <7, "Sporadic", 4, 0, false, false>;
    end if;

    // Case : M24
    if n eq 24 and gorder eq [<2, 10>, <3, 3>, <5, 1>, <7, 1>, <11, 1>, <23, 1>]
    then
	return true, <7, "Sporadic", 5, 0, false, false>;
    end if;

    // Case : Aut(PSL(2,8)) acting on 28 points
    if n eq 28 and gorder eq [<2, 3>, <3, 3>, <7, 1>] then
	return true, <7, "A", 1, 8, true, false>;
    end if;

    // Case : Higman-Sims on 176 points
    if n eq 176 and gorder eq [<2, 9>, <3, 2>, <5, 3>, <7, 1>, <11, 1>] then
	return true, <7, "Sporadic", 7, 0, false, false>;
    end if;

    // Case : Conway Group co3 on 276 points
    if n eq 276 and gorder eq [<2, 10>, <3, 7>, <5, 3>, <7, 1>, <11, 1>, <23,1>]
    then
	return true, <7, "Sporadic", 14, 0, false, false>;
    end if;

    return false, 0;
end function;	// sporadic(g)

function dtgroups(g)
// Identify <t, f, d, q, aut, exact> information for doubly-transitive group g
/*************************************************
*                                                *
*   Analyze the doubly transitive Group g.       *
*                                                *
**************************************************/
    t := Cputime();
    n := Degree(g);

    // Case : alternating or symmetric on n letters
    if IsAltsym(g) then
	is_sym := false;
	for i in {1..Ngens(g)} do
	    if not IsEven(g.i) then
		is_sym := true;
		break;
	    end if;
	end for;

	return <0, is_sym select "Sym" else "Alt", n, 0, false, true>;
    end if;	// symmetric/alternating case

    t := Cputime(t);
    zeit := t / 1000.0;
    // print " Stage 1 time := ", zeit, " seconds";

    // Case : g is not 2-transitive
    error if not IsTransitive(g, 2), "Group is not 2-transitive";

    // define the Stabilizer gab of two points a and b
    gbase := Base(g);
    gab := Stabilizer(g, [gbase[1], gbase[2]]);
    gorder := FactoredOrder(g);
    o := Orbits(gab);
    norbits := #o;
    lorbit := Sort([#o[i]: i in {1..norbits}]);

    // determine last breakpoint (if any)
    breakpoint := false;
    if norbits gt 3 then
	for i in [norbits - 1 .. 3 by -1] do
	    sum := 0;
	    for j in {1..i} do
		sum +:= lorbit[j];
	    end for;
	    sumsqr := (sum - 1) ^ 2;
	    if i ne 2 and lorbit[i+1] ge sumsqr then
		bp := i;
		breakpoint := true;
		break;
	    end if;
	end for;
    end if;

    // The 2 point Stabilizer has a breakpoint
    if breakpoint then
	// Case : PGL( d, q ) , d ge 3, and A(7) on 15 points
	m := 0;
	for j in {1..bp} do
	    m := m + lorbit[j];
	end for;

	pow := ispower(n, m);
	if not pow then
	    if norbits ne bp + 1 then dterror(g,12,0,7); end if;
	    if n eq 15 and gorder eq [<2, 3>, <3, 2>, <5, 1>, <7, 1>] then
		return <1, "Alt", 7, 0, false, true>;
	    end if;
	    q := m - 1;
	    d := logthm(q, n * (q - 1) + 1);
	    return <1, "A", d - 1, q, false, false>;
	end if;	// PGL(d, q), d ge 3, and A7

	// Case : T . SL( d, q ), d ge 3
	q := m;
	d := logthm(q, n);
	if norbits eq bp + 1 and d ge 3 then
	    return <9, "A", d - 1, q, false, false>;
	end if;	// t . sl(d, q)

	// Case : T . Sp( d, q ), q ne 2
	if bp + 2 le norbits then
	    if lorbit[bp+1] eq q^(d - 1) - q then
		spl := true;
		for j in {bp + 1 .. norbits} do
		    olength := lorbit[j];
		    spl := spl and (olength mod q^(d - 1) eq 0);
		end for;
		if spl then
		    return <10, "C", d div 2, q, false, false>;
		end if;
	    end if;	// t . sp(d, q)
	end if;

	// Case : T . G2( q ), q ne 2
	if bp + 3 le norbits then
	    if d eq 6 and lorbit[bp+1] eq (q^3 - q) and
			  lorbit[bp+2] eq (q^5 - q^3) then
		g2q := true;
		for j in {bp + 3 .. norbits} do
		    olength := lorbit[j];
		    g2q := g2q and (olength mod q^5 eq 0);
		end for;
		if g2q then
		    return <11, "G", 2, q, false, false>;
		end if;
	    end if;
	end if;	// t . g(2, q)

	// Case : soluble groups; Hering exceptions; T.SL(2, q)
	res, tup := exceptions(g, norbits, lorbit);
	if res then
	    return tup;
	end if;

	// The 2 point Stabilizer does not have a break point
    else	// no breakpoint
	e := Factorization(n);
	f := Factorization(n - 1);

	// Case : PSL(2, q) and 2-transitive extensions
	if #f eq 1 and norbits eq 4 then
	    if lorbit[3] eq lorbit[4] then
		// if n := 8, must distinguish between psl(2, 7)) and ayl(1, 8)
		if n eq 8 then
		    if IsSolvable(g) then
			return <16, "A", 0, 8, true, false>;
		    end if;
		    return <2, "A", 1, 7, false, false>;
		end if;
		q := n - 1;
		if (q - 1) div 2 ne lorbit[3] then
		    dterror(g,4,2,q);
		end if;
		return <2, "A", 1, q, false, false>;
	    end if;
	end if;	// PSL(2, q)

	// Cases : 3-transitive groups - PGL(2, q), T.SL(d, 2), T.A7
	if norbits eq 3 then
	    res, tup := sporadic(g);
	    if res then return tup; end if;
	    gabc := Stabilizer(g, [gbase[1], gbase[2], gbase[3]]);
	    o3 := Orbits(gabc);
	    lastorbit := Max([#o[i]: i in {1..norbits}]);

	    // Degree is a power of 2
	    if #e eq 1 and e[1][1] eq 2 then
		q := e[1][1];
		d := e[1][2];

		// Subcases : PGL( 2, 7 ) and 2^3 . SL( 3, 2 )
		if d eq 3 then
		    if gorder eq [<2, 4>, <3, 1>, <7, 1>] then
			return <2, "A", 1, 7, false, false>;
		    end if;
		    if gorder eq [<2, 6>, <3, 1>, <7, 1>] then
			return <12, "A", 2, 2, false, false>;
		    end if;
		end if;

		// Subcases : 2^4 . A7 and 2^4 . SL( 4, 2 )
		if d eq 4 then
		    if gorder eq [<2, 7>, <3, 2>, <5, 1>, <7, 1>] then
			return <12, "Alt", 7, 0, false, false>;
		    end if;
		    if gorder eq [<2, 10>, <3, 2>, <5, 1>, <7, 1>] then
			return <12, "A", 3, 2, false, false>;
		    end if;
		end if;

		// Subcases : PGL(2, q) and 2^d . SL(d, 2), d gt 4 
		if d gt 4 then
		    if lastorbit eq 2^d - 4 then
			return <12, "A", d - 1, 2, false, false>;
		    end if;
		    return <2, "A", 1, n - 1, false, false>;
		end if;

	    // Subcase : PGL(2, q), q + 1 not a power of 2
	    else	// Degree is not a Prime power
		if #f ne 1 then dterror(g,4,2,n-1); end if;
		return <2, "A", 1, n - 1, false, false>;
	    end if;
	end if;	// 3-transitive cases

	// Cases : T . Sp( d, 2 ) and T . A6 ( d := 4 )
	if #e eq 1 and e[1][1] eq 2 then
	    q := 2;
	    d := e[1][2];
	    if lorbit[3] eq 2^(d - 1) - 2 then
		if d eq 4 then
		    if gorder eq [<2, 7>, <3, 2>, <5, 1>] then
			return <13, "Alt", 6, 0, false, false>;
		    end if;
		end if;
		// d gt 4
		return <13, "C", d div 2, q, false, false>;
	    end if;
	end if;	// t.sp(d,2) and t.a6

	// Cases : T . G2( 2 ) and T . PSU( 3, 3 )
	if n eq 2^6 and norbits eq 5 then
	    if lorbit[3] eq 6 and lorbit[4] eq 24 then
		if gorder eq [<2, 12>, <3, 3>, <7, 1>] then
		    return <14, "G", 2, 2, false, false>;
		end if;
		if gorder eq [<2, 11>, <3, 3>, <7, 1>] then
		    return <14, "2A", 2, 3, false, false>;
		end if;
	    end if;
	end if;	// t.g2(2) and t.psu(3, 3)

	// Case : PSp( 2d, 2 )
	//   check whether the Degree n satisfies either
	//     n := 2^(d-1) * (2^d - 1) OR
	//     n :=  2^(d-1) * ( 2^d + 1 ) and n gt 10
	if norbits eq 4 then
	    if e[1][1] eq 2 then
		d := e[1][2] + 1;
		if (n eq 2^(d-1) * (2^d - 1))
			and lorbit[3] eq 2*(2^(2*d - 3) - 2^(d - 2) - 1)
			and lorbit[4] eq 2^(2*d - 2) then
		    return <6, "C", d, 2, false, false>;
		end if;
		if (n eq 2^(d-1) * (2^d + 1)) and (n gt 10)
			and lorbit[3] eq 2^(2*d - 2)
			and lorbit[4] eq 2*(2^(2*d - 3) + 2^(d - 2) - 1) then
		    return <6, "C", d, 2, false, false>;
		end if;
	    end if;
	end if;	// case PSP(2d, 2)

	// Case : Sporadic groups
	res, tup := sporadic(g);
	if res then return tup; end if;

	// Case : Sz(q)
	if #f eq 1 and f[1][1] eq 2 and f[1][2] mod 2 eq 0 and n ne 5 then
	    q := f[1][1] ^ (f[1][2] div 2);
	    if lorbit[3] eq q - 1 then
		return <3, "2B", 2, q, false, false>;
	    end if;
	end if;	// sz(q)

	// Cases : PSU(3, q) and R(q)
	if #f eq 1 and f[1][2] mod 3 eq 0 then
	    q := f[1][1] ^ ( f[1][2] div 3 );
	    if lorbit[3] eq q - 1 and n ne 9 then
		return <4, "2A", 2, q, false, false>;
	    end if;
	    if lorbit[3] eq (q - 1) div 2 then
		return <5, "2G", 2, q, false, false>;
	    end if;
	    if not (lorbit[3] in [q - 1, (q - 1) div 2]) then
		dterror(g, 6, 0, q);
	    end if;
	end if;	// psu(3, q) and r(q)

	// Case : soluble groups; Hering exceptions; T . SL(2, q)
	res, tup := exceptions(g, norbits, lorbit);
	if res then
	    return tup;
	end if;
    end if;	// no breakpoints
    dterror(g, 0, 0, 0);
end function;

intrinsic TwoTransitiveGroupIdentification(g::GrpPerm: Print := false) -> Tup
{ Identify a doubly-transitive group g}
    tup := dtgroups(g);
    if Print then
	result(g, tup);
    end if;
    return tup;
end intrinsic;
