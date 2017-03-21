freeze;

function reldegs(G, N, p)

// The following function takes p, a rational prime, G a a finite p-group,
// and N a central, cyclic subgroup of G.  If lambda is a faithful character
// of N, then we return a sequence S [C_0, C_1, ...], where C_i is the
// number of irreducible characters of G lying over lambda with degree p^i.

    if IsAbelian(G) then
	return [Index(G, N)];
    end if;

    // The index of N in G is greater than p

    G := ConditionedGroup(G);
    k := NPCgens(G);
    repeat
	y := G.k; k -:= 1;
    until y notin N;
    M := sub<G | y, N>;
    // assert IsAbelian(M);
    // assert IsNormal(G, M);
    C := Centralizer(G, y);
    k := Index(G, C);
    // assert k eq 1 or k eq p;
    // assert IsNormal(G, C);
    // N is central in G, so C is Centralizer(G,M)
    if IsCyclic(M) then
	T := $$(C, M, p);
	if k eq 1 then
	    // G = C
	    return [p * T[i] : i in [1..#T]];
	end if;
	// G > C
	Insert( ~T, 1, 0 );
	return T;
    end if;

    // M is not cyclic, but is abelian.
    // M has abelian invariants [p, #N]
    if not IsIdentity(y^p) then
	// Find a replacement for y having order p.
	// The proportion in M is p(p-1)/#M = (p-1)/#N, which could be bad 
	// for random search if #N >> p. But M is abelian, so the following
	// line should work ok, giving H of order p^2, still containing all
	// p(p-1) possible y's
	/*
	H := Omega(M, 1); // assert #H eq p^2;
	repeat
	    y := Random(H);
	until y notin N; // success probability is (p-1)/p >= 1/2
	// assert IsIdentity(y^p);
	*/
	ab := AbelianBasis(M);
	fl := exists(y){y:y in ab | IsIdentity(y^p)};
	assert fl;
    end if;
    if k eq 1 then
	// G = C
	y := G!y;
	Q, f := quo<G | y >;
	M2 := M@f;
	S := $$(Q, M2, p);
	x := G!(N.NPCgens(N));
	for i := 2 to p do
	    y := y * x;
	    Q, f := quo<G | y >;
	    M2 := M@f;
	    T := $$(Q, M2, p);
	    if #S lt #T then
		S := [S[i] + T[i] : i in [1..#S]] cat T[#S + 1..#T];
	    elif #S eq #T then
		S := [S[i] + T[i] : i in [1..#S]];
	    else
		S := [S[i] + T[i] : i in [1..#T]] cat S[#T + 1..#S];
	    end if;
	end for;
	return S;
    end if;

    // G > C
    Q, f := quo<C | y >;
    M := M@f;
    T := $$(Q, M, p);
    Insert (~T, 1, 0);
    return T;
end function;

// Given a finite p-group G, return an integer sequence [C_0, C_1, ...],
// where C_i is the number of irreducible characters of G with degree p^i;

function chardegs(G)

    G := ConditionedGroup(G);
    f := FactoredOrder(G);
// "Enter chardegs", f;
    if #f eq 0 then return [1]; end if;
    // assert #f eq 1;

    p := f[1, 1];
    if IsAbelian(G) then
	k := #G;
	vprintf Chtr: "Chardegs p-grp: End order %o^%o with %o characters\n",
		p, f[1,2], k;
	return [k];
    end if;

    // order of G is > p^2
    X := sub<G | G.NPCgens(G) >;
    // assert IsCentral(G,X);
    S := $$(G / X);
    vprintf Chtr, 2: "Chardegs p-grp: Order %o^%o\n", p, f[1,2];
    T := reldegs(G, X, p);
    p1 := p-1;
    if #S lt #T then
	T :=  [S[i] + p1*T[i] : i in [1..#S]] cat
			 [p1*T[i] : i in [#S + 1..#T]];
    elif #S eq #T then
	T :=  [S[i] + p1*T[i] : i in [1..#S]];
    else
	T :=  [S[i] + p1*T[i]: i in [1..#T]] cat S[#T + 1..#S];
    end if;
// "Leave chardegs", f, T;
    vprintf Chtr: "Chardegs p-grp: End order %o^%o with %o characters\n", p, f[1,2], &+T;
    return T;
end function;

// The following function returns whether the character degrees as given
// in S are correct for the group G

function checkchardegs(G, S)
    p := FactoredOrder(G)[1][1];
    assert( p ge 2 );
    k := Order(G);
    sum := 0;
    for i := 1 to #S do
	sum +:= S[i] * p^(2 * (i - 1));
    end for;
    return sum eq k;
end function;

// Given a finite p-group G, return an integer sequence [C_0, C_1, ...],
// where C_i is the number of irreducible characters of G with degree p^i;

intrinsic CharacterDegreesPGroupOld(G::GrpPC) -> []
{}
    require #FactoredOrder(G) le 1: "Argument must be a p-group";
    return chardegs(G);
end intrinsic;

intrinsic CharacterDegreesPGroup(G::GrpAb) -> []
{}
    require #FactoredOrder(G) le 1: "Argument must be a p-group";
    return [#G];
end intrinsic;

intrinsic CharacterDegreesPGroup(G::GrpPerm) -> []
{}
    require #FactoredOrder(G) le 1: "Argument must be a p-group";
    return CharacterDegreesPGroup(PCGroup(G));
end intrinsic;

intrinsic CharacterDegreesPGroup(G::GrpMat) -> []
{The sequence [C_0, C_1, ...] where C_i is the number of irreducible characters of G with degree p^i for the finite p-group G}
    require #FactoredOrder(G) le 1: "Argument must be a p-group";
    return CharacterDegreesPGroup(PCGroup(G));
end intrinsic;
