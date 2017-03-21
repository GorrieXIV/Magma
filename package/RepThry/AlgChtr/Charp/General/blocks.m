freeze;

/*******************************************************************************
 * Blocks, Block intrinsics:
 *
 * Produce p-blocks by inspection of the character table.
 * Algorithm first takes out characters of p-defect zero,
 * then applies Corollary 3.25 of Navarro, Characters and Blocks of Finite
 * Groups, to get the rest of the split. The blocks are produced
 * by decreasing defect. If X is the character table in Magma's usual 
 * order then the principal block will come first and the
 * defect zeros are tacked on the end.
 * Characters are represented by their index in X. Second return value
 * is the sequence of block defects.
 *
 * Bill Unger, Dec 2005
 *
 * Method is to compute inner products over p-regular elements and see which
 * are zero and non-zero. Different blocks implies inner product zero.
 * Same block and one character with height zero implies inner product
 * non-zero. This is why we look at characters by increasing defect.
 *
 * For speed, we compute inner products in prime field GF(q),
 * such that q = 1 mod (exponent of G) and q > 2p^a, where p^a = p_part of #G.
 * It can be shown that the complex inner product can be deduced from the
 * mod q one. Sketch of proof:
 * a) All the (complex) inner products are rational with denominator
 *    dividing p^a.
 *      Pf: Investigate Cartan matrix and its inverse. Cartan matrix has
 *          all elementary divisors dividing p^a (Curtis & Reiner Thm 89.8)
 *          and all the inner products are integer linear combs of entries
 *          of the inverse of the Cartan matrix, since these entries are
 *          the inner products of the Brauer irreducibles.
 * b) All the inner products are <= 1 in absolute value.
 *      Pf: Comparing with ordinary norm shows that diagonal inner products
 *            are <= 1. Now apply Cauchy-Schwarz inequality.
 * c) Sort it out from here on your own...
 *
 * In the code we only need to distinguish zero and non-zero, and we omit
 * the factor of 1/#G.
 *
 * Bill Unger, April 2006
 */

intrinsic Blocks(X::SeqEnum[AlgChtrElt],  p::RngIntElt) -> SeqEnum, SeqEnum
{The partition of the character table X into blocks for the prime p}

    require IsPrime(p): "Second argument must be prime";
    R := Universe(X);
    if assigned R`Group then
	G_ord := FactoredOrder(R`Group);
    else
	G_ord := Factorization(GroupOrder(R));
    end if;
    if exists(t){t:t in G_ord|t[1] eq p} then
	G_val := t[2];
    else
	return [{i}:i in [1..#X]], [0:i in [1..#X]];
    end if;

    /* set up pairs <chtr number, defect> */
    pairs := [<i, G_val - Valuation(Degree(X[i]), p)>: i in [1..#X]];

    d0 := [t[1]:t in pairs|t[2] eq 0]; /* p-defect zero characters */
    if #d0 gt 0 then
	pairs := [t:t in pairs|t[2] ne 0];
    end if;
    if #pairs eq 0 then
	return [{i}:i in [1..#X]], [0:i in [1..#X]];
    end if;

    /* find a prime q */
    cl := ClassesData(R);
    e := LCM([c[1]: c in cl]);
    L := 2*p^G_val;
    if e ge L then q := e + 1;
    elif L mod e eq 0 then q := L + 1;
    else q := ((L div e) + 1)*e + 1;
    end if;
    while not IsPrime(q) do q +:= e; end while;
    K := GF(q);
    zeta := PrimitiveElement(K);

    res := [];
    res_d := [];
    p_reg := {i:i in [1..#cl]|cl[i,1] mod p ne 0};
    sizes := [cl[i,2]:i in [1..#cl]];
    Z := Integers();
    V := VectorSpace(K, #cl);
    X_K := [V|];
    for t in pairs do
	X_K[t[1]] := CharacterToModular(X[t[1]], zeta);
    end for;
    old_max_d := G_val;
    repeat
	/*
	 * Search remaining characters for one of maximal defect. It will
	 * become the reference character of height 0 in the next block.
         */
	max := pairs[1,1];
	max_d := pairs[1,2];
	if max_d ne old_max_d then
	    for i := 2 to #pairs do
		if pairs[i,2] gt max_d then
		    max := pairs[i,1];
		    max_d := pairs[i,2];
		    if max_d eq old_max_d then break; end if;
		end if;
	    end for;
	end if;
	/*
	 * Find block containing X[max] - assumes X[max] has height 0.
	 * This is true as we chose max so that X[max] has maximal defect
	 * amongst the remaining characters
	 */
	chi_K := CharacterToModular(ComplexConjugate(X[max]), zeta);
	chi_K := Eltseq(chi_K);
	chi_K := V![K|sizes[i]*chi_K[i]:i in [1..#cl]];
	b := {t[1]:t in pairs|
	    not IsZero(InternalChtrTableIPK(K, p_reg, X_K[t[1]], chi_K))};
	Append(~res, b);
	Append(~res_d, max_d);
	if #b eq #pairs then break; end if;
	pairs := [t:t in pairs|t[1] notin b];
	old_max_d := max_d;
    until false;
    return res cat [{i}:i in d0], res_d cat [0:i in d0];
end intrinsic;

intrinsic Blocks(X::SeqEnum[AlgChtrElt], Q::SeqEnum[RngIntElt]) -> SeqEnum
{The partition of the character table X into blocks for all primes in Q}

    require forall{p:p in Q|IsPrime(p)}: "Third argument must be sequence of primes";

    R := Universe(X);
    if assigned R`Group then
	G_ord := Order(R`Group);
	G_fact := FactoredOrder(R`Group);
    else
	G_ord := &+[(Integers()!Degree(x))^2 : x in X];
	G_fact := Factorization(G_ord);
    end if;

    /* find a prime q for calculations */
    L := 2 * Max( [ t[1]^t[2]:t in G_fact] ); // lower bound for q
    cl := ClassesData(R);
    e := LCM([c[1]: c in cl]);
    if e ge L then q := e+1;
    elif L mod e eq 0 then q := L + 1;
    else q := ((L div e) + 1)*e + 1;
    end if;
    while not IsPrime(q) do q +:= e; end while;
    K := GF(q);
    zeta := PrimitiveElement(K);
    sizes := [cl[i,2]:i in [1..#cl]];
    V := VectorSpace(K, #cl);
    X_K := [V|CharacterToModular(x, zeta):x in X];
    result := [];
    for p in Q do

	if exists(t){t : t in G_fact | t[1] eq p } then
	    G_val := t[2];
	else
	    Append(~result, <p, [{i}:i in [1..#X]], [0:i in [1..#X]]>);
	    continue p;
	end if;

	/* set up pairs <chtr number, defect> */
	pairs := [<i, G_val - Valuation(Degree(X[i]), p)>: i in [1..#X]];

	d0 := [t[1]:t in pairs|t[2] eq 0]; /* p-defect zero characters */
	if #d0 gt 0 then
	    pairs := [t:t in pairs|not t[2] eq 0];
	end if;
	assert #pairs gt 0;

	res := [];
	res_d := [];
	p_reg := {i:i in [1..#cl]|cl[i,1] mod p ne 0};
	old_max_d := G_val;
	repeat
	    max := pairs[1,1];
	    max_d := pairs[1,2];
	    if max_d ne old_max_d then
		for i := 2 to #pairs do
		    if pairs[i,2] gt max_d then
			max := pairs[i,1];
			max_d := pairs[i,2];
			if max_d eq old_max_d then break; end if;
		    end if;
		end for;
	    end if;
	    /*
	     * Find block containing X[max] - assumes X[max] has height 0.
	     * To make this true we chose max so that X[max] has maximal defect
	     * amongst the remaining characters
	     */
	    chi_K := CharacterToModular(ComplexConjugate(X[max]), zeta);
	    chi_K := Eltseq(chi_K);
	    chi_K := V![K|sizes[i]*chi_K[i]:i in [1..#cl]];
	    b := {t[1]:t in pairs|
		not IsZero(InternalChtrTableIPK(K, p_reg, X_K[t[1]], chi_K))};
	    Append(~res, b);
	    Append(~res_d, max_d);
	    if #b eq #pairs then break; end if;
	    pairs := [t:t in pairs|t[1] notin b];
	    /*
	     * Search remaining characters for one of maximal defect. It will
	     * become the reference character of height 0 in the next block.
	     */
	    old_max_d := max_d;
	until false;
	Append(~result, <p, res cat [{i}:i in d0], res_d cat [0:i in d0]>);
    end for;
    return result;
end intrinsic;

intrinsic Blocks(X::SeqEnum[AlgChtrElt]) -> SeqEnum
{The partition of the character table X into blocks for all primes
dividing the group order}
    R := Universe(X);
    if assigned R`Group then
	G_ord := Order(R`Group);
	G_fact := FactoredOrder(R`Group);
    else
	G_ord := &+[(Integers()!Degree(x))^2 : x in X];
	G_fact := Factorization(G_ord);
    end if;
    return Blocks(X, [t[1]:t in G_fact]);
end intrinsic;

intrinsic Block(X::SeqEnum[AlgChtrElt],  i::RngIntElt, p::RngIntElt) -> SetEnum, RngIntElt
{The p-block of the character table X containing X[i]}

    require IsPrime(p): "Third argument must be prime";
    require 1 le i and i le #X: "Second argument must index first";

    R := Universe(X);
    if assigned R`Group then
	G_ord := Order(R`Group);
	G_fact := FactoredOrder(R`Group);
    else
	G_ord := &+[(Integers()!Degree(x))^2 : x in X];
	G_fact := Factorization(G_ord);
    end if;

    if exists(t){t:t in G_fact|t[1] eq p} then
	G_val := t[2];
    else
	return {i}, 0;
    end if;
    defect :=  G_val - Valuation(Integers()!Degree(X[i]), p);
    if defect eq 0 then
	return {i}, 0;
    end if;

    /* set up pairs <chtr number, defect> */
    pairs := [<j, d>: j in [1..#X] | i ne j and d ne 0 where 
		d := G_val - Valuation(Degree(X[j]), p)];
    assert #pairs gt 0;

    /* find a prime q */
    cl := ClassesData(R);
    e := LCM([c[1]: c in cl]);
    L := 2*p^G_val;
    if e ge L then q := e + 1;
    elif L mod e eq 0 then q := L + 1;
    else q := ((L div e) + 1)*e + 1;
    end if;
    while not IsPrime(q) do q +:= e; end while;
    K := GF(q);
    zeta := PrimitiveElement(K);

    res := {i};
    res_d := defect;
    max := pairs[1,1];
    max_d := pairs[1,2];
    max_p := 1;
    if max_d lt G_val then
	for i := 2 to #pairs do
	    if pairs[i,2] gt max_d then
		max := pairs[i,1];
		max_d := pairs[i,2];
		max_p := i;
	    end if;
	end for;
    end if;
    p_reg := {i:i in [1..#cl]|cl[i,1] mod p ne 0};
    sizes := [cl[i,2]:i in [1..#cl]];
    V := VectorSpace(K, #cl);
    X_K := [V|];
    for t in pairs do
	X_K[t[1]] := CharacterToModular(X[t[1]], zeta);
    end for;
    chi := CharacterToModular(ComplexConjugate(X[i]), zeta);
    chi := Eltseq(chi);
    chi := V![K|sizes[i]*chi[i]:i in [1..#cl]];
    search := true;
    repeat
	test := X_K[max];
	if not IsZero(InternalChtrTableIPK(K, p_reg, test, chi))
	then
	    if max_d gt defect then 
		/*
		 * The test character has height zero in the block.
		 * Replace chi.
		 */
		assert search;
		chi := CharacterToModular(ComplexConjugate(X[max]), zeta);
		chi := Eltseq(chi);
		chi := V![K|sizes[i]*chi[i]:i in [1..#cl]];
		defect := max_d;
		search := false;
	    end if;
	    Include(~res, max);
	end if;
	if #pairs eq 1 then break; end if;
	Remove(~pairs, max_p);
	old_max_d := max_d;
	max := pairs[1,1];
	max_d := pairs[1,2];
	max_p := 1;
	if search then
	    for i := 2 to #pairs do
		if old_max_d eq max_d then break; end if;
		if pairs[i,2] gt max_d then
		    max := pairs[i,1];
		    max_d := pairs[i,2];
		    max_p := i;
		end if;
	    end for;
	end if;
    until false;
    return res, defect;
end intrinsic;

intrinsic Block(X::SeqEnum[AlgChtrElt],  i::RngIntElt, Q::SeqEnum[RngIntElt]) -> SeqEnum
{The p-blocks of the character table X containing X[i] for each p in Q}

    require forall{p:p in Q|IsPrime(p)}: "Third argument must be sequence of primes";
    require 1 le i and i le #X: "Second argument must index first";
    R := Universe(X);

    /* find a prime q */
    cl := ClassesData(R);
    Gord := GroupOrder(R);
    L := 2*Max( [p^Valuation(Gord,p): p in Q] );
    e := LCM([c[1]: c in cl]);
    if e ge L then q := e + 1;
    elif L mod e eq 0 then q := L + 1;
    else q := ((L div e) + 1)*e + 1;
    end if;
    while not IsPrime(q) do q +:= e; end while;
    K := GF(q);
    zeta := PrimitiveElement(K);
    sizes := [cl[i,2]:i in [1..#cl]];
    X_K := [CharacterToModular(x, zeta):x in X];
    V := VectorSpace(K, #cl);
    resQ := [];

    Gfact := Factorization(Gord);
    for p in Q do
	if exists(t){t:t in Gfact|t[1] eq p} then
	    G_val := t[2];
	else
	    Append(~resQ, {i});
	    continue p;
	end if;
	chi := Eltseq(CharacterToModular(ComplexConjugate(X[i]), zeta));
	chi := V![K|chi[j]*sizes[j]:j in [1..#cl]];
	defect :=  G_val - Valuation(Integers()!Degree(X[i]), p);
	if defect eq 0 then
	    Append(~resQ, {i});
	    continue p;
	end if;

	/* set up pairs <chtr number, defect> */
	pairs := [<i, G_val - Valuation(Degree(X[i]), p)>: i in [1..#X]];
	pairs := [t:t in pairs|not t[2] eq 0 and t[1] ne i];
	assert #pairs gt 0;

	res := {i};
	res_d := defect;
	max := pairs[1,1];
	max_d := pairs[1,2];
	max_p := 1;
	if max_d lt G_val then
	    for i := 2 to #pairs do
		if pairs[i,2] gt max_d then
		    max := pairs[i,1];
		    max_d := pairs[i,2];
		    max_p := i;
		end if;
	    end for;
	end if;
	p_reg := {i:i in [1..#cl]|cl[i,1] mod p ne 0};
	search := true;
	repeat
	    test := X_K[max];
	    if not IsZero(InternalChtrTableIPK(K, p_reg, test, chi))
	    then
		if max_d gt defect then 
		    /*
		     * test has height zero in the block we are after
		     * make test the new chi
		     */
		    assert search;
		    chi := Eltseq(CharacterToModular(ComplexConjugate(X[max]),zeta));
		    chi := V![K|chi[j]*sizes[j]:j in [1..#cl]];
		    defect := max_d;
		    search := false;
		end if;
		Include(~res, max);
	    end if;
	    if #pairs eq 1 then break; end if;
	    Remove(~pairs, max_p);
	    old_max_d := max_d;
	    max := pairs[1,1];
	    max_d := pairs[1,2];
	    max_p := 1;
	    if search then
		for i := 2 to #pairs do
		    if old_max_d eq max_d then break; end if;
		    if pairs[i,2] gt max_d then
			max := pairs[i,1];
			max_d := pairs[i,2];
			max_p := i;
		    end if;
		end for;
	    end if;
	until false;
	Append(~resQ, res);
    end for;
    return resQ;
end intrinsic;
    
/*****************************************************************************
 * DefectGroup: written by Bill Unger, 4 April 2006.
 * Use character table X to find a defect group for the given p-block.
 * Calculations are based on the definition of defect group given
 * in Chapter 15 of Isaacs text preceeding 15.31. Justification for
 * powering mod p to test membership of M is as in Isaacsx' proof of 15.18.
 */

intrinsic DefectGroup(x::AlgChtrElt, p::RngIntElt) -> Grp
{A defect group for the p-block containing the ordinary irreducible
character x}
    require IsPrime(p): "Argument 2 must be a prime";
    require Norm(x) eq 1: "Argument 1 must be an irreducible character";
    G := Group(Parent(x));
    G_val := Valuation(#G, p);
    Z := Integers();
    fl, deg := IsCoercible(Z, Degree(x));
    require fl and #G mod deg eq 0:
	    "Argument 1 must be an irreducible character";
    deg_val := Valuation(deg, p);
    if deg_val eq G_val then /* defect 0 */
	return sub<G|>;
    end if;
    if deg_val eq 0 then /* maximal defect */
	return Sylow(G, p);
    end if;
    X := CharacterTable(G);
    pos := Position(X, x);
    require pos gt 0: "Argument 1 must be an irreducible character";
    block, defect := Block(X, pos, p);
    if defect eq G_val then /* maximal defect */
	return Sylow(G, p);
    end if;
    return DefectGroup(X, block, p);
end intrinsic;

intrinsic DefectGroup(X::SeqEnum[AlgChtrElt], b::SetEnum[RngIntElt], p::RngIntElt) -> Grp
{A defect group for the p-block b, where b contains the indices in X of
the ordinary irreducibles in the block}
    /* Assumes b really does give a block */
    require IsPrime(p): "Argument 3 must be a prime";
    require forall{i:i in b|1 le i and i le #X}: "Argument 2 must be set of indices into argument 1";
    G := Group(Universe(X));
    if #b eq 1 then return sub<G|>; end if;
    G_val := Valuation(#G, p);
    Z := Integers();
    deg_val := Min([Valuation(Degree(X[i]),p):i in b]);
    assert deg_val lt G_val;
    if deg_val eq 0 then /* maximal defect */
	return Sylow(G, p);
    end if;
    defect := G_val - deg_val;
    cl := ClassesData(G);

    /* get p-regular classes with right size defect group */
    orb_reps := [t[2]:t in OrbitRepresentatives(ClassPowerGroup(G))];
    poss_cl := [i : i in orb_reps | cl[i,1] mod p ne 0 and
        defect eq Valuation(#G div cl[i,2], p) ];
    assert #poss_cl ge 1;
    if #poss_cl eq 1 then
        return Sylow(ClassCentralizer(G, poss_cl[1]), p);
    end if;

    /* restrict to classes where lambda_b is non-zero */
    /* first throw out obvious zeros */
    poss_cl := [i :i in poss_cl |not exists{j:j in b | IsZero(X[j,i])}];
    assert #poss_cl ge 1;
    if #poss_cl eq 1 then
        return Sylow(ClassCentralizer(G, poss_cl[1]), p);
    end if;

    /* work harder on lambda */
    j := Rep(b); /* could do better in choice of j? */
    w_vals := [ X[j,i] * cl[i,2] / X[j, 1] : i in poss_cl ];
    if Degree(Universe(w_vals)) gt 1 then Minimize(~w_vals); end if;
    C := Universe(w_vals);
    R := Integers(C);
    ChangeUniverse(~w_vals, R);
    e := EulerPhi(#G);
    w_pows := [ Modexp(x, e, p) : x in w_vals ];
    poss_cl := [poss_cl[i] :i in [1..#poss_cl] |not IsZero(w_pows[i])];
    assert #poss_cl ge 1;
    if #poss_cl eq 1 then
        return Sylow(ClassCentralizer(G, poss_cl[1]), p);
    end if;

    /* work out a_b */
    a_vals := [**];
    for i in poss_cl do
        a := &+[ X[j,1]*X[j,i] : j in b] / (p^G_val);
        Append(~a_vals, a);
    end for;
    n := 1;
    for i := 1 to #a_vals do
        x := Minimize(a_vals[i]);
        a_vals[i] := x;
        n := LCM(n, CyclotomicOrder(Parent(x)));
    end for;
    C := CyclotomicField(n);
    a_vals := [C|x:x in a_vals];
    R := Integers(C);
    a_vals := [R|x:x in a_vals];
    a_pows := [Modexp(x, e, p) : x in a_vals ];
    poss_cl := [poss_cl[i] :i in [1..#poss_cl] |not IsZero(a_pows[i])];
    assert #poss_cl ge 1;

    i := Rep(poss_cl);
    return Sylow(ClassCentralizer(G,i), p);

end intrinsic;
