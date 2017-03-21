freeze;

CGRF := recformat<grp_ab, powers, N>;

cyclo_gal_subgroup_powers := function(G, G_pows, n, H)
    res := [];
    for i := 1 to Ngens(H) do
	e := 1;
	q := Eltseq(G!(H.i));
	for j := 1 to #q do
	    e := (e * Modexp(G_pows[j], q[j], n)) mod n;
	end for;
	Append(~res, e);
    end for;
    return res;
end function;

CycloGal_p := function(p, n)
    /*
       Compute galois group of Q_p(zeta_n)/Q_p as an abelian group.
       Action is given as corresponding powers of zeta_n.
       Theory by Gabriele Nebe,
       Implementation by Bill Unger, March 2006.
       Return values:
       (1) record with format CGRF containing
	    (a) Group as an abelian group
	    (b) sequence of integers giving action of each group
		    generator G.i as power of zeta_n
	    (c) n
       (2) order of the Frobenius automorphism on the p' part of n
       (3) the projection of the galois group onto this part
     */
    v, n2 := Valuation(n,p);
    Ar, fr := UnitGroup(Integers(p^v));
    ram_len := Ngens(Ar);
    if n2 gt 1 then
	d := Modorder(p, n2);
    else
	d := 1;
    end if;
    if d eq 1 then
	gal_zeta_n := Ar;
    else
	str := [Order(Ar.i):i in [1..ram_len]];
	Append(~str, d);
	gal_zeta_n := AbelianGroup(str);
	assert Ngens(gal_zeta_n) eq ram_len + 1;
    end if;
    generator_action := [];
    Z := Integers();
    for i := 1 to ram_len do
	pow := Z!(Ar.i @ fr);
	Append(~generator_action, ChineseRemainderTheorem([pow,1], [p^v,n2]));
    end for;
    if d eq 1 then
	pi := hom<gal_zeta_n->gal_zeta_n|[gal_zeta_n!0:i in [1..ram_len]]>;
    else
	Append(~generator_action, ChineseRemainderTheorem([1,p], [p^v,n2]));
	pi := hom<gal_zeta_n->gal_zeta_n|[gal_zeta_n!0:i in [1..ram_len]] cat
		    [gal_zeta_n.(ram_len+1)] >;
    end if;
    res := rec<CGRF|grp_ab := gal_zeta_n, powers := generator_action, N := n>;
    return res, d, pi;
end function;

CycloGalInField := function(CG, vals)

    if Type(vals) eq AlgChtrElt then vals := Eltseq(vals);
    elif Type(vals) eq FldCycElt then vals := [vals];
    end if;
    // assert  CG`N mod CyclotomicOrder(Universe(vals)) eq 0;

    red_vals := [v: v in vals | not IsCoercible(Z, v)]
	    where Z := Integers();
    if #red_vals eq 0 then return true; end if;
    Minimize(~red_vals);
    gens_action := [e mod co:e in CG`powers]
	where co := CyclotomicOrder(Universe(red_vals));
    return forall{0:v in red_vals, a in gens_action|
	Conjugate(v, a) eq v};
end function;

CycloGalStabilizer := function(CG, vals)
    /* 
     * Compute subgroup of G that stabilizes each
     * field value in vals.
     * Assumes vals is a sequence of cyclotomic field elts,
     * all contained in CyclotomicField(GG`N)
     */
    G := CG`grp_ab;
    generator_action := CG`powers;
    n := CG`N;

    if Type(vals) eq AlgChtrElt then vals := Eltseq(vals);
    elif Type(vals) eq FldCycElt then vals := [vals];
    end if;
    Z := Rationals();
    // assert  CG`N mod CyclotomicOrder(Universe(vals)) eq 0;

    /* Stabilize each alpha in vals */
    stab := CG`grp_ab;
    gens_action :=  generator_action;
    do_set_up := true;
    for alpha in vals do
	if #stab eq 1 then break; end if;
	if IsCoercible(Z, alpha) then continue alpha; end if;
	/* find stabilizer (in stab) of alpha and replace stab */
	if do_set_up then
	    /* set up minimal gens of stab & action of gens */
	    gens := AbelianBasis(stab);
	    gens_action := [];
	    for i := 1 to #gens do
		q := Eltseq(G!gens[i]);
		e := 1;
		for j := 1 to #q do
		    e := (e * Modexp(generator_action[j], q[j], n)) mod n;
		end for;
		Append(~gens_action, e);
	    end for;
	end if;
	/* reduce gens action to current situation */
	beta := Minimize(alpha);
	g_a := [e mod co:e in gens_action]
		    where co := CyclotomicOrder(Parent(beta));
	if forall{e:e in g_a|Conjugate(beta, e) eq beta} then
	    /* this alpha is already stabilized, we can bail out now */
	    do_set_up := false;
	    continue alpha;
	end if;
	/* do the orbit-stabilizer thing */
	orb := {@ beta @};
	new_stab := sub<stab|>;
	sv := [ stab!0 ];
	done := 0;
	repeat
	    done +:= 1;
	    pt := orb[done];
	    sv_done := sv[done];
	    for i := 1 to #gens do
		im := Conjugate(pt, g_a[i]);
		ind := Index(orb, im);
		if ind eq 0 then
		    Include(~orb, im);
		    Append(~sv, sv_done + gens[i]);
		else
		    s := sv_done + gens[i] - sv[ind];
		    if s notin new_stab then
			new_stab := sub<stab|new_stab, s>;
		    end if;
		end if;
	    end for;
	until 2*#orb*#new_stab gt #stab;
	assert #orb gt 1;
	stab := sub<G|AbelianBasis(new_stab)>;
	do_set_up := true;
    end for;
    gens_action := cyclo_gal_subgroup_powers(G, generator_action, n, stab);
    res := rec<CGRF|grp_ab := stab, powers := gens_action, N := n >;
    return res;
end function;

CycloGalIndex := function(CG1, CG2)
// assumes CG2 is subgroup of CG1
    return Index(CG1`grp_ab, CG2`grp_ab);
end function;

CycloGal_Q := function(n)
    A, f := UnitGroup(Integers(n));
    acts := [Integers() | (A.i)@f : i in [1..Ngens(A)]];
    res := rec<CGRF|grp_ab := A, powers := acts, N:= n>;
    return res;
end function;

CycloGalSylow := function(CG, p)
    S := SylowSubgroup(CG`grp_ab, p);
    S_pows := cyclo_gal_subgroup_powers(CG`grp_ab, CG`powers, CG`N, S);
    res := rec<CGRF|grp_ab := S, powers := S_pows, N := CG`N >;
    return res;
end function;

CycloGalJoin := function(CG1, CG2, CG3)
    H := sub<CG1`grp_ab|CG2`grp_ab, CG3`grp_ab>;
    H_pows := cyclo_gal_subgroup_powers(CG1`grp_ab, CG1`powers, CG1`N, H);
    res := rec<CGRF|grp_ab := H, powers := H_pows, N := CG1`N >;
    return res;
end function;

CycloGalQuo := function(CG1, CG2)
    H, toH := quo<CG1`grp_ab| CG2`grp_ab>;
    if #H eq 1 then
	return rec<CGRF|grp_ab:=sub<H|>, powers := [], N := CG1`N>;
    end if;
    H_pows := [];
    G_pows := CG1`powers;
    n := CG1`N;
    for i := 1 to Ngens(H) do 
	e := 1;
	q := Eltseq(H.i@@toH);
	for j := 1 to #q do
	    e := (e * Modexp(G_pows[j], q[j], n)) mod n;
	end for;
	Append(~H_pows, e);
    end for;
    return rec<CGRF|grp_ab:= H, powers := H_pows,  N := n>;
end function;

CycloGalOrder := function(CG)
    return #CG`grp_ab;
end function;

CycloGalIsCyclicSylow := function(CG, p)
    S := SylowSubgroup(CG`grp_ab, p);
    return #S eq 1 or IsCyclic(S);
end function;

CycloGal_Q_p := function(p, n)
    v, n2 := Valuation(n,p);
    Ar, fr := UnitGroup(Integers(p^v));
    A2, f2 := UnitGroup(Integers(n2));
    p2 := p @@ f2;
    // assert Order(p2) eq Modorder(p, n2);
    Q_grp, inc := DirectProduct([Ar, A2]);
    pows_r := [Integers()|Ar.i@fr:i in [1..Ngens(Ar)]];
    pows_2 := [Integers()|A2.i@f2:i in [1..Ngens(A2)]];
    pows := pows_r cat pows_2;
    Q := rec<CGRF|grp_ab := Q_grp, powers := pows, N := n >;
    p_grp := sub<Q_grp|AbelianBasis(sub<Q_grp | Ar @ inc[1], p2 @ inc[2]>)>;
    Qp := rec<CGRF|grp_ab := p_grp, N := n,
	powers := cyclo_gal_subgroup_powers(Q_grp, pows, n, p_grp)>;
    return Q, Qp;
end function;

CycloGalStabilizerPM := function(CG, pm, base)
    /* G, generator_action is as output from 
     * G <= gal_zeta_n: Compute subgroup of G that stabilizes base
     * using the power map action given by pm.
     * Output is abelian group S (subgroup of G), sequence giving
     * action of S.i as power of nth root of unity
     */
    G := CG`grp_ab;
    generator_action := CG`powers;
    n := CG`N;

    stab := CG`grp_ab;
    gens_action :=  generator_action;
    new_stab := sub<stab|>;
    orb := {@ base @};
    sv := [ stab!0 ];
    done := 0;
    /* set up gens of stab & action of gens */
    gens := AbelianBasis(stab);
    gens_action := [];
    for i := 1 to #gens do
	q := Eltseq(G!gens[i]);
	e := 1;
	for j := 1 to #q do
	    e := (e * Modexp(generator_action[j], q[j], n)) mod n;
	end for;
	Append(~gens_action, e);
    end for;
    while 2*#orb*#new_stab le #stab do
	assert done lt #orb;
	done +:= 1;
	pt := orb[done];
	for i := 1 to #gens do
	    im := pm(pt, gens_action[i]);
	    ind := Index(orb, im);
	    if ind eq 0 then
		Include(~orb, im);
		Append(~sv, sv[done] + gens[i]);
	    else
		s := sv[done] + gens[i] - sv[ind];
		if s notin new_stab then
		    new_stab := sub<stab|new_stab, s>;
		end if;
	    end if;
	    if 2*#orb*#new_stab gt #stab then break; end if;
	end for;
    end while;
    if #orb gt 1 then
	stab := sub<G|AbelianBasis(new_stab)>;
    end if;
    gens_action := cyclo_gal_subgroup_powers(G, generator_action, n, stab);
    res := rec<CGRF|grp_ab := stab, powers := gens_action, N := n >;
    return res;
end function;
