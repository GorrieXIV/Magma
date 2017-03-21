freeze;

import "cyclo_gal.m": CycloGal_Q, CycloGal_p, CycloGalStabilizer,
CycloGalIndex, CycloGalSylow, CycloGalOrder, CycloGalInField, CycloGalQuo,
CycloGalStabilizerPM;
import "schur_fusion.m": SubgroupFusion;

p_part := function(x, p)
    n := Order(x);
    v, m := Valuation(n, p);
    d, a, b := XGCD(p^v, m);
    return x^(b*m);
end function;

reduce_subgroup_character := function(H, eta, Gamma)
    Z := Integers();
    repeat
	/* make faithful */
	deg := Degree(eta);
	if KernelOrder(eta) gt 1 then
	    H, toH := quo<H|Kernel(eta)>;
	    eta := CharacterOfImage(eta, toH, H);
	end if;
	if deg eq 1 then return H, eta; end if;
	/* try for a subgroup on the way to Q-primitive */
	reduced := true;
	m := MaximalSubgroups(H);
	if Type(m[1]) eq Rec then
	    m := [r`subgroup:r in m];
	end if;
	for M in m do
	    /*
	     * Try to find a character of M that induces up to eta and doesn't
	     * extend the field.
	     */
	    ind := Index(H, M);
	    want_deg := deg / ind;
	    is_int, want_deg := IsCoercible(Z, want_deg);
	    if not is_int then continue M; end if;
	    eta_M := Restriction(eta, M);
	    if Norm(eta_M) eq 1 then continue M; end if;
	    XM := CharacterTable(M);
	    if exists(new_eta){x:x in XM | Degree(x) eq want_deg
		and InnerProduct(x, eta_M) eq 1 
		and CycloGalInField(Gamma, x) }
	    then
		reduced := false;
		H := M;
		eta := new_eta;
		break;
	    end if;
	end for;
    until reduced;
    return H, eta;
end function;

subgroup_search_cyclic := function(chi, q)
/*
 * chi in Irr(G), q a rational prime
 * Try to find a q-quasi-elementary subgroup H of G
 * and eta in Irr(H) such that <eta, chi_H> mod q ne 0
 * and [Q(chi, eta), Q(chi)] mod q ne 0.
 *
 * Try to do this by extending cyclic subgroups of G
 * and testing without constructing H
 */

    G := Group(Parent(chi));
    cl := ClassesData(G);
    pm := PowerMap(G);
    n := Exponent(G);
    Gam := CycloGal_Q(n);
    Gamchi := CycloGalStabilizer(Gam, chi);
    cyclics := [t[2]: t in OrbitRepresentatives(ClassPowerGroup(G))];
    wait := [* *];
    for i in cyclics do
	n := cl[i,1];
	done := {};
	C := CyclotomicField(n);
	z := RootOfUnity(n, C);
	for j := 0 to n-1 do
	    if j in done then continue j; end if;
	    Include(~done, j);
	    upto := 0;
	    pows := [j];
	    zeta_ind := 1;
	    while upto lt #pows do
		upto +:= 1;
		k := pows[upto];
		for e in Gamchi`powers do
		    im := k*e mod n;
		    if im notin done then
			zeta_ind +:= 1;
			Append(~pows, im);
			Include(~done, im);
		    end if;
		end for;
	    end while;
	    zeta := z^j;
	    ip := chi[1];
	    zeta_jj := 1;
	    for jj := 1 to n-1 do
		zeta_jj *:= zeta;
		ip +:= zeta_jj*chi[pm(i,jj)];
	    end for;
	    ip := ip / n;
	    ip := Integers()!ip;
	    if ip mod q eq 0 then continue j; end if;
	    if zeta_ind mod q ne 0 then
		/* JACKPOT! - cyclic group will do */
		//"cyclic jackpot";
		return [* <i, zeta, [], 1> *];
	    end if;
	    Gamchizeta := CycloGalStabilizer(Gamchi, zeta);
	    assert zeta_ind eq CycloGalIndex(Gamchi, Gamchizeta);
	    Q := CycloGalQuo(Gamchi, Gamchizeta);
	    S := CycloGalSylow(Q, q);
	    if exists{e:e in S`powers|pm(i,e) ne i} then continue i; end if;
	    Append(~wait, <i, zeta, [e mod n: e in S`powers], CycloGalOrder(S)>);
	end for;
    end for;
//    "found", #wait;
    return wait;
end function;

subgroup_search_cyclic_p := function(chi, p, q)
/*
 * chi in Irr(G), q a rational prime
 * Try to find a q-quasi-elementary subgroup H of G
 * and eta in Irr(H) such that <eta, chi_H> mod q ne 0
 * and [Q_p(chi, eta), Q_p(chi)] mod q ne 0.
 *
 * Try to do this by extending cyclic subgroups of G
 * and testing without constructing H
 */

    G := Group(Parent(chi));
    cl := ClassesData(G);
    pm := PowerMap(G);
    n := Exponent(G);
    Gam := CycloGal_p(p, n);
    Gamchi := CycloGalStabilizer(Gam, chi);
    cyclics := [t[2]: t in OrbitRepresentatives(ClassPowerGroup(G))];
    wait := [* *];
    for i in cyclics do
	n := cl[i,1];
	done := {};
	z := RootOfUnity(n);
	for j := 0 to n-1 do
	    if j in done then continue j; end if;
	    Include(~done, j);
	    upto := 0;
	    pows := [j];
	    zeta_ind := 1;
	    while upto lt #pows do
		upto +:= 1;
		k := pows[upto];
		for e in Gamchi`powers do
		    im := k*e mod n;
		    if im notin done then
			zeta_ind +:= 1;
			Append(~pows, im);
			Include(~done, im);
		    end if;
		end for;
	    end while;
	    zeta := z^j;
	    ip := chi[1];
	    for jj := 1 to n-1 do
		ip +:= zeta^jj*chi[pm(i,jj)];
	    end for;
	    ip := ip / n;
	    ip := Integers()!ip;
	    if ip mod q eq 0 then continue j; end if;
	    if zeta_ind mod q ne 0 then
		/* JACKPOT! - cyclic group will do */
		return [* <p, q, i, zeta, [], 1> *];
	    end if;
	    Gamchizeta := CycloGalStabilizer(Gamchi, zeta);
	    assert zeta_ind eq CycloGalIndex(Gamchi, Gamchizeta);
	    Q := CycloGalQuo(Gamchi, Gamchizeta);
	    S := CycloGalSylow(Q, q);
	    if exists{e:e in S`powers|pm(i,e) ne i} then continue i; end if;
	    return [*<p, q, i, zeta, [e mod n: e in S`powers], CycloGalOrder(S)>*];
	end for;
    end for;
    return wait;
end function;

subgroup_construct_from_cyclic_data := function(chi, tup)
    G := Group(Parent(chi));
    n := Exponent(G);
    cl := ClassesData(G);
    p, q, c, zeta, pows, gal_ord := Explode(tup);
    a := ClassRepresentative(G, c);
    a_ord := cl[c,1];
    A := sub<G|a>;
    base := a @ ClassMap(A);
    eta := [];
    pm := PowerMap(A);
    for i := 1 to a_ord do eta[pm(base, i)] := zeta^i; end for;
    eta := CharacterRing(A)!eta;
    AssertAttribute(eta, "IsCharacter", true);
    pm := PowerMap(G);
    if gal_ord eq 1 then
	"cyclic case";
	assert #pows eq 0;
	if Type(A) ne GrpPC then
	    A, toA := PCGroup(A);
	    eta := LiftCharacter(eta, Inverse(toA), A);
	end if;
	Gam := CycloGal_p(p, n);
	Gameta := CycloGalStabilizer(Gam, eta);
	Gamchieta := CycloGalStabilizer(Gameta, chi);
	return A, eta, CycloGalIndex(Gameta, Gamchieta);
    end if;
    assert #pows gt 0;
    gens := [];
    for e in pows do
	fl, x := IsConjugate(G, a, a^e);
	assert fl;
	Append(~gens, p_part(x, q));
    end for;
    H := sub<G|a, gens>;
    if #H eq a_ord*gal_ord then
	// "good case";
	if Type(G) ne GrpPC then
	    H, toH := PCGroup(H);
	    A := sub<H|a@toH>;
	    eta := CharacterOfImage(eta, toH, A);
	end if;
	eta := Induction(eta, H);
	assert Norm(eta) eq 1;
	n := Exponent(G);
	Gam := CycloGal_p(p, n);
	Gameta := CycloGalStabilizer(Gam, eta);
	Gamchieta := CycloGalStabilizer(Gameta, chi);
	return H, eta, CycloGalIndex(Gameta, Gamchieta);
    end if;
    assert #H mod a_ord*gal_ord eq 0;
    if not IsPrimePower(#H div a_ord) then
	// "outside quasi-elem";
	S := Sylow(H, q);
	H := sub<H|a, S>;
    end if;

    fl, q2 := IsPrimePower(#H div a_ord);
    assert fl and q2 eq q;

    if Type(G) eq GrpPC then
	chi_H := Restriction(chi, H);
    else
	H, toH := PCGroup(H);
	fuse := SubgroupFusion(G, toH);
	chi_H := CharacterRing(H)![chi[fuse[i]]:i in [1..#ClassesData(H)]];
	AssertAttribute(chi_H, "IsCharacter", true);
	A := sub<H|a@toH>;
	eta := CharacterOfImage(eta, toH, A);
    end if;

    eta_H := Induction(eta, H);
    Gam := CycloGal_p(p, n);
    Gamchi := CycloGalStabilizer(Gam, chi);

    // "getting char table";
    XH := CharacterTable(H);
    Z := Integers();
    ip_chi := [Z|i:i in Decomposition(XH, chi_H)];
    ip_eta := [Z|i:i in Decomposition(XH, eta_H)];
    for j := 1 to #XH do
	if ip_eta[j] mod q eq 0 or ip_chi[j] mod q eq 0 then
	    continue j;
	end if;
	eta := XH[j];
	Gamchieta := CycloGalStabilizer(Gamchi, eta);
	if CycloGalIndex(Gamchi, Gamchieta) mod q ne 0 then
	    Gameta := CycloGalStabilizer(Gam, eta);
	    assert Gamchieta`grp_ab subset Gameta`grp_ab;
	    return H, eta, CycloGalIndex(Gameta, Gamchieta);
	end if;
    end for;
    return false, _, _;
end function;

subgroup_search := function(G, chi, q)
    X := CharacterTable(G);
    cl := ClassesData(G);
    pm := PowerMap(G);
    cpg := ClassPowerGroup(G);
    OR := OrbitRepresentatives(cpg);
    cycs := [t[2]:t in OR|cl[t[2],1] mod q ne 0]; // q-regular cyclic subgroups
    Sort(~cycs);
    Reverse(~cycs);
    Z := Integers();
    Gam := CycloGal_Q(Exponent(G));
    Gamchi := CycloGalStabilizer(Gam, chi);
    for i in cycs do
	cent := ClassCentralizer(G,i);
	if i gt 1 then
	    a := ClassRepresentative(G,i);
	    gal := CycloGal_Q(cl[i,1]);
	    gal := CycloGalSylow(gal, q);
	    gal := CycloGalStabilizerPM(gal, pm, i);
	    gens := [];
	    for e in gal`powers do
		assert pm(i,e) eq i;
		fl, x := IsConjugate(G, a, a^e);
		assert fl;
		Append(~gens, p_part(x, q));
	    end for;
	    H := sub<G|cent, gens>;
	    H := sub<G|a, Sylow(H, q)>;
	else
	    H := Sylow(cent, q);
	end if;
	if Type(G) eq GrpPC then 
	    chi_H := Restriction(chi, H);
	else
	    H, toH := PCGroup(H);
	    fuse := SubgroupFusion(G, toH);
	    chi_H := CharacterRing(H)![chi[fuse[i]]:i in [1..#ClassesData(H)]];
	    AssertAttribute(chi_H, "IsCharacter", true);
	end if;
	XH := CharacterTable(H);
	dec := Decomposition(XH, chi_H);
	ChangeUniverse(~dec, Z);
	poss := [j:j in [1..#XH]|dec[j] mod q ne 0];
	for j in poss do
	    eta := XH[j];
	    Gamchieta := CycloGalStabilizer(Gamchi, eta);
	    if CycloGalIndex(Gamchi, Gamchieta) mod q ne 0 then
		/* found good H, eta: reduce to faithful & Q-primitive */
		H, eta := reduce_subgroup_character(H, eta, Gamchieta);
		// printf "Subgroup search: q = %o, order = %o, deg = %o\n",
		//    q, #H, Degree(eta);
		return true, H, eta;
	    end if;
	end for;
    end for;
    return false, _, _;
end function;

