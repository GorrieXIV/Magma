freeze;

import "schur_index_bounds.m": Schur_index_bounds, scan_multiplicities;
import "schur_subgroup.m": subgroup_construct_from_cyclic_data, subgroup_search;
import "cyclo_gal.m": CycloGal_p, CycloGal_Q, CycloGalStabilizer, CycloGalIndex;
import "dyadic_schur.m": Riese_Schmid_2_2;

forward reconcile_p_q, reconcile_q;

Schur_index := function(chi: Easy := false, DegreeBound := -1)
/*
 * Compute m_x(chi) where x is Q, Q_p, R
 * Setting Easy true will just do m_Q and leave the others vague.
 * Returns m_Q(chi) followed by sequence of tuples giving non 1 local Schur indices
 * If Easy is true then only the first return value is valid.
 */

    Q := Rationals();
    G := Group(Parent(chi));

    if DegreeBound eq -1 then DegreeBound := Ilog(100,#G)+1; end if;
    q, loc, cyclics, do_mult := Schur_index_bounds(chi:
	    Easy := Easy, DegreeBound := DegreeBound);

    L, U := Explode(q);
    if U eq L and Easy or forall{t:t in loc|t[2] eq t[3]} then
	return U, [<t[1],t[2]>:t in loc|t[2] ne 1];
    end if;

    if not assigned cyclics then cyclics := [* *]; end if;

    for t in cyclics do
	H, eta, deg := subgroup_construct_from_cyclic_data(chi, t);
	if H cmpeq false then continue t; end if;
	q, new_loc := Schur_index_bounds(eta);
	reconcile_p_q(~loc, t[1], t[2], new_loc, deg);
	L := LCM([t[2]:t in loc]);
	U := LCM([t[3]:t in loc]);
	if Easy and L eq U or forall{t:t in loc|t[2] eq t[3]} then
	    return U, [<t[1],t[2]>:t in loc|t[3] ne 1];
	end if;
	if do_mult then
	    scan_multiplicities(~L, ~U, ~loc, ~fin);
	    if fin then return U, [<t[1],t[2]>:t in loc|t[2] ne 1]; end if;
	end if;
	if t[1] eq 2 and t[2] eq 2 then
	    fl := exists(u){u:u in loc|u[1] eq 2 and u[2] ne u[3]};
	    if not fl then continue t; end if;
	    assert u[2] eq 1 and u[3] eq 2;
	    m := Riese_Schmid_2_2(H, eta);
	    reconcile_p_q(~loc, 2, 2, [<2, m, m>], deg);
	    L := LCM([t[2]:t in loc]);
	    U := LCM([t[3]:t in loc]);
	    if Easy and L eq U or forall{t:t in loc|t[2] eq t[3]} then
		return U, [<t[1],t[2]>:t in loc|t[3] ne 1];
	    end if;
	    if do_mult then
		scan_multiplicities(~L, ~U, ~loc, ~fin);
		if fin then return U, [<t[1],t[2]>:t in loc|t[2] ne 1]; end if;
	    end if;
	end if;
    end for;
    
    q_seq := PrimeDivisors(LCM([t[3] div t[2]:t in loc]));
    for q in q_seq do
	found, H, eta := subgroup_search(G, chi, q);
	if not found then new_loc := [];
	else
	    m, new_loc := $$(eta);
	end if;
	reconcile_q(~loc, q, new_loc, chi, eta);
	L := LCM([t[2]:t in loc]);
	U := LCM([t[3]:t in loc]);
	if Easy and L eq U or forall{t:t in loc|t[2] eq t[3]} then
	    return U, [<t[1],t[2]>:t in loc|t[3] ne 1];
	end if;
	if do_mult then
	    scan_multiplicities(~L, ~U, ~loc, ~fin);
	    if fin then return U, [<t[1],t[2]>:t in loc|t[2] ne 1]; end if;
	end if;
    end for;
    return <L,U>, loc;
end function;

reconcile_p_q := procedure(~list, p, q, new_list, deg)
    fl := exists(i){i:i in [1..#list]|list[i,1] eq p};
    if not fl then return; end if;
    t1 := list[i];
    if t1[2] eq t1[3] or
	Valuation(t1[2],q) eq Valuation(t1[3],q) then return; end if;
    fl := exists(t2){t:t in new_list|t[1] eq p};
    if not fl then /* q part of m_p(chi) is 1 */
	assert Valuation(t1[2],q) eq 0;
	_,t1[3] := Valuation(t1[3], q);
	list[i] := t1;
	return;
    end if;
    m := t2[2];
    m div:= GCD(m, deg);
    v := Valuation(m, q);
    _, t1[2] := Valuation(t1[2], q);
    t1[2] *:= q^v;
    m := t2[3];
    m div:= GCD(m, deg);
    v := Valuation(m, q);
    _, t1[3] := Valuation(t1[3], q);
    t1[3] *:= q^v;
    list[i] := t1;
end procedure;

reconcile_q := procedure(~list, q, new_list, chi, eta)
    p_list := {@ t[1]:t in new_list @};
    for i := 1 to #list do
	t := list[i];
	p := t[1];
	if p eq 0 or t[2] eq t[3] or
		Valuation(t[2],q) eq Valuation(t[3],q)
	then
	    continue i;
	end if;
	pos := Index(p_list, p);
	if pos eq 0 then
	    _, t[3] := Valuation(t[3], q);
	    assert Valuation(t[2],q) eq 0;
	    list[i] := t;
	    continue i;
	end if;
	u := new_list[pos];
	Gamma := CycloGal_p(p, Exponent(Group(Parent(chi))));
	Gameta := CycloGalStabilizer(Gamma, eta);
	Gametachi := CycloGalStabilizer(Gameta, chi);
	deg := CycloGalIndex(Gameta, Gametachi);
	m := u[2];
	m div:= GCD(deg, m);
	v := Valuation(m, q);
	_, t[2] := Valuation(t[2], q);
	t[2] *:= q^v;
	_, t[3] := Valuation(t[3], q);
	t[3] *:= q^v;
	list[i] := t;
    end for;
end procedure;
