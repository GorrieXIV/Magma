freeze;

import "cyclo_gal.m": CycloGal_p, CycloGalStabilizer, CycloGalInField,
CycloGalIndex;

is_Q8 := function(G)
    return #G eq 8 and not IsAbelian(G) and #[x:x in G|Order(x) eq 2] eq 1;
end function;

is_dyadic_2 := function(P)
/* Lemma 2 of Riese & Schmid, Schur Indices and Schur Groups II */
/* assumes P is a 2-group, with a PC representation */
    Z := DerivedGroup(P);
    if #Z lt 4 or not IsCyclic(Z) then return false; end if;
    z := &*AbelianBasis(Z); /* generator of Z */
    z := z^ (#Z div 4);/* z has order 4 in Z */
    Y := Centralizer(P, z);
    return IsCyclic(quo<Y|z>);
end function;

is_dyadic_schur := function(G)
/* 
 * Is G = Q8 or of type (Q8,q) or of type (QD,q)?
 *
 *  (Q8,q) is defined in P. Schmid, "Schur Indices and Schur Groups",
 *           J. Algebra 169 (1994), 226-247.
 *
 *  (QD,q) is defined in U. Riese & P. Schmid, op cit.
 *
 *  The latter paper also defines "dyadic Schur group" and proves that
 *  this is equivalent to being one of these types. As it happens, every
 *  faithful irreducible character of a group of these types has
 *  2-adic Schur index equal to 2.
 *
 *  Assumes that G is a PC group.
 *
 */
    if IsCyclic(G) then
	// "cyclic";
	return false; /* gets rid of small cases */
    end if;
    f := FactoredOrder(G);
    assert #f ge 1;
    if #f eq 1 then
	//"p-group";
	return is_Q8(G);
    end if;
    if #f gt 2 or f[1,1] ne 2 or f[1,2] lt 3 or f[2,2] gt 1 then
	//"order wrong";
	return false;
    end if;

    q := f[2,1];
    P := Sylow(G, 2);
    U := Sylow(G, q); /* U has prime order q, hence is cyclic */
    if not IsNormal(G,U) then
	//"2-complement not normal";
	return false;
    end if;
    X := Centralizer(P, U);
    if IsAbelian(X) then
	//"abelian 2'-centralizer";
	return false;
    end if;
    if is_Q8(X) and X ne P and IsCyclic(quo<P|X>) 
    	and P eq sub<P|X, Centralizer(P,X)>
    then
	/* could be type (Q8, q) */
	s := Valuation(Modorder(2,q),2);
	if 2^s eq Index(P,X) then
	    //printf "(Q8, %o)\n", q;
	    return true;
	end if;
    end if;

    /* only got type (QD, q) left to check for */

    if not is_dyadic_2(P) then
	//"QD: not dyadic 2-group";
	return false;
    end if;
    
    D := DerivedGroup(P);
    if not (D subset X and Index(X,D) eq 2) then 
	//"QD: derived";
	return false;
    end if;

    s := Valuation(Index(P,D),2)-1;
    o := Modorder(2, q);
    v := Valuation(o, 2);
    if v lt s then
	//"QD: order of 2";
	return false;
    end if;
    if v eq s and is_Q8(X) then
	//"QD: f odd & Q8";
	return false;
    end if;

    //printf "(QD, %o)\n", q;
    return true;
    
end function;

reduce_group_chtr_dyadic := function(G, chi, gal_chi)
/* assumes G is a PC group */
    assert G eq Group(Parent(chi));
    done := false;
    repeat
	if KernelOrder(chi) gt 1 then
	    K := Kernel(chi);
	    G, toG := quo<G|K>;
	    chi := CharacterOfImage(chi, toG, G);
	end if;
	done := true;
	m := MaximalSubgroups(G);
	if Type(m[1]) eq Rec then
	    m := [r`subgroup: r in m];
	end if;
	for H in m do
	    XH := CharacterTable(H);
	    chi_H := Restriction(chi, H);
	    XH := [x:x in XH|IsOdd(Integers()!InnerProduct(x,chi_H))];
	    for x in XH do
		gal_x := CycloGalStabilizer(gal_chi, x);
		if IsOdd(CycloGalIndex(gal_chi, gal_x)) then
		    done := false;
		    gal_chi := CycloGalStabilizer(CycloGal_p(2, #G), x);
		    if IsLinear(x) or
			IsEven(CycloGalIndex(gal_chi,CycloGalStabilizer(gal_chi,chi)))
		    then
			/* whatever the ultimate 2-adic Schur index is,
			   the initial index is 1 */
			return 1;
		    end if;
		    G := H;
		    chi := x;
		    break H;
		end if;
	    end for;
	end for;
    until done;
    return G;
end function;

Riese_Schmid_2_2 := function(G, chi)
    if #G mod 8 ne 0 then
	return 1;
    end if;
    gal := CycloGal_p(2, #G);
    gal_chi := CycloGalStabilizer(gal, chi);
    if CycloGalInField(gal_chi, RootOfUnity(4)) then
	return 1;
    end if;
    if Type(G) ne GrpPC then
	G, toG := PCGroup(G);
	chi := CharacterOfImage(chi, toG, G);
    end if;
    if IsAbelian(Sylow(G,2)) then
	return 1;
    end if;
    H := reduce_group_chtr_dyadic(G, chi, gal_chi);
    if H cmpeq 1 then
	return 1;
    else
	return is_dyadic_schur(H) select 2 else 1;
    end if;
end function;
