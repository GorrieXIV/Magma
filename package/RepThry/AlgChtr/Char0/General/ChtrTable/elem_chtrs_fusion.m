freeze;

import "elem_chtrs_conlon.m": p_pp_parts;

class_invariant_perm := function(G, x)
    return CycleStructure(x);
end function;

class_invariant_pc := function(G, x)
    return ClassRepresentative(G, x);
end function;

class_invariant_mat_1 := function(G, x)
    return CharacteristicPolynomial(x);
end function;

class_invariant_mat_2 := function(G, x)
    a,b := MinimalAndCharacteristicPolynomials(x);
    return <a,b>;
end function;

class_invariant_mat_3 := function(G, x)
    return PrimaryInvariantFactors(x);
end function;

ClassInvariants := procedure(~CP, fn)

    cl := CP`Classes;

    G := CP`G;
    if ISA(Type(G), GrpPC) then
	invs := {@ c[3]:c in cl @};
	poss := [ [i]: i in [1..#invs] ];
	CP`ClassInvariants := <invs, poss>;
	return;
    end if;

    invs := {@ @};
    poss := [];
    for i := 1 to #cl do
	inv := fn(G, ClassRepresentative(G,i));
	pos := Position(invs, inv);
	if pos eq 0 then
	    Include(~invs, inv);
	    Append(~poss, [i]);
	else
	    Append(~(poss[pos]), i);
	end if;
    end for;
    CP`ClassInvariants := <invs, poss>;
end procedure;

ClassNumber := function(G, cl, elt, poss)
    n := #poss-1;
    if ISA(Type(G), GrpPerm) then
	for i := 1 to n do
	    fl, x := IsConjugate(G, elt, cl[poss[i],3] :
			RightSubgroup := ClassCentralizer(G, poss[i]));
	    if fl then return poss[i], x; end if;
	end for;
    else
	for i := 1 to n do
	    fl, x := IsConjugate(G, elt, cl[poss[i],3]);
	    if fl then return poss[i], x; end if;
	end for;
    end if;
    return poss[#poss], _;
end function;

find := procedure(a, ~fus, ~res)
    aa := a;
    b := fus[aa];
    while b gt 0 and b ne aa do aa := b; b := fus[aa]; end while;
    res := b;
    aa := a;
    b := fus[aa];
    fus[aa] := res;
    while b gt 0 and b ne aa do
	aa := b; b := fus[aa]; fus[aa] := res;
    end while;
end procedure;

merge := procedure(a, b, ~tree, ~sizes, ~fusion);
    /*
    assert a ne b; // assumes non-trivial merge
    assert tree[a] eq a; // assumes a & b are both class reps
    assert tree[b] eq b;
    assert fusion[a] eq 0 or fusion[b] eq 0 or fusion[a] eq fusion[b];
    */
    if sizes[a] lt sizes[b] then t := a; a := b; b := t; end if;
    sizes[a] +:= sizes[b];
    sizes[b] := 0;
    tree[b] := a;
    if fusion[a] eq 0 then fusion[a] := fusion[b]; end if;
end procedure;

SubgroupFusion := procedure(~CP, iso, Pp, x, ~fusion)

    G := CP`G;
    H := Domain(iso);
    assert H subset G;
    P := Codomain(iso);
    assert #P eq #H;
    assert x in P;
    assert Pp subset P;
    p := FactoredOrder(Pp)[1,1];
    pp_ord := Order(x);
    assert pp_ord mod p ne 0;
    assert #P eq pp_ord*#Pp;

    vprintf Chtr, 1:"Getting fusion into group. Subgroup order %o^%o * %o\n",
    p, FactoredOrder(Pp)[1,2], pp_ord; timer := Cputime();

    clp := Classes(Pp);
    cmp := ClassMap(Pp);
    pmp := PowerMap(Pp);

    vprintf Chtr, 2:"Subgroup fusion: subgroup has %o classes\n", #clp * pp_ord;

    /* 
      The classes of P are pairs <i,j> with 1<=i<=#clp and 0<=j<pp_ord

      For sequences we take j varying faster, so:
      Fusion into Pp is [1...1,2...2,3...3,.....,#clp...#clp]
      Fusion into Ppp is [0,1,..,pp_ord-1,0,1,..,pp_ord-1,.....,0,1..pp_ord-1]

      Elements of Ppp are [x^j:j in [0..pp_ord-1]]
      Class size of <i,j> is clp[i,2].
      PowerMap(P): (<i,j>, k) :-> <pmp(i,k), j*k mod pp_ord>

      We get the fusion map into G.
    */

    pm := CP`PowerMap;
    fusion := [0:i in [1..#clp*pp_ord]];
    tree := [i:i in [1..#clp*pp_ord]];
    sizes := [1:i in [1..#clp*pp_ord]];
    fusion[1] := 1;
    
    /* look-up table for powers of x (in the right order for the above) */
    x_powers := {@ P!1 @};
    for i := 1 to pp_ord-1 do Include(~x_powers, x*x_powers[i]); end for;

    t := Type(G);
    pc_flag := false;
    if ISA(t, GrpPerm) then class_invariant := class_invariant_perm;
    elif ISA(t, GrpPC) then class_invariant := class_invariant_pc; pc_flag := true;
    elif ISA(t, GrpMat) then
	R := BaseRing(G);
	if IsField(R) then
	    class_invariant := class_invariant_mat_3;
	elif R cmpeq Integers() then
	    class_invariant := class_invariant_mat_2;
	else
	    class_invariant := class_invariant_mat_1;
	end if;
    else
	error "Unable to compute SubgroupFusion - unknown type";
    end if;
    if not assigned CP`ClassInvariants then
	ClassInvariants(~CP, class_invariant);
    end if;
    invs := CP`ClassInvariants[1];
    poss := CP`ClassInvariants[2];

    conj_saved := [G|];

    cm_count := 0;
    i_offset := #clp*pp_ord + 1;
    for i := #clp to 1 by -1 do
	i_offset -:= pp_ord;
	for j := pp_ord-1 to 0 by -1 do
	    rep := i_offset+j;
	    if rep ne tree[rep] then continue j; end if;
	    if fusion[rep] gt 0 then continue j; end if;
	    G_elt := (clp[i,3]*x_powers[j+1]) @@ iso;
	    G_elt_inv := class_invariant(G, G_elt);
	    inv_pos := Position(invs, G_elt_inv);
	    assert inv_pos gt 0;
	    possibles := poss[inv_pos];
	    if #possibles gt 1 or pc_flag then cm_count +:= 1; end if;
	    G_class, conj_elt :=  ClassNumber(G, CP`Classes, G_elt, possibles);

	    fusion[rep] := G_class;
	    P_ord := clp[i,1] * (pp_ord div Gcd(pp_ord, j));
	    // assert P_ord eq Order(clp[i,3]*x^j);
	    for k := 2 to P_ord-1 do
		f_pos_k := (pmp(i, k)-1)*pp_ord + (j*k mod pp_ord) + 1;
		find(f_pos_k, ~tree, ~f_pos_k);
		if fusion[f_pos_k] ne 0 then
		    // assert fusion[f_pos_k] eq pm(G_class, k);
		    continue k; 
		end if;
		fusion[f_pos_k] := pm(G_class, k);
	    end for;

	    if assigned conj_elt then
		if IsDefined(conj_saved, G_class) then
		    conj_elt := conj_elt * conj_saved[G_class];
		    conj_elt_2 := conj_elt ^ -1;
		    // assert conj_elt notin H;
		    i2_offset := #clp*pp_ord + 1;
		    for i2 := #clp to 1 by -1 do
			i2_offset -:= pp_ord;
			for j2 := pp_ord-1 to 0 by -1 do
			    f2_pos := i2_offset + j2;
			    if f2_pos ne tree[f2_pos] then
				continue j2;
			    end if;
			    G_elt := ((clp[i2,3]*x_powers[j2+1]) @@ iso)^conj_elt;
			    if G_elt in H then
				P_elt := G_elt @ iso;
				Pp_elt, Ppp_elt := p_pp_parts(P_elt, p);
				imi2 := Pp_elt @ cmp;
				imj2 := Position(x_powers, Ppp_elt);
// assert IsConjugate(G, (clp[i2,3]*x^j2) @@ iso,
//                       (clp[imi2,3]*x^(imj2-1)) @@ iso);
				im := (imi2-1)*pp_ord + imj2;
				find(im, ~tree, ~im2);
				if im2 ne f2_pos then
				    merge(im2, f2_pos, ~tree, ~sizes, ~fusion);
				end if;
			    end if;
			    G_elt := ((clp[i2,3]*x_powers[j2+1]) @@ iso)^conj_elt_2;
			    if G_elt in H then
				P_elt := G_elt @ iso;
				Pp_elt, Ppp_elt := p_pp_parts(P_elt, p);
				imi2 := Pp_elt @ cmp;
				imj2 := Position(x_powers, Ppp_elt);
// assert IsConjugate(G, (clp[i2,3]*x^j2) @@ iso,
//                       (clp[imi2,3]*x^(imj2-1)) @@ iso);
				im := (imi2-1)*pp_ord + imj2;
				find(im, ~tree, ~im2);
				if im2 ne f2_pos then
				    merge(im2, f2_pos, ~tree, ~sizes, ~fusion);
				end if;
			    end if;
			end for;
		    end for;
		else
		    conj_saved[G_class] := conj_elt^-1;
		end if;
	    end if;

	end for;
    end for;

    for i := 1 to #fusion do
	if fusion[i] eq 0 then
	    find(i, ~tree, ~j);
	    assert fusion[j] ne 0;
	    fusion[i] := fusion[j];
	end if;
    end for;

    vprintf Chtr, 1:"Time to get fusion %o secs, %o hard class maps\n", 
	Cputime(timer), cm_count;

end procedure;
