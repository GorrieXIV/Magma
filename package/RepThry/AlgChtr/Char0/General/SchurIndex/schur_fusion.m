freeze;

class_invariant_perm := function(G, x)
    return CycleStructure(x);
end function;

class_invariant_pc := function(G, x)
    return ClassRepresentative(G, x);
end function;

class_invariant_mat := function(G, x)
    a,b := MinimalAndCharacteristicPolynomials(x);
    return <a,b>;
end function;

ClassInvariants := function(G, fn)

    if ISA(Type(G), GrpPC) then
	cl := Classes(G);
	invs := {@ c[3]:c in cl @};
	poss := [ [i]: i in [1..#invs] ];
	return <invs, poss>;
    end if;

    invs := {@ @};
    poss := [];
    cl := ClassesData(G);
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
    return <invs, poss>;
end function;

ClassNumber := function(G, elt, poss)
    n := #poss-1;
    if ISA(Type(G), GrpPerm) then
	for i := 1 to n do
	    fl, x := IsConjugate(G, elt, ClassRepresentative(G,poss[i]) :
			RightSubgroup := ClassCentralizer(G, poss[i]));
	    if fl then return poss[i], x; end if;
	end for;
    else
	for i := 1 to n do
	    fl, x := IsConjugate(G, elt, ClassRepresentative(G,poss[i]));
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

SubgroupFusion := function(G, iso)

    H := Domain(iso);
    assert H subset G;
    P := Codomain(iso);
    assert #P eq #H;

    clP := Classes(P);
    cmP := ClassMap(P);
    pmP := PowerMap(P);

    pm := PowerMap(G);
    fusion := [0:i in [1..#clP]];
    tree := [i:i in [1..#clP]];
    sizes := [1:i in [1..#clP]];
    fusion[1] := 1;

    t := Type(G);
    pc_flag := false;
    if ISA(t, GrpPerm) then class_invariant := class_invariant_perm;
    elif ISA(t, GrpPC) then class_invariant := class_invariant_pc; pc_flag := true;
    elif ISA(t, GrpMat) then class_invariant := class_invariant_mat;
    else
	error "Unable to compute SubgroupFusion - unknown type";
    end if;
    t := ClassInvariants(G, class_invariant);
    invs := t[1];
    poss := t[2];

    conj_saved := [G|];

    cm_count := 0;
    for rep := #clP to 1 by -1 do
	if rep ne tree[rep] then continue rep; end if;
	if fusion[rep] gt 0 then continue rep; end if;
	G_elt := (clP[rep,3]) @@ iso;
	G_elt_inv := class_invariant(G, G_elt);
	inv_pos := Position(invs, G_elt_inv);
	assert inv_pos gt 0;
	possibles := poss[inv_pos];
	if #possibles gt 1 or pc_flag then cm_count +:= 1; end if;
	G_class, conj_elt :=  ClassNumber(G, G_elt, possibles);

	fusion[rep] := G_class;
	P_ord := clP[rep,1];
	for k := 2 to P_ord-1 do
	    f_pos_k := pmP(rep, k);
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
		for f2_pos := #clP to 1 by -1 do
		    if f2_pos ne tree[f2_pos] then
			continue f2_pos;
		    end if;
		    G_elt := (clP[f2_pos,3] @@ iso)^conj_elt;
		    if G_elt in H then
			P_elt := G_elt @ iso;
			im := P_elt @ cmP;
			find(im, ~tree, ~im2);
			if im2 ne f2_pos then
			    merge(im2, f2_pos, ~tree, ~sizes, ~fusion);
			end if;
		    end if;
		    G_elt := (clP[f2_pos,3] @@ iso)^conj_elt_2;
		    if G_elt in H then
			P_elt := G_elt @ iso;
			im := P_elt @ cmP;
			find(im, ~tree, ~im2);
			if im2 ne f2_pos then
			    merge(im2, f2_pos, ~tree, ~sizes, ~fusion);
			end if;
		    end if;
		end for;
	    else
		conj_saved[G_class] := conj_elt^-1;
	    end if;
	end if;

    end for;

    for i := 1 to #fusion do
	if fusion[i] eq 0 then
	    find(i, ~tree, ~j);
	    assert fusion[j] ne 0;
	    fusion[i] := fusion[j];
	end if;
    end for;

    return fusion;

end function;
