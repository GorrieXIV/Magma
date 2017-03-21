freeze;

RF := recformat<subgroup, order,length>;

ms := function(G)
    M := MaximalSubgroups(G);
    if Type(M[1]) eq Rec then return M; end if;
    res := [];
    for K in M do
	N := Normalizer(G,K);
	L := Index(G,N);
	r := rec<RF|subgroup := K, order := #K, length := L>;
	Append(~res, r);
    end for;
    return res;
    /*
    return [ rec<RF|subgroup := K, order := #K, length := L> : K in M |
	    true where L := Index(G,Normalizer(G,K))];
    */
end function;

maximal_subgroup_classes := function(G, H)
    if #FactoredOrder(H) gt 1 then return ms(H); end if;
    if IsTrivial(H) then return []; end if;
    N := Normalizer(G,H);
    if N eq H then return ms(H); end if;
    F := FrattiniSubgroup(H);
    M,f:= GModule(N,H,F);
    d := Dimension(M)-1;
    p := #BaseRing(M);
    ord := #H div p;
    orbs := OrbitsOfSpaces(ActionGroup(M), d);
    res := [];
    for o in orbs do
	K := sub<H|F, [(M!o[2].i)@@f:i in [1..d]]>;
	if Type(K) in {GrpPerm, GrpMat} then 
	    K`Order := ord;
	end if;
	Append(~res, rec<RF|subgroup := K, order := ord, length := o[1]>);
    end for;
    return res;
end function;

subgroup_lattice := function(G)
    Print := GetVerbose("Subgroups");
    if Print ge 1 then
	zeit := Cputime();
	printf "+SubgroupLattice: group order %o\n", #G;
    end if;
    orders := {@ #G @};
    grps := [G];
    grp_with_order := [[1]];
    incls := {@ @}; /* edges of lattice graph (Hasse diagram) */
    weights := [ ]; /* weights of corresponding edges */
    done := 0;
    while done lt #grps do
	done +:= 1;
	if Print ge 2 then
	    printf "Doing subgroup %o of order %o - have %o subgroup classes\n",
			done, #grps[done], #grps;
	end if;
	s := maximal_subgroup_classes(G, grps[done]);
	for i := 1 to #s do
	    U := s[i]`subgroup;
	    ind := Index(orders, #U);
	    if ind gt 0 and exists(j){j:j in grp_with_order[ind] |
		IsConjugate(G, grps[j], U)} then
		/* old group */
		k := Index(incls, [done, j]);
		if k gt 0 then
		    weights[k] +:= s[i]`length;
		else
		    Include(~incls, [done, j]);
		    Append(~weights, s[i]`length);
		end if;
	    else
		/* new group */
		Append(~grps, U);
		if ind eq 0 then
		    Include(~orders, #U);
		    Append(~grp_with_order,[#grps]);
		else
		    Append(~grp_with_order[ind], #grps);
		end if;
		Include(~incls, [done, #grps]);
		Append(~weights, s[i]`length);
	    end if;
	end for;
    end while; /* main while loop */

    if Print ge 1 then
	printf "Found %o classes after %o secs, computing class lengths\n", 
		    #grps, RealField(5)!Cputime(zeit);
    end if;

    len := [];
    for i := 1 to #grps do
	a := Index(G, Normalizer(G, grps[i]));
	Append(~len, [i, #grps[i], a]);
    end for;

    if Print ge 1 then
	print "Computing the weighted subgroup lattice";
    end if;

    wlat := [];
    for i :=1 to #incls do
	a := incls[i];
	Append(~a, weights[i]);
	Append(~a, len[a[1],3]*a[3] div len[a[2],3]);
	Append(~wlat, a);
    end for;
    delete weights;

    /* sort everything to standard order */
    sort_cmp := function(x,y)
	if not IsTrivial(grps[x]) and not IsTrivial(grps[y]) then
	    res := &+[t[2]:t in FactoredOrder(grps[x])] - 
			&+[t[2]:t in FactoredOrder(grps[y])];
	    if not IsZero(res) then return res; end if;
	end if;
	res := #grps[x]-#grps[y];
	if not IsZero(res) then return res; end if;
	return len[x,3] - len[y,3];
    end function;

    resort := [1..#grps];
    Sort(~resort, sort_cmp);
    perm := [];
    for i := 1 to #grps do
	perm[resort[i]]:=i;
    end for;
    new_len := [];
    len :=  [[perm[l[1]],l[2],l[3]]:l in len];
    sort_cmp := func<x,y|x[1]-y[1]>;
    Sort(~len,sort_cmp);
    wlat := [[perm[l[1]], perm[l[2]], l[3]]:l in wlat];
    Sort(~wlat, sort_cmp);
    grps := [grps[resort[i]]:i in [1..#grps]];

    /* at this point "grps" is sorted list of class reps
     * "len" contains triples [subgrp_num, subgrp_order, class_length]
     *     sorted by subgrp_num so len[i] eq [i, O, L]
     * "wlat" contains edges of hasse diagram as 4-tuples
     *  [super_grp, maximal_sub_grp, x, y] where x,y are NInclusion info
     *  x = number of conjugates of sub_grp contained in each single super_grp
     *  y = number of conjugates of super_grp contained in each single sub_grp
     */

    /* set up maximals so maximals[i] = list of maximal classes of grps[i] 
    maximals := [ []:i in [1..#grps]];
    for t in wlat do
	Append(~maximals[t[1]], t[2]);
    end for;
    */

    /* return vertex info, edges info */
    return [<grps[i], len[i,3]>:i in [1..#grps]], wlat;
end function;

intrinsic ComputeSubgroupLattice(G::GrpPerm) -> SeqEnum, SeqEnum
{}
    E, V := subgroup_lattice(G);
    return E, V;
end intrinsic

intrinsic ComputeSubgroupLattice(G::GrpMat) -> SeqEnum, SeqEnum
{}
    E, V := subgroup_lattice(G);
    return E, V;
end intrinsic

intrinsic ComputeSubgroupLattice(G::GrpPC) -> SeqEnum, SeqEnum
{Compute data for subgroup lattice of G}
    E, V := subgroup_lattice(G);
    return E, V;
end intrinsic
