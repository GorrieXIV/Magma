freeze;

import "chtr_table.m": GaloisGroup, do_factors_solution, can_use_p;
import "chtr_table.m": ProcessCharacters;
import "elem_chtrs_fusion.m": SubgroupFusion;

forward EXTLINCHAR, GaloisGroupOrbit, ProcessElementaryCharacters;

stufffmt := recformat<P, Field, Expo, Zeta, Chtrs, CCN, M_calls, M_time,
    E_calls, E_time, PEC_time, pp_ord, pp_V, fusion, sizes, mults, n_clp, CP, 
    mask>;

PGPCHARS_layer := procedure(G, zeta, pp_ord, pp_V,
~JJ, ~fusion, ~sizes, ~mults, ~CP, kernels:Print := 0)

    assert Type(G) eq GrpPC;
    ord := FactoredOrder(G);
    assert #ord eq 1;
    P := ord[1,1];
    CC := [c[3]:c in Classes(G)];
    GG := ConditionedGroup(G);
    E := NPCgens(GG);
    exp := Exponent(G);
    Chtr_lim := Max(50, CP`n_Classes div 20);
    stuff := rec<stufffmt| P := P, Zeta := zeta, Chtrs := {}, CCN := [],
	pp_ord := pp_ord, pp_V := pp_V, fusion := fusion, sizes := sizes,
	mults := mults, n_clp := #Classes(G), CP := CP,
	mask := Seqset(fusion)>;
    assert forall{k:k in kernels|not IsTrivial(k)};
    for J := JJ to E do
	if J lt E then
	    kern := sub<GG|[GG.i:i in [J+1..E]]>;
	    assert IsNormal(GG, kern);
	    if exists{k:k in kernels|k subset kern} then continue J; end if;
	    FG, F := quo<GG|kern>;
	    local_kers := [k @ F:k in kernels];
	    assert forall{k:k in local_kers|not IsTrivial(k)};
	    /* if IsAbelian(FG) then continue J; end if; */
	    FGCC := [c[3]:c in Classes(FG)];
	    CMFG := ClassMap(FG);
	    if Print gt 2 then "finding quotient fusion"; end if;
	    zeit := Cputime();
	    stuff`CCN := [CMFG(F(CC[K])): K in [1..#CC]];
	    if Print gt 2 then "Time:", Cputime(zeit); end if;
	else
	    FG := G;
	    /* if IsAbelian(FG) then JJ := -1; break; end if; */
	    FGCC := CC;
	    stuff`CCN := [1..#CC];
	    local_kers := kernels;
	end if;
	LFGCC := #FGCC;
	SS := [[K]:K in [1..LFGCC]];
	MUSS := [[1]:i in [1..LFGCC]];
	zeit := Cputime(); time_field := Parent(zeit);
	stuff`M_calls := 0;
	stuff`M_time := time_field!0.0;
	stuff`E_calls := 0;
	stuff`E_time := time_field!0.0;
	stuff`PEC_time := time_field!0.0;
	exit_flag := false;
	if J lt E then
	    EXTLINCHAR(FG,FGCC,SS,MUSS,F(GG.J),sub<FG|>,~stuff,P,
		~exit_flag, local_kers);
	else
	    EXTLINCHAR(FG,FGCC,SS,MUSS,GG.E,sub<FG|>,~stuff, P,
		~exit_flag, local_kers);
	end if;
	if Print gt 2 then
	    printf "EXTLIN time for layer %o: %o\n", J, Cputime(zeit);
	    printf "MAX calls %o, time %o\n", stuff`M_calls, stuff`M_time;
	    printf "EVAL calls %o, time %o, time in processing %o\n", 
		stuff`E_calls, stuff`E_time, stuff`PEC_time;
	end if;
	do_factors_solution(~stuff`CP);
	if J eq E then JJ := -1; else JJ := J+1; end if;
	if not can_use_p(stuff`CP, P) then
	    CP := stuff`CP;
	    if #stuff`Chtrs gt 0 then
		reds := Setseq(stuff`Chtrs);
		ProcessCharacters(~CP, reds, stuff`mask, 2);
	    end if;
	    return;
	end if;
	if #stuff`Chtrs ge Chtr_lim then
	    break;
	end if;
    end for;
    CP := stuff`CP;
    len := #stuff`Chtrs;
    if len gt 0 then
	reds := Setseq(stuff`Chtrs);
	blks := Ceiling(len/Chtr_lim);
	blk := Ceiling(len/blks);
	for i := 1 to blks do
	    ProcessCharacters(~CP, reds[(i-1)*blk+1..Min(len,i*blk)], stuff`mask
	    , 2);
	    do_factors_solution(~CP);
	end for;
    end if;

end procedure;

forward EVAL;
EXTLINCHAR := procedure(G,CC,SS,MUSS,T,KER,~stuff,P,~exit_flag,kernels)
//"ELC", #G;
    F_flag := not IsTrivial(KER);
    if F_flag then
	FG,F := quo<G|KER>;
	FG := ConditionedGroup(FG);
	FT := F(T);
	FCC := [x@F:x in CC];
	local_kers := [];
	for k in kernels do
	    kF := k @ F;
	    if IsTrivial(kF) then return; end if;
	    Append(~local_kers, kF);
	end for;
	delete F;
    else
	FG := ConditionedGroup(G);
	FT := T;
	FCC := CC;
	local_kers := kernels;
    end if;
    FZ := Centre(FG);
    while true do
	FC := sub<FG|FT>;
	if FC eq FG then
	/* Final section - get character */
	    zeit := Cputime();
	    EVAL(~FG,~FCC,~SS,~MUSS,~stuff,~P);
	    stuff`E_calls +:= 1;
	    stuff`E_time +:= Cputime(zeit);
	    exit_flag := not can_use_p(stuff`CP, P);
	    return;
	end if;
	if FC eq FZ then
	/* one must pass to a maximal subgroup */
	    H,V := quo<FG|FC>;
	    H := ConditionedGroup(H);
	    EH := NPCgens(H);
	    FX := (H.EH)@@V;
	    FXC := ConditionedGroup(sub<FG|FT,FX>);
	    delete H,V;
	    FM := Centralizer(FG,FX);
	    zeit := Cputime();
	    MAXSGPInternal(FG,FM,~FCC,~SS,~MUSS);
	    // assert #SS eq #MUSS;
	    // assert forall{i:i in [1..#SS]|#SS[i] eq #MUSS[i]};
	    stuff`M_calls +:= 1;
	    stuff`M_time +:= Cputime(zeit);
	    if IsCyclic(FXC) then
	    /* enlarge central cyclic to FXC */
		/* search continues, loop */
		/* $$(FM,FCC,SS,MUSS,FX,sub<FM|>,~stuff,P,~exit_flag,local_kers); */
		local_kers := [sub<FM|k>:k in local_kers|k subset FM];
		FG := FM;
		FT := FG!FX;
		FZ := Centre(FG);
	    else
	    /* divide out by central subgp of order P */
		while FX^P ne Identity(FG) do
		    FX *:= FT;
		end while;
		MKER := sub<FM|FX>;
		delete FG,FC,FZ;
		/* recursive search continues */
		local_kers := [sub<FM|k>:k in local_kers|k subset FM];
		$$(FM,FCC,SS,MUSS,FM!FT,MKER,~stuff, P,~exit_flag, local_kers);
		return;
	    end if;
	else
	/* one can avoid passing to a maximal subgroup */
	    FZ := ConditionedGroup(FZ);
	    N := NPCgens(FZ);
	    repeat
		FZN := FG!(FZ.N);
		N -:= 1;
	    until FZN notin FC;
	    FNC := sub<FG|FC,FZN>;
	    if IsCyclic(FNC) then
	    /* enlarge central cyclic */
		FT := FG!(FNC.1);
		/* and go looking for more characters: loop */
		/* $$(FG,FCC,SS,MUSS,FT,sub<FG|>,~stuff,P,~exit_flag,local_kers);*/
	    else
	    /* pass to P distinct quotients by central subgps of order P */
	    /* the branching step of the search */
		FY := FT ^ (Order(FT) div P);
		delete FC;
		while FZN^P ne Identity(FG) do
		    FZN *:= FT;
		end while;
		FYKZN := FZN;
		for K := 1 to P do
		    FYKZN *:= FY;
		    NKER := sub<FG|FYKZN>;
		    $$(FG,FCC,SS,MUSS,FT,NKER,~stuff, P,~exit_flag,local_kers);
		    if exit_flag then break; end if;
		end for;
		return;
	    end if;
	end if;
    end while;
end procedure;

GaloisGroupOrbit:= procedure(~CP, ~orb0)
    K := CP`K;
    GaloisGroup(~CP);
    gens := CP`GalGroup;
    R := Universe(orb0);
    if #gens eq 0 then return; end if;
    len := #gens[1];
    res := {};
    for x in orb0 do
	if x in res then continue; end if;
	this_orb := {x};
	for g in gens do
	    blk0 := this_orb;
	    repeat
		x0 := Rep(blk0);
		im0 := InternalChtrTablePermute(K, x0, g);
		if im0 in this_orb then break; end if;
		nextblk := { R!InternalChtrTablePermute(K, x1, g) :
				x1 in blk0 | x1 ne x0}; 
		Include(~nextblk, im0);
		this_orb join:= nextblk;
		blk0 := nextblk;
	    until false;
	end for;
	res join:= this_orb;
    end for;
    orb0 := res;
end procedure;

EVAL := procedure(~G,~CC,~SS,~MUSS,~stuff, ~P)
    c := EVALInternal(G, CC, SS, MUSS, stuff`CCN, stuff`Zeta);
    n_clp := stuff`n_clp;
    pp_ord := stuff`pp_ord;
    x := [];
    for i := 1 to n_clp do x cat:= [c[i]:j in [1..pp_ord]]; end for;
    x := Universe(stuff`pp_V)!x;
    if #stuff`pp_V gt 1 then
	chtrs := [x*w:w in stuff`pp_V];
    else
	chtrs := [x];
    end if;
    zeit := Cputime();
    ProcessElementaryCharacters(~stuff`CP, ~stuff`Chtrs, ~stuff`fusion, ~stuff`sizes, ~stuff`mults, ~stuff`mask, chtrs);
    stuff`PEC_time +:= Cputime(zeit);
end procedure;

p_pp_parts := function(g, p)
// return the p- and p'-parts of g
    ord := Order(g);
    v,y := Valuation(ord, p);
    ppow := p^v;
    _,a,b := Xgcd(ppow, y);
    return g^(b*y), g^(a*ppow);
end function;

p_pp_subgroups := function(G, p)
// Assumes G is a p-elementary PC-group.
// Return the p- and p'-parts of G as subgroups of G.
    ngens := NPCgens(G);
    p_gens := [];
    pp_gens := [];
    // Split generators of G into their p- and p'-parts
    for i := 1 to ngens do
	gp, gpp := p_pp_parts(G.i, p);
	Append(~p_gens, gp);
	Append(~pp_gens, gpp);
    end for;
    Gp := sub<G|p_gens>;
    Gpp := sub<G|pp_gens>;
    return Gp, Gpp;
end function;

ProcessElementaryCharacters := procedure(~CP, ~chtrs, ~fusion, ~sizes, ~mults, ~mask, subgp_chtrs)
    clG := CP`Classes;
    V := CP`V;
    for x in subgp_chtrs do
	y := InternalInduce(V, fusion, sizes, mults, mask, x);
	if y notin chtrs then
	    orb := {y};
	    GaloisGroupOrbit(~CP, ~orb);
	    chtrs join:= orb;
	end if;
    end for;
end procedure;

ElementaryInduction := procedure(~CP, H, p, ~JJ, ~fusion, ~sizes, ~mults, ~Pp, ~pp_V, kernels)


    if JJ eq 0 then
	p_grp := #FactoredOrder(H) le 1;
    vprintf Chtr, 1: "Induction from %o-Elementary, Order = %o, Layer = 0\n",
	p, FactoredOrder(H);

	/* first time through, set things up */

	if Type(H) eq GrpPC then
	    P := H;
	    iso := IdentityHomomorphism(H);
	else
	    P, iso := PCGroup(H);
	end if;

	if p_grp then
	    Pp := P;
	    x := P!1;
	    Ppp := sub<P|x>;
	    pp_ord := 1;
	    pp_chtrs := [[CP`K|1]];
	else
	    Pp, Ppp := p_pp_subgroups(P, p);
	    x := P!(&*AbelianBasis(Ppp)); /* generator for Ppp */
	    pp_ord := #Ppp;
	    assert Order(x) eq pp_ord;
	    pp_zeta := CP`zeta^((#CP`K-1) div pp_ord);
	    pp_chtrs := [];
	    divisors := Divisors(pp_ord);
	    for i in divisors do
		z := pp_zeta^i;
		chtr := [CP`K|1, z];
		for j := 3 to pp_ord do
		    Append(~chtr, z*chtr[j-1]);
		end for;
		Append(~pp_chtrs, chtr);
	    end for;
	end if;

	SubgroupFusion(~CP, iso, Pp, x, ~fusion);
	clp := Classes(Pp);

	/* set up some more induction stuff */
	mask := Seqset(fusion); /* G classes that might not be zero valued */
	index := CP`K!(CP`G_order div #P);
	invsizes := CP`InvSizes;
	mults := [CP`K|];
	for i in mask do mults[i] := index*invsizes[i]; end for;
	sizes := [CP`K|];
	ptr := 0;
	for i := 1 to #clp do
	    s := CP`K!clp[i,2];
	    for j := 1 to pp_ord do
		ptr +:= 1;
		sizes[ptr] := s;
	    end for;
	end for;

	/* pull the Ppp_chtrs back into P */
	pp_V := [VectorSpace(CP`K,#clp*pp_ord)|];
	for c in pp_chtrs do
	    Append(~pp_V, &cat[c:i in [1..#clp]]);
	end for;

	PGPCHARS_layer(Pp, CP`zeta,
	    pp_ord, pp_V, ~JJ, ~fusion, ~sizes, ~mults, ~CP, kernels : 
		    Print := GetVerbose("Chtr"));

    else
	vprintf Chtr, 1: "Induction from %o-Elementary, Order = %o, Layer = %o\n",
			    p, H, JJ;
	pp_ord := Integers()!H div #Pp;
	PGPCHARS_layer(Pp, CP`zeta,
	    pp_ord, pp_V, ~JJ, ~fusion, ~sizes, ~mults, ~CP, kernels : 
		    Print := GetVerbose("Chtr"));
    end if;

end procedure;
