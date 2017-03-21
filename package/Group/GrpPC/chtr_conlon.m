freeze;

PR := RealField(5);

forward EXTLINCHAR, GaloisGroup, GaloisOrbit;
PGPCHARS := function(G:Print := 0)
    assert Type(G) eq GrpPC;
    ord := FactoredOrder(G);
    assert #ord eq 1;
    P := ord[1,1];
    CC := [c[3]:c in Classes(G)];
    GG := ConditionedGroup(G);
    E := NPCgens(GG);
    exp := Exponent(G);
    zeta := [* *];
    pow := 1;
    for i := 1 to Ilog(P, exp) do
	pow *:= P;
	fld := CyclotomicField(pow);
	Append(~zeta, RootOfUnity(pow, fld));
    end for;
    stufffmt := recformat<P, Field, Expo, Zeta, Chtrs, CCN, M_calls, M_time,
	E_calls, E_time>;
    stuff := rec<stufffmt| P := P, Zeta := zeta, Chtrs := [**], CCN := []>;
    for J := 1 to E do
	if J lt E then
	    FG, F := quo<GG|[GG.i:i in [J+1..E]]>;
	    FGCC := [c[3]:c in Classes(FG)];
	    CMFG := ClassMap(FG);
	    if Print gt 0 then "PGPCHARS finding quotient fusion"; end if;
	    zeit := Cputime();
	    stuff`CCN := [CMFG(F(CC[K])): K in [1..#CC]];
	    if Print gt 0 then "Time:", PR!Cputime(zeit); end if;
	else
	    FG := G;
	    FGCC := CC;
	    stuff`CCN := [1..#CC];
	end if;
	LFGCC := #FGCC;
	SS := [[K]:K in [1..LFGCC]];
	MUSS := [[1]:i in [1..LFGCC]];
	zeit := Cputime();
	stuff`M_calls := 0;
	stuff`M_time := PR!0.0;
	stuff`E_calls := 0;
	stuff`E_time := PR!0.0;
	if J lt E then
	    EXTLINCHAR(FG,FGCC,SS,MUSS,F(GG.J),sub<FG|>,~stuff, P);
	else
	    EXTLINCHAR(FG,FGCC,SS,MUSS,GG.E,sub<FG|>,~stuff, P);
	end if;
	if Print gt 0 then
	    printf "EXTLIN time for J = %o: %o\n", J, Cputime(zeit);
	    printf "after J = %o: %o classes, %o chtrs\n", J, #FGCC, 1+#(stuff`Chtrs);
	    if Print gt 1 then
	    printf "MAX calls %o, time %o\n", stuff`M_calls, stuff`M_time;
	    printf "EVAL calls %o, time %o\n", stuff`E_calls, stuff`E_time;
	    end if;
	end if;
    end for;
    zeit := Cputime();
    gal_gens := GaloisGroup(G);
    if Print gt 1 then 
	"PGPCHARS: Galois group:", PR!Cputime(zeit), "secs";
    end if;
    zeit := Cputime();
    R := CharacterRing(G);
    X := [R|1];
    for i := 1 to #stuff`Chtrs do
	l := stuff`Chtrs[i];
	x := Minimize(l);
	orb := {x};
	GaloisOrbit(G, gal_gens, ~orb);
	for x in orb do
	    Append(~X, x);
	end for;
    end for;
    if Print gt 1 then 
	"PGPCHARS: get orbits and coerce into character ring:", 
	PR!Cputime(zeit), "secs";
    end if;
    for i := 1 to #zeta do
	fld := Parent(zeta[i]);
    end for;
    return X;
end function;

forward EVAL;
EXTLINCHAR := procedure(G,CC,SS,MUSS,T,KER,~stuff, P)
    F_flag := not IsTrivial(KER);
    if F_flag then
	FG,F := quo<G|KER>;
	FG := ConditionedGroup(FG);
	FT := F(T);
	FCC := [x@F:x in CC];
	delete F;
    else
	FG := ConditionedGroup(G);
	FT := T;
	FCC := CC;
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
		/* $$(FM,FCC,SS,MUSS,FX,sub<FM|>,~stuff, P); */
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
		$$(FM,FCC,SS,MUSS,FM!FT,MKER,~stuff, P);
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
		/* $$(FG,FCC,SS,MUSS,FT,sub<FG|>,~stuff, P);*/
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
		    $$(FG,FCC,SS,MUSS,FT,NKER,~stuff, P);
		end for;
		return;
	    end if;
	end if;
    end while;
end procedure;

EVAL := procedure(~G,~CC,~SS,~MUSS,~stuff, ~P)
    Append(~(stuff`Chtrs), 
	EVALInternal(G, CC, SS, MUSS, stuff`CCN, stuff`Zeta)
    );
end procedure;

GaloisGroup := function(G)
    e := Exponent(G);
    U, f := UnitGroup(Integers(e));
    gens := [Integers() | g@f : g in Generators(U) ];
    pm := PowerMap(G);
    d := #Classes(G);
    S := Sym(d);
    gens := [ p : g in gens | not IsIdentity(p) where
		p is S![pm(i,g): i in [1..d]] ];
    grp := sub<S|gens>;
    P, f :=  PCGroup(grp);
    gens := [Eltseq(g@@f):g in PCGenerators(P)];
    Reverse(~gens);
    return gens;
end function;

GaloisOrbit:= procedure(G, gens, ~orb0)
    R := Universe(orb0);
    if #gens eq 0 then return; end if;
    len := #gens[1];
    for g in gens do
	blk0 := orb0;
	repeat
	    x0 := Rep(blk0);
	    im0 := R![x0[g[i]]:i in [1..len]];
	    if im0 in orb0 then break; end if;
	    nextblk := { R![x0[g[i]]:i in [1..len]] : x0 in blk0 }; 
	    orb0 join:= nextblk;
	    blk0 := nextblk;
	until false;
    end for;
end procedure;

intrinsic CharacterTableConlon(G::GrpPC) -> SeqEnum
{Character table of the p-group G using Conlon's algorithm}
    require #FactoredOrder(G) le 1:"Group is not a p-group";
    R := CharacterRing(G);
    if #G eq 1 then return [R|1]; end if;
    X := PGPCHARS(G:Print:=GetVerbose("Chtr"));

    for x in X do AssertAttribute(x, "IsIrreducible", true); end for;
    return KnownIrreducibles(R);
end intrinsic;
