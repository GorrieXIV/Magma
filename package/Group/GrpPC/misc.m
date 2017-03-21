freeze;

intrinsic PCGroup(G::GrpPC) -> GrpPC, Map
{Returns itself, and an identity map}
    return G,iso<G->G|[G.i : i in [1..NPCgens(G)]]>;
end intrinsic; 

intrinsic Radical(G::GrpPC) -> GrpPC
{Returns itself}
    return G;
end intrinsic; 

intrinsic IsFinite(G::GrpPC) -> BoolElt
{True iff G is finite}
    return true;
end intrinsic;

intrinsic IsSupersoluble(G::GrpPC) -> BoolElt
{Is the soluble group G supersoluble}
    while not IsNilpotent(G) do
	M := MinimalNormalSubgroup(G);
	if not IsCyclic(M) then
	    return false;
	end if;
	G := quo<G|M>;
    end while;
    return true;
end intrinsic;

intrinsic MinimalNormalSubgroups(G::GrpPC) -> SeqEnum
{The minimal normal subgroups of G}
    pCs := [Op : t in FactoredOrder(G) | #Op gt 1 where Op := pCore(G, t[1])];
    MNS := [];
    for Op in pCs do
	M, toM := GModule(G, Omega(Centre(Op), 1));
	MS := MinimalSubmodules(M);
	assert #MS gt 0;
	for m in MS do
	    Append(~MNS, m @@ toM);
	end for;
    end for;
    return MNS;
end intrinsic;

intrinsic Socle(G::GrpPC) -> GrpPC
{The socle of G}
    G_ord := FactoredOrder(G);
    if #G_ord eq 0 then return G; end if;
    if #G_ord eq 1 then return Omega(Centre(G), 1); end if;
    pCs := [Op : t in G_ord | #Op gt 1 where Op := pCore(G, t[1])];
    socs := [];
    for Op in pCs do
	M, toM := GModule(G, Omega(Centre(Op), 1));
	Append(~socs, Socle(M) @@ toM);
    end for;
    S := sub<G|socs>;
    return S;
end intrinsic;

intrinsic CarterSubgroup(G::GrpPC) -> GrpPC
{A Carter subgroup of G. A nilpotent and self-normalizing subgroup of G, 
also a nilpotent projector in G}
    if IsNilpotent(G) then return G; end if;
    M := MinimalNormalSubgroup(G);
    Q,f := quo<G|M>;
    K := CarterSubgroup(Q)@@f;
    if #FactoredOrder(K) eq 1 then return K; end if;
    p := FactoredOrder(M)[1,1]; 
    Kpprime := HallSubgroup(K, -p);
    return Normalizer(K, Kpprime);
end intrinsic;

intrinsic FischerSubgroup(G::GrpPC) -> GrpPC
{A Fischer subgroup of G. A nilpotent injector in G} 
    if IsNilpotent(G) then return G; end if;
    N := FittingSubgroup(G);
    G_ord := FactoredOrder(G);
    N_ord := FactoredOrder(N);
    if #G_ord gt #N_ord then
	p_set := {t[1]:t in G_ord} diff {t[1]:t in N_ord};
	Cp := Centralizer(G, N);
	H := sub<G|N, HallSubgroup(Cp, p_set)>;
    end if;
    for t in N_ord do
	p := t[1];
	Cp := Centralizer(G, HallSubgroup(N, -p));
	H := sub<G|H, Sylow(Cp, p)>;
    end for;
    return H;
end intrinsic;

covering := function(G, test)
    repeat
        if test(G) then return G; end if;
        M := MinimalNormalSubgroup(G);
        Q, f := quo<G|M>;
        V := $$(Q, test);
        if V eq Q then
            Cs := Complements(G, M);
            assert #Cs eq 1;
            return Cs[1];
        else
            G := V @@ f;
        end if;
    until false;
end function;

intrinsic CoveringSubgroup(G::GrpPC, T::Intrinsic) -> GrpPC
{A covering T-subgroup of G, where it is assumed that the boolean function T
defines a saturated formation}
    return covering(G, T);
end intrinsic;

intrinsic CoveringSubgroup(G::GrpPC, T::UserProgram) -> GrpPC
{"} // "
    return covering(G, T);
end intrinsic;

intrinsic DoubleCosetRepresentatives ( G :: GrpPC, H :: GrpPC, I :: GrpPC ) -> SetIndx
{Alias for Transversal (A set of representatives for the double cosets HuK in G, where H and K
are subgroups of finite index in G.)}
    return Transversal( G, H, I );
end intrinsic;
