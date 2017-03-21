freeze;

intrinsic MaximalOddOrderNormalSubgroup(G::GrpPC) -> GrpPC
{The maximal odd order normal subgroup of G}
    return Core(G, HallSubgroup(G,-2));
end intrinsic;

intrinsic MaximalOddOrderNormalSubgroup(G::GrpPerm) -> GrpPerm
{The maximal odd order normal subgroup of G}
    R := SolubleRadical(G);
    if IsOdd(#R) then return R; end if;
    if #FactoredOrder(R) eq 1 then
	R := sub<G|>;  R`Order := 1; return R;
    end if;
    PR, toPR := PCGroup(R);
    return Core(PR, HallSubgroup(PR,-2)) @@ toPR;
end intrinsic;


intrinsic MaximalOddOrderNormalSubgroup(G::GrpMat) -> GrpMat
{The maximal odd order normal subgroup of G}
    R := SolubleRadical(G);
    if IsOdd(#R) then return R; end if;
    if #FactoredOrder(R) eq 1 then
	R := sub<G|>;  R`Order := 1; return R;
    end if;
    PR, toPR := PCGroup(R);
    return Core(PR, HallSubgroup(PR,-2)) @@ toPR;
end intrinsic;

intrinsic MaximalOddOrderNormalSubgroup(G::GrpAb) -> GrpAb
{The maximal odd order normal subgroup of G}
    PG, toPG := PCGroup(G);
    return  Core(PG, HallSubgroup(PG,-2)) @@ toPG;
end intrinsic;
