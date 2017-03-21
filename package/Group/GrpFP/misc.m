freeze;

intrinsic TestHomomorphism(G::GrpFP, Q::SeqEnum) -> BoolElt
{Does the function G.i :-> Q[i] define a homomorphism}
    require Ngens(G) eq #Q: "Number of images must equal number of generators";
    "Testing";
    rels := [LHS(r)*RHS(r)^-1:r in Relations(G)];
    I := [x^-1:x in Q];
    U := Universe(Q);
    for r in rels do
	e := Eltseq(r);
	res := U!1;
	for i := 1 to #e do
	    if e[i] gt 0 then res := res * Q[e[i]];
	    else res := res * I[-e[i]];
	    end if;
	end for;
	if not IsIdentity(res) then r; return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic TestHomomorphism(G::GrpFP, Q::SeqEnum, K::Grp) -> BoolElt
{Does the function G.i :-> Q[i] define a homomorphism modulo K}
    require Ngens(G) eq #Q: "Number of images must equal number of generators";
    "Testing";
    rels := [LHS(r)*RHS(r)^-1:r in Relations(G)];
    I := [x^-1:x in Q];
    U := Universe(Q);
    for r in rels do
	e := Eltseq(r);
	res := U!1;
	for i := 1 to #e do
	    if e[i] gt 0 then res := res * Q[e[i]];
	    else res := res * I[-e[i]];
	    end if;
	end for;
	if not res in K then r; return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic FibonacciGroup(n :: RngIntElt) -> GrpFP
{The n-th Fibonacci group}
    require n ge 3:"Must have at least 3 generators";
    rels := [[i, i+1, -(i+2)]:i in [1..n-2]];
    rels cat:= [[n-1, n, -1], [n, 1, -2]];
    F := quo<FreeGroup(n)|rels>;
    return F;
end intrinsic;

intrinsic PermutationGroup(G :: GrpFP) -> GrpPerm, HomGrp
{A faithful permutation representation of the group G}
    ord := Order(G);
    require ord gt 0 and ord lt 2^30 : "Group order too large";
    P1 := CosetImage(G, sub<G|>);
    P1`Order := ord;
    P2 := DegreeReduction(P1);
    assert Ngens(P2) eq Ngens(G);
    return P2, iso<G->P2|[P2.i:i in [1..Ngens(G)]]>;
end intrinsic;

intrinsic PCGroup(G :: GrpFP) -> GrpPC, HomGrp
{A representation of the finite soluble group G as a pc-group}
    ord := Order(G);
    require ord gt 0: "Group order too large";
    P, f := PCGroupInternal(G, ord);
    return P, f;
end intrinsic;

intrinsic AbelianQuotientRewrite(G::GrpFP, H::GrpFP) -> GrpAb, HomGrp
{Abelian quotient of H <= G, with quotient map}
    X := Rewrite(G,H);
    Q, f := AbelianQuotient(X);
    ims := [ (X!G!H.i) @ f: i in [1..Ngens(H)]];
    return Q, hom<H->Q | ims >;
end intrinsic;

