
freeze;

intrinsic MatrixQuotient(G::GrpPerm) -> GrpMat, Map
{Given an affine group G, compute the socle quotient as a
subgroup of GL(n, p), where Degree(G) eq p^n, and the quotient 
homomorphism}

    a, S := IsAffine(G);
    require a : "Permutation group must be of affine type";
    M := GModule(G, S);
    assert Nagens(M) eq Ngens(G);
    A := [ActionGenerator(M, i): i in [1..Nagens(M)]];
    f := Factorization(Degree(G));
    gl := GeneralLinearGroup(f[1,2], f[1,1]);
    Q := sub<gl|A>;
    AssertAttribute(Q, "Order", #G div Degree(G));
    pQ := hom<G->Q|A>;
    return Q, pQ;
end intrinsic;

intrinsic MatrixQuotient(G::GrpPerm, A::GrpPerm) -> GrpMat, Map
{Given a group G and an elementary abelian normal subgroup A, compute the 
quotient group defined by G's linear action on A. Returns a
subgroup of GL(n, p), where #A eq p^n, and the quotient homomorphism}

    M := GModule(G, A);
    assert Nagens(M) eq Ngens(G);
    act := [ActionGenerator(M, i): i in [1..Nagens(M)]];
    f := FactoredOrder(A);
    gl := GeneralLinearGroup(f[1,2], f[1,1]);
    pQ := hom<G->gl|act>;
    return Image(pQ), pQ;
end intrinsic;

intrinsic MatrixQuotient(G::GrpPerm, A::GrpPerm, B::GrpPerm) -> GrpMat, Map
{Given a group G and an elementary abelian section A/B, compute the 
quotient group defined by G's linear action on A/B. Returns a
subgroup of GL(n, p), where #A/B eq p^n, and the quotient homomorphism}

    M := GModule(G, A, B);
    assert Nagens(M) eq Ngens(G);
    act := [ActionGenerator(M, i): i in [1..Nagens(M)]];
    f := Factorization(#A div #B);
    gl := GeneralLinearGroup(f[1,2], f[1,1]);
    pQ := hom<G->gl|act>;
    return Image(pQ), pQ;
end intrinsic;
