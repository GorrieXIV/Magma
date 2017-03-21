freeze;

intrinsic ExteriorSquare(g::GrpMatElt) -> GrpMatElt
{The exterior square of g}
    G := Parent(g);
    E := GL(Binomial(Degree(G), 2), BaseRing(G));
    return E!ExteriorSquare(Matrix(g));
end intrinsic;

intrinsic ExteriorSquare(G::GrpMat) -> GrpMat, []
{The exterior square representation of G and commutator basis for space}

    n := Degree(G);
    E := GL(Binomial(n, 2), BaseRing(G));
    H := sub<E | [ExteriorSquare(Matrix(G.i)): i in [1 .. Ngens(G)]]>;

    Q := [[i, j]: j in [1 .. i - 1], i in [2 .. n]];
    return H, Q;
end intrinsic;
