freeze;

intrinsic SemiLinearGroup(G::GrpMat, S::FldFin) -> GrpMat
{The semilinear extension of G over the subfield S};

    K := CoefficientRing(G);
    require Type(K) eq FldFin: "Argument 1 is not over a finite field";
    d := Degree(G);
    e := Degree(K, S);
    q := #S;

    AK := MatrixAlgebra(K, d);
    AS, f := MatrixAlgebra(AK, S);

    L := [f(AK ! G.i): i in [1 .. Ngens(G)]];

    g := Generator(K, S);
    s := MatrixAlgebra(S, e) ! &cat[Eltseq(g^(i * q), S): i in [0 .. e - 1]];
    sd := DiagonalJoin([s: i in [1 .. d]]);

    H := sub<GL(d * e, S) | L, sd>;
    return H;
end intrinsic;
