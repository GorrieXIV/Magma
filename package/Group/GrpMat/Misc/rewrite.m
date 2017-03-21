freeze;

intrinsic WriteOverSmallerField(G::GrpMat, F::FldFin) -> GrpMat, Map
{Given a group G of d by d matrices over a finite field E having degree e
and a subfield F of E having degree f, write the matrices of G as
d*e/f by d*e/f matrices over F and return the group and the isomorphism};

    K := CoefficientRing(G);
    require Type(K) eq FldFin: "Argument 1 is not over a finite field";
    require PrimeField(K) eq PrimeField(F): "Arguments are not compatible";

    d := Degree(G);
    A := MatrixRing(K, d);
    B, f := MatrixRing(A, F);

    H := MatrixGroup<Degree(K, F) * d, F | [f(G.i): i in [1 .. Ngens(G)]]>;
    g := map<G -> Generic (H) | x :-> f(x)>;
    return H, g;
end intrinsic;
