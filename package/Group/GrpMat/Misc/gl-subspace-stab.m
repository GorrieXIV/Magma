freeze;

intrinsic GLSubspaceStabiliser ( G :: GrpMat, W :: ModTupFld ) -> GrpMat
{Computes the subgroup of G (assumed to be GL(n, p) for some n and p) which stabilises W}

    V := VectorSpace(G);
    b := Basis(W);
    e := ExtendBasis(W, V);
    p := #Field(V);

    /* change_of_basis takes basis e to standard basis... */
    change_of_basis := G![ Eltseq(e[i]) : i in [1..#e] ];
    change_of_basis_inv := change_of_basis^-1;

    k := #b;
    n := Degree(G);

    /* In the basis e, we have w_1, w_2,..,w_r, v_1, ..., v_n where w_i is the basis for W
       and v_1,..., v_n extends w_i basis to basis of V */
    W_G1 := GL(k, p);
    W_G2 := GL(n - k, p);
    W_G1_gens := [ G!Transpose(DiagonalJoin(W_G1.i, Identity(W_G2))) : i in [1..Ngens(W_G1)] ];
    W_G2_gens := [ G!Transpose(DiagonalJoin(Identity(W_G1), W_G2.i)) : i in [1..Ngens(W_G2)] ];

    other_gen := Identity(G);
    other_gen := Eltseq(other_gen);
    other_gen[k * n + 1] := 1;
    gens := W_G1_gens cat W_G2_gens cat [ G!other_gen ];

    return sub < G | [ change_of_basis_inv * gens[i] * change_of_basis : i in [1..#gens]] >;

end intrinsic;


intrinsic GLSubspaceStabiliser ( n :: RngIntElt, p :: RngIntElt, W :: ModTupFld ) -> GrpMat
{Computes the subgroup of GL(n,p) which stabilises W}
    return GLSubspaceStabiliser( GL(n, p), W);
end intrinsic;


intrinsic GLSubspaceStabilizer ( G :: GrpMat, W :: ModTupFld ) -> GrpMat
{Alias for GLSubspaceStabiliser}
    return GLSubspaceStabiliser (G, W);
end intrinsic;