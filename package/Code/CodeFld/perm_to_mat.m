freeze;

intrinsic CodePermutationToMatrix(C::CodeLinFld, p::GrpPermElt) -> ModMatFldElt
{Return the matrix giving the equivalent action on C to the permutation p}
    return CodePermutationToMatrix(BaseRing(C), Length(C), p);
end intrinsic;

intrinsic CodePermutationToMatrix(C::CodeLinFld, G::GrpPerm) -> GrpMat
{Return the matrix group giving the equivalent action on C to the permutation group G}
    F := BaseRing(C);
    n := Length(C);
    gens := [CodePermutationToMatrix(F, n, G.i): i in [1..Ngens(G)]];
    M := MatrixGroup<n, F|gens>;
    fl, ord := HasAttribute(G, "Order");
    if fl then M`Order := ord; end if;
    return M;
end intrinsic;

intrinsic CodePermutationToMatrix(F::FldFin, n::RngIntElt, G::GrpPerm) -> GrpMat
{Return the matrix group giving the equivalent action on code over field F with block length n to the permutation group G}
    gens := [CodePermutationToMatrix(F, n, G.i): i in [1..Ngens(G)]];
    M := MatrixGroup<n, F|gens>;
    fl, ord := HasAttribute(G, "Order");
    if fl then M`Order := ord; end if;
    return M;
end intrinsic;

intrinsic AutomorphismGroupAsMatrixGroup(C::CodeLinFld) -> GrpMat
{The monomial automorphism group of code C as a matrix group}
    return CodePermutationToMatrix(C, AutomorphismGroup(C));
end intrinsic;
