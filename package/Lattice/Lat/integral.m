freeze;

/*
Various things for integral lattices and related operations.
AKS, Jan 2007.
*/

Q := RationalField();

////////////////////////////////////////////////////////////////////////////////

intrinsic IntegralBasisLattice(L::Lat) -> Lat, RngIntElt
{Return the lattice obtained from L by multiplying the basis
by the smallest positive scalar S so that the resulting basis is integral,
and S}

   require IsExact(L): "Argument 1 must be an exact lattice";
   S := BasisDenominator(L);
   return S*L, S;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////

intrinsic Complement(L::Lat) -> Lat
{The complement of L in the standard lattice (assuming the quotient is free)}

    B := BasisMatrix(L);
    r := Nrows(B);
    n := Ncols(B);
    S, P, Q := SmithForm(B);
    require forall{i: i in [1 .. r] | S[i, i] le 1}:
	"Lattice basis is not saturated so integral complement does not exist";

    QI := Q^-1;

    C := RowSubmatrixRange(QI, r + 1, n);
    return Lattice(C);

    /*
    B := HermiteForm(BasisMatrix(L));

    n := Ncols(B);
    P := {Min(Support(B[i])): i in [1 .. Nrows(B)]};
    P := {1 .. n} diff P;
    P := Sort(Setseq(P));
    q := n - Nrows(B);
    G := RMatrixSpace(Q, q, n) ! 0;
    for i := 1 to q do
	G[i][P[i]] := 1;
    end for;
    J := VerticalJoin(Matrix(Q, B), G);
    d := Determinant(J);
    assert d ne 0;
    G[q] := G[q]*1/d;

    return Lattice(G);
    */

end intrinsic;
