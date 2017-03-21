freeze;

/*
Machinery for dealing with invariants over projective matrix groups.
Allan Steel, Oct 2011.
*/

/*******************************************************************************
			    InvariantsOfDegree
*******************************************************************************/

intrinsic SemiInvariantsOfDegree(R::RngInvar, d::RngIntElt, chi::AlgChtrElt)
-> []
{The semi-invariants of R of degree d w.r.t. the linear character chi}

    requirege d, 0;
    require Degree(chi) eq 1: "Character must be linear";

    G := Group(R);
    P := PolynomialRing(R);
    K := BaseRing(P);

    CF := CharacterField(chi);
    require Degree(CF) eq 1 and Degree(K) eq 1 or IsSubfield(CF, K):
"Character field must be subfield of the coefficient field of the matrix group";

    ng := Ngens(G);

    M := MonomialsOfDegree(P, d);
    X := SparseMatrix(K);
    r := 1;
    for i := 1 to #M do
	m := M[i];
	for j := 1 to ng do
	    g := G.j;
	    L := m^g - m*K!chi(g);
	    //i, j, L;
	    LC, LM := CoefficientsAndMonomials(L);
	    for k := 1 to #LC do
		SetEntry(~X, r, (j - 1)*#M + Index(M, LM[k]), LC[k]);
	    end for;
	end for;
	r +:= 1;
    end for;

    //X, Density(X);
    if 1 eq 1 then
	X := Matrix(X);
	N := BasisMatrix(Nullspace(X)); delete X;
    else
	X := Transpose(X);
	NullspaceOfTransposeMatrix(~X, ~N);
    end if;

    return [
	&+[N[i, j]*M[j]: j in [1 .. #M]]: i in [1 .. Nrows(N)]
    ];

end intrinsic;
