freeze;

/*
Automorphism Group of a G-module (unit group of endomorphism ring).
AKS, April 10, 1998.
Algorithm by D.F. Holt from M. Smith's thesis.
*/

VERB := false;

intrinsic AutomorphismGroup(M::ModRng) -> GrpMat
{The automorphism group of M}

    K := BaseRing(M);
    MA := MatrixRing(K, Dimension(M));
    Md := Dimension(M);

    // Build inhomogeneous components
    L := [];
    C := [**];
    for S in IndecomposableSummands(M) do
	for i := 1 to #L do
	    b, T := IsIsomorphic(S, L[i][1]);
	    if b then
		Append(~L[i], S);
		C[i] := DiagonalJoin(C[i], T);
		continue S;
	    end if;
	end for;
	Append(~L, [S]);
	Append(~C, MatrixRing(K, Dimension(S)) ! 1);
    end for;

    pos := [];
    p := 1;
    for I in L do
	Append(~pos, p);
	p +:= &+[Dimension(S): S in I];
    end for;

    U1 := [MA|];
    for i := 1 to #L do
	I := L[i];
	d := Dimension(I[1]);
	CT := C[i];
	CTI := CT^-1;
	V := [];
	if VERB then
	    "i:", i;
	    IndentPush();
	    "I:", I;
	    //"CT:", CT;
	    //"CTI:", CTI;
	end if;
	//for s := 1 to #I do
	for s := 1 to 1 do
	    S := I[s];
	    assert Dimension(S) eq d;

	    E := EndomorphismRing(S);
	    J := JacobsonRadical(E);
	    Q, f := quo<E | J>;
	    repeat
		r := Random(Q);
		m := MinimalPolynomial(r);
	    until Degree(m) eq Dimension(Q) and IsPrimitive(m);
	    X := r @@ f;
	    //"X:", X;

	    Kd := ext<K | Dimension(Q)>;
	    h := hom<Kd -> Parent(X) | x :-> IsZero(x) select 0 else X^Log(x)>;
	    n := #I;
	    H := GL(n, Kd);
	    for g in [1 .. Ngens(H)] do
		Y := VerticalJoin(
		    [
			HorizontalJoin([h((H.g)[i][j]): j in [1 .. n]]):
			i in [1 .. n]
		    ]
		);
		Append(~V, CT * Y * CTI);
	    end for;

	    if VERB then
		"S:", S;
		"E:", E;
		"J:", J;
		"Field degree:", Dimension(Q);
	    end if;

	    GA := Generic(J);
	    JL := [];
	    Jp := J;
	    while not IsZero(Jp) do
		Append(~JL, Jp);
		Jp := Jp * J;
	    end while;

	    A := sub<GA |>;
	    B := [GA | ];
	    for k in [#JL .. 1 by -1] do
		Jp := JL[k];
		for b in Basis(Jp) do
		    if b notin A then
			A := sub<GA | A, b>;
			Append(~B, b);
		    end if;
		end for;
	    end for;

	    /*
	    II := MatrixRing(K, (n - 1) * Degree(J)) ! 1;
	    for b in B do
		Append(~V, DiagonalJoin(b + 1, II));
	    end for;
	    */
	    for b in B do
		X := b + 1;
		Y := MatrixRing(K, n * d) ! 1;
		p := (s - 1) * d + 1;
		InsertBlock(~Y, X, p, p);
		Append(~V, Y);
	    end for;
	end for;
	if VERB then
	    //"V:", V;
	    IndentPop();
	end if;
	for X in V do
	    Y := MA ! 1;
	    p := pos[i];
	    InsertBlock(~Y, X, p, p);
	    Append(~U1, Y);
	end for;
    end for;

    U2 := [MA|];
    for i := 1 to #L do
	SI := L[i][1];
	for j := 1 to #L do
	    if j eq i then
		continue;
	    end if;
	    SJ := L[j][1];
	    H := AHom(SI, SJ);
	    Z := RMatrixSpace(
		K,
		(#L[i] - 1) * Dimension(SI), 
		(#L[j] - 1) * Dimension(SJ)
	    ) ! 0;
	    B := ChangeUniverse(
		Basis(H),
		KMatrixSpace(K, Dimension(Domain(H)), Dimension(Codomain(H)))
	    );
	    for b in B do
		D := DiagonalJoin(b, Z);
		X := MA ! 1;
		InsertBlock(~X, D, pos[i], pos[j]);
		Append(~U2, X);
	    end for;
	end for;
    end for;

    T := RMatrixSpace(K, 0, Md) ! 0;
    for I in L do
	T := VerticalJoin(T, VerticalJoin([Morphism(S, M): S in I]));
    end for;
    TI := T^-1;

    U1 := [MA | TI*X*T: X in U1];
    U2 := [MA | TI*X*T: X in U2];
    U := U1 cat U2;

    // Assign to get rid of map
    A := MatrixGroup<Md, K | U>;
    return A;
end intrinsic;
