freeze;

intrinsic AGL(t :: Cat, n :: RngIntElt, q :: RngIntElt) -> Grp
{AGL(n, q) as a group of type t, which can be either GrpMat or GrpPerm};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    require n ge 2: "Argument 2 must be at least 2";

    f := Factorization(q);

    require  q gt 1 and #f eq 1: "Argument 3 must be a prime power";

    if t eq GrpPerm then
	return AGL(n, q);
    end if;

    K := GF(f[1][1], f[1][2]);
    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    gl := GL(n, K);
    V := VectorSpace(gl);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(gl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(gl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;

intrinsic AGL(t :: Cat, n :: RngIntElt, K :: FldFin) -> Grp
{AGL(n, K) as a group of type t, which can be either GrpMat or GrpPerm};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    require n ge 2: "Argument 2 must be at least 2";

    if t eq GrpPerm then
	return AGL(n, K);
    end if;

    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    gl := GL(n, K);
    V := VectorSpace(gl);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(gl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(gl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;

intrinsic AGL(t :: Cat, V :: ModTupRng) -> Grp
{AGL(n, K) as a group of type t, which can be either GrpMat or GrpPerm, where
n is the dimension of V and K is its base field};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    K := BaseRing(V);
    n := Dimension(V);

    require Type(K) eq FldFin: "Argument 2 must have base ring a finite field";

    require n ge 2: "Argument 2 must have dimension at least 2";

    if t eq GrpPerm then
	return AGL(n, K);
    end if;

    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    gl := GL(n, K);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(gl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(gl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;


intrinsic ASL(t :: Cat, n :: RngIntElt, q :: RngIntElt) -> Grp
{ASL(n, q) as a group of type t, which can be either GrpMat or GrpPerm};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    require n ge 2: "Argument 2 must be at least 2";

    f := Factorization(q);

    require  q gt 1 and #f eq 1: "Argument 3 must be a prime power";

    if t eq GrpPerm then
	return ASL(n, q);
    end if;

    K := GF(f[1][1], f[1][2]);
    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    sl := SL(n, K);
    V := VectorSpace(sl);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(sl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(sl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;

intrinsic ASL(t :: Cat, n :: RngIntElt, K :: FldFin) -> Grp
{ASL(n, K) as a group of type t, which can be either GrpMat or GrpPerm};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    require n ge 2: "Argument 2 must be at least 2";

    if t eq GrpPerm then
	return ASL(n, K);
    end if;

    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    sl := SL(n, K);
    V := VectorSpace(sl);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(sl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(sl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;

intrinsic ASL(t :: Cat, V :: ModTupRng) -> Grp
{ASL(n, K) as a group of type t, which can be either GrpMat or GrpPerm, where
n is the dimension of V and K is its base field};

    require t eq GrpMat or t eq GrpPerm: "Argument 1 must be GrpMat or GrpPerm";

    K := BaseRing(V);
    n := Dimension(V);

    require Type(K) eq FldFin: "Argument 2 must have base ring a finite field";

    require n ge 2: "Argument 2 must have dimension at least 2";

    if t eq GrpPerm then
	return ASL(n, K);
    end if;

    gl1 := GL(n+1, K);
    last_col := Matrix(n+1, 1, [K | 0 : i in [1..n]] cat [K|1]);
    sl := SL(n, K);
    last_row := V!0;
    gens := [ gl1 | HorizontalJoin(VerticalJoin(m, last_row), last_col) :
		    m in Generators(sl) ];
    Append(~gens, gl1!HorizontalJoin(VerticalJoin(sl!1, V.1), last_col));
    G := sub<gl1 | gens>;
    return G;

end intrinsic;

intrinsic AffineGroup(G :: GrpMat[FldFin]) -> GrpPerm, SetIndx
{The semidirect product of G by the natural G-module.}

    d := Degree(G);
    q := #BaseRing(G);
    prime := IsPrime(q);
    require q^d lt 2^30 : "Degree of permutation group too large";
    if prime then
	vecs := Getvecs(G);
	if IsIrreducible(G) then
	    A := Semidir(G, vecs);
	    fl, ord := HasAttribute(G, "Order");
	    if fl then A`Order := ord * #vecs; end if;
	    return A, vecs;
	end if;
    else
	V := VectorSpace(G);
	vecs := {@ v : v in V @};
    end if;

    deg := #vecs;
    len := Ngens(G);
    Agens := [ Sym(deg) | 
	[Position(vecs, vecs[j] * G.i) : j in [1..deg]] : i in [1..len]
    ];
    K := BaseRing(G);
    V := VectorSpace(G);
    if prime then
	Kp := K;
	Gp := G;
    else
	Kp := PrimeField(K);
	Gp := WriteOverSmallerField(G, Kp);
    end if;
    _, phi := VectorSpace(V, Kp);
    M := GModule(Gp);
    S := sub<M|>;
    for v in vecs do
	v2 := phi(v);
	if M!v2 in S then continue; end if;
	Append(~Agens, [Position(vecs, vecs[j] + v) : j in [1..deg]]);
	S := sub<M | S, v2>;
	if S eq M then break; end if;
    end for;
    A := PermutationGroup<deg | Agens>;
    fl, ord := HasAttribute(G, "Order");
    if fl then A`Order := ord * deg; end if;
    return A , vecs;

end intrinsic;
