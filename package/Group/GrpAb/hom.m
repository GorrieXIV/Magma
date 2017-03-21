// Computation of homomorphisms from one finite abelian group to another
// AKS, 03/08/98.

freeze;

Z := IntegerRing();

intrinsic Hom(G::GrpAb, H::GrpAb) -> GrpAb, Map
{An abelian group A isomorphic to Hom(G, H) (where G and H are finite
abelian groups), together with the transfer map t which, given an
element of A, returns the corresponding group homomorphism from G to H};

    require IsFinite(G): "Argument 1 is not finite";
    require IsFinite(H): "Argument 2 is not finite";

    Gr := [Eltseq(LHS(r)): r in Relations(G)];
    Hr := [Eltseq(LHS(r)): r in Relations(H)];
    Gn := #Gr;
    Hn := #Hr;

    d := Gn * Hn;
    R := RMatrixSpace(Z, d, 2 * d) ! 0;
    for g := 0 to Gn - 1 do
	for h := 0 to Hn - 1 do
	    r := g * Hn + h + 1;
	    for j := 0 to Gn - 1 do 
		R[r][j * Hn + h + 1] := Gr[g + 1][j + 1];
	    end for;
	    for j := 0 to Hn - 1 do 
		R[r][d + g * Hn + j + 1] := Hr[j + 1][h + 1];
	    end for;
	end for;
    end for;

    N := KernelMatrix(Transpose(R));

    Gd := #Eltseq(G.0);
    Hd := #Eltseq(H.0);
    M := RMatrixSpace(Z, Gd, Hd);

    L := [M | ];
    R := [M | ];

    for i := 1 to Nrows(N) do
	X := M ! Eltseq(N[i])[1 .. d];
	Append(~L, X);
    end for;

    for r in Hr do
	for i := 1 to Gd do
	    X := M ! 0;
	    for j := 1 to Hd do
		X[i][j] := r[j];
	    end for;
	    Append(~R, X);
	end for;
    end for;

    V := RSpace(Z, Gd * Hd);
    h := hom<M -> V | Basis(V)>;
    K := sub<V | [h(X): X in R]>;
    W := sub<V | [h(X): X in L]> + K;

    Q, f := quo<W | K>;
    S := Moduli(Q);
    A := AbelianGroup(S);
    L := [Q.i @@ f @@ h: i in [1 .. #S]];

    function sum(Q)
	if #Q eq 0 then
	    return 0;
	end if;
	s := Q[1];
	for i := 2 to #Q do
	    s := s + Q[i];
	end for;
	return s;
    end function;

    t := map<A -> PowerStructure(Map) |
	x :->
	    hom<G -> H |
		[sum([a[i][j]*H.j: j in [1 .. Hd]]): i in [1 .. Gd]]
	    > where a is (Q!Eltseq(x)) @@ f @@ h
    >;
    return A, t;
end intrinsic;

intrinsic Hom(G::GrpPC, H::GrpPC) -> GrpAb, Map
{An abelian group A isomorphic to Hom(G, H) (where G and H are finite
abelian PC groups), together with the transfer map t which, given an
element of A, returns the corresponding group homomorphism from G to H};

    require IsAbelian(G): "Argument 1 is not abelian";
    require IsAbelian(H): "Argument 2 is not abelian";

    GA, Gf := AbelianGroup(G);
    HA, Hf := AbelianGroup(H);

    A, t := Hom(GA, HA);
    tt := map<A -> PowerStructure(Map) |
	x :->
	    hom<G -> H | [h(Gf(G.i))@@Hf: i in [1..NPCgens(G)]]> where
	    h is t(x)
    >;

    return A, tt;
end intrinsic;

intrinsic HomGenerators(G::GrpAb, H::GrpAb) -> []
{A sequence of (Z-module) generators of the set of all homomorphims
from the finite abelian group G to the finite abelian group H}

    require IsFinite(G): "Argument 1 is not finite";
    require IsFinite(H): "Argument 2 is not finite";

    A, t := Hom(G, H);
    return [t(A.i): i in [1 .. Ngens(A)]];
end intrinsic;

/* 
//Will be shadowed by an intrinsic with the same signature in 
//Group/GrpPC/central/central.m, so commented out here 
//-- DR 2 nov 2010.
intrinsic HomGenerators(G::GrpPC, H::GrpPC) -> []
{A sequence of (Z-module) generators of the set of all homomorphims
from the finite abelian PC group G to the finite abelian PC group H}

    require IsAbelian(G): "Argument 1 is not abelian";
    require IsAbelian(H): "Argument 2 is not abelian";

    A, t := Hom(G, H);
    return [t(A.i): i in [1 .. Ngens(A)]];
end intrinsic;
*/

intrinsic Homomorphisms(G::GrpAb, H::GrpAb) -> []
{A sequence of all homomorphims from the finite abelian group G to the
finite abelian group H}

    require IsFinite(G): "Argument 1 is not finite";
    require IsFinite(H): "Argument 2 is not finite";

    A, t := Hom(G, H);
    return [t(a): a in A];
end intrinsic;

intrinsic Homomorphisms(G::GrpPC, H::GrpPC) -> []
{A sequence of all homomorphims from the finite abelian PC group G to the
finite abelian PC group H}

    require IsAbelian(G): "Argument 1 is not abelian";
    require IsAbelian(H): "Argument 2 is not abelian";

    A, t := Hom(G, H);
    return [t(a): a in A];
end intrinsic;

intrinsic AllHomomorphisms(G::GrpAb, H::GrpAb) -> []
{OBSOLETE: Use Homomorphisms};
    return Homomorphisms(G, H);
end intrinsic;

intrinsic AllHomomorphisms(G::GrpPC, H::GrpPC) -> []
{OBSOLETE: Use Homomorphisms};
    return Homomorphisms(G, H);
end intrinsic;
