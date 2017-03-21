freeze;

intrinsic OddGraph(n::RngIntElt) -> GrphUnd
{The n-th odd graph O_n};
    requirege n, 1;
    V := Subsets({1..2*n-1}, n-1);
    E := { {u,v} : u,v in V | IsDisjoint(u, v) };
    return StandardGraph(Graph< V | E >);
end intrinsic;

intrinsic TriangularGraph(n::RngIntElt) -> GrphUnd
{The triangular graph T_n (n > 1)};
    requirege n, 2;
    V := Subsets({1..n}, 2);
    E := { {u,v} : u,v in V | IsDisjoint(u, v) };
    return Complement(StandardGraph(Graph< V | E >));
end intrinsic;

intrinsic SquareLatticeGraph(n::RngIntElt) -> GrphUnd
{The n-th square lattice graph};
    requirege n, 1;
    return CartesianProduct(P, P) where P is CompleteGraph(n);
end intrinsic;

intrinsic PaleyGraph(n::RngIntElt) -> GrphUnd
{The Paley graph of n; n must be a prime power congruent to 1 mod 4};
    require n gt 1 and n mod 4 eq 1: "Argument must be a prime power congruent to 1 mod 4";
    require #Factorization(n) eq 1: "Argument must be a prime power congruent to1 mod 4";
    V := { x : x in GF(n) };
    E := { {u,v} : u,v in V | not IsSquare(u - v) };
    return StandardGraph(Graph< V | E >);
end intrinsic;

intrinsic PaleyTournament(n::RngIntElt) -> GrphDir
{The Paley tournament of n; n must be a prime power congruent to 3 mod 4};
    require n gt 1 and n mod 4 eq 3: "Argument must be a prime power congruent to 3 mod 4";
    require #Factorization(n) eq 1: "Argument must be a prime power congruent to3 mod 4";
    V := { x : x in GF(n) };
    E := { [u,v] : u,v in V | u ne v and IsSquare(v - u) };
    return StandardGraph(Digraph< V | E >);
end intrinsic;

intrinsic HadamardGraph(H::Mtrx : Labels := false) -> GrphUnd
{The graph of the the Hadamard matrix H};
    m := Nrows(H);
    n := Ncols(H);
    V := {1 .. 2*(m + n)};
    E := {};
    R1 := CoefficientRing(Parent(H))!1;
    for i := 0 to m-1 do 
	for j := 0 to n-1 do 
	    if H[i+1, j+1] eq R1 then
		Include(~E, {2*i + 1, 2*m + 2*j + 1});
		Include(~E, {2*i + 2, 2*m + 2*j + 2});
	    else
		require H[i+1, j+1] eq -R1: "Matrix entries must be 1 or -1";
		Include(~E, {2*i + 1, 2*m + 2*j + 2});
		Include(~E, {2*i + 2, 2*m + 2*j + 1});
	    end if;
	end for;
    end for;
    gr, vs, es := Graph< V | E >;
    if Labels then
	AssignLabels( 
	    vs, [i le 2*m select "row" else "col": i in V]
	);
    end if;
    return gr, vs, es;
end intrinsic;

intrinsic ClebschGraph() -> GrphUnd
{The Clebsch graph};
    S := { 1..5 };
    V := &join[ Subsets(S, 2*k) : k in [0..#S div 2]];
    E := { {u,v} : u,v in V | #(u sdiff v) eq 4 };
    return StandardGraph(Graph< V | E >);
end intrinsic;

intrinsic ShrikhandeGraph() -> GrphUnd
{The Shrikhande graph};
    return Switch(MaximumIndependentSet(SquareLatticeGraph(4)));
end intrinsic;

intrinsic ChangGraphs() -> []
{The sequence of the three Chang graphs};
    V := Subsets({1..8}, 2);
    E := { {u,v} : u,v in V | IsDisjoint(u, v) };
    T8 := Complement(Graph< V | E >);
    S := [
	    { {i, i + 1 } : i in [1..7 by 2] },
	    { {i, i mod 8 + 1} : i in [1..8] },
	    { {i, i mod 5 + 1} : i in [1..5] } join Subsets({ 6, 7, 8 }, 2)
	];
    VS := VertexSet(T8);
    SS := [ { VS!s : s in vs } : vs in S ];
    return [ Switch(s) : s in SS ];
end intrinsic;

intrinsic GewirtzGraph() -> GrphUnd
{The Gewirtz graph};
    P := {@ {1} join x: x in Subsets({2 .. 6}, 2) @};
    Q := {@ x: x in Class(A6, A6!(1,2)(3,4)) @} where A6 is Alt(6);
    Pinf := {{1, i + 1}: i in [1 .. #P]};
    PQ := {{i+1, j+1+#P}: i in [1 .. #P], j in [1 .. #Q] | P[i]^Q[j] eq P[i]};
    QQ := {{i+1+#P, j+1+#P}: i, j in [1 .. #Q] | Order(Q[i] * Q[j]) eq 4};
    return Graph<1 + #P + #Q | Pinf, PQ, QQ>;
end intrinsic;

intrinsic CayleyGraph(G::Grp : Labelled := true, Directed := true) -> Grph, GrphVertSet, GrphEdgeSet
{The Cayley graph of the group G as a directed graph with vertices labelled
by the group elements and edges labelled by group generators};
    if Type(G) eq GrpFP then
	/* Need to do this as GrpFP does not have element normal forms. */
	return SchreierGraph(G, sub<G|Id(G)> :
		Labelled := Labelled, Directed := Directed);
    end if;
    I := Transversal(G, sub<G|Id(G)>);
    S := Generators(G);
    graph := Directed select EmptyDigraph(#I) else EmptyGraph(#I);
    for u in [1..#I] do
	for y in S do
	    x := I[u];
	    v := Index(I, x*y);
	    if Labelled then
		AddEdge(~graph, u, v, y);
	    else
		AddEdge(~graph, u, v);
	    end if;
	end for;
    end for;
    if Labelled then
	AssignLabels(VertexSet(graph), IndexedSetToSequence(I));
    end if;
    return graph, VertexSet(graph), EdgeSet(graph);
end intrinsic;

intrinsic SchreierGraph(G::Grp, H::Grp : Labelled := true, Directed := true) -> Grph, GrphVertSet, GrphEdgeSet
{The Schreier graph for group G and subgroup H as a directed graph with
vertices labelled by coset representatives and edges labelled by group
generators};
    I,h := Transversal(G, H);
    S := Generators(G);
    graph := Directed select EmptyDigraph(#I) else EmptyGraph(#I);
    for u := 1 to #I do
	for y in S do
	    x := I[u];
	    v := Index(I, h(x*y));
	    if Labelled then
		AddEdge(~graph, u, v, y);
	    else
		AddEdge(~graph, u, v);
	    end if;
	end for;
    end for;
    if Labelled then
	AssignLabels(VertexSet(graph), IndexedSetToSequence(I));
    end if;
    return graph, VertexSet(graph), EdgeSet(graph);
end intrinsic;
