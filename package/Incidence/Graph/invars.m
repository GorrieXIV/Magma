freeze;

intrinsic NumberOfVertices(G::Grph) -> RngIntElt
{}
    return Order(G);
end intrinsic;

intrinsic NumberOfVertices(G::GrphMult) -> RngIntElt
{The number of vertices in the graph G}
    return Order(G);
end intrinsic;

intrinsic NumberOfEdges(G::Grph) -> RngIntElt
{}
    return Size(G);
end intrinsic;

intrinsic NumberOfEdges(G::GrphMult) -> RngIntElt
{The number of edges in the graph G}
    return Size(G);
end intrinsic;
