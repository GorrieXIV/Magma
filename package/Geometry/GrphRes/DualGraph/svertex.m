freeze;
///////////////////////////////////////////////////////////////////////
// svertex.m
//	Contents:
//		type/attributes
//		Print/IsCoercible
//		testing vertices
///////////////////////////////////////////////////////////////////////

declare type GrphSplVert;
declare attributes GrphSplVert:
    splice_diagram,
    vertex,
    index,
    underlying_vertex,
    arrows,
    total_linking;


intrinsic Print(v::GrphSplVert,l::MonStgElt)
{}
    print Index(v);
end intrinsic;

intrinsic IsCoercible(v::GrphSplVert,x::.) -> BoolElt
{}
    return false,"Illegal coercion";
end intrinsic;

intrinsic SpliceDiagramVertex(S::GrphSpl,i::RngIntElt) -> GrphSplVert
{The ith vertex of the underlying graph of S}
    v := New(GrphSplVert);
    gs := UnderlyingGraph(S);
    vs := VertexSet(gs);
    nvs := #vs;
    require i ge 1 and i le nvs:
	"Illegal coercion --- i is not in the range of the vertices of S";
    v`vertex := vs ! i;
    v`index := i;
    v`splice_diagram := S;
    return v;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Attribute retrieval
///////////////////////////////////////////////////////////////////////

intrinsic SpliceDiagram(v::GrphSplVert) -> GrphSpl
{The splice diagram of which v is a vertex}
    return v`splice_diagram;
end intrinsic;

intrinsic Vertex(v::GrphSplVert) -> GrphVert
{The vertex v in the underlying graph of its splice diagram}
    return v`vertex;
end intrinsic;

intrinsic Index(v::GrphSplVert) -> RngIntElt
{The index of v in its splice diagram}
    return v`index;
end intrinsic;

intrinsic UnderlyingVertex(v::GrphSplVert) -> GrphVert
{The vertex corresponding to v in the graph underlying the splice diagram}
    if not assigned v`underlying_vertex then
	S := SpliceDiagram(v);
	G := UnderlyingGraph(S);
	VG := VertexSet(G);
	i := Index(v);
	vund := VG ! i;
	v`underlying_vertex := vund;
    end if;
    return v`underlying_vertex;
end intrinsic;

intrinsic Arrows(v::GrphSplVert) -> RngIntElt
{The number of arrows at v}
    if not assigned v`arrows then
	S := SpliceDiagram(v);
	a := Arrows(S);
	i := Index(v);
	v`arrows := a[i];
    end if;
    return v`arrows;
end intrinsic;

intrinsic VertexLabel(v::GrphSplVert) -> RngIntElt
{The number of arrows at v}
    return Arrows(v);
end intrinsic;

intrinsic EdgeLabel(u::GrphSplVert,v::GrphSplVert) -> SeqEnum
{The sequence of near and far labels on the edge joining u and v}
    S := SpliceDiagram(u);
    require SpliceDiagram(v) eq S:
        "Arguments lie in different splice diagrams";
    u0 := UnderlyingVertex(u);
    v0 := UnderlyingVertex(v);
    require EndVertices(InEdge(v0))[1] eq u0:
        "There is no edge from the first argument to the second";
    E := Edges(UnderlyingGraph(S));
    edge_index := Index(E,E![Index(u),Index(v)]);
    return EdgeLabels(S)[edge_index];
end intrinsic;

intrinsic 'eq'(u::GrphSplVert,v::GrphSplVert) -> BoolElt
{True iff u and v have the same index in a common splice diagram}
    Su := SpliceDiagram(u);
    Sv := SpliceDiagram(v);
    if not Su eq Sv then
	return false;
    else
	return Index(u) eq Index(v);
    end if;
end intrinsic;

