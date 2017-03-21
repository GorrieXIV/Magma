freeze;

///////////////////////////////////////////////////////////////////////
// rvertex.m
//	Contents:
//		type/attributes
//		Print/IsCoercible
//		vertex attribute retrieval
//		graph attribute retrieval at a vertex
//		testing vertices
//		components of a graph containing a vertex
///////////////////////////////////////////////////////////////////////

declare type GrphResVert;
declare attributes GrphResVert:
    resolution_graph,	// the resolution graph containing vertex v
    vertex,		// the vx underlying v
    index;		// the index of v


intrinsic Print(v::GrphResVert,l::MonStgElt)
{}
    print Index(v);
end intrinsic;

intrinsic IsCoercible(v::GrphResVert,x::.) -> BoolElt
{}
    return false,"Illegal coercion";
end intrinsic;

intrinsic ResolutionGraphVertex(G::GrphRes,i::RngIntElt) -> GrphResVert
{The ith vertex of the underlying graph of G}
    v := New(GrphResVert);
    g := UnderlyingGraph(G);
    Vg := VertexSet(g);
    v`resolution_graph := G;
    require i ge 1 and i le #Vg:
	"Illegal coercion --- i is not in the range of the vertices of G";
    v`vertex := Vg!i;
    v`index := i;
    return v;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Attribute retrieval
///////////////////////////////////////////////////////////////////////

intrinsic ResolutionGraph(v::GrphResVert) -> GrphRes
{The resolution graph of which v is a vertex}
    return v`resolution_graph;
end intrinsic;

intrinsic Vertex(v::GrphResVert) -> GrphVert
{The vertex v in the underlying graph of its resolution graph}
    return v`vertex;
end intrinsic;

intrinsic Index(v::GrphResVert) -> RngIntElt
{The index of v in its resolution graph}
    return v`index;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Characteristic label retrieval
///////////////////////////////////////////////////////////////////////

intrinsic Selfintersection(v::GrphResVert) -> RngIntElt
{The selfintersection of v}
    G := ResolutionGraph(v);
    S := Selfintersections(G);
    i := Index(v);
    si := S[i];
    return si;
end intrinsic;

intrinsic Multiplicity(v::GrphResVert) -> RngIntElt
{The multiplicity of v in the total pullback of the defining germ along its
resolution graph}
    G := ResolutionGraph(v);
    M := Multiplicities(G);
    i := Index(v);
    mult := M[i];
    return mult;
end intrinsic;

intrinsic CanonicalMultiplicity(v::GrphResVert) -> RngIntElt
{The multiplicity of v in the canonical class of the germ of a surface along
its resolution graph}
    G := ResolutionGraph(v);
    K := CanonicalClass(G);
    i := Index(v);
    can := K[i];
    return can;
end intrinsic;

intrinsic TransverseIntersections(v::GrphResVert) -> RngIntElt
{The number of transverse intersections of the resolved germ with v}
    G := ResolutionGraph(v);
    A := TransverseIntersections(G);
    i := Index(v);
    places := A[i];
    return places;
end intrinsic;

intrinsic Places(v::GrphResVert) -> RngIntElt
{The number of transverse intersections of the resolved germ with v}
    return TransverseIntersections(v);
end intrinsic;

intrinsic ProjectivePatchMap(v::GrphResVert) -> MapSch
{The map from a patch on v to the base space of the defining germ}
    G := ResolutionGraph(v);
    pp := PrePatchMaps(G);
    i := Index(v);
    require IsDefined(pp,i):
	"Required projective patch map is not calculated";
    factors := pp[i];
    map := factors[1];
    for j in [2..#factors] do
	// THINK map := Composition(map,factors[j]: CheckDefined:=false);
	map := factors[j] * map;
    end for;
    return map;
end intrinsic;

intrinsic PatchGerms(v::GrphResVert) -> MapSch
{The germs that lie on a patch of v during the resolution process}
    G := ResolutionGraph(v);
    gs := PatchGerms(G);
    i := Index(v);
    germs := gs[i];
    return germs;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Testing vertices
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(v::GrphResVert,w::GrphResVert) -> BoolElt
{True iff v and w are the same resolution graph vertex}
    v1 := Vertex(v);
    w1 := Vertex(w);
    bool := v1 eq w1;
    return bool;
end intrinsic;

intrinsic IsVertex(G::GrphRes,v::GrphResVert) -> BoolElt
{True iff v is a vertex of G}
    Gv := ResolutionGraph(v);
    bool := Gv cmpeq G;
    return bool;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Components of graphs
///////////////////////////////////////////////////////////////////////

intrinsic Component(v::GrphResVert) -> GrphRes
{The connected component of the resolution graph containing v}
// The associated data of G preserved is self- and transverse intersections
    i := Index(v);
    G := ResolutionGraph(v);
    g := UnderlyingGraph(UnderlyingGraph(G));
    comps := Components(g);
    for c in comps do
	if i in c then
	    comp := c;
	    break c;
	end if;
    end for;
    cverts := [ G ! Index(vg) : vg in comp ];
    G1 := Subgraph(G,cverts);
    return G1;
end intrinsic;

