freeze;

///////////////////////////////////////////////////////////////////////
// modify.m
//	Contents:
//		performing modifications to graphs
//		calculating canonical and pullback mults for resolution graphs
//		calc transverse intersections from selfints and mults
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//		Graph surgery
///////////////////////////////////////////////////////////////////////

intrinsic Connect(v::GrphResVert,w::GrphResVert) -> GrphRes
{Connect the resolution graphs containing v and w together by an edge
from v to w}
    /* preliminaries */
    G := ResolutionGraph(v);
    H := ResolutionGraph(w);
    g := UnderlyingGraph(G);
    h := UnderlyingGraph(H);
    vv := Vertex(v);
    ww := Vertex(w);
    /* glue the graphs together with an extra edge */
    gluestart := Index(vv);
    glueend := #VertexSet(g) + Index(ww);
    k := Union(g,h);
    AddEdge(~k,gluestart,glueend);
    /* build the new resolution graph with its selfintersections */
    si := Selfintersections(G) cat Selfintersections(H);
    K := MakeResolutionGraph(k,si);
    /* recover numerical data that had already been calculated */
    if assigned G`multiplicities and assigned H`multiplicities then
	mults := Multiplicities(G) cat Multiplicities(H);
	SetMultiplicities(~K,mults);
    end if;
    if assigned G`canonical_class and assigned H`canonical_class then
	can := CanonicalClass(G) cat CanonicalClass(H);
	SetCanonicalClass(~K,can);
    end if;
    if assigned G`transverse_intersections and
      assigned H`transverse_intersections then
	ti := TransverseIntersections(G) cat TransverseIntersections(H);
	SetTransverseIntersections(~K,ti);
    end if;
    return K;
end intrinsic;

intrinsic Disconnect(v::GrphResVert,w::GrphResVert) -> GrphRes
{Remove the edge of the resolution graph containing both u and w by cutting the
edge between them. The resulting graph may well have more than one component}
// The associated data of G that is preserved is selfintersections and
// transverse intersections.
    /* preliminaries */
    G := ResolutionGraph(v);
    g := UnderlyingGraph(G);
    s := Selfintersections(G);
    t := TransverseIntersections(G);
    /* error checks */
    require  ResolutionGraph(w) eq G:
	"Arguments must lie in the same resolution graph";
    /* remove that edge */
    i := Index(v);
    j := Index(w);
    RemoveEdge(~g,i,j);
    /* make a new resolution graph */
    G1 := MakeResolutionGraph(g,s,t);
    return G1;
end intrinsic;

intrinsic AddEdge(G::GrphRes,i::RngIntElt,j::RngIntElt) -> GrphRes
{The resolution graph G with an edge between the i-th and j-th vertices of G
added}
    /* preliminaries */
    g := UnderlyingGraph(G);
    s := Selfintersections(G);
    t := TransverseIntersections(G);
    /* error checks */
    require Max(i, j) le Size(G) : 
        "Vertex indices provided are greater than the size of the graph";
    /* add the edge */
    AddEdge(~g, i, j);
    /* make a new resolution graph */
    G1 := MakeResolutionGraph(g, s, t);
    return G1;
end intrinsic;

intrinsic AddEdges(G::GrphRes,E::[SeqEnum]) -> GrphRes
{The resolution graph G with the edges specified in E added}
    /* preliminaries */
    g := UnderlyingGraph(G);
    s := Selfintersections(G);
    t := TransverseIntersections(G);
    /* error checks */
    require Max(&cat(E)) le Size(G) : 
        "Vertex indices provided are greater than the size of the graph";
    /* add the edges */
    AddEdges(~g, E);
    /* make a new resolution graph */
    G1 := MakeResolutionGraph(g, s, t);
    return G1;
end intrinsic;

intrinsic Subgraph(G::GrphRes,V::[GrphResVert]) -> GrphRes
{The subgraph of G on the vertices of V}
// The associated data of G preserved is self- and transverse intersections
    require #V ne 0:
	"A graph must have at least one vertex";
    require IsVertex(G,V[1]):
	"The vertices of V do not belong to G";
    /* build the new graph with its selfintersections alone */
    vertices := { Vertex(v) : v in V};
    preindices := { Index(v) : v in V };
    indices := [ i : i in [1..Size(G)] | i in preindices ];
    // important to get the index list in the correct order.
    // using indices := [ Index(v) : v in V ]; is wrong.
    g := UnderlyingGraph(G);
    s := Selfintersections(G);
    t := TransverseIntersections(G);
    g1 := sub< g | vertices >;
    s1 := [ s[i] : i in indices ];
    t1 := [ t[i] : i in indices ];
    G1 := MakeResolutionGraph(g1,s1,t1);
    return G1;
end intrinsic;

intrinsic RemoveVertex(~G::GrphRes,i::RngIntElt)
{Remove the i-th vertex from G}
    RemoveVertex(~G`graph,i);
    if #G`selfintersections ge i then
        Remove(~G`selfintersections,i);
    end if;
    if assigned G`transverse_intersections and #G`transverse_intersections ge i
then
        Remove(~G`transverse_intersections,i);
    end if;
    if assigned G`multiplicities and #G`multiplicities ge i then
        Remove(~G`multiplicities,i);
    end if;
    if assigned G`canonical_class and #G`canonical_class ge i then
        Remove(~G`canonical_class,i);
    end if;
    if assigned G`galois_multiplicities and #G`galois_multiplicities ge i then
        Remove(~G`galois_multiplicities,i);
    end if;
    if assigned G`neighbouring_germs and #G`neighbouring_germs ge i then
        Remove(~G`neighbouring_germs,i);
    end if;
    if assigned G`projective_patch_maps and #G`projective_patch_maps ge i then
        Remove(~G`projective_patch_maps,i);
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Canonical class
///////////////////////////////////////////////////////////////////////

intrinsic CalculateCanonicalClass(~G::GrphRes)
{Calculate the canonical class on the exceptional curves corresponding to G}
// this uses the selfintersections at the vertices.
    /* preliminaries */
    g := UnderlyingGraph(G);
    VG := VertexSet(g);
    n := #VG;
    W := VectorSpace(Rationals(),n);
    R := MatrixAlgebra(Rationals(),n);
    /* use the genus formula to give a system of eqns for K.
     * ie for each excl curve E, 0 - 2 = KE + E^2. */
    if n gt 1 then
	M := CartanMatrix(G);
	si := Selfintersections(G);
	sa := [ -2 - s : s in si ];
	a := W!sa;
	k := Solution(M,a);
	/* convert the solution to a sequence */
	sk := ElementToSequence(k);
    elif n eq 1 then
	/* there has only been one blowup so the canonical class mult is 1 */
	sk := [ Rationals() | 1 ];
    else
	/* there were no blowups at all */
	sk := [ Rationals() | ];
    end if;
    /* set the canonical class */
    G`canonical_class := sk;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Multiplicities
///////////////////////////////////////////////////////////////////////

intrinsic CalculateMultiplicities(~G::GrphRes)
{Calculate the multiplicities of the pullback of the germ used to create G}
// this uses the selfintersections and transverse intersections to find
// a 1-dimensional solution space for the multiplicities vector.
// then it uses the canonical class to identify the first exceptional curve
// knowing that the multiplicity there is equal to that of the singularity
// used to create the graph.
// if no singularity was used the solution calculated so far is used.
// THINK: stupidity --- this requires the can class to find first excl curve.

    // This uses the fact that f^*(C).E = 0 for all exceptional curves.
    // It needs G`selfintersections and G`transverse_intersections set.

    // make and solve linear equations for the multiplicities
    M := CartanMatrix(G);
    ti := TransverseIntersections(G);
    n := Size(G);
    V := VectorSpace(Rationals(),n);
    a := V ! ti;
    mults := Solution(M,-a);

    // convert the solution to a sequence
    smults := ElementToSequence(mults);
    if assigned G`base_germ then
	// the solution is only correct up to a multiple: use the multiplicity
	// of the base germ to correct this
// THINK: what's going on here when splicing at infinity?
	m := Multiplicity(BaseGerm(G));
	c := CanonicalClass(G);
	for i in [1..n] do
	    if c[i] eq 1 then
		index := i;
		break i;
	    end if;
	end for;
        factor := (m/smults[index]);
        smults := [ Integers() | factor*sm : sm in smults ];
    end if;
    // set the multiplicities
    G`multiplicities := smults;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Transverse intersections
///////////////////////////////////////////////////////////////////////

intrinsic CalculateTransverseIntersections(~G::GrphRes)
{Calculate the transverse intersections of G}
// this uses the selfintersections and multiplicities of vertices.
    /* make and solve linear equations for the multiplicities */
    M := CartanMatrix(G);
    m := Multiplicities(G);
    n := Size(G);
    V := VectorSpace(Rationals(),n);
    a := V ! m;
    ti := Solution(M^-1,-a);
    /* convert the solution to a sequence */
    sti := ElementToSequence(ti);
    /* set the multiplicities */
    G`transverse_intersections := sti;
end intrinsic;


