freeze;
///////////////////////////////////////////////////////////////////////
// sgraph.m
//	Contents:
//		type/attributes
//		Print/IsCoercible
//		printing
//		attribute recovery
//		making splice diagrams from resolution diagrams
//		splice diagrams of curve singularities
///////////////////////////////////////////////////////////////////////

declare type GrphSpl;
declare attributes GrphSpl:
    /* essential attributes */
    graph,
    edge_labels,
    vertex_labels,
    arrows,
    /* optional or calculated attributes */
    corresponding_graph,
    corresponding_vertices,
    linking_numbers,
    canonical_class,
    galois_multiplicities,
    vertices,
    is_regular,
    arrow_weights;


intrinsic Print(S::GrphSpl,l::MonStgElt)
{}
    if assigned S`edge_labels then
	elabels := EdgeLabels(S);
	gs := UnderlyingGraph(S);
	DeleteLabels(EdgeSet(gs));
	eset := EdgeSet(gs);
	nes := #eset;
	edges := [ eset.i : i in [1..nes] ];
	DeleteLabels(eset);
	AssignLabels(edges,elabels);
    end if;
    if assigned S`vertex_labels then
	vlabels := VertexLabels(S);
	gs := UnderlyingGraph(S);
	DeleteLabels(VertexSet(gs));
	vset := VertexSet(gs);
	nvs := #vset;
	vertices := [ vset.i : i in [1..nvs] ];
	DeleteLabels(vset);
	AssignLabels(vertices,vlabels);
    end if;
    graph := UnderlyingGraph(S);
    print "The splice diagram on the",graph:Maximal;
end intrinsic;

intrinsic IsCoercible(S::GrphSpl,i::.) -> BoolElt
{}
    if Type(i) eq RngIntElt then
	ns := Size(S);
	if i le 0 or i gt ns then
	    return false,"Integer argument is not in the range of the vertices of splice diagram";
	end if;
	v := SpliceDiagramVertex(S,i);
	return true,v;
    elif Type(i) eq GrphVert then
	g := UnderlyingGraph(S);
	require ParentGraph(i) eq g:
	    "Vertex argument does not lie on splice diagram";
	return true,S!Index(i);
    else
	return false,"Illegal coercion";
    end if;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Creation
///////////////////////////////////////////////////////////////////////

intrinsic MakeSpliceDiagram(g::GrphDir,e::SeqEnum,a::SeqEnum) -> GrphSpl
{The splice diagram on graph g with edge labels e and arrows a}
    E := EdgeSet(g);
    V := VertexSet(g);
    require #e eq #E:
	"Wrong number of edge labels";
    require #a eq #V:
	"Wrong number of arrow entries";
    S := New(GrphSpl);
    S`graph := g;
    S`edge_labels := e;
    S`vertex_labels := a;
    S`arrows := a;
    return S;
end intrinsic;

intrinsic MakeSpliceDiagram(e::[SeqEnum],l::[SeqEnum],a::[RngIntElt])
-> GrphSpl
{The splice diagram with edges corresponding to the elements of e (sequences of
vertex numbers), which have edge labels given by the elements of l; and with 
arrows (all of weight 1) corresponding to a (the ith element of a
becomes the number of arrows of the ith vertex)}
    require not(IsEmpty(a)) : "Arrow sequence is empty";
    require #e eq #l : "Number of edges does not equal number of edge labels"; 
    require Max(&cat(e)) le #a : 
	    "Too few arrows given indices of end vertices of edges";
    edgeset := SequenceToSet(e);
    require #edgeset eq #e : "Repeated edges occur in edge sequence";
    D := Digraph<#a| edgeset>;
    require IsRootedTree(D) : "Graph described is not a rooted tree";
    E := Edges(D);
    lposns := {@ Index(E, E ! edge) : edge in e @};
	//lposns[n] is the appropriate position for l[n]
    newl := [ l[Index(lposns, i)] : i in [1..#lposns]];
    return MakeSpliceDiagram(D, newl, a);
end intrinsic;

forward resolution_to_splice;
intrinsic SpliceDiagram(G::GrphRes: Reduced:=1,L:=0,K:=0) -> GrphSpl
{The reduced splice diagram corresponding to the resolution graph G}
    require Type(Reduced) eq RngIntElt and Type(L) eq RngIntElt and Type(K) eq RngIntElt:
	"Parameters must be integers";
    if Reduced eq 1 then param := "Reduced"; else param := ""; end if;
    S := resolution_to_splice(G,param);
    if L eq 1 then
	mults := Multiplicities(G);
	cv := CorrespondingVertices(S);
	links := [ mults[i] : i in cv ];
	// or maybe the linking numbers calculation for a splice diag is better?
	S`linking_numbers := links;
    end if;
    if K eq 1 then
	can := CanonicalClass(G);
	cv := CorrespondingVertices(S);
	k := [ can[i] : i in cv ];
	S`canonical_class := k;
    end if;
    return S;
end intrinsic;

intrinsic SpliceDiagram(G::GrphRes,v::GrphResVert: Reduced:=1,L:=0,K:=0) -> GrphSpl
{The reduced splice diagram corresponding to the graph G but without
reduction at v}
    require Type(Reduced) eq RngIntElt and Type(L) eq RngIntElt and Type(K) eq RngIntElt:
	"Parameter 'Reduced' must be an integer";
    ind := Index(v);
    /* add some arrows to prevent v from being contracted */
    ti := TransverseIntersections(G);
    ti[ind] +:= 3;
    SetTransverseIntersections(~G,ti);
    /* calculate the splice diagram as usual, but delete the extra arrows */
    S := SpliceDiagram(G: Reduced:=Reduced,L:=L,K:=K);
    arrows := Arrows(S);
    corr_inds := {@ i : i in CorrespondingVertices(S) @};
    new_ind := Position(corr_inds,ind);
    arrows[new_ind] -:= 3;
    SetArrows(~S,arrows);
    /* finally remove the arrows from v as a vertex of G */
    ti[ind] -:= 3;
    SetTransverseIntersections(~G,ti);
    return S;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Attribute recovery
///////////////////////////////////////////////////////////////////////

intrinsic UnderlyingGraph(S::GrphSpl) -> GrphDir
{The underlying graph of S}
    return S`graph;
end intrinsic;

intrinsic Size(S::GrphSpl) -> RngIntElt
{The number of vertices of S}
    gs := UnderlyingGraph(S);
    vs := VertexSet(gs);
    ns := #vs;
    return ns;
end intrinsic;

intrinsic EdgeLabels(S::GrphSpl) -> SeqEnum
{The labels on the edges of S}
    return S`edge_labels;
end intrinsic;

intrinsic VertexLabels(S::GrphSpl) -> SeqEnum
{The labels on the vertices of S, by default the arrows of S but also
linking or canonical class information if calculated}
    require assigned S`vertex_labels:
	"Print data not yet assigned";
    return S`vertex_labels;
end intrinsic;

intrinsic CorrespondingResolutionGraph(S::GrphSpl) -> SeqEnum
{The resolution graph that corresponds to S}
    require assigned S`corresponding_graph:
	"THINK: not yet automated";
    return S`corresponding_graph;
end intrinsic;

intrinsic CorrespondingVertices(S::GrphSpl) -> SeqEnum
{The vertices of the resolution graph of S corresponding to the vertices of S}
    require assigned S`corresponding_vertices:
	"THINK: not yet automated";
    return S`corresponding_vertices;
end intrinsic;

intrinsic LinkingNumbers(S::GrphSpl) -> SeqEnum
{The linking numbers at vertices of S}
    if not assigned S`linking_numbers then
	links := [ TotalLinking(v) : v in Vertices(S) ];
	S`linking_numbers := links;
    end if;
    return S`linking_numbers;
end intrinsic;

intrinsic CanonicalClass(S::GrphSpl) -> SeqEnum
{The canonical multiplicities at vertices of S of corresponding vertices in the
resolution graph}
    if not assigned S`canonical_class then
	// THINK:
	error "algorithm missing";
    end if;
    return S`canonical_class;
end intrinsic;

intrinsic GaloisMultiplicities(S::GrphSpl) -> SeqEnum
{The galois multiplities at vertices of S of corresponding vertices in the
resolution graph}
    return S`galois_multiplicities;
end intrinsic;

intrinsic Arrows(S::GrphSpl) -> SeqEnum
{The arrows at vertices of the splice diagram}
    return S`arrows;
end intrinsic;

intrinsic ArrowWeights(S::GrphSpl) -> SeqEnum
{The weights of the arrows at vertices of the splice diagram}
    if not assigned S`arrow_weights then
        // unused at the moment so give them all weight 1
	S`arrow_weights := [ [1 : i in [1..arrnum]] : arrnum in Arrows(S)];
    end if;
    return S`arrow_weights;
end intrinsic;

intrinsic Vertices(S::GrphSpl) -> SeqEnum
{The vertices of S}
    if not assigned S`vertices then
	n := Size(S);
	verts := [ S ! i : i in [1..n] ];
	S`vertices := verts;
    end if;
    return S`vertices;
end intrinsic;

///////////////////////////////////////////////////////////////////////
//		Setting attributes
///////////////////////////////////////////////////////////////////////

intrinsic SetArrows(~S::GrphSpl,a::SeqEnum)
{Set the numbers arrows on vertices of S to be the entries of a}
    ns := Size(S);
    require #a eq ns:
	"a has the wrong length";
    require IsComplete(a):
	"a must be complete";
    S`arrows := a;
    S`vertex_labels := a;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Splice from resolution
///////////////////////////////////////////////////////////////////////

forward graph_reduction;
forward splice_edge_labels;
resolution_to_splice := function(G,param)
    /* preliminaries */
    g := UnderlyingGraph(G);
    a := TransverseIntersections(G);

    /* first reduce the resolution graph */
    if param eq "Reduced" then
	g1,ov,a1 := graph_reduction(g,a);
    else
	g1 := g; ov := [1..Size(G)]; a1 := a;
    end if;
	// g1 = red'd graph, a1 = arrs on g1, ov = vxs of g corr to vxs of g1

    /* second calculate the edge labels of the splice diagram */
    e := splice_edge_labels(g1,ov,G);

    /* third create the splice diagram */
    S := MakeSpliceDiagram(g1,e,a1);
    S`corresponding_graph := G;
    S`corresponding_vertices := ov;

    return S;
end function;


///////////////////////////////////////////////////////////////////////
//		Associated functions
///////////////////////////////////////////////////////////////////////

splice_edge_labels := function(g1,ov,G)
/* Label the edges of g1 by [a,b], the two subdeterminants of G:
 *	a := OutDet(outgoing edge _of G_ at first vx of e)
 *	b := InDet(incoming edge _of G_ at second vx of e)
 * The calculation is carried out on g = UnderlyingGraph(G) and 
 * g1 = splicereduction(G).
 * Moreover, it is assumed that the root vertex has not been contracted
 * so that paths between vertices of g1 when lifted to g comprise edges
 * all pointing in the same direction.
 * DRAW A PICTURE OF G TO SEE WHAT IS GOING ON.
 *
 * Compare with Neumann, "Irregular Links at Infinity of Complex Affine
 * Plane Curves" Quart. J. Math. (to appear 1999ish).
 */

    g := UnderlyingGraph(G);
    elabels := [];
    E := EdgeSet(g);
    V := VertexSet(g);
    E1 := EdgeSet(g1);
    V1 := VertexSet(g1);
    for e in E1 do
        /* find v0, v1, the endpoints of e as they were in g */
        i0 := ov[Index(EndVertices(e)[1])];
        i1 := ov[Index(EndVertices(e)[2])];
	v0 := V ! i0;
	v1 := V ! i1;

        /* look for outgedge the edge of g starting at v0 pointing at v1 */
        for vg in OutNeighbours(v0) do
            DP := DistancePartition(vg);
            infinitedist := DP[#DP];
            if v1 notin infinitedist then
                v0out := vg;
                break vg;
            else
                continue;
            end if;
            error "No good neighbour, illegal graph";
        end for;
	i0out := Index(v0out);
        outgedge := E ! [i0,i0out];
        /* it's easier to find ingedge, the last edge of G on path v0 to v1 */
        v1in := Representative(InNeighbours(v1)); /* which is unique */
	i1in := Index(v1in);
        ingedge := E ! [i1in,i1];

        /* the subdeterminant at these edges provide the splice edge labels */
	Ginpieces := Disconnect(G!i1in,G!i1);
	Gin := Component(Ginpieces!i0);
        indet := (-1)^Size(Gin)*Determinant(Gin);

	Goutpieces := Disconnect(G!i0,G!i0out);
	Gout := Component(Goutpieces!i1);
        outdet := (-1)^Size(Gout)*Determinant(Gout);
        Append(~elabels,[Integers() ! outdet, Integers() ! indet]);
    end for;
    return elabels;
end function;

graph_reduction := function(g,a)
/* remove all valency 2 vertices from g; the second return value is the list
 * of vertices of g corresponding to those of the reduced graph.
 * valency 2 occurs either by
 *	Degree(vi)==2, narrows==0 or
 *	Degree(vi)==1, narrows==1 or
 *	Degree(vi)==0, narrows==2.
 * Cases treated separately below in the central if-elif-else.
 * The arguments are:
 *	g is the underlying graph of a splice diagram;
 *	a is a sequence listing the number of arrows at corr'ing vxs of g. */
    vg := VertexSet(g);
    ng := #vg;
    original_vertices := [1..ng];
    done := false;
    while not done do
	vprintf Splice: "graph reduction, arrows: %o\n",a;
        done := true;
        for i in [1..ng] do
            vi := vg ! i;
            na := a[i];
	    vprintf Splice: "  at vertex %o: arrows = %o; adjacents = %o\n",i,na,Degree(vi);
            valency := Degree(vi) + na;
            if valency eq 2 then
                done := false;
		in_neigh := InNeighbours(vi);	// either 0 or 1 of these
		if #in_neigh eq 0 then
		    // this is the odd case arising from using directed graphs
		    out_neigh := OutNeighbours(vi);
		    if #out_neigh eq 2 then
			out_seq := SetToSequence(out_neigh);
			v0 := out_seq[1];
			v1 := out_seq[2];
			AddEdge(~g,Index(v0),Index(v1)); // direction irrelevant
			RemoveVertex(~g,i);
			Remove(~original_vertices,i);
			Remove(~a,i);
			vg := VertexSet(g);
			ng -:= 1;
			break i;
		    elif #out_neigh eq 1 then // glue the arrow onto the next vx
			v0 := Representative(out_neigh);
			RemoveVertex(~g,i);
			Remove(~original_vertices,i);
			number_of_deleted_arrows := a[i];
			Remove(~a,i);
			/* put any deleted arrows on to v0 */
			a[Index(v0)] +:= number_of_deleted_arrows;
			vg := VertexSet(g);
			ng -:= 1;
			break i;
		    else	// no neighbours at all so done
			done := true;
			break i;
		    end if;
		else		// there is a unique InNeighbour, the good case
		    // this is the main section
		    if na eq 0 then
			v0 := Representative(in_neigh);
			v1 := Representative(OutNeighbours(vi)); // also unique
			AddEdge(~g,Index(v0),Index(v1));
			RemoveVertex(~g,i);
			Remove(~original_vertices,i);
			Remove(~a,i);
			vg := VertexSet(g);
			ng -:= 1;
			break i;
		    elif na eq 1 then
			v0 := Representative(in_neigh);
			RemoveVertex(~g,i);
			Remove(~original_vertices,i);
			number_of_deleted_arrows := a[i];
			Remove(~a,i);
			/* put any deleted arrows on to v0 */
			a[Index(v0)] +:= number_of_deleted_arrows;
			vg := VertexSet(g);
			ng -:= 1;
			break i;
		    else
			done := true;
			break i;
		    end if;
		end if;
            end if;
        end for;
    end while;
    return g,original_vertices,a;
end function;


///////////////////////////////////////////////////////////////////////
//		Splice diagrams of singularities
///////////////////////////////////////////////////////////////////////

intrinsic SpliceDiagram(C::Crv,p::Pt) -> GrphSpl
{The splice diagram of the singularity of C at p}
    require p in C(BaseRing(C)):
	"Second argument must be a rational point on the first";
    require not IsNonsingular(C,p):
	"Second argument must be a singular point on the first";
    G := ResolutionGraph(C,p);
    return SpliceDiagram(G);
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Equality
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(S::GrphSpl,T::GrphSpl) -> BoolElt
{True iff S and T are the same graph}
    return S cmpeq T;
end intrinsic;

