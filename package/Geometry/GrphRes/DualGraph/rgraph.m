freeze;
///////////////////////////////////////////////////////////////////////
// rgraph.m
//	Contents:
//		type/attributes
//		Print/IsCoercible functions
//		sensitive printing
//		attribute recovery
//		setting optional attributes
//		modifying attributes
//		creation from a newton polygon
//		equality of graphs
///////////////////////////////////////////////////////////////////////

declare type GrphRes;
declare attributes GrphRes:
    /* essential attributes */
    graph,
    labels,
    selfintersections,
    /* optional or calculated attributes */
    base_germ,
    base_space,
    base_blowup_contribution,
    multiplicities,
    canonical_class,
    galois_multiplicities,
    axis_multiplicities,
    transverse_intersections,
    projective_patch_maps,
    pre_patch_maps,
    base_points,
    neighbouring_germs;


///////////////////////////////////////////////////////////////////////
// printing

forward fix_print_labels;
intrinsic UpdateGraphLabels(G::GrphRes)
{Updates the vertex labels on the underlying graph of G}
    fix_print_labels(~G);
end intrinsic;

intrinsic Print(G::GrphRes,l::MonStgElt)
{}
    UpdateGraphLabels(G);
    print "The resolution graph on the",G`graph:Maximal;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// coercion

intrinsic IsCoercible(G::GrphRes,i::RngIntElt) -> BoolElt
{}
    v := ResolutionGraphVertex(G,i);
    return true,v;
end intrinsic;

///////////////////////////////////////////////////////////////////////
// creation

intrinsic MakeResolutionGraph(g::GrphDir,s::SeqEnum) -> GrphRes
{The resolution graph supported on g.
The list 'base' can contain a base germ and a base selfintersection
contribution;
the list L contains the following sequences of data associated to
the vertices of g as follows: s = selfintersections, germ pullback
multiplicities, canonical multiplicities, galois multiplicities,
t = transverse intersections, projective patch maps, birational pullback germs}
    G := MakeResolutionGraph(g,[* *],[* s,[],[],[],[],[],[] *]);
    return G;
end intrinsic;

intrinsic MakeResolutionGraph(g::GrphDir,s::SeqEnum,t::SeqEnum) -> GrphRes
{"} // "
    G := MakeResolutionGraph(g,[* *],[* s,[],[],[],t,[],[] *]);
    return G;
end intrinsic;

intrinsic MakeResolutionGraph(g::GrphDir,base::List,L::List) -> GrphRes
{"} // "
/* this is the primitive construtor for resolution graphs.
 * all error checking for label length and type is done here. */

    /* dig out data from the list */
    s := L[1];
    m := L[2];
    k := L[3];
    gal := L[4];
    ti := L[5];
    phi := L[6];
    germs := L[7];

    /* impose demands on additional data: the rigour varies from data to data */
    ng := #VertexSet(g);
    ns := #s;
    require ns eq ng or ns eq 0:
	"If selfintersections are specified they must correspond exactly to the vertices of g";
    nm := #m;
    require nm eq ng or nm eq 0:
	"If multiplicities are specified they must correspond exactly to the vertices of g";
    nk := #k;
    require nk eq ng or nk eq 0:
	"If canonical multiplicities are specified they must correspond exactly to the vertices of g";
    ni := #ti;
    require ni eq ng or ni eq 0:
	"If tranverse intersections are specified they must correspond exactly to the vertices of g";

    /* create the resolution graph: only attribute true values */
    G := New(GrphRes);
    G`graph := g;
    if ns gt 0 then
	G`selfintersections := s;
    end if;
    if nm gt 0 then
	G`multiplicities := m;
    end if;
    if nk gt 0 then
	G`canonical_class := k;
    end if;
    if ni gt 0 then
	G`transverse_intersections := ti;
    end if;
    G`galois_multiplicities := gal;
    G`projective_patch_maps := phi;
    G`neighbouring_germs := germs;
    if #base eq 2 then
	if IsGerm(Type(base[1])) then
	    G`base_germ := base[1];
	end if;
	if Type(base[2]) eq RngIntElt then
	    G`base_blowup_contribution := base[2];
	end if;
    end if;
    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Printing
///////////////////////////////////////////////////////////////////////

fix_print_labels := procedure(~G)
    graph := G`graph;
    DeleteLabels(VertexSet(graph));
    DeleteLabels(EdgeSet(graph));	// edge labels can appear by mistake
    vset := VertexSet(graph);
    ng := #vset;
    /* determine the type of labels that we ought to be seeing */
    siok := assigned G`selfintersections;
    multsok := assigned G`multiplicities;
    canok := assigned G`canonical_class;
    intok := assigned G`transverse_intersections;
    if siok then si := Selfintersections(G); end if;
    if multsok then mults := Multiplicities(G); end if;
    if canok then can := CanonicalClass(G); end if;
    if intok then int := TransverseIntersections(G); end if;
    if siok and multsok and canok and intok then
	labels := [ [ si[i],mults[i],can[i],int[i] ] : i in [1..ng] ];
    elif siok and multsok and intok then
	labels := [ [ si[i],mults[i],int[i] ] : i in [1..ng] ];
    elif siok and intok then
	labels := [ [ si[i],int[i] ] : i in [1..ng] ];
    elif siok then
	labels := [ [ si[i] ] : i in [1..ng] ];
    else
	labels := [ [] : i in [1..ng] ];
    end if;
    /* always assign new labels since the current ones could be outdated */
    vertices := [ vset.i : i in [1..ng] ];
    AssignLabels(vertices,labels);
end procedure;


///////////////////////////////////////////////////////////////////////
//		Recover essential attributes
///////////////////////////////////////////////////////////////////////

intrinsic UnderlyingGraph(G::GrphRes) -> GrphDir
{The underlying graph of G}
    return G`graph;
end intrinsic;

intrinsic Size(G::GrphRes) -> RngIntElt
{The number of vertices of G}
    return #VertexSet(G`graph);
end intrinsic;

intrinsic Selfintersections(G::GrphRes) -> SeqEnum
{The sequence of selfintersections of vertices of G}
    return G`selfintersections;
end intrinsic;

intrinsic Multiplicities(G::GrphRes) -> SeqEnum
{The multiplicities of the pullback of the base germ}
    if not assigned G`multiplicities then
	CalculateMultiplicities(~G);
    end if;
    return G`multiplicities;
end intrinsic;

intrinsic CanonicalClass(G::GrphRes) -> SeqEnum
{The multiplicities of the canonical class of the germ of a surface along G}
    if not assigned G`canonical_class then
	CalculateCanonicalClass(~G);
    end if;
    return G`canonical_class;
end intrinsic;

intrinsic AxisMultiplicities(G::GrphRes) -> SeqEnum
{The axis multiplicities of the nearby germs to G}
    if not assigned G`axis_multiplicities then
// THINK
	error "code gap";
    end if;
    return G`axis_multiplicities;
end intrinsic;

intrinsic GaloisMultiplicities(G::GrphRes) -> SeqEnum
{The galois multiplicities of the nearby germs to G}
    if not assigned G`galois_multiplicities then
// THINK
	error "code gap";
    end if;
    return G`galois_multiplicities;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Recover optional attributes
///////////////////////////////////////////////////////////////////////

intrinsic BaseGerm(G::GrphRes) -> Pt
{The germ used to create G, if assigned}
    require assigned G`base_germ:
	"G has no base germ assigned";
    return G`base_germ;
end intrinsic;

intrinsic BaseSpace(G::GrphRes) -> Sch
{The space on which coordinate transformations used in the creation of G take
place}
    if not assigned G`base_space then
	germ := BaseGerm(G);
	P := Ambient(ProjectiveRepresentative(germ));
	G`base_space := P;
    end if;
    return G`base_space;
end intrinsic;

intrinsic TransverseIntersections(G::GrphRes) -> SeqEnum
{The number of transverse intersections of the germ used to create G with the
nodes of G}
    if not assigned G`transverse_intersections then
	CalculateTransverseIntersections(~G);
    end if;
    return G`transverse_intersections;
end intrinsic;

intrinsic NeighbouringGerms(G::GrphRes) -> SeqEnum
{The sequence of neighbouring germs along G}
    require assigned G`neighbouring_germs:
// THINK
	"Algorithm for neighbouring germs missing";
    return G`neighbouring_germs;
end intrinsic;

/*
intrinsic ProjectivePatchMaps(G::GrphRes) -> SeqEnum
{The sequence of projectised maps from the patch at a vertex to the base germ}
// THINK: this is far too costly to ever compute.
error "Error --- ProjectivePatchMaps() removed";
    require assigned G`projective_patch_maps:
	"Algorithm for projective patch maps missing";
    return G`projective_patch_maps;
end intrinsic;
*/

intrinsic PrePatchMaps(G::GrphRes) -> SeqEnum
{Internal function}
    return G`pre_patch_maps;
end intrinsic;

intrinsic BaseBlowupContribution(G::GrphRes) -> RngIntElt
{Minus the number of blowups on the x-axis in the process of constructing G}
    if not assigned G`base_blowup_contribution then
// THINK
error "warning: temporary error in BBC(G)";
    end if;
    return G`base_blowup_contribution;
end intrinsic;

intrinsic GenusContribution(G::GrphRes) -> RngIntElt
{The number, often referred to as delta, which is the contribution to
the genus of a plane curve by a singularity having this resolution graph}
/* Notation is as follows:
 *	E 	the total exceptional locus corresponding to G
 *	C	the birational pullback of the curve germ
 *	kc	the degree of the relative canonical class on C
 * Then	    g = arithmetic_genus - \sum\genus_contributions.
 */
    CE := ExceptionalCurveIntersection(G);
    E2 := ExceptionalSelfIntersection(G);
    kc := CanonicalDegree(G);
    delta := Integers() ! ( 1/2*(kc - 2*CE - E2) );
    return delta;
end intrinsic;

intrinsic RootVertex(g::GrphRes) -> GrphResVert
{The root vertex of g with respect to the directions on its underlying graph}
    return g ! Index(Root(g`graph));
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Setting attributes
///////////////////////////////////////////////////////////////////////

intrinsic SetBaseGerm(~G::GrphRes,p::Pt)
{Nominate p as the base germ of G}
    G`base_germ := p;
end intrinsic;

intrinsic SetMultiplicities(~G::GrphRes,m::SeqEnum)
{Set the multiplicities of G to be the integers of the sequence m}
    require IsComplete(m):
	"m must be a complete sequence";
    require #m eq Size(G):
	"m has the wrong length";
    G`multiplicities := m;
end intrinsic;

intrinsic SetCanonicalClass(~G::GrphRes,c::SeqEnum)
{Set the canonical multiplicities of G to be the integers of the sequence c}
    require IsComplete(c):
	"c must be a complete sequence";
    require #c eq Size(G):
	"c has the wrong length";
    G`canonical_class := c;
end intrinsic;

intrinsic SetSelfintersections(~G::GrphRes,s::SeqEnum)
{Set the selfintersections of G to be the integers of the sequence s}
    require IsComplete(s):
	"s must be a complete sequence";
    require #s eq Size(G):
	"s has the wrong length";
    G`selfintersections := s;
end intrinsic;

intrinsic SetTransverseIntersections(~G::GrphRes,t::SeqEnum)
{Set the number of transverse intersections of G to be the integers of the
sequence t}
    require IsComplete(t):
	"t must be a complete sequence";
    require #t eq Size(G):
	"t has the wrong length";
    G`transverse_intersections := t;
end intrinsic;

intrinsic SetNeighbouringGerms(~G::GrphRes,s::SeqEnum)
{Set s to be the sequence of neighbouring germs along G}
    G`neighbouring_germs := s;
end intrinsic;

intrinsic SetProjectivePatchMaps(~G::GrphRes,s::SeqEnum)
{Set s to be the sequence of projective patch maps along G}
    G`projective_patch_maps := s;
end intrinsic;

intrinsic SetPrePatchMaps(~G::GrphRes,s::SeqEnum)
{Internal function}
    G`pre_patch_maps := s;
end intrinsic;

intrinsic SetGaloisMultiplicities(~G::GrphRes,s::SeqEnum)
{Set s to be the sequence of galois multipliticies along G}
    G`galois_multiplicities := s;
end intrinsic;

intrinsic SetAxisMultiplicities(~G::GrphRes,s::SeqEnum)
{Set s to be the sequence of axis multipliticies along G}
    G`axis_multiplicities := s;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Modifying attributes
// These are intended as internal functions on the assumption that all
// natural facilities for resolution graph modification are provided.
///////////////////////////////////////////////////////////////////////

intrinsic ModifyTransverseIntersection(~v::GrphResVert,n::RngIntElt)
{Add n to the number of transverse intersections at v}
    i := Index(v);
    G := ResolutionGraph(v);
    t := TransverseIntersections(G);
    t[i] +:= n;
    SetTransverseIntersections(~G,t);
end intrinsic;

intrinsic ModifySelfintersection(~v::GrphResVert,n::RngIntElt)
{Add n to the selfintersection of v}
    i := Index(v);
    G := ResolutionGraph(v);
    si := Selfintersections(G);
    si[i] +:= n;
    SetSelfintersections(~G,si);
end intrinsic;
    

///////////////////////////////////////////////////////////////////////
//		Creation from a newton polygon
///////////////////////////////////////////////////////////////////////

intrinsic MakeResolutionGraph(N::NwtnPgon) -> GrphRes
{The resolution graph corresponding to N}
    fan := ResolvedDualFan(N);
    Prune(~fan);
    Reversion(~fan);
    Prune(~fan);
    nf := #fan;
    graph := LinearGraph(nf);
    si := [ ray[3] : ray in fan ];
    G := MakeResolutionGraph(graph,si);
    return G;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Graph equality
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(G::GrphRes,H::GrphRes) -> BoolElt
{True iff G and H are the same graph}
    if G`graph ne H`graph then
	return false;
    end if;
    if G`selfintersections ne H`selfintersections then
	return false;
    end if;
    if assigned G`axis_multiplicities and assigned H`axis_multiplicities and G`axis_multiplicities ne H`axis_multiplicities then
	return false;
    end if;
    if assigned G`galois_multiplicities and assigned H`galois_multiplicities and G`galois_multiplicities ne H`galois_multiplicities then
	return false;
    end if;
    return true;
end intrinsic;

