freeze;
///////////////////////////////////////////////////////////////////////
// linking.m
//	Contents:
//		edge determinants and reduction
//		routines to calculate linking numbers in splice diagrams
//		calculating the off-path splice weights
//		other splice diagram calculations
///////////////////////////////////////////////////////////////////////


///////////////////////////////////////////////////////////////////////
//		Edge determinants
///////////////////////////////////////////////////////////////////////

intrinsic EdgeDeterminant(u::GrphSplVert,v::GrphSplVert) -> RngIntElt
{The edge determinant at the edge joining u to v}
    S := SpliceDiagram(u);
    require SpliceDiagram(v) eq S:
	"Arguments lie in different splice diagrams";
    VP,wp := VertexPath(u,v);
    innerwt := &*EdgeLabel(u,v);
    outerwt := &*wp;
    return innerwt - outerwt;
end intrinsic;

intrinsic Valency(u::GrphSplVert) -> RngIntElt
{The valency of u}
    uu := UnderlyingVertex(u);
    return Degree(uu) + Arrows(u);
end intrinsic;

intrinsic RootVertex(S::GrphSpl) -> GrphSplVert
{The root vertex of S given the directions on the edges of its underlying graph}
    return S ! Index(Root(UnderlyingGraph(S)));
end intrinsic;

intrinsic IsReduced(S::GrphSpl: Rooted := false) -> BoolElt
{True iff S has no nodes of valency 2 and no weight 1 leaves}
// ignore root vertex if Rooted eq true
    V := Vertices(S);
    done := false;
    // simply check each vertex in turn for valency 2 or valency 1 and weight 1
    if Rooted then
	root := RootVertex(S);
    end if;
    for v in V do

	na := Arrows(v);
	val := Valency(v);
	if na + val eq 2 then
	    if Rooted then
		if v eq root then
		    continue;
		end if;
	    end if;
	    return false;
	end if;
	if val eq 1 then
	    if Rooted then
		if v eq root then
		    continue;
		end if;
	    end if;
	    uv := UnderlyingVertex(v);
	    inns := InNeighbours(uv);
	    if #inns eq 1 then
		uw := Representative(inns);
		w := S ! Index(uw);
		wt := EdgeLabel(w,v)[1];
	    else
		uw := Representative(OutNeighbours(uv));
		w := S ! Index(uw);
		wt := EdgeLabel(v,w)[2];
	    end if;
	    if wt eq 1 then
		return false;
	    end if;
	end if;
    end for;
    return true;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Linking numbers
///////////////////////////////////////////////////////////////////////

intrinsic Linking(u::GrphSplVert,v::GrphSplVert) -> RngIntElt
{The linking number of the (virtual) link at u with the link at v}
    _,links := VertexPath(u,v);
    linking := 1;
    for i in links do
	linking *:= i;
    end for;
    return linking;
end intrinsic;

intrinsic TotalLinking(u::GrphSplVert) -> RngIntElt
{The total linking of u with its splice diagram}
    if not assigned u`total_linking then
	S := SpliceDiagram(u);
	VS := Vertices(S);
	total := 0;
	for v in VS do
	    narrows := Arrows(v);
	    if narrows eq 0 then
		continue;
	    end if;
	    locallink := Linking(u,v);
	    total +:= narrows*locallink;
	end for;
	u`total_linking := total;
    end if;
    return u`total_linking;
end intrinsic;

intrinsic IsRegular(S::GrphSpl) -> BoolElt
{True iff S is a regular splice diagram}
    if not assigned S`is_regular then
	if assigned S`linking_numbers then
	    S`is_regular := &and[ l ge 0 : l in LinkingNumbers(S) ];
	else
	    // don't need to calculate all linking numbers if result is false
	    bool := true;
	    VS := Vertices(S);
	    for v in VS do;
		tl := TotalLinking(v);
		if tl lt 0 then
		    bool := false;
		    break v;
		end if;
	    end for;
	    S`is_regular := bool;
	end if;
    end if;
    return S`is_regular;
end intrinsic;

intrinsic Degree(S::GrphSpl) -> RngIntElt
{The total linking of the root vertex in S}
    return TotalLinking(RootVertex(S));
end intrinsic;


///////////////////////////////////////////////////////////////////////
//		Vertex paths and splice weights
///////////////////////////////////////////////////////////////////////

intrinsic VertexPath(u::GrphSplVert,v::GrphSplVert) -> SeqEnum,SeqEnum
{A sequence of vertices comprising the adjacent vertices on the path
from u to v. The second return value is a sequence of products of those
edge weights not lying on the path at the corresponding vertex}
    S := SpliceDiagram(u);
    require SpliceDiagram(v) eq S:
	"Arguments lie on different splice diagrams";
    root := RootVertex(S);
    uund := UnderlyingVertex(u);
    vund := UnderlyingVertex(v);
    /* VP will be the vertexpath, sp the off-path edge-weight products */
    VP := VertexPath(uund,vund);
    nvp := #VP;

    /* sp will be the relevant splice weights along VP */
    sp := [];

    /* now to find the splice weight contribution sw at each edge on the path */
    for i in [1..nvp] do
	sw := 1;
	if i ne 1 then
	    u := VP[i-1];
	end if;
	v := VP[i];
	if i ne nvp then
	    w := VP[i+1];
	end if;
	// so locally the path is u-v-w, possibly minus one of the ends
	pathedges := 0;	// how many of the path edges at v i've already seen
	outeds := OutEdges(v);
	/* run through outedges including any edge weights not lying on path */
	for e in outeds do
	    far := EndVertices(e)[2];
	    edgeliesonpath := (i ne 1 and far eq u) or (i ne nvp and far eq w);
	    if edgeliesonpath then
		pathedges +:= 1;
		continue;
	    end if;
	    // edge e doesn't lie on the path so multiply sw by its near weight
	    label := EdgeLabel(S!v,S!far);
	    sw *:= label[1];
	end for;
	/* I include the inedgeweight if I've already seen two path edges
	going out, or I'm at an end of the path and have seen one; I'm careful
	not to try this if at the root vertex since it doesn't have in inedge */
	notroot := S!v ne root;
	seenenough := (pathedges eq 2) or (pathedges eq 1 and (i eq 1 or i eq nvp)) or (nvp eq 1);
	if seenenough and notroot then
	    // multipy sw by far weight of incoming edge
	    label := EdgeLabel(S!Representative(InNeighbours(v)),S!v);
	    sw *:= label[2];
	end if;
	sp[i] := sw;
    end for;

    return VP,sp;
end intrinsic;


///////////////////////////////////////////////////////////////////////
//			Other calculations
///////////////////////////////////////////////////////////////////////

intrinsic EulerCharacteristic(s::GrphSpl) -> RngIntElt
{The euler characteristic of a generic fibre of s}
    return &+[ (2 - Valency(v))*TotalLinking(v) : v in Vertices(s) ];
end intrinsic;

intrinsic HasIrregularFibres(s::GrphSpl) -> RngIntElt
{True iff s has a vertex with zero total linking number}
    for v in Vertices(s) do
	if TotalLinking(v) eq 0 then
	    return true;
	end if;
    end for;
    return false;
end intrinsic;

