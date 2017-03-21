freeze;
///////////////////////////////////////////////////////////////////////
// misc_graph.m
//	miscellaneous graphy functions for directed graphs
///////////////////////////////////////////////////////////////////////

intrinsic VertexPath(u::GrphVert,v::GrphVert) -> SeqEnum
{A sequence of vertices comprising the adjacent vertices on the path
from u to v. G is assumed to be a directed graph}
    VG := Parent(u);
    require Parent(v) eq VG:
        "u and v lie in different graphs.";
    /* VP will be the vertexpath */
    VP := [ VG | ];
    VP[1] := u;
    nvp := 1;
    done := u eq v;
    /* main loop: keep finding the next point until you reach v
     * by using DistancePartition: only one neighbour 'improves' this. */
    while not done do
        endvx := VP[nvp];
        nvp +:= 1;
        DP := DistancePartition(endvx);
        ndp := #DP;
        if v in DP[ndp] then
            /* v is rootside of endvx so take a step backwards */
            nextvx := RootSide(endvx);
            VP[nvp] := nextvx;
            done := nextvx eq v;
            continue;
        end if;
        /* v is somewhere in front so look for the right forward branch */
        outvxs := DP[2];
        for vx in outvxs do
            if Distance(vx,v) ge 0 then
                nextvx := vx;
                VP[nvp] := nextvx;
                done := nextvx eq v;
                break;
            else
                continue;
            end if;
	require false:
            "No succesive vertex, illegal graph";
        end for;
    end while;
    return VP;
end intrinsic;

intrinsic BranchVertexPath(u::GrphVert,v::GrphVert) -> SeqEnum
{The sequence of branching vertices --- those of valency at least 3 --- on the
path from u to v; u and v are included as first and last elements of the
sequence}
/* this might be better done as a parameter value calculation in VertexPath. */
    vp := VertexPath(u,v);
    Prune(~vp);
    bvp := [u];
    for v in vp do
	if Degree(v) ge 3 then
	    Append(~bvp,v);
	end if;
    end for;
    Append(~bvp,v);
    return bvp;
end intrinsic;

intrinsic IsRootedTree(G::GrphDir) -> BoolElt,GrphVert
{True if and only if G is a tree and for some vertex v, given any vertex w
there exists a directed path from v to w. In this case, also return v as a
second value}
    if not IsTree(G) then
	return false,_;
    end if;
    /* The last entry in DistancePartition(v) is the list of vertices not
    reachable from v by a directed path. I compress the natural loop into
    a magma 'there exists' statement */
    VG := VertexSet(G);
    bool := exists(root){ w : w in VG | #DP[#DP] eq 0 where DP := DistancePartition(w) };
    if bool then
	return bool,root;
    else
	return false,_;
    end if;
end intrinsic;

intrinsic RootSide(v::GrphVert) -> GrphVert
{The vertex which is rootside of v in a known rooted tree or v itself if it
has no in-neighbours}
    inset := InNeighbours(v);
    require #inset le 1:
	"The directed graph is not directed as a tree";
    if #inset eq 1 then
	return Representative(inset);
    else
	return v;
    end if;
end intrinsic;

intrinsic Root(G::GrphDir) -> GrphVert
    {Root of directed tree}
    require not IsNull(G):
        "This is the null digraph";
    /* Pick a vertex and work back along arrows until you stop */
    V := VertexSet(G);
    v := V!1;
    done := false;
    while not done do
	rootside := RootSide(v);
	done := rootside eq v;
	v := rootside;
    end while;
    return v;
end intrinsic;

intrinsic LinearGraph(n::RngIntElt) -> GrphDir
{The line graph on n vertices}
    G := Digraph< n | >;
    for i in [1..n-1] do
	AddEdge(~G,i,i+1);
    end for;
    return G;
end intrinsic;

intrinsic OutEdges(v::GrphVert) -> SeqEnum
{The sequence of edges pointing away from v}
    G := ParentGraph(v);
    E := EdgeSet(G);
    outeds := [ E | ];
    outvxs := OutNeighbours(v);
    if Type(G) eq GrphMultDir then
      for w in outvxs do
        outeds cat:= Edges(v, w);
      end for;
      return outeds;
    end if;
    for w in outvxs do
        edge := E![v,w];
        Include(~outeds,edge);
    end for;
    return outeds;
end intrinsic;
 
intrinsic InEdge(v::GrphVert) -> GrphEdge
{The unique edge directed in to v in a directed tree}
    inset := InNeighbours(v);
    require #inset eq 1:
	"Argument does not have a unique in-edge";
    E := EdgeSet(ParentGraph(v));
    w := Representative(inset);
    edge := E![w,v];
    return edge;
end intrinsic;

intrinsic IsRoot(v::GrphVert) -> BoolElt
{True iff v is the root of a known rooted tree}
    G := ParentGraph(v);
    root := Root(G);
    return v eq root;
end intrinsic;

