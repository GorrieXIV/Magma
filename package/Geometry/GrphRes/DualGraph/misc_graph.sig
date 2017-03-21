174,1
S,VertexPath,A sequence of vertices comprising the adjacent vertices on the path from u to v. G is assumed to be a directed graph,0,2,0,0,0,0,0,0,0,309,,0,0,309,,82,-38,-38,-38,-38,-38
S,BranchVertexPath,The sequence of branching vertices --- those of valency at least 3 --- on the path from u to v; u and v are included as first and last elements of the sequence,0,2,0,0,0,0,0,0,0,309,,0,0,309,,82,-38,-38,-38,-38,-38
S,IsRootedTree,"True if and only if G is a tree and for some vertex v, given any vertex w there exists a directed path from v to w. In this case, also return v as a second value",0,1,0,0,0,0,0,0,0,57,,36,309,-38,-38,-38,-38
S,RootSide,The vertex which is rootside of v in a known rooted tree or v itself if it has no in-neighbours,0,1,0,0,0,0,0,0,0,309,,309,-38,-38,-38,-38,-38
S,Root,Root of directed tree,0,1,0,0,0,0,0,0,0,57,,309,-38,-38,-38,-38,-38
S,LinearGraph,The line graph on n vertices,0,1,0,0,0,0,0,0,0,148,,57,-38,-38,-38,-38,-38
S,OutEdges,The sequence of edges pointing away from v,0,1,0,0,0,0,0,0,0,309,,82,-38,-38,-38,-38,-38
S,InEdge,The unique edge directed in to v in a directed tree,0,1,0,0,0,0,0,0,0,309,,79,-38,-38,-38,-38,-38
S,IsRoot,True iff v is the root of a known rooted tree,0,1,0,0,0,0,0,0,0,309,,36,-38,-38,-38,-38,-38
