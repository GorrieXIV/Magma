174,1
A,TorPol,8,amb_fp_generators,amb_ng,amb_supporting_cones,amb_is_lattice,amb_are_vertices,amb_num_facets,amb_facet_idxs,amb_facets
S,Vertices,The sequence of vertices of the polyhedron P,0,1,0,0,0,0,0,0,0,TorPol,,82,-38,-38,-38,-38,-38
S,NumberOfVertices,The number of vertices of the polyhedron P,0,1,0,0,0,0,0,0,0,TorPol,,148,-38,-38,-38,-38,-38
S,Facets,The sequence of facets of the polyhedron P,0,1,0,0,0,0,0,0,0,TorPol,,82,-38,-38,-38,-38,-38
S,FacetIndices,A sequence of sets describing the facets of the polytope P. The j-th set gives the indices of the vertices of P which define the j-th facet of P,0,1,0,0,0,0,0,0,0,TorPol,,82,-38,-38,-38,-38,-38
S,NumberOfFacets,The number of facets of the polyhedron P,0,1,0,0,0,0,0,0,0,TorPol,,148,-38,-38,-38,-38,-38
S,VertexEdgeIncidenceMatrix,"The vertex-edge incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th vertex is contained in the j-th edge)",0,1,0,0,0,0,0,0,0,TorPol,,190,-38,-38,-38,-38,-38
S,EdgeFacetIncidenceMatrix,"The edge-facet incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th edge is contained in the j-th facet)",0,1,0,0,0,0,0,0,0,TorPol,,190,-38,-38,-38,-38,-38
S,VertexFacetIncidenceMatrix,"The vertex-facet incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th vertex is contained in the j-th facet)",0,1,0,0,0,0,0,0,0,TorPol,,190,-38,-38,-38,-38,-38
S,VertexFacetHeightMatrix,"The vertex-facet height matrix of the polyhedron P (where the i,j-th entry is equal to the height of the i-th vertex over the j-th facet)",0,1,0,0,0,0,0,0,0,TorPol,,177,-38,-38,-38,-38,-38
S,Inequalities,"The defining inequalities of the polyhedron P. These are given as a sequence of pairs <v,h>, where the first element v lies in the dual to the ambient toric lattice containing P and the second element h is an integer, such that v * u >= h is a supporting half-space of P. Also gives an integer k such that the first k inequalities correspond to the facets of P, and the remaining inequalities cut out the subspace containing P",0,1,0,0,0,0,0,0,0,TorPol,,82,148,-38,-38,-38,-38
S,SupportingCone,"The cone C such that C + v is a supporting cone of the polyhedron P, where v is a vertex of P",0,2,0,0,0,0,0,0,0,TorLatElt,,0,0,TorPol,,TorCon,-38,-38,-38,-38,-38
S,IsSupportingHyperplane,,0,3,0,0,0,0,0,0,0,TorPol,,0,0,148,,0,0,TorLatElt,,36,148,-38,-38,-38,-38
S,IsSupportingHyperplane,"True iff the hyperplane defined by v * u = h is a supporting hyperplane of the polyhedron P. If so, also gives the sign o such the hyperplane is a support of P (i.e. o in {-1,0,+1} such that Sign(v * u - h) is either 0 or o for all u in P). If P is contained within the hyperplane, then o will be 0",0,3,0,0,0,0,0,0,0,TorPol,,0,0,267,,0,0,TorLatElt,,36,148,-38,-38,-38,-38
S,in,True iff the point Q lies in the interior of the polyhedron P,0,2,0,0,0,0,0,0,0,TorPol,,0,0,TorLatElt,,36,-38,-38,-38,-38,-38
S,IsInInterior,True iff the point Q lies strictly in the relative interior of the polyhedron P,0,2,0,0,0,0,0,0,0,TorPol,,0,0,TorLatElt,,36,-38,-38,-38,-38,-38
S,IsOnBoundary,True iff the point Q lies on the relative boundary of the polyhedron P,0,2,0,0,0,0,0,0,0,TorPol,,0,0,TorLatElt,,36,-38,-38,-38,-38,-38
