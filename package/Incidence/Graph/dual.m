freeze;

/* Creating the dual graph of a planar graph.
 * Dan Roozemond, June 2011
 */

intrinsic PlanarDual(G::GrphUnd) -> GrphUnd
{ Construct the dual G' of a planar graph G. The numbering of the vertices of G' 
  corresponds to the order of the faces as returned by Faces(G). }
	require IsPlanar(G) : "G must be planar";
	
	EG := EdgeSet(G);
	fc := [ f : f in Faces(G) | Universe(f) cmpeq EG ];
	fc := [ { {InitialVertex(e), TerminalVertex(e)} : e in f } : f in fc ];
	n := #fc;
	edges_dual := { {i,j} : i,j in [1..n] | (i lt j) and #(fc[i] meet fc[j]) ne 0 };
	
	Gp := Graph<n | edges_dual>;
	return Gp;
end intrinsic;
