freeze;

/////////////////////////////////////////////////////////////////////////
// simplicial.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 40873 $
// $Date: 2012-11-13 03:12:43 +1100 (Tue, 13 Nov 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the lattice points in an integral polytope that contains
// the origin in its strict interior.
/////////////////////////////////////////////////////////////////////////

import "../../lattice/lattice.m": lattice_get_Zlattice_of_dim;
import "../convexhull/sublattice.m": fp_emb_map;
import "../convexhull/convexhull.m": fp_get_pullback_vertices;
import "../triangulation.m": calculate_triangulation_of_boundary;

/////////////////////////////////////////////////////////////////////////
// Point functions
/////////////////////////////////////////////////////////////////////////

// Given an integral polytope P containing the origin in its strict interior,
// returns the points in P. If necessary, a triangulation of the boundary of P
// will be computed.
function points_in_simplicialcomplex(P)
    // Move to the equivalent maximum dimensional polytope
    verts:=fp_get_pullback_vertices(P);
    trans,Lemb:=fp_emb_map(P);
    // Create the initial set of points
    pts:=SequenceToSet(Vertices(P));
    Include(~pts,Zero(Ambient(P)));
    // Fetch the ZZ-module to work with
    d:=Dimension(P);
    R:=lattice_get_Zlattice_of_dim(d);
    // Start working through the cones of the boundary triangulation
    calculate_triangulation_of_boundary(P);
    for F in P`fp_boundary_triang do
        // Is this cone smooth? If so, we can ignore it.
        M:=Matrix(Rationals(),[verts[i] : i in F]);
        r:=Abs(Determinant(M));
        if r ne 1 then
            // Create the mapping matrix
            Minv:=r * M^-1;
            M /:= r;
            // Calculate the generators
            quolat,proj:=quo<R | [Eltseq(verts[i]) : i in F]>;
            gens:=[Eltseq(Vector(Rationals(),Eltseq(g)) * Minv) :
                             g in Generators(TorsionSubmodule(quolat)) @@ proj];
            ChangeUniverse(~gens,PowerSequence(Integers()));
            // Create the fundamental domain
            A:=AbelianGroup([Integers() | r : i in [1..d]]);
            G,emb:=sub< A | [&+[g[i] * A.i : i in [1..d]] : g in gens] >;
            // Extract the points with height <= 1
            for g in G do
                pt:=Eltseq(emb(g));
                if &+pt le r then
                    // Pull back the points to the ambient of P
                    u:=Eltseq(Vector(Rationals(),pt) * M);
                    Include(~pts,Lemb(u) + trans);
                end if;
            end for;
        end if;
    end for;
    // Return the points
    return pts;
end function;
