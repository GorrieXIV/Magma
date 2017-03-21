freeze;

/////////////////////////////////////////////////////////////////////////
// dim2.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38140 $
// $Date: 2012-04-13 00:18:58 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating lattice points in lattice polygons.
// NOTE: These functions really do require that P is integral.
/////////////////////////////////////////////////////////////////////////

import "../faces/support.m": amb_facet_indices;
import "../convexhull/convexhull.m": fp_get_pullback_vertices, fp_facet_indices;

/////////////////////////////////////////////////////////////////////////
// Local functions for dimension 2.
/////////////////////////////////////////////////////////////////////////

// Returns the number of points in the integral case.
function dim_2_number_of_points(P)
    return Volume(P) - NumberOfInteriorPoints(P) + 2;
end function;

// Returns the boundary points in the integral case.
function dim_2_boundary_points(P)
    V:=Vertices(P);
    pts:=V;
    for edge in amb_facet_indices(P) do
        idx:=SetToSequence(edge);
        u:=V[idx[1]] - V[idx[2]];
        k:=GCD(Eltseq(u));
        if k gt 1 then
            u /:= k;
            pts cat:= [Universe(V) | i * u + V[idx[2]] : i in [1..k-1]];
        end if;
    end for;
    return SequenceToSet(pts);
end function;

// Returns the number boundary points in the integral case.
function dim_2_number_of_boundary_points(P)
    V:=fp_get_pullback_vertices(P);
    num:=#V;
    for edge in fp_facet_indices(P) do
        idx:=SetToSequence(edge);
        num +:= GCD(Eltseq(V[idx[1]] - V[idx[2]])) - 1;
    end for;
    return num;
end function;

// Returns the number of interior points in the integral case.
function dim_2_number_of_interior_points(P)
    return Integers() ! ((Volume(P) - NumberOfBoundaryPoints(P) + 2) / 2);
end function;
