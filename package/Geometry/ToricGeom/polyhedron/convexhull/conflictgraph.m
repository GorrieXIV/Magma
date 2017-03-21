freeze;

/////////////////////////////////////////////////////////////////////////
// conflictgraph.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 26463 $
// $Date: 2010-05-05 14:23:03 +1000 (Wed, 05 May 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Implements a conflict graph, used when calculating the convex hull
// of a sequence of points.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// We define a conflict graph via a list:
//    [* points, facets, graph *]
// where 'points' is the sequence of points under consideration;
//       'facets' is the sequence of currently constructed facets,
//               represented by the corresponding half-space;
//       'graph' is a matrix where a 1 in the (i,j) entry indicates that
//               facets[j] is visible from points[i].
/////////////////////////////////////////////////////////////////////////

import "../../lattice/hyperplane.m": point_in_halfspace;

/////////////////////////////////////////////////////////////////////////
// Creation function
/////////////////////////////////////////////////////////////////////////

// Returns the conflict graph for the given point/facet data.
// Note: 'points' and 'facets' should be sequences, NOT sets.
function cg_build(points,facets)
    M:=ZeroMatrix(Integers(),#points,#facets);
    for i in [1..#points] do
        for j in [1..#facets] do
            if not point_in_halfspace(facets[j],points[i]) then
                M[i][j]:=1;
            end if;
        end for;
    end for;
    return [* points, facets, M *];
end function;

/////////////////////////////////////////////////////////////////////////
// Access functions
/////////////////////////////////////////////////////////////////////////

// Returns the set of all facets visible from the given point.
function cg_visible_facets(G,v)
    i:=Index(G[1],v);
    assert i ne 0;
    return {Universe(G[2]) | G[2][j] : j in [1..#G[2]] | G[3][i][j] ne 0};
end function;

// If the conflict graph contains any points, then returns true along with a
// point from the conflict graph point set and the set of all facets visible
// from that point. Otherwise returns false.
// Note: Does NOT remove the point from the conflict graph.
function cg_next_point(G)
    for v in G[1] do
        conflict:=cg_visible_facets(G,v);
        if #conflict gt 0 then return true,v,conflict; end if;
    end for;
    return false,_,_;
end function;

/////////////////////////////////////////////////////////////////////////
// Modification functions
/////////////////////////////////////////////////////////////////////////

// Adds the given facet to the conflict graph.
procedure cg_add_facet(~G,f)
    // Is there anything to do?
    if Index(G[2],f) eq 0 then
        // Add the facet
        Append(~G[2],f);
        M:=RowSequence(Transpose(G[3])) cat [[Integers()|0 : i in [1..#G[1]]]];
        G[3]:=Transpose(Matrix(Integers(),M));
        // Update the graph
        j:=#G[2];
        for i in [1..#G[1]] do
            if not point_in_halfspace(f,G[1][i]) then
                G[3][i][j]:=1;
            end if;
        end for;
    end if;
end procedure;

// Deletes the given point from the conflict graph.
procedure cg_delete_point(~G,v)
    i:=Index(G[1],v);
    assert i ne 0;
    Remove(~G[1],i);
    RemoveRow(~G[3],i);
end procedure;

// Deletes the given set (or sequence) of facets from the conflict graph.
procedure cg_delete_facets(~G,fs)
    idxs:={Integers() | Index(G[2],f) : f in fs};
    assert not 0 in idxs;
    for j in Reverse(Sort(SetToSequence(idxs))) do
        Remove(~G[2],j);
        RemoveColumn(~G[3],j);
    end for;
end procedure;
