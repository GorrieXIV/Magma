freeze;

/////////////////////////////////////////////////////////////////////////
// neighbourlygraph.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Implements a neighbourly graph, used to calculate the vertices of
// a convex hull.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// We define a neighbourly graph via a list:
//    [* points, facets, graph *]
// where 'points' is the sequence of points generating the convex hull;
//       'facets' is the sequence of facets, represented by the corresponding
//               supporting half-space;
//       'graph' is a matrix where a 1 in the (i,j) entry indicates that
//               facets[j] contains points[i].
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": maximal_sets_by_inclusion;
import "../../lattice/hyperplane.m": is_hyperplane, is_supporting_hyperplane, exists_point_not_in_hyperplane, to_halfspace, is_halfspace, is_supporting_halfspace, hyperplane_to_halfspace, halfspace_image, halfspace_image_pullback, halfspace_translation, halfspace_negation, halfspace_change_ambient;

/////////////////////////////////////////////////////////////////////////
// Access functions
/////////////////////////////////////////////////////////////////////////

// Returns the ambient of the points in the neighbourly graph.
function ng_ambient(G)
    try
        ambient:=Universe(G[1]);
    catch e
        if #G[2] gt 0 then
            ambient:=Dual(Parent(G[2][1][1][1]));
        else
            error "ng_ambient: Undefined ambient";
        end if;
    end try;
    return ambient;
end function;

// Returns a sequence of all facets in the neighbourly graph.
function ng_facets(G)
    return G[2];
end function;

// Returns a sequence F whose elements are in bijection with the facets
// returned by ng_facets(). Each element in F is a set of indices of all
// points in the sequence ng_points() such that that point lies on the
// corresponding facet.
function ng_facet_indices(G)
    return [PowerSet(Integers()) | 
        {Integers() | i : i in [1..#G[1]] | G[3][i][j] ne 0} : j in [1..#G[2]]];
end function;

// Returns a sequence of all points in the neighbourly graph.
function ng_points(G)
    return G[1];
end function;

// Returns the set of all points in the neighbourly graph contained in the
// given facet.
function ng_points_in_facet(G,f)
    j:=Index(G[2],f);
    assert j ne 0;
    return {Universe(G[1]) | G[1][i] : i in [1..#G[1]] | G[3][i][j] ne 0};
end function;

// Returns a set whose elements are the indices of the points contained in the
// given facet.
function ng_points_in_facet_by_index(G,f)
    j:=Index(G[2],f);
    assert j ne 0;
    return {Integers() | i : i in [1..#G[1]] | G[3][i][j] ne 0};
end function;

// Returns the set of all points in the neighbourly graph contained in the
// union of the given sequence (or set) of facets.
function ng_points_in_union_facets(G,fs)
    return &join[PowerSet(Universe(G[1])) | ng_points_in_facet(f) : f in fs];
end function;

// Returns the set of all points in the neighbourly graph contained in the
// intersection of the given sequence (or set) of facets.
function ng_points_in_intersection_facets(G,fs)
    idxs:={Integers() | Index(G[2],f) : f in fs};
    assert not 0 in idxs;
    return {Universe(G[1]) | G[1][i] :
                i in [1..#G[1]] | &and[G[3][i][j] ne 0 : j in idxs]};
end function;

// Returns the set of all facets containing the given point.
function ng_facets_containing_point(G,v)
    i:=Index(G[1],v);
    assert i ne 0;
    return {Universe(G[2]) | G[2][j] : j in [1..#G[2]] | G[3][i][j] ne 0};
end function;

// Given a sequence (or set) 'fs' of facets, returns a set whose elements are
// the maximal (ordered by inclusion) sets of those points in the neighbourly
// graph contained in fs and also in a facet not listed in fs.
function ng_penumbra(G,fs)
    // First we build the sets of indices we'll need
    fs_idxs:={Integers() | Index(G[2],f) : f in fs};
    assert not 0 in fs_idxs;
    fs_compliment:={Integers() | j : j in [1..#G[2]] | not j in fs_idxs};
    // Build the set of "shadow" facet indices for each facet
    pts:={PowerSet(Integers())|};
    for j in fs_idxs do
        pt_idxs:={Integers() | i : i in [1..#G[1]] | G[3][i][j] ne 0};
        fs_shadow:={Integers() | j : j in fs_compliment |
                                        &or[G[3][i][j] ne 0 : i in pt_idxs]};
        // Make a first attempt at building the set of points (as indices)
        pts join:= {PowerSet(Integers()) |
            {Integers() | i : i in pt_idxs | G[3][i][j] ne 0} : j in fs_shadow};
    end for;
    // Now we need to extract the maximal sets
    res:=maximal_sets_by_inclusion(pts);
    // Finally return the actual points
    return {PowerSet(Universe(G[1])) | {Universe(G[1]) | G[1][i] : i in S} :
                S in res};
end function;

/////////////////////////////////////////////////////////////////////////
// Modification functions
/////////////////////////////////////////////////////////////////////////

// Add the facet 'f' to the neighbourly graph. 'pts' is the set (or sequence)
// of the points already in the neighbourly graph which lie on 'f'.
procedure ng_add_facet(~G,f,pts)
    // Add this facet
    j:=Index(G[2],f);
    if j eq 0 then
        Append(~G[2],f);
        j:=#G[2];
        M:=RowSequence(Transpose(G[3])) cat [[Integers()|0 : i in [1..#G[1]]]];
        G[3]:=Transpose(Matrix(Integers(),M));
    end if;
    // Update the graph
    for pt in pts do
        i:=Index(G[1],pt);
        assert i ne 0;
        G[3][i][j]:=1;
    end for;
end procedure;

// Deletes the given set (or sequence) of facets from the neighbourly graph.
procedure ng_delete_facets(~G,fs)
    idxs:={Integers() | Index(G[2],f) : f in fs};
    assert not 0 in idxs;
    for j in Reverse(Sort(SetToSequence(idxs))) do
        Remove(~G[2],j);
        RemoveColumn(~G[3],j);
    end for;
end procedure;

// Add the point 'pt' to the neighbourly graph. It is assumed that the point
// does NOT lie on any of the existing facets.
procedure ng_add_point(~G,pt)
    // Add this point
    if Index(G[1],pt) eq 0 then
        Append(~G[1],pt);
        M:=RowSequence(G[3]) cat [[Integers()|0 : j in [1..#G[2]]]];
        G[3]:=Matrix(Integers(),M);
    end if;
end procedure;

// Deletes the given point from the neighbourly graph.
procedure ng_delete_point(~G,v)
    i:=Index(G[1],v);
    assert i ne 0;
    Remove(~G[1],i);
    RemoveRow(~G[3],i);
end procedure;

// Refines the points in the neighbourly graph by removing all non-vertices.
procedure ng_prune_points(~G)
    // Construct the subgraph for each point
    subgraphs:=[PowerSet(Integers()) |
                    {Integers() | j : j in [1..#G[2]] | G[3][i][j] ne 0} :
                    i in [1..#G[1]]];
    // The vertices are maximal amongst those
    maxsubgraphs:=maximal_sets_by_inclusion(subgraphs);
    vertices:={Integers() | Index(subgraphs,g) : g in maxsubgraphs};
    assert not 0 in vertices;
    // Delete the points that aren't vertices
    for i in [#G[1]..1 by -1] do
        if not i in vertices then
            Remove(~G[1],i);
            RemoveRow(~G[3],i);
        end if;
    end for;
end procedure;

// Removes the given vertex from the neighbourly graph and fills in the hole
// with new facets (if necessary). 'newfacets' will be set to equal the set of
// new facets that were created (represented as supporting half-spaces).
procedure ng_remove_point_recurse(S,k,idxs,~penumbra,~G,~oldfacets,~newfacets)
    if k eq 0 then
        bool,H:=is_hyperplane([penumbra[idx] : idx in idxs]);
        if bool then
            bool,orientation,pts:=is_supporting_hyperplane(H,G[1]);
            if bool and not <H,orientation> in G[2] then
                // We've found a new facet
                pts:={Universe(G[1]) | G[1][i] : i in pts};
                facet:=<H,orientation>;
                ng_add_facet(~G,facet,pts);
                // Of course, it's possible we're simply adding back in a
                // hyperplane we just removed (if, for example, v lies on
                // that hyperplane). We don't want to record those cases.
                if not facet in oldfacets then
                    Include(~newfacets,facet);
                end if;
            end if;
        end if;
    else
        s:=S[#S];
        Prune(~S);
        if k le #S then $$(S,k,idxs,~penumbra,~G,~oldfacets,~newfacets); end if;
        $$(S,k - 1,Append(idxs,s),~penumbra,~G,~oldfacets,~newfacets);
    end if;
end procedure;

procedure ng_remove_point(~G,v,~newfacets)
    // Calculate the facets to be removed and the points in the penumbra
    oldfacets:={Universe(G[2])|};
    penumbra:={Universe(G[1])|};
    i:=Index(G[1],v);
    assert i ne 0;
    for j in [1..#G[2]] do
        if G[3][i][j] ne 0 then
            Include(~oldfacets,G[2][j]);
            penumbra join:= {Universe(G[1]) | G[1][k] : k in [1..#G[1]] |
                                                    k ne i and G[3][k][j] ne 0};
        end if;
    end for;
    // Remove the vertex and affected facets
    ng_delete_point(~G,v);
    ng_delete_facets(~G,oldfacets);
    // Now work through the possible new facets
    newfacets:={Universe(G[2])|};
    penumbra:=SetToSequence(penumbra);
    ng_remove_point_recurse([1..#penumbra],Dimension(Universe(G[1])),
                              [Integers()|],~penumbra,~G,~oldfacets,~newfacets);
    assert #newfacets gt 0;
end procedure;

// Reorders the points of the neighbourly graph according to the given order.
procedure ng_reorder_points(~G,order)
    // Sanity check
    assert #order eq #G[1];
    // First reorder the points
    G[1]:=[Universe(G[1]) | G[1][i] : i in order];
    // Now reorder the rows of the matrix
    G[3]:=PermutationMatrix(Integers(),order) * G[3];
end procedure;

/////////////////////////////////////////////////////////////////////////
// Creation function
/////////////////////////////////////////////////////////////////////////

// Returns the neighbourly graph for the given simplex data.
// Note: 'vertices' should be a sequence, NOT a set. Assumes that the convex
// hull is of maximum dimension.
function ng_build_simplex(vertices)
    // Make the simplex's facets
    facets:=[CartesianProduct(CartesianProduct(
                             Dual(Universe(vertices)),Integers()),Integers())|];
    d:=#vertices;
    for i in [1..d] do
        bool,halfspace:=is_halfspace(Remove(vertices,i),vertices[i]);
        assert bool;
        Append(~facets,halfspace);
    end for;
    // Create the graph
    M:=Matrix(Integers(),[[Integers() | 1 : i in [1..d]] : j in [1..d]]);
    for i in [1..d] do
        M[i][i]:=0;
    end for;
    // Return the data
    return [* vertices, facets, M *];
end function;

// Returns the neighbourly graph for the given sequence of vertices and set
// of supporting half-spaces.
// Note: Assumes that the convex hull is of maximum dimension.
function ng_build_from_facets(vertices,facets)
    // Create the data
    if #facets eq 0 then
        facets:=[CartesianProduct(CartesianProduct(
                             Dual(Universe(vertices)),Integers()),Integers())|];
    else
        facets:=SetToSequence(facets);
    end if;
    M:=ZeroMatrix(Integers(),#vertices,#facets);
    // Is there anything to do?
    if #vertices gt 0 then
        for j in [1..#facets] do
            bool,I:=is_supporting_halfspace(facets[j],vertices);
            assert bool;
            for i in I do
                M[i][j]:=1;
            end for;
        end for;
    end if;
    // Return the data
    return [* vertices, facets, M *];
end function;

// Returns the neighbourly graph for the given sequence of points, where
// 'facets' is a sequence of sequences I of indices from 'points' such that 
// i in I iff pts[i] lie on a common facet.
// Note: Assumes that the convex hull is of maximum dimension.
function ng_build_from_facet_indices(points,facets)
    // Create the data
    fs:=[CartesianProduct(CartesianProduct(
                               Dual(Universe(points)),Integers()),Integers())|];
    j:=0;
    M:=ZeroMatrix(Integers(),#points,#facets);
    // Is there anything to do?
    if #points gt 0 then
        for f in facets do
            // Create the defining hyperplane
            bool,H:=is_hyperplane([Universe(points) | points[i] : i in f]);
            assert bool;
            // Find a point not on the hyperplane and construct the half-space
            bool,v:=exists_point_not_in_hyperplane(H,points);
            assert bool;
            bool,halfspace:=hyperplane_to_halfspace(H,v);
            assert bool;
            // Add the half-space to the facet sequence
            Append(~fs,halfspace);
            j+:=1;
            // Update the graph
            for i in f do
                M[i][j]:=1;
            end for;
        end for;
    end if;
    // Return the data
    return [* points, fs, M *];
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Returns a new neighbourly graph given by applying the given embedding and
// translation to the given graph
function ng_image(G,emb,trans)
    G[1]:=[Codomain(emb) | emb(v) + trans : v in G[1]];
    G[2]:=[CartesianProduct(CartesianProduct(
                             Dual(Codomain(emb)),Integers()),Integers()) |
                             halfspace_image(f,emb,trans) : f in G[2]];
    return G;
end function;

// Returns a new neighbourly graph given by pullingback the given embedding and
// translation from the given graph
function ng_image_pullback(G,emb,trans)
    G[1]:=[Domain(emb) | (v - trans) @@ emb : v in G[1]];
    G[2]:=[CartesianProduct(CartesianProduct(
                             Dual(Domain(emb)),Integers()),Integers()) |
                             halfspace_image_pullback(f,emb,trans) : f in G[2]];
    return G;
end function;

// Returns a new neighbourly graph given by applying the given rescaling to
// the points in the given graph.
function ng_scale(G,k)
    G[1]:=[Universe(G[1]) | k * v : v in G[1]];
    G[2]:=[Universe(G[2]) | to_halfspace(H[1][1],H[1][2] * k,H[2]) : H in G[2]];
    return G;
end function;

// Returns a new neighbourly graph given by applying the translation Q to the
// given graph.
function ng_translation(G,Q)
    G[1]:=[Universe(G[1]) | v + Q : v in G[1]];
    G[2]:=[Universe(G[2]) | halfspace_translation(H,Q) : H in G[2]];
    return G;
end function;

// Returns a new neighbourly graph given by taking the negation of all the
// points in the given graph.
function ng_negation(G)
    G[1]:=[Universe(G[1]) | -v : v in G[1]];
    G[2]:=[Universe(G[2]) | halfspace_negation(H) : H in G[2]];
    return G;
end function;

// Returns a new neighbourly graph given by changing the ambient of the given
// graph to L.
// Note: Assumes that the dimensions agree.
function ng_change_ambient(G,L)
    ChangeUniverse(~G[1],L);
    G[2]:=[CartesianProduct(CartesianProduct(
                             Dual(L),Integers()),Integers()) |
                             halfspace_change_ambient(f,L) : f in G[2]];
    return G;
end function;
