freeze;

/////////////////////////////////////////////////////////////////////////
// convexhull.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42129 $
// $Date: 2013-02-16 06:27:29 +1100 (Sat, 16 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the convex hull of the finite part of a polyhedron.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// We work in the sublattice L' -- i.e. we can assume that the points
// define a polytope P of maximal dimension in L'.
// We calculate the convex hull of a finite set of points by constructing
// the corresponding neighbourly graph, where the points that appear are
// all vertices. Thus, for the purposes of this file, we regard
// "convex hull" as synonymous with "neighbourly graph".
//
// This file contains only functions intended for internal use.
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": reorder_wrt_mapping, negate_sequence, negate_subsequences;
import "../../lattice/hyperplane.m": is_hyperplane, exists_point_not_in_hyperplane, hyperplane_to_halfspace;
import "../../lattice/point.m": nonvanishing_form;
import "../../cone/barvinok.m": barvinok_cone_decomposition;
import "sublattice.m": fp_emb_lattice_dimension, create_lattice_embedding, fp_emb_pullback_of_generating_points, fp_emb_lattice, fp_emb_map;
import "neighbourlygraph.m": ng_build_from_facet_indices, ng_build_simplex, ng_ambient, ng_translation, ng_negation, ng_scale, ng_points, ng_facets, ng_points_in_facet, ng_facets_containing_point, ng_facet_indices, ng_penumbra, ng_add_point, ng_add_facet, ng_delete_facets, ng_prune_points, ng_remove_point, ng_reorder_points;
import "conflictgraph.m": cg_build, cg_next_point, cg_add_facet, cg_delete_point, cg_delete_facets;
import "../faces/support.m": amb_get_fp_generating_points;

declare attributes TorPol:
    fp_ng,                  // The neighbourly graph for the finite part of P
    fp_are_vertices,        // True iff the generators are known to be verticies
                            // of the finite part of P
    fp_supporting_cones,    // The supporting cones of the finite part of P
    fp_decomposition,       // The decompositions of the supporting cones of the
                            // finite part of P
    fp_nonvanishing_form,   // A form not vanishing on any of the rays of the
                            // cones in fp_decomposition
    fp_dimension;           // The dimension of the finite part of P

/////////////////////////////////////////////////////////////////////////
// The zero and one dimensional algorithms
/////////////////////////////////////////////////////////////////////////

// The dimension 0 case
function convex_hull_dimension_0(P)
    points:=fp_emb_pullback_of_generating_points(P);
    return ng_build_from_facet_indices(points,[]);
end function;

// The dimension 1 case
function convex_hull_dimension_1(P)
    S:=Sort(fp_emb_pullback_of_generating_points(P));
    return ng_build_from_facet_indices([S[1],S[#S]],[[1],[2]]);
end function;

/////////////////////////////////////////////////////////////////////////
// The two dimensional algorithm
// The resulting vertices are in the "natural" ordering such that
// [v_i, v_{i+1}] is an edge.
/////////////////////////////////////////////////////////////////////////

// Returns true iff the last three points in the sequence S make a right turn;
// i.e. if the point S[#S] lies to the right of the directed line from
// S[#S - 2] through S[#S - 1].
function right_turn(S)
    M:=Matrix(S[#S-2..#S]);
    return Determinant(HorizontalJoin(
                        ColumnMatrix([CoefficientRing(M) | 1,1,1]),M)) lt 0;
end function;

// The dimension 2 case
function convex_hull_dimension_2(P)
    // Begin by sorting the points into lex order
    S:=Sort(fp_emb_pullback_of_generating_points(P));
    // Calculate the upper hull
    upperhull:=[S[1],S[2]];
    for i in [3..#S] do
        Append(~upperhull,S[i]);
        while #upperhull gt 2 and not right_turn(upperhull) do
            Remove(~upperhull,#upperhull - 1);
        end while;
    end for;
    // Now the lower hull
    lowerhull:=[S[#S],S[#S - 1]];
    for i in [#S - 2..1 by -1] do
        Append(~lowerhull,S[i]);
        while #lowerhull gt 2 and not right_turn(lowerhull) do
            Remove(~lowerhull,#lowerhull - 1);
        end while;
    end for;
    // Remove the first and last point from the lower hull (since they'll be in
    // the upper hull) and combine the two halves
    points:=upperhull cat lowerhull[2..#lowerhull - 1];
    // Create the edges and neighbourly graph
    edges:=[PowerSequence(Integers()) | [i,i+1] : i in [1..#points - 1]] cat
           [PowerSequence(Integers()) | [#points,1]];
    return ng_build_from_facet_indices(points,edges);
end function;

/////////////////////////////////////////////////////////////////////////
// The higher dimensional algorithm
/////////////////////////////////////////////////////////////////////////

// Given a sequence of points, adds them to the given neighbourly graph to
// calculate the combined convex hull.
procedure add_points_to_ng(~ng,pts)
    // Build the conflict graph
    cg:=cg_build(pts,ng_facets(ng));
    // Get the points currently known to the neighbourly graph
    pts:=ng_points(ng);
    // Work through the points in the conflict graph
    while true do
        // Get the next point and its conflicting facets
        bool,v,Hs:=cg_next_point(cg);
        if not bool then break; end if;
        // Get the "shadow" sets of points
        shadow:=ng_penumbra(ng,Hs);
        // Update the neighbourly graph
        ng_add_point(~ng,v);
        ng_delete_facets(~ng,Hs);
        // Update the conflict graph
        cg_delete_point(~cg,v);
        cg_delete_facets(~cg,Hs);
        // Work through the shadow sets
        for S in shadow do
            // First build the defining half-space
            SS:=Include(S,v);
            bool,H:=is_hyperplane(SS);
            assert bool;
            bool,pt:=exists_point_not_in_hyperplane(H,pts);
            assert bool;
            bool,halfspace:=hyperplane_to_halfspace(H,pt);
            assert bool;
            // Add this half-space to the graphs
            ng_add_facet(~ng,halfspace,SS);
            cg_add_facet(~cg,halfspace);
        end for;
        // Update our internal sequence of points
        Append(~pts,v);
    end while;
    // Finally prune all non-vertices from the neighbourly graph
    ng_prune_points(~ng);
end procedure;

// Given a sequence of (known) vertices, adds them to the given neighbourly
// graph to calculate the combined convex hull. Also produces a triangulation.
procedure add_vertices_to_ng(~ng,~triangulation,pts)
    // Build the conflict graph
    cg:=cg_build(pts,ng_facets(ng));
    // Get the points currently known to the neighbourly graph and note the
    // initial triangulation
    vtxs:=ng_points(ng);
    d:=#vtxs - 1;
    idx:=#vtxs + 1;
    triangulation:={PowerSet(Integers()) | {1..#vtxs}};
    // Work through the points in the conflict graph
    while true do
        // Get the next point and its conflicting facets
        bool,v,Hs:=cg_next_point(cg);
        if not bool then break; end if;
        // Update the triangulation
        facets:={PowerSet(Integers()) | {Integers() | Index(vtxs,u) :
                              u in ng_points_in_facet(ng,facet)} : facet in Hs};
        facettri:={PowerSet(Integers()) | simplex meet facet :
                                     facet in facets, simplex in triangulation};
        triangulation join:= {PowerSet(Integers()) | Include(tri,idx) :
                                                   tri in facettri | #tri eq d};
        // Get the "shadow" sets of points
        shadow:=ng_penumbra(ng,Hs);
        // Update the neighbourly graph
        ng_add_point(~ng,v);
        ng_delete_facets(~ng,Hs);
        // Update the conflict graph
        cg_delete_point(~cg,v);
        cg_delete_facets(~cg,Hs);
        // Work through the shadow sets
        newtriangs:={PowerSet(Integers())|};
        for S in shadow do
            // Build the defining half-space
            SS:=Include(S,v);
            bool,H:=is_hyperplane(SS);
            assert bool;
            bool,pt:=exists_point_not_in_hyperplane(H,vtxs);
            assert bool;
            bool,halfspace:=hyperplane_to_halfspace(H,pt);
            assert bool;
            // Add this half-space to the graphs
            ng_add_facet(~ng,halfspace,SS);
            cg_add_facet(~cg,halfspace);
        end for;
        // Update our sequence of vertices
        Append(~vtxs,v);
        idx +:= 1;
    end while;
end procedure;

// Returns the indicies of d+1 points in S that generate a (non-degenerate)
// simplex (of dimension d).
function find_simplex_indicies_recurse(S,idxs,offset,k)
    for i in [offset..#S - k + 1] do
        if k eq 1 then
            M:=Matrix([Universe(S) | S[j] - S[i] : j in idxs]);
            if Rank(M) eq #idxs then
                return true,Append(idxs,i);
            end if;
        else
            bool,result:=$$(S,Append(idxs,i),i + 1,k - 1);
            if bool then return true,result; end if;
        end if;
    end for;
    return false,_;
end function;

function find_simplex_indicies(S,d)
    for i in [1..#S-d] do
        bool,idxs:=find_simplex_indicies_recurse(S,[i],i + 1,d);
        if bool then return idxs; end if;
    end for;
    assert false;
end function;

// The dimension >= 3 case. If the points are known to be vertices then the
// algorithm can also produce a triangulation for little extra cost.
function convex_hull_dimension_general(P)
    // We need to find a (non-degenerate) simplex to get started with
    pts:=fp_emb_pullback_of_generating_points(P);
    idxs:=find_simplex_indicies(pts,fp_emb_lattice_dimension(P));
    vertices:=[Universe(pts) | pts[i] : i in idxs];
    // Prune the simplex's points from the sequence
    Reverse(~idxs);
    for i in idxs do
        Remove(~pts,i);
    end for;
    // Create the neighbourly graph
    ng:=ng_build_simplex(vertices);
    if (assigned P`amb_are_vertices and P`amb_are_vertices) or
       (assigned P`fp_are_vertices and P`fp_are_vertices) then
        add_vertices_to_ng(~ng,~triangulation,pts);
        P`fp_triangulation:=triangulation;
    else
        add_points_to_ng(~ng,pts);
    end if;
    return ng;
end function;

/////////////////////////////////////////////////////////////////////////
// Calculate convex hull
/////////////////////////////////////////////////////////////////////////

// Calculates the convex hull of the finite part of the polyhedron, taking a
// different approach depending on the dimension. If the points are known to
// be vertices then the general algorithm can also produce a triangulation.
procedure calculate_convex_hull(P)
    // Begin by resetting any data that depends on this
    if assigned P`fp_supporting_cones then
        delete P`fp_supporting_cones; end if;
    if assigned P`fp_triangulation then
        delete P`fp_triangulation; end if;
    if assigned P`fp_boundary_triang then
        delete P`fp_boundary_triang; end if;
    // Get the dimension
    dim:=fp_emb_lattice_dimension(P);
    // Calculate the neighbourly graph
    if dim eq 0 then
        P`fp_ng:=convex_hull_dimension_0(P);
    elif dim eq 1 then
        P`fp_ng:=convex_hull_dimension_1(P);
    elif dim eq 2 then
        P`fp_ng:=convex_hull_dimension_2(P);
    else
        P`fp_ng:=convex_hull_dimension_general(P);
    end if;
    // Reorder the vertices in the neighbourly graph so that they occur in the
    // same order as the sequence of generators
    trans,emb:=fp_emb_map(P);
    image:=[Ambient(P) | emb(u) + trans : u in ng_points(P`fp_ng)];
    if assigned P`amb_fp_generators then
        order:=reorder_wrt_mapping(image,amb_get_fp_generating_points(P));
        image:=[Ambient(P) | image[i] : i in order];
        ng_reorder_points(~P`fp_ng,order);
        if assigned P`fp_triangulation then
            shuffle:=[Integers() | Index(order,i) : i in [1..#order]];
            P`fp_triangulation:={PowerSet(Integers()) | {shuffle[i] : i in tri}:
                                                     tri in P`fp_triangulation};
        end if;
    end if;
    // Update the generators so that they're only vertices
    P`fp_are_vertices:=true;
    P`amb_fp_generators:=image;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Modify the convex hull
/////////////////////////////////////////////////////////////////////////

// Prunes the given vertices from the convex hull of the finite part of the
// polyhedron, recalculating the neighbourly graph and updating the
// generators accordingly.
procedure fp_prune_vertices(P,verts)
    trans,emb:=fp_emb_map(P);
    assert Universe(verts) eq Domain(emb);
    // Remove the points from the generators
    if assigned P`amb_fp_generators then
        for v in verts do
            idx:=Index(P`amb_fp_generators,v);
            assert idx ne 0;
            Remove(~P`amb_fp_generators,idx);
        end for;
    end if;
    // Remove the vertices from the neighbourly graph
    if assigned P`fp_ng then
        for v in verts do
            ng_remove_point(~P`fp_ng,v,~unused);
        end for;
    end if;
    // Has the dimension dropped? If so, we've got a lot of work to do
    if assigned P`fp_dimension then
        S:=amb_get_fp_generating_points(P);
        v:=Representative(S);
        L:=Universe(S);
        M:=Matrix([L | s - v : s in S]);
        if Rank(M) ne P`fp_dimension then
            // Yes -- Basically we have to throw everything away and start again
            P`fp_dimension:=Rank(M);
            create_lattice_embedding(P);
            if assigned P`fp_ng then delete P`fp_ng; end if;
        end if;
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure fp_apply_translation(P,CP,Q)
    if assigned P`fp_dimension then
        CP`fp_dimension:=P`fp_dimension; end if;
    if assigned P`fp_are_vertices then
        CP`fp_are_vertices:=P`fp_are_vertices; end if;
    if assigned P`fp_ng then
        if assigned P`fp_dimension and
            P`fp_dimension eq Dimension(Ambient(P)) then
            CP`fp_ng:=ng_translation(P`fp_ng,Q);
        elif IsIntegral(Q) then
            CP`fp_ng:=P`fp_ng;
        end if;
    end if;
    if (assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P))) or
       IsIntegral(Q) then
        if assigned P`fp_supporting_cones then
            CP`fp_supporting_cones:=P`fp_supporting_cones; end if;
        if assigned P`fp_decomposition then
            CP`fp_decomposition:=P`fp_decomposition; end if;
        if assigned P`fp_nonvanishing_form then
            CP`fp_nonvanishing_form:=P`fp_nonvanishing_form; end if;
    end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure fp_apply_negation(P,CP)
    if assigned P`fp_dimension then
        CP`fp_dimension:=P`fp_dimension; end if;
    if assigned P`fp_are_vertices then
        CP`fp_are_vertices:=P`fp_are_vertices; end if;
    if assigned P`fp_supporting_cones then
        if assigned P`fp_dimension and
            P`fp_dimension eq Dimension(Ambient(P)) then
            CP`fp_supporting_cones:=[PowerStructure(TorCon)|];
            for idx in [1..#P`fp_supporting_cones] do
                if IsDefined(P`fp_supporting_cones,idx) then
                    CP`fp_supporting_cones[idx]:=-P`fp_supporting_cones[idx];
                end if;
            end for;
        else
            CP`fp_supporting_cones:=P`fp_supporting_cones;
        end if;
    end if;
    if assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P)) then
        if assigned P`fp_ng then
            CP`fp_ng:=ng_negation(P`fp_ng); end if;
        if assigned P`fp_decomposition then
            CP`fp_decomposition:=[];
            for idx in [1..#P`fp_decomposition] do
                if IsDefined(P`fp_decomposition,idx) then
                    CP`fp_decomposition[idx]:=[<negate_subsequences(pair[1]),
                                    pair[2]> : pair in P`fp_decomposition[idx]];
                end if;
            end for;
        end if;
        if assigned P`fp_nonvanishing_form then
            CP`fp_nonvanishing_form:=negate_sequence(P`fp_nonvanishing_form);
        end if;
    else
        if assigned P`fp_ng then
            CP`fp_ng:=P`fp_ng; end if;
        if assigned P`fp_decomposition then
            CP`fp_decomposition:=P`fp_decomposition; end if;
        if assigned P`fp_nonvanishing_form then
            CP`fp_nonvanishing_form:=P`fp_nonvanishing_form; end if;
    end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure fp_apply_dilation(P,CP,k)
    if assigned P`fp_dimension then
        CP`fp_dimension:=P`fp_dimension; end if;
    if assigned P`fp_are_vertices then
        CP`fp_are_vertices:=P`fp_are_vertices; end if;
    if ((assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P))) or
       (assigned P`sub_origin and IsIntegral((k - 1) * P`sub_origin))) then
        if assigned P`fp_supporting_cones then
            CP`fp_supporting_cones:=P`fp_supporting_cones; end if;
        if assigned P`fp_ng then
            CP`fp_ng:=ng_scale(P`fp_ng,k);
        end if;
        if assigned P`fp_decomposition then
            CP`fp_decomposition:=P`fp_decomposition; end if;
        if assigned P`fp_nonvanishing_form then
            CP`fp_nonvanishing_form:=P`fp_nonvanishing_form; end if;
    end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
// Note: Actually we don't need to do anything clever, since the ambient of P
// doesn't affect the sublattice the finite-part is constructed in.
procedure fp_change_ambient(P,CP,L)
    if assigned P`fp_are_vertices then
        CP`fp_are_vertices:=P`fp_are_vertices; end if;
    if assigned P`fp_dimension then
        CP`fp_dimension:=P`fp_dimension; end if;
    if assigned P`fp_supporting_cones then
        CP`fp_supporting_cones:=P`fp_supporting_cones; end if;
    if assigned P`fp_ng then
        CP`fp_ng:=P`fp_ng; end if;
    if assigned P`fp_decomposition then
        CP`fp_decomposition:=P`fp_decomposition; end if;
    if assigned P`fp_nonvanishing_form then
        CP`fp_nonvanishing_form:=P`fp_nonvanishing_form; end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
// Note: We can't copy over most of the data, since P wasn't maximal dimensional
// and CP is, and we handle the two cases slightly differently.
procedure fp_change_to_maximal(P,CP,emb,trans)
    if assigned P`fp_are_vertices then
        CP`fp_are_vertices:=P`fp_are_vertices; end if;
    if assigned P`fp_dimension then
        CP`fp_dimension:=P`fp_dimension; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Helper functions
/////////////////////////////////////////////////////////////////////////

// Input: A sequence of sequences representing the rays of a univariate cone,
// and a lattice point apex.
// Output: Returns the unique lattice point (given as a sequence) in the
// fundamental parallelepiped generated by rays, shifted to apex.
function point_in_fundamental_domain(apex,rays)
    if IsIntegral(apex) then return Eltseq(apex); end if;
    apex:=Eltseq(apex);
    ChangeUniverse(~apex,Rationals());
    d:=#apex;
    weights:=[Ceiling(c) : c in Eltseq(Solution(
                        Matrix(Rationals(),rays),Matrix(1,d,apex)))];
    return [&+[weights[i] * rays[i][j] : i in [1..d]] : j in [1..d]];
end function;

/////////////////////////////////////////////////////////////////////////
// Access functions
/////////////////////////////////////////////////////////////////////////

// Returns the dimension of the finite part of the polyhedron.
function fp_get_dimension(P)
    if not assigned P`fp_dimension then
        create_lattice_embedding(P);
    end if;
    return P`fp_dimension;
end function;

// Returns the neighbourly graph of the finite part of the polyhedron
function fp_neighbourly_graph(P)
    if not assigned P`fp_ng then
        calculate_convex_hull(P);
    end if;
    return P`fp_ng;
end function;

// Returns the vertices in L' of the finite part of the polyhedron
function fp_get_pullback_vertices(P)
    if not assigned P`fp_ng then
        calculate_convex_hull(P);
    end if;
    return ng_points(P`fp_ng);
end function;

// Returns the defining half-spaces in Dual(L') of the finite part of the
// polyhedron
function fp_get_pullback_halfspaces(P)
    if not assigned P`fp_ng then
        calculate_convex_hull(P);
    end if;
    return ng_facets(P`fp_ng);
end function;

// Returns a sequence F whose elements are in bijection with the defining
// hyperplanes. Each element in F is a set of indices of all vertices such that
// that vertex lies on the corresponding hyperplane.
function fp_facet_indices(P)
    if not assigned P`fp_ng then
        calculate_convex_hull(P);
    end if;
    return ng_facet_indices(P`fp_ng);
end function;

// Returns the cone (in L') supported locally at vertex v in L' by the
// halfspaces of the finite part of P.
function fp_get_cone_at_pullback_vertex(P,v)
    ng:=fp_neighbourly_graph(P);
    idx:=Index(ng[1],v);
    assert idx ne 0;
    if assigned P`fp_supporting_cones then
        if IsDefined(P`fp_supporting_cones,idx) then
            return P`fp_supporting_cones[idx];
        end if;
    else
        P`fp_supporting_cones:=[PowerStructure(TorCon)|];
    end if;
    Hs:=ng_facets_containing_point(ng,v);
    C:=ConeWithInequalities([Dual(Parent(v)) | h[1][1] * h[2] : h in Hs]);
    C`cone_in_sublattice:=C;
    C`cone_in_sublattice_map:=IdentityMap(Ambient(C));
    P`fp_supporting_cones[idx]:=C;
    return C;
end function;

// Returns the decomposition of the indicated supporting cone of the finite
// part of P. These data are represented as a triple: <numerator, rays, sign>.
// To avoid complications concerning inclusion/exclusion of lower
// dimensional faces we exploit Brion's polarisation trick and work with
// the cone dual to C, where C is a supporting cone of P. However, this
// might change in the future (see the recent work on avoiding dualisation
// via the use of irrational cones).
// Important note: The numerator and the rays are presented as Eltseqs, and
// are not case into the ambient lattice. You can easily do this yourself --
// the ambient is given by fp_emb_lattice(P).
function fp_decomposition_of_cone_at_pullback_vertex(P,v)
    ng:=fp_neighbourly_graph(P);
    idx:=Index(ng[1],v);
    assert idx ne 0;
    if not assigned P`fp_decomposition then
        P`fp_decomposition:=[];
    end if;
    if not IsDefined(P`fp_decomposition,idx) then
        P`fp_decomposition[idx]:=
             [<RowSequence(Transpose(Matrix(Rationals(),pair[1])^-1)),pair[2]> :
                                    pair in barvinok_cone_decomposition(
                                    Dual(fp_get_cone_at_pullback_vertex(P,v)))];
    end if;
    return [<point_in_fundamental_domain(v,pair[1]),pair[1],pair[2]> :
                                    pair in P`fp_decomposition[idx]];
end function;

// Returns a form lambda not vanishing on the rays of any of the cones in
// the decomposition of the supporting cones of (the finite part of) P.
// Important note: The form is presented as an Eltseq; it is not cast into
// the dual of the ambient lattice. You can easily do this yourself --
// simply coerce into Dual(fp_emb_lattice(P)).
function fp_get_nonvanishing_form(P)
    if not assigned P`fp_nonvanishing_form then
        ng:=fp_neighbourly_graph(P);
        if not assigned P`fp_decomposition then
            P`fp_decomposition:=[];
        end if;
        rays:=[PowerSequence(Integers())|];
        for idx in [1..#ng[1]] do
            if not IsDefined(P`fp_decomposition,idx) then
                P`fp_decomposition[idx]:=[<RowSequence(Transpose(Matrix(
                           Rationals(),pair[1])^-1)),pair[2]> :
                           pair in barvinok_cone_decomposition(
                           Dual(fp_get_cone_at_pullback_vertex(P,ng[1][idx])))];
            end if;
            rays cat:= &cat[PowerSequence(Universe(rays)) | pair[1] :
                                               pair in P`fp_decomposition[idx]];
        end for;
        P`fp_nonvanishing_form:=nonvanishing_form(SequenceToSet(rays));
    end if;
    return P`fp_nonvanishing_form;
end function;
