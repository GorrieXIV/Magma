freeze;

/////////////////////////////////////////////////////////////////////////
// support.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 44005 $
// $Date: 2013-07-26 19:57:14 +1000 (Fri, 26 Jul 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the supporting hyperplanes of a polyhedron.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// We have two sets of supporting hyperplanes. One describing the finite
// part, and the other the infinite part. These need combining to give the
// support of P.
// Facets and vertices are determined in this file, however general face
// enumeration functions are located in faces.m.
/////////////////////////////////////////////////////////////////////////

import "../../lattice/hyperplane.m": cmp_hyperplane_and_point, to_halfspace, point_in_halfspace, point_strictly_in_halfspace, point_on_halfspace_boundary;
import "../../cone/barvinok.m": barvinok_cone_decomposition;
import "../convexhull/neighbourlygraph.m": ng_build_from_facets, ng_image, ng_image_pullback, ng_translation, ng_negation, ng_scale, ng_change_ambient, ng_points, ng_facets, ng_add_facet, ng_facets_containing_point, ng_delete_facets;
import "../convexhull/sublattice.m": fp_emb_map, fp_emb_hyperplanes, ambient_lattice_to_embedded_lattice;
import "../convexhull/convexhull.m": fp_prune_vertices, fp_get_dimension, fp_neighbourly_graph, fp_get_pullback_vertices, fp_get_cone_at_pullback_vertex, fp_decomposition_of_cone_at_pullback_vertex, point_in_fundamental_domain;
import "../coneembedding.m": ce_get_cone, ce_get_embedding;

declare attributes TorPol:
    amb_fp_generators,     // The generators of the finite part of P
    amb_ng,                // The neighbourly graph of P
    amb_supporting_cones,  // The supporting cones of P
    amb_is_lattice,        // Does the subspace containing P have a volume form?
    amb_are_vertices,      // True iff the generators are known to be vertices
    amb_num_facets,        // The number of facets of P
    amb_facet_idxs,        // The facet indices of P
    amb_facets;            // The facets (as polyhedra) of P

/////////////////////////////////////////////////////////////////////////
// Calculates the neighbourly graph of P
/////////////////////////////////////////////////////////////////////////

// Assumes that there is no infinite part to consider. Simply lifts the finite
// part data to the ambient lattice.
procedure lift_fp_data(P)
    if fp_get_dimension(P) eq Dimension(Ambient(P)) then
        P`amb_ng:=fp_neighbourly_graph(P);
        P`amb_num_facets:=#ng_facets(P`amb_ng);
    else
        // Embed the finite part into the ambient lattice
        trans,emb:=fp_emb_map(P);
        ng:=ng_image(fp_neighbourly_graph(P),emb,trans);
        P`amb_num_facets:=#ng_facets(ng);
        // We need to add the half-spaces that cut out the subspace containing P
        verts:=ng_points(ng);
        v:=Representative(verts);
        D:=Dual(Universe(verts));
        M:=Transpose(Matrix(Rationals(),[Universe(verts)|u - v : u in verts]));
        B:=[D | PrimitiveLatticeVector(D ! Eltseq(b)) : b in Basis(Kernel(M))];
        Append(~B,-&+B);
        for normal in B do
            halfspace:=to_halfspace(normal,normal * v,1);
            ng_add_facet(~ng,halfspace,verts);
        end for;
        // Finally, record the neighbourly graph
        P`amb_ng:=ng;
    end if;
end procedure;

// Combines the finite part of P with its infinite part.
procedure combine_fp_and_ip_data(P)
    // Get the infinite part and the embedding
    infC:=InfinitePart(P);
    trans,emb:=fp_emb_map(P);
    // Get the inequalities described by the subspace hyperplanes
    Hs:=fp_emb_hyperplanes(P);
    subCineq:=[Dual(Ambient(P)) | H[1] : H in Hs]
                                    cat [Dual(Ambient(P)) | -H[1] : H in Hs];
    // We now consider the supporting hyperplanes when the apex of the cone is
    // shifted to each vertex in turn.
    verts:=[Ambient(infC)|];
    badvert:=[Domain(emb)|];
    halfspaces:={};
    for v in fp_get_pullback_vertices(P) do
        localC:=Image(emb,fp_get_cone_at_pullback_vertex(P,v)) + infC;
        u:=emb(v) + trans;
        halfspaces join:= {to_halfspace(normal,normal * u,1) :
                                         normal in MinimalInequalities(localC)};
        // Is this a vertex of P?
        if IsEmpty(LinearSubspaceGenerators(localC)) then
            Append(~verts,u);
        // Else should this even be a vertex of the finite part?
        elif not IsMaximumDimensional(Cone(subCineq cat Inequalities(localC)))
            then
            Append(~badvert,v);
        end if;
    end for;
    // Delete the "bad" vertices from the finite part (i.e. points we thought
    // were vertices but are redundant because they're absorbed by the cone)
    if #badvert gt 0 then
        fp_prune_vertices(P,badvert);
    end if;
    // Build the neighbourly graph for this data
    P`amb_ng:=ng_build_from_facets(verts,halfspaces);
end procedure;

// Calculates the neighbourly graph of P
procedure calculate_neighbourly_graph(P)
    // First reset any data that depends on this
    if assigned P`amb_supporting_cones then
        delete P`amb_supporting_cones; end if;
    if assigned P`amb_facet_idxs then
        delete P`amb_facet_idxs; end if;
    // Calculate the supporting half-spaces and the resulting vertices (if any)
    if IsPolytope(P) then
        lift_fp_data(P);
    else
        combine_fp_and_ip_data(P);
    end if;
    // Are the generators equal to the vertices?
    if not assigned P`amb_are_vertices and
       #P`amb_fp_generators eq #ng_points(P`amb_ng) then
        P`amb_are_vertices:=true;
    end if;
end procedure;
    
/////////////////////////////////////////////////////////////////////////
// Access functions
/////////////////////////////////////////////////////////////////////////

// Returns the ambient generating points of the finite part of P
function amb_get_fp_generating_points(P)
    return P`amb_fp_generators;
end function;

// Returns true if the generating points of the finite part of P are known
// to be vertices of P
function amb_are_fp_generating_points_vertices(P)
    return assigned P`amb_are_vertices and P`amb_are_vertices;
end function;

// Returns the neighbourly graph of P
function amb_neighbourly_graph(P)
    if not assigned P`amb_ng then
        calculate_neighbourly_graph(P);
    end if;
    return P`amb_ng;
end function;

// Returns the defining half-spaces in Dual(L) of P
function amb_get_halfspaces(P)
    if not assigned P`amb_ng then
        calculate_neighbourly_graph(P);
    end if;
    return ng_facets(P`amb_ng);
end function;

// Returns the defining half-spaces of P partitioned into two sequences.
// The first sequence contains those half-spaces which define a facet of P,
// the second sequence contains those half-spaces which are there simply to
// cut the dimension of the ambient down to size.
function amb_partition_halfspaces_by_task(P)
    hs:=amb_get_halfspaces(P);
    if not assigned P`amb_num_facets then
        // Does the dimension of P agree with the dimension of the ambient?
        if (not assigned P`dimension) or
            P`dimension ne Dimension(Ambient(P)) then
            V:=amb_get_fp_generating_points(P);
            u:=Representative(V);
            gens:=[v - u : v in V] cat RGenerators(InfinitePart(P));
            if not assigned P`dimension then
                P`dimension:=Rank(Matrix(Rationals(),gens));
            end if;
            if P`dimension ne Dimension(Ambient(P)) then
                // The dimensions don't agree, so we collect together the
                // half-spaces which are there simply to cut down the dimension
                P`amb_num_facets:=0;
                subspace_halfspaces:=[];
                for halfspace in hs do
                    if &and[v * halfspace[1][1] eq 0 : v in gens] then
                        Append(~subspace_halfspaces,halfspace);
                    else
                        P`amb_num_facets+:=1;
                    end if;
                end for;
                // Now we remove the subspace half-spaces, compute the minimum
                // number required, and append those to the end of the
                // neighbourly graph
                ng_delete_facets(~P`amb_ng,subspace_halfspaces);
                C:=ConeWithInequalities([Dual(Ambient(P)) |
                                 halfspace[1][1] * halfspace[2] :
                                 halfspace in subspace_halfspaces]);
                verts:=ng_points(P`amb_ng);
                for normal in MinimalInequalities(C) do
                    halfspace:=to_halfspace(normal,normal * u,1);
                    ng_add_facet(~P`amb_ng,halfspace,verts);
                end for;
                // Update the half-spaces
                hs:=ng_facets(P`amb_ng);
            else
                // All the half-spaces are supporting facets of P
                P`amb_num_facets:=#hs;
            end if;
        else
            // All the half-spaces are supporting facets of P
            P`amb_num_facets:=#hs;
        end if;
    end if;
    return hs[1..P`amb_num_facets], hs[P`amb_num_facets + 1..#hs];
end function;

// Returns the cone in the ambient of P equal to the subspace containing P,
// shifted to the origin
function amb_emb_cone(P)
    _,subspace_halfspaces:=amb_partition_halfspaces_by_task(P);
    return ConeWithInequalities([Dual(Ambient(P)) |
                                 halfspace[1][1] * halfspace[2] :
                                 halfspace in subspace_halfspaces]);
end function;

// Returns a sequence F whose elements correspond to the facets of P.
// Each element in F is a set of indices of all generators such that that
// generator lies on the corresponding facet.
// Note: To get the corresponding sequence of half-spaces, use the first
// returned value of amb_partition_halfspaces_by_task()
function amb_facet_indices(P)
    if not assigned P`amb_facet_idxs then
        ng:=amb_neighbourly_graph(P);
        gens:=amb_get_fp_generating_points(P);
        P`amb_facet_idxs:=[PowerSet(Integers()) | {i : i in [1..#gens] |
                                point_on_halfspace_boundary(f,gens[i])} :
                                f in amb_partition_halfspaces_by_task(P)];
    end if;
    return P`amb_facet_idxs;
end function;

// Returns true iff the subspace containing P posseses a volume form (i.e.
// contains an affine sublattice).
function amb_has_volume_form(P)
    if not assigned P`amb_is_lattice then
        if (assigned P`dimension and P`dimension eq Dimension(Ambient(P))) or
           (assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P)))
           then
            // The subspace containing P is equal to the ambient, so easy
            P`amb_is_lattice:=true;
        else
            // Get the half-spaces cutting out P's subspace
            _,halfspaces:=amb_partition_halfspaces_by_task(P);
            // Is there anything to check?
            if #halfspaces eq 0 then
                P`amb_is_lattice:=true;
            else
                normals:=[Dual(Ambient(P)) | halfspace[1][1] :
                                                       halfspace in halfspaces];
                heights:=[Integers()|halfspace[1][2] : halfspace in halfspaces];
                try
                    _:=Solution(Transpose(Matrix(Integers(),normals)),
                                                    Matrix(1,#heights,heights));
                    // If we're here then it contains an affine sublattice
                    P`amb_is_lattice:=true;
                catch e
                    // If we're here then it doesn't contain any lattice points 
                    P`amb_is_lattice:=false;
                end try;
            end if;
        end if;
    end if;
    return P`amb_is_lattice;
end function;

// Returns the decomposition of the indicated supporting cone of P. These data
// are represented as a triple: <numerator, rays, sign>. To avoid complications
// concerning inclusion/exclusion of lower dimensional faces we exploit Brion's
// polarisation trick and work with the cone dual to C, where C is a supporting
// cone of P. However, this might change in the future (see the recent work on
// avoiding dualisation via the use of irrational cones).
// Also returns the embedding required to make C of maximal dimension.
// Important note: The numerator and the rays are presented as Eltseqs, and
// are not cast into the ambient lattice. You can easily do this yourself --
// the appropriate ambient is the domain of the embedding.
function amb_decomposition_of_cone_at_vertex(P,v)
    if IsPolytope(P) then
        trans,emb:=fp_emb_map(P);
        return fp_decomposition_of_cone_at_pullback_vertex(P,
                                (v - trans) @@ emb), emb;
    end if;
    C,emb:=ConeInSublattice(SupportingCone(P,v));
    D:=Dual(C);
    v:=v @@ emb;
    decomp:=[<RowSequence(Transpose(Matrix(Rationals(),pair[1])^-1)),pair[2]> :
                                pair in barvinok_cone_decomposition(D)];
    return [<point_in_fundamental_domain(v,pair[1]),pair[1],pair[2]> :
                                pair in decomp],emb;
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the facets, nor the supporting cones, but we do copy the facet indices.
procedure amb_apply_translation(P,CP,Q)
    if assigned P`amb_fp_generators then
        CP`amb_fp_generators:=[Ambient(P) | v + Q : v in P`amb_fp_generators];
    end if;
    if assigned P`amb_are_vertices then
        CP`amb_are_vertices:=P`amb_are_vertices; end if;
    if assigned P`amb_ng then
        CP`amb_ng:=ng_translation(P`amb_ng,Q); end if;
    if assigned P`amb_num_facets then
        CP`amb_num_facets:=P`amb_num_facets; end if;
    if assigned P`amb_facet_idxs then
        CP`amb_facet_idxs:=P`amb_facet_idxs; end if;
    if assigned P`amb_is_lattice and
       ((assigned P`dimension and P`dimension eq Dimension(Ambient(P))) or
       (assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P))) or
       IsIntegral(Q)) then
        CP`amb_is_lattice:=P`amb_is_lattice;
    end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the facets, nor the supporting cones, but we do copy the facet indices.
procedure amb_apply_negation(P,CP)
    if assigned P`amb_fp_generators then
        CP`amb_fp_generators:=[Ambient(P) | -v : v in P`amb_fp_generators];
    end if;
    if assigned P`amb_are_vertices then
        CP`amb_are_vertices:=P`amb_are_vertices; end if;
    if assigned P`amb_ng then
        CP`amb_ng:=ng_negation(P`amb_ng); end if;
    if assigned P`amb_num_facets then
        CP`amb_num_facets:=P`amb_num_facets; end if;
    if assigned P`amb_facet_idxs then
        CP`amb_facet_idxs:=P`amb_facet_idxs; end if;
    if assigned P`amb_is_lattice then
        CP`amb_is_lattice:=P`amb_is_lattice; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the facets, nor the supporting cones, but we do copy the facet indices.
procedure amb_apply_dilation(P,CP,k)
    if assigned P`amb_fp_generators then
        CP`amb_fp_generators:=[Ambient(P) | k * v : v in P`amb_fp_generators];
    end if;
    if assigned P`amb_are_vertices then
        CP`amb_are_vertices:=P`amb_are_vertices; end if;
    if assigned P`amb_ng then
        CP`amb_ng:=ng_scale(P`amb_ng,k);
    end if;
    if assigned P`amb_num_facets then
        CP`amb_num_facets:=P`amb_num_facets; end if;
    if assigned P`amb_facet_idxs then
        CP`amb_facet_idxs:=P`amb_facet_idxs; end if;
    if assigned P`amb_is_lattice and
       ((assigned P`dimension and P`dimension eq Dimension(Ambient(P))) or
       (assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P))) or
       (assigned P`sub_origin and IsIntegral((k - 1) * P`sub_origin))) then
        CP`amb_is_lattice:=P`amb_is_lattice;
    end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the facets, nor the supporting cones, but we do copy the facet indices.
procedure amb_change_ambient(P,CP,L)
    if assigned P`amb_fp_generators then
        CP`amb_fp_generators:=ChangeUniverse(P`amb_fp_generators,L); end if;
    if assigned P`amb_is_lattice then
        CP`amb_is_lattice:=P`amb_is_lattice; end if;
    if assigned P`amb_are_vertices then
        CP`amb_are_vertices:=P`amb_are_vertices; end if;
    if assigned P`amb_facet_idxs then
        CP`amb_facet_idxs:=P`amb_facet_idxs; end if;
    if assigned P`amb_num_facets then
        CP`amb_num_facets:=P`amb_num_facets; end if;
    if assigned P`amb_ng then
        CP`amb_ng:=ng_change_ambient(P`amb_ng,L); end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the facets, nor the supporting cones, but we do copy the facet indices.
procedure amb_change_to_maximal(P,CP,emb,trans)
    L:=Domain(emb);
    if assigned P`amb_fp_generators then
        CP`amb_fp_generators:=[L|(v - trans) @@ emb : v in P`amb_fp_generators];
    end if;
    CP`amb_is_lattice:=true;
    if assigned P`amb_are_vertices then
        CP`amb_are_vertices:=P`amb_are_vertices; end if;
    if assigned P`amb_facet_idxs then
        CP`amb_facet_idxs:=P`amb_facet_idxs; end if;
    if assigned P`amb_num_facets then
        CP`amb_num_facets:=P`amb_num_facets; end if;
    if assigned P`amb_ng then
        ng:=P`amb_ng;
        _,Hs:=amb_partition_halfspaces_by_task(P);
        ng_delete_facets(~ng,Hs);
        CP`amb_ng:=ng_image_pullback(ng,emb,trans);
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a polytope P, returns a sequence S of sequences of integers, such that
// the i-th sequence J in S lists the indices j of the facets containing the
// i-th edge.
function edge_facet_indices(P)
    // Sanity check
    error if not IsPolytope(P), "The polyhedron must be a polytope.";
    // Collect the facet index data
    fidxs:=FacetIndices(P);
    // Sort working through the edge indices building up our pairs
    S:=[PowerSet(Integers())|];
    for E in EdgeIndices(P) do
        Append(~S,{i : i in [1..#fidxs] | E subset fidxs[i]});
    end for;
    return S;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Vertices(P::TorPol) -> SeqEnum[TorLatElt]
{The sequence of vertices of the polyhedron P}
    if amb_are_fp_generating_points_vertices(P) then
        return amb_get_fp_generating_points(P);
    else
        return ng_points(amb_neighbourly_graph(P));
    end if;
end intrinsic;

intrinsic NumberOfVertices(P::TorPol) -> RngIntElt
{The number of vertices of the polyhedron P}
    if not assigned P`amb_ng then
        if IsAffineLinear(P) then
            return 0;
        elif IsPolytope(P) and assigned P`fp_ng then
            return #ng_points(P`fp_ng);
        end if;
    end if;
    return #Vertices(P);
end intrinsic;

intrinsic Facets(P::TorPol) -> SeqEnum[TorPol]
{The sequence of facets of the polyhedron P}
    if not assigned P`amb_facets then
        require not IsEmpty(P): "Cannot compute facets for an empty polyhedron";
        if Dimension(P) eq 0 then return [EmptyPolyhedron(Ambient(P))]; end if;
        facetidxs:=amb_facet_indices(P);
        gens:=amb_get_fp_generating_points(P);
        P`amb_facets:=[PowerStructure(TorPol)|];
        if IsPolytope(P) then
            for facet in facetidxs do
                Append(~P`amb_facets,Polytope([Ambient(P) |
                                    gens[i] : i in facet] : areVertices:=true));
            end for;
        else
            NC:=NormalisedCone(P);
            for F in Facets(NC) do
                PF:=Polyhedron(F);
                if not IsEmpty(PF) then
                    Append(~P`amb_facets,ChangeAmbient(PF,Ambient(P)));
                end if;
            end for;
        end if;
    end if;
    return P`amb_facets;
end intrinsic;

intrinsic FacetIndices(P::TorPol) -> SeqEnum[SetEnum[RngIntElt]]
{A sequence of sets describing the facets of the polytope P. The j-th set gives the indices of the vertices of P which define the j-th facet of P.}
    require IsPolytope(P): "Polyhedron must be a polytope";
    require Dimension(P) gt 0:
        "Cannot compute facets for a 0-dimensional polytope";
    return amb_facet_indices(P);
end intrinsic;

intrinsic NumberOfFacets(P::TorPol) -> RngIntElt
{The number of facets of the polyhedron P}
    if not assigned P`amb_num_facets then
        if Dimension(P) eq 0 then
            return 0;
        elif IsPolytope(P) and assigned P`fp_ng then
            return #ng_facets(P`fp_ng);
        else
            _,_:=amb_partition_halfspaces_by_task(P);
        end if;
    end if;
    return P`amb_num_facets;
end intrinsic;

intrinsic VertexEdgeIncidenceMatrix(P::TorPol) -> ModMatRngElt
{The vertex-edge incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th vertex is contained in the j-th edge).}
    M:=ZeroMatrix(Integers(),NumberOfVertices(P),NumberOfEdges(P));
    if Dimension(P) ge 1 then
        if IsPolytope(P) then
            S:=EdgeIndices(P);
        else
            verts:=Vertices(P);
            S:=[PowerSet(Integers())|];
            for E in Edges(P) do
                Append(~S,{i : i in [1..#verts] | verts[i] in E});
            end for;
        end if;
        for j in [1..#S] do
            for i in S[j] do
                M[i,j]:=1;
            end for;
        end for;
    end if;
    return M;
end intrinsic;

intrinsic EdgeFacetIncidenceMatrix(P::TorPol) -> ModMatRngElt
{The edge-facet incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th edge is contained in the j-th facet).}
    M:=ZeroMatrix(Integers(),NumberOfEdges(P),NumberOfFacets(P));
    if Dimension(P) ge 2 then
        if IsPolytope(P) then
            S:=edge_facet_indices(P);
        else
            facets:=Facets(P);
            S:=[PowerSet(Integers())|];
            for E in Edges(P) do
                Append(~S,{i : i in [1..#facets] | E subset facets[i]});
            end for;
        end if;
        for i in [1..#S] do
            for j in S[i] do
                M[i,j]:=1;
            end for;
        end for;
    end if;
    return M;
end intrinsic;

intrinsic VertexFacetIncidenceMatrix(P::TorPol) -> ModMatRngElt
{The vertex-facet incidence matrix of the polyhedron P (where the i,j-th entry is 1 if and only if the i-th vertex is contained in the j-th facet).}
    if Dimension(P) le 0 then
        return Matrix(Integers(),NumberOfVertices(P),0,[Integers()|]);
    elif IsPolytope(P) then
        facets:=FacetIndices(P);
        M:=[ZeroSequence(Integers(),#facets) : i in [1..NumberOfVertices(P)]];
        for j in [1..#facets] do
            for i in facets[j] do
                M[i][j]:=1;
            end for;
        end for;
    else
        facets:=Facets(P);
        vertices:=Vertices(P);
        M:=[ZeroSequence(Integers(),#facets) : i in [1..#vertices]];
        for j in [1..#facets] do
            for i in [1..#vertices] do
                if vertices[i] in facets[j] then
                    M[i][j]:=1;
                end if;
            end for;
        end for;
    end if;
    return Matrix(M);
end intrinsic;

intrinsic VertexFacetHeightMatrix(P::TorPol) -> AlgMatElt
{The vertex-facet height matrix of the polyhedron P (where the i,j-th entry is equal to the height of the i-th vertex over the j-th facet).}
    if Dimension(P) le 0 then
        return Matrix(Integers(),NumberOfVertices(P),0,[Integers()|]);
    end if;
    vertices:=Vertices(P);
    ineqs,k:=Inequalities(P);
    M:=[PowerSequence(Rationals())|];
    for j in [1..k] do
        u:=ineqs[j][1];
        h:=ineqs[j][2];
        Append(~M,[Rationals() | u * v - h : v in vertices]);
    end for;
    bool,MM:=CanChangeUniverse(M,PowerSequence(Integers()));
    if bool then M:=MM; end if;
    return Matrix(M);
end intrinsic;

intrinsic Inequalities(P::TorPol) -> SeqEnum[Tup],RngIntElt
{The defining inequalities of the polyhedron P. These are given as a sequence of pairs <v,h>, where the first element v lies in the dual to the ambient toric lattice containing P and the second element h is an integer, such that v * u >= h is a supporting half-space of P. Also gives an integer k such that the first k inequalities correspond to the facets of P, and the remaining inequalities cut out the subspace containing P.}
    h1,h2:=amb_partition_halfspaces_by_task(P);
    return [CartesianProduct(Dual(Ambient(P)),Integers()) |
                <hs[1][1] * hs[2], hs[1][2] * hs[2]> : hs in h1]
       cat [CartesianProduct(Dual(Ambient(P)),Integers()) |
                <hs[1][1] * hs[2], hs[1][2] * hs[2]> : hs in h2], #h1;
end intrinsic;

intrinsic SupportingCone(P::TorPol,v::TorLatElt) -> TorCon
{The cone C such that C + v is a supporting cone of the polyhedron P, where v is a vertex of P}
    // Is the supporting cone cached?
    ng:=amb_neighbourly_graph(P);
    idx:=Index(ng[1],v);
    require idx ne 0: "The lattice point must be a vertex of the polyhedron";
    if assigned P`amb_supporting_cones then
        if IsDefined(P`amb_supporting_cones,idx) then
            return P`amb_supporting_cones[idx];
        end if;
    else
        P`amb_supporting_cones:=[PowerStructure(TorCon)|];
    end if;
    // We missed the cache -- need to create the cone
    if IsPolytope(P) then
        // If this is a polytope we lift the cone from the finite part
        trans,emb:=fp_emb_map(P);
        CC:=fp_get_cone_at_pullback_vertex(P,(v - trans) @@ emb);
        C:=Image(emb,CC);
        C`cone_in_sublattice:=CC;
        C`cone_in_sublattice_map:=emb;
    else
        // Otherwise we make it from scratch
        Hs:=ng_facets_containing_point(ng,v);
        C:=ConeWithInequalities([Dual(Parent(v)) | h[1][1] * h[2] : h in Hs]);
    end if;
    // Cache the cone and return
    P`amb_supporting_cones[idx]:=C;
    return C;
end intrinsic;

intrinsic IsSupportingHyperplane(v::TorLatElt,h::RngIntElt,P::TorPol)
    -> BoolElt,RngIntElt
{}
    return IsSupportingHyperplane(v,Rationals()!h,P);
end intrinsic;

intrinsic IsSupportingHyperplane(v::TorLatElt,h::FldRatElt,P::TorPol)
    -> BoolElt,RngIntElt
{True iff the hyperplane defined by v * u = h is a supporting hyperplane of the polyhedron P. If so, also gives the sign o such the hyperplane is a support of P (i.e. o in \{-1,0,+1\} such that Sign(v * u - h) is either 0 or o for all u in P). If P is contained within the hyperplane, then o will be 0.}
    require IsInDual(v,Ambient(P)):
        "Argument 1 must lie in the dual to the ambient lattice of argument 3";
    orientation:=0;
    found:=false;
    // Calculate the orientation of the finite part
    for s in amb_get_fp_generating_points(P) do
        cmp:=Sign(s * v - h);
        if cmp eq 0 then
            found:=true;
        else
            if orientation eq 0 then
                orientation:=cmp;
            elif orientation ne cmp then
                return false,_;
            end if;
        end if;
    end for;
    // Is this a supporting hyperplane?
    if not found then
        return false,_;
    end if;
    // Do we need to take account of the infinite part?
    if not IsPolytope(P) then
        for s in RGenerators(InfinitePart(P)) do
            cmp:=Sign(s * v);
            if cmp ne 0 then
                if orientation eq 0 then
                    orientation:=cmp;
                elif orientation ne cmp then
                    return false,_;
                end if;
            end if;
        end for;
    end if;
    // Return the result
    return true,orientation;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Point membership
/////////////////////////////////////////////////////////////////////////

intrinsic 'in'(Q::TorLatElt, P::TorPol) -> BoolElt
{True iff the point Q lies in the interior of the polyhedron P}
    require Q in Ambient(P):
        "Argument 1 must live in the ambient of argument 2";
    return &and[point_in_halfspace(halfspace,Q) :
                                halfspace in amb_get_halfspaces(P)];
end intrinsic;

intrinsic IsInInterior(Q::TorLatElt, P::TorPol) -> BoolElt
{True iff the point Q lies strictly in the relative interior of the polyhedron P}
    require Q in Ambient(P):
        "Argument 1 must live in the ambient of argument 2";
    facets,subspace:=amb_partition_halfspaces_by_task(P);
    return &and[point_strictly_in_halfspace(halfspace,Q) : halfspace in facets]
              and &and[point_in_halfspace(halfspace,Q) : halfspace in subspace];
end intrinsic;

intrinsic IsOnBoundary(Q::TorLatElt, P::TorPol) -> BoolElt
{True iff the point Q lies on the relative boundary of the polyhedron P}
    require Q in Ambient(P):
        "Argument 1 must live in the ambient of argument 2";
    facets,subspace:=amb_partition_halfspaces_by_task(P);
    boundary:=false;
    for halfspace in facets do
        cmp:=cmp_hyperplane_and_point(halfspace[1],Q);
        if cmp eq 0 then
            boundary:=true;
        elif cmp ne halfspace[2] then
            return false;
        end if;
    end for;
    return boundary and
                  &and[point_in_halfspace(halfspace,Q) : halfspace in subspace];
end intrinsic;
