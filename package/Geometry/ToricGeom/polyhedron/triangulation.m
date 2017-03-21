freeze;

/////////////////////////////////////////////////////////////////////////
// triangulation.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38132 $
// $Date: 2012-04-12 21:15:25 +1000 (Thu, 12 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates a triangulation of the finite part of a polyhedron.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// We define a "triangulation" as a set of disjoint simplices such that
// their union equals the finite part of a polyhedron P.
// Simplices are presented in terms of the indices of the corresponding
// vertices in the vertex sequence. For example, {1,2,3} corresponds to:
//      {vertices[1],vertices[2],vertices[3]}.
// Thus a triangulation of:
//      [(0,0),(1,0),(1,1),(0,1)]
// is represent by the set:
//      {{1,2,3},{1,3,4}}.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": mapping_of_sequences;
import "convexhull/sublattice.m": fp_emb_has_volume_form;
import "convexhull/convexhull.m": fp_get_dimension, fp_neighbourly_graph, fp_facet_indices, fp_get_pullback_vertices, fp_get_pullback_halfspaces;
import "convexhull/neighbourlygraph.m": ng_facet_indices, ng_remove_point, ng_points, ng_points_in_facet;

declare attributes TorPol:
    fp_triangulation,       // A triangulation of the finite part of P
    poly_triangulation,     // The triangulation as polyhedra
    fp_boundary_triang,     // A triangulation of the boundary of P
    poly_boundary_triang,   // The trinagulation as polyhedra
    fp_volume,              // The normalised volume of the finite part of P
    fp_boundary_volume;     // The normalised volume of the boundary of the
                            // finite part of P

/////////////////////////////////////////////////////////////////////////
// Zero, one- and two-dimensional triangulation
/////////////////////////////////////////////////////////////////////////

// Returns the triangulation for a point
function triangulation_dimension_0(P)
    return {PowerSet(Integers()) | {Integers() | 1}};
end function;

// Returns the triangulation for a line segment.
function triangulation_dimension_1(P)
    return {PowerSet(Integers()) | {Integers() | 1,2}};
end function;

// Returns a triangulation for a polygon.
function triangulation_dimension_2(P)
    edges:=fp_facet_indices(P);
    apex:=Representative(edges[1]);
    Remove(~edges,1);
    T:={PowerSet(Integers())|};
    for edge in edges do
        if not apex in edge then
            Include(~T,Include(edge,apex));
        end if;
    end for;
    return T;
end function;

/////////////////////////////////////////////////////////////////////////
// Higher-dimensional triangulation
/////////////////////////////////////////////////////////////////////////

// General polytope triangulation algorithm (actually works on the neighbourly
// graph as a representation of the polytope). The idea is simple: remove a
// vertex from P such that the resulting polytope P' is still of maximal
// dimension, noting the new facets created. Recursively triangulate P', then
// calculate the triangulation over the triangulations of the new facets.
// Merge the two and we're done.
function triangulation_recursive(ng,d)
    // First check that the data doesn't describe a simplex
    vertices:=ng_points(ng);
    if #vertices eq d + 1 then
        return {PowerSet(Integers()) | {1..d + 1}};
    end if;
    // Pick a vertex so that the convex hull of the remaining vertices is still
    // d dimensional
    idx:=0;
    repeat
        idx+:=1;
        S:=Remove(vertices,idx);
        v:=Representative(S);
        d_new:=Rank(Matrix(Rationals(),[s - v : s in S]));
    until d_new eq d;
    // Get the new facets created by removing this vertex and calculate its
    // triangulation (i.e. of P\v)
    ng_remove_point(~ng,vertices[idx],~facets);
    triangulation:=$$(ng,d);
    // We removed the 'idx' vertex, so any indices >= idx are out by one in the
    // triangulation. Correct for this.
    mapping:=[Integers() | i : i in [1..#vertices] | i ne idx];
    triangulation:={PowerSet(Integers()) |
           {Integers() | mapping[i] : i in simplex} : simplex in triangulation};
    // Convert the new facets to sets of vertex indices
    facets:={PowerSet(Integers()) | {Integers() | Index(vertices,v) :
                          v in ng_points_in_facet(ng,facet)} : facet in facets};
    // Extract the triangulations of the new facets
    facettri:={PowerSet(Integers()) | simplex meet facet :
                                     facet in facets, simplex in triangulation};
    // The triangulation for P is given by the triangulation for P\v plus the
    // triangulations over the new facets
    return triangulation join {PowerSet(Integers()) | Include(tri,idx) :
                                                   tri in facettri | #tri eq d};
end function;

function triangulation_dimension_general(P)
    // It's possible that computing the neighbourly graph calculates the
    // triangulation, so we check for that
    ng:=fp_neighbourly_graph(P);
    if assigned P`fp_triangulation then return P`fp_triangulation; end if;
    return triangulation_recursive(ng,fp_get_dimension(P));
end function;

/////////////////////////////////////////////////////////////////////////
// Calculate triangulation
/////////////////////////////////////////////////////////////////////////

// Calculates a triangulation for the finite part of the polyhedron, taking a
// different approach depending on the dimension. The resulting boundary
// triangulation is stored in P`fp_triangulation.
procedure calculate_triangulation(P)
    if not assigned P`fp_triangulation then
        // Get the dimension
        dim:=fp_get_dimension(P);
        // Calculate the triangulation
        if dim eq 0 then
            P`fp_triangulation:=triangulation_dimension_0(P);
        elif dim eq 1 then
            P`fp_triangulation:=triangulation_dimension_1(P);
        elif dim eq 2 then
            P`fp_triangulation:=triangulation_dimension_2(P);
        else
            P`fp_triangulation:=triangulation_dimension_general(P);
        end if;
    end if;
end procedure;

// Calculates a triangulation of the boundary for the finite part of the
// polyhedron, taking a different approach depending on the dimension. The
// resulting boundary triangulation is stored in P`fp_boundary_triang.
procedure calculate_triangulation_of_boundary(P)
    if not assigned P`fp_boundary_triang then
        // Get the facet indexes
        facetidxs:=fp_facet_indices(P);
        // Calculate the boundary triangulation
        if IsSimplicial(P) then
            P`fp_boundary_triang:=SequenceToSet(facetidxs);
        else
            // Calculate the boundary triangulation by intersecting the facets
            // with the triangulation
            calculate_triangulation(P);
            d:=fp_get_dimension(P);
            boundary_triang:={PowerSet(Integers()) |
                                  facet meet simplex : facet in facetidxs,
                                  simplex in P`fp_triangulation};
            P`fp_boundary_triang:={PowerSet(Integers()) | triang :
                                  triang in boundary_triang | #triang eq d};
        end if;
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure triangulation_apply_translation(P,CP,Q)
    if assigned P`fp_triangulation then
        CP`fp_triangulation:=P`fp_triangulation; end if;
    if assigned P`poly_triangulation then
        CP`poly_triangulation:={PP + Q : PP in P`poly_triangulation}; end if;
    if assigned P`fp_boundary_triang then
        CP`fp_boundary_triang:=P`fp_boundary_triang; end if;
    if assigned P`poly_boundary_triang then
        CP`poly_boundary_triang:={PP + Q :PP in P`poly_boundary_triang}; end if;
    if assigned P`fp_volume and
        (IsIntegral(Q) or fp_get_dimension(P) eq Dimension(Ambient(P))) then
        CP`fp_volume:=P`fp_volume; end if;
    if assigned P`fp_boundary_volume and IsIntegral(Q) then
        CP`fp_boundary_volume:=P`fp_boundary_volume; end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure triangulation_apply_negation(P,CP)
    if assigned P`fp_triangulation then
        CP`fp_triangulation:=P`fp_triangulation; end if;
    if assigned P`poly_triangulation then
        CP`poly_triangulation:={-Q : Q in P`poly_triangulation}; end if;
    if assigned P`fp_boundary_triang then
        CP`fp_boundary_triang:=P`fp_boundary_triang; end if;
    if assigned P`poly_boundary_triang then
        CP`poly_boundary_triang:={-Q : Q in P`poly_boundary_triang}; end if;
    if assigned P`fp_volume then
        CP`fp_volume:=P`fp_volume; end if;
    if assigned P`fp_boundary_volume then
        CP`fp_boundary_volume:=P`fp_boundary_volume; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure triangulation_apply_dilation(P,CP,k)
    if assigned P`fp_triangulation then
        CP`fp_triangulation:=P`fp_triangulation; end if;
    if assigned P`poly_triangulation then
        CP`poly_triangulation:={k * Q : Q in P`poly_triangulation}; end if;
    if assigned P`fp_boundary_triang then
        CP`fp_boundary_triang:=P`fp_boundary_triang; end if;
    if assigned P`poly_boundary_triang then
        CP`poly_boundary_triang:={k * Q : Q in P`poly_boundary_triang}; end if;
    if assigned P`fp_volume and assigned P`fp_dimension and
        (P`fp_dimension eq Dimension(Ambient(P)) or
        (assigned P`sub_origin and IsIntegral((k - 1) * P`sub_origin))) then
        CP`fp_volume:=(k^P`fp_dimension) * P`fp_volume; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure triangulation_change_ambient(P,CP,L)
    if assigned P`fp_triangulation then
        CP`fp_triangulation:=P`fp_triangulation; end if;
    if assigned P`poly_triangulation then
        CP`poly_triangulation:={ChangeAmbient(Q,L) : Q in P`poly_triangulation};
    end if;
    if assigned P`fp_boundary_triang then
        CP`fp_boundary_triang:=P`fp_boundary_triang; end if;
    if assigned P`poly_boundary_triang then
        CP`poly_boundary_triang:={ChangeAmbient(Q,L) :
                                                   Q in P`poly_boundary_triang};
    end if;
    if assigned P`fp_volume then
        CP`fp_volume:=P`fp_volume; end if;
    if assigned P`fp_boundary_volume then
        CP`fp_boundary_volume:=P`fp_boundary_volume; end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure triangulation_change_to_maximal(P,CP,emb,trans)
    if assigned P`fp_triangulation then
        CP`fp_triangulation:=P`fp_triangulation; end if;
    if assigned P`fp_boundary_triang then
        CP`fp_boundary_triang:=P`fp_boundary_triang; end if;
    if assigned P`fp_volume then
        CP`fp_volume:=P`fp_volume; end if;
    if assigned P`fp_boundary_volume then
        CP`fp_boundary_volume:=P`fp_boundary_volume; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Delaunay Mesh
/////////////////////////////////////////////////////////////////////////

// The lifting function used when calculating the Delaunay mesh
function delaunay_lift(v)
    return &+[Rationals() | c^2 : c in Eltseq(v)];
end function;

// Strips away the "top" of the hull and returns the indicies of the
// "bottom" facets.
function remove_upper_hull(d,facets)
    keel:=[Integers()|];
    for i in [1..#facets] do
        val:=Sign(Eltseq(facets[i][1][1])[d]) * facets[i][2];
        if val ge 0 then
            // This facet is on the bottom, so keep it
            Append(~keel,i);
        end if;
    end for;
    return keel;
end function;

// Calculates the Delaunay mesh of the given sequence of lattice points.
function calculate_delaunay_mesh(S)
    // Increase the ambient dimension by one by lifting the points, then
    // calculate the convex hull and extract the data we need
    S:=[PowerSequence(Rationals()) |
            Append(Eltseq(v),delaunay_lift(v)) : v in S];
    D:=Polytope(S);
    d:=fp_get_dimension(D);
    facetidxs:=fp_facet_indices(D);
    // Remove the "top" of the hull -- only the "bottom" is meaningful
    if d eq Dimension(Ambient(D)) then
        keel:=remove_upper_hull(d,fp_get_pullback_halfspaces(D));
        facetidxs:=[PowerSet(Integers()) | facetidxs[i] : i in keel];
    end if;
    // Now, we need to map the vertices of D back onto the lattice points of S;
    // there's no guarantee that the order hasn't changed
    S_D:=[PowerSequence(Rationals()) | Eltseq(v) : v in Vertices(D)];
    mapping:=mapping_of_sequences(S_D,S);
    // Now remap the facet indices and return
    return {PowerSet(Integers()) | {Integers() | mapping[i] : i in facet} :
            facet in facetidxs};
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic DelaunayMesh(S::SeqEnum[SeqEnum[RngIntElt]])
    -> SetEnum[SetEnum[RngIntElt]]
{}
    require not IsEmpty(S): "Sequence must not be empty";
    dim:=#S[1];
    require &and[#v eq dim:v in S]: "Vectors must be of the same dimension";
    F:=calculate_delaunay_mesh(S);
    return F;
end intrinsic;

intrinsic DelaunayMesh(S::SeqEnum[SeqEnum[FldRatElt]])
    -> SetEnum[SetEnum[RngIntElt]]
{}
    require not IsEmpty(S): "Sequence must not be empty";
    dim:=#S[1];
    require &and[#v eq dim:v in S]: "Vectors must be of the same dimension";
    F:=calculate_delaunay_mesh(S);
    return F;
end intrinsic;

intrinsic DelaunayMesh(S::SeqEnum[TorLatElt]) -> SetEnum[SetEnum[RngIntElt]]
{The Delaunay mesh of the lattice points in the sequence S}
    require not IsEmpty(S): "Sequence must not be empty";
    F:=calculate_delaunay_mesh(S);
    return F;
end intrinsic;

intrinsic Triangulation(P::TorPol) -> SetEnum[SetEnum[RngIntElt]]
{A triangulation of the polytope P}
    if not assigned P`poly_triangulation then
        if not assigned P`fp_triangulation then
            require IsPolytope(P): "The polyhedron must be a polytope";
            calculate_triangulation(P);
        end if;
        // Translate the triangulation back into the ambient lattice and build
        // the polytopes
        V:=Vertices(P);
        P`poly_triangulation:={Polytope([Universe(V) | V[i] : i in simplex] :
                            areVertices:=true) : simplex in P`fp_triangulation};
    end if;
    return P`poly_triangulation;
end intrinsic;

intrinsic TriangulationOfBoundary(P::TorPol) -> SetEnum[SetEnum[RngIntElt]]
{A triangulation of the boundary of the polytope P}
    if not assigned P`poly_boundary_triang then
        if not assigned P`fp_boundary_triang then
            require IsPolytope(P): "The polyhedron P must be a polytope";
            require not IsEmpty(P): "The polytope is empty and has no boundary";
            calculate_triangulation_of_boundary(P);
        end if;
        // Translate the triangulation back into the ambient lattice and build
        // the polytopes
        V:=Vertices(P);
        P`poly_boundary_triang:={Polytope([Universe(V) | V[i] : i in triang] :
                           areVertices:=true) : triang in P`fp_boundary_triang};
    end if;
    return P`poly_boundary_triang;
end intrinsic;

intrinsic Volume(P::TorPol) -> FldRatElt
{The normalised volume of the polytope P}
    if not assigned P`fp_volume then
        require IsPolytope(P): "The polyhedron must be a polytope";
        require fp_emb_has_volume_form(P):
            "No volume form exists for the subspace containing the polytope";
        // Get the dimension
        d:=fp_get_dimension(P);
        // Calculate the volume
        if d eq 0 then
            P`fp_volume:=1;
        elif d eq 1 then
            vertices:=fp_get_pullback_vertices(P);
            v:=Eltseq(vertices[2] - vertices[1]);
            P`fp_volume:=Abs(v[1]);
        elif d eq 2 and assigned P`interior_points and IsIntegral(P) then
            // 2-dimensional case where we can use Pick's Theorem (note that
            // we don't worry about whether the boundary points are known, since
            // the number of boundary points is an easy calculation)
            P`fp_volume:=2 * NumberOfInteriorPoints(P) + 
                                                  NumberOfBoundaryPoints(P) - 2;
        else
            // In the general case we sum the volumes of each simplex given by
            // a triangulation.
            // If the Ehrhart series is known, we can use that...
            if not assigned P`fp_triangulation and assigned P`Ehrhart_gen_func
                and IsIntegral(P) then
                vol:=&+EhrhartDeltaVector(P);
            // If P is simplicial we can avoid calculating the triangulation...
            elif not assigned P`fp_triangulation and IsSimplicial(P) then
                vertices:=fp_get_pullback_vertices(P);
                if ContainsZero(P) then
                    bary:=Zero(Universe(vertices));
                else
                    bary:=(&+vertices) / #vertices;
                end if;
                vol:=0;
                for facet in fp_facet_indices(P) do
                    M:=Matrix(Rationals(), [Universe(vertices) |
                                              vertices[i] - bary : i in facet]);
                    vol +:= Abs(Determinant(Matrix(M)));
                end for;
            // If P contains the origin we can avoid the triangulation at the
            // expense of computing the facets as polytopes, so we reserve this
            // for when the number of vertices is large...
            elif not assigned P`fp_triangulation and d ge 3 and
                    (assigned P`amb_facets or NumberOfVertices(P) gt 20) and
                    ContainsZero(P) and
                    &and[IsPrimitive(n[1]) : n in Inequalities(P)] then
                F:=Facets(P);
                I:=Inequalities(P);
                vol:=&+[Volume(F[i]) * Abs(I[i][2]) : i in [1..#F]];
            // If the polytopes of the triangulation are known, we use them...
            elif assigned P`poly_triangulation then
                vol:=&+[Rationals() | Volume(Q) : Q in P`poly_triangulation];
            // Otherwise compute the triangulation and work with that
            else
                if not assigned P`fp_triangulation then
                    calculate_triangulation(P);
                end if;
                vol:=0;
                vertices:=fp_get_pullback_vertices(P);
                for simplex in P`fp_triangulation do
                    o:=Representative(simplex);
                    M:=Matrix(Rationals(), [Universe(vertices) |
                            vertices[i] - vertices[o] : i in simplex | i ne o]);
                    vol +:= Abs(Determinant(Matrix(M)));
                end for;
            end if;
            P`fp_volume:=vol;
        end if;
    end if;
    return P`fp_volume;
end intrinsic;

intrinsic VolumeOfBoundary(P::TorPol) -> FldRatElt
{The normalised volume of the boundary of the polytope P}
    if not assigned P`fp_boundary_volume then
        require IsPolytope(P): "The polyhedron must be a polytope";
        require not IsEmpty(P): "The polytope is empty and has no boundary";
        if Dimension(P) eq 0 then
            P`fp_boundary_volume:=0;
        else
            // Perhaps we can use the Ehrhart polynomial?
            if assigned P`Ehrhart_gen_func and IsIntegral(P) then
                d:=Dimension(P);
                L:=Coefficients(Representative(EhrhartPolynomial(P)));
                P`fp_boundary_volume:=2 * Factorial(d - 1) * L[d];
            // Otherwise calculate the facets
            else
                facets:=Facets(P);
                require &and[fp_emb_has_volume_form(F) : F in facets]:
                    "No volume form exists for one of the subspaces containing a facet of the polytope";
                P`fp_boundary_volume:=&+[Volume(F) : F in facets];
            end if;
        end if;
    end if;
    return P`fp_boundary_volume;
end intrinsic;
