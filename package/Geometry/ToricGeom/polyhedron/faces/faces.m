freeze;

/////////////////////////////////////////////////////////////////////////
// faces.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43190 $
// $Date: 2013-05-17 18:05:36 +1000 (Fri, 17 May 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the faces of a polyhedron.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// General i-dimensional faces are determined by functions in this file,
// along with the faces graph, f-vector, and the generalised h-vector.
// Facets and vertices, however, are determined in support.m.
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": mapping_of_sequences;
import "../../lattice/hyperplane.m": points_on_halfspace_boundary;
import "../convexhull/sublattice.m": in_embedded_lattice;
import "../isomorphism/isomorphism.m": labeled_graph;
import "../coneembedding.m": ce_get_cone, ce_normalised_cone, ce_get_embedding, ce_get_origin;
import "support.m": amb_facet_indices, amb_get_fp_generating_points, amb_partition_halfspaces_by_task;

declare attributes TorPol:
    faces_known,       // The value such that all i-faces indices for
                       // i >= faces_known have been calculated.
    faces_indices,     // A sequence of sequences of sets of indicies of
                       // vertices; the i-th set describes the i-faces.
    faces_seq,         // A sequence of sequences of polyhedra; the (i+1)-th
                       // sequence gives the i-faces. NOTE THE SHIFT!
    faces_lattice,     // A sequence of sequences representing the face lattice,
                       // where the (i,j) entry is the set of indices of the
                       // (i-2)-faces of the j-th (i-1)-face. NOTE THE SHIFTS!
    faces_auts,        // The automorphism group (as a subgroup of GL(n,Z))
    faces_f_vector,    // The f-vector of P
    faces_h_vector;    // The h-vector of P

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true iff the i-faces are known. If true, then also returns the
// sequence of i-faces. Note that this does not calculate the i-faces if they
// are not known.
// Note: i must be in the range 0 <= i <= Dimension(P).
function faces_known(P,i)
    // Basic sanity check
    d:=Dimension(P);
    assert i ge 0 and i le d;
    // There are two special cases to take care of first
    if i eq d then
        return true,[P];
    elif i eq d - 1 then
        if assigned P`amb_facets then return true,P`amb_facets;
        else return false,_; end if;
    end if;
    // Now for the more general case
    if not assigned P`faces_seq then
        return false,_;
    else
        if IsDefined(P`faces_seq,i + 1) then return true,P`faces_seq[i + 1];
        else return false,_; end if;
    end if;
end function;

// Returns true if the indices of vertices for the i-faces of a polytope P are
// known. If true, also returns the indices. Note that this does not calculate
// the indices if they are not known.
// Note: i must be in the range 1 <= i <= Dimension(P) - 2.
function faces_indices_known(P,i)
    assert i le Dimension(P) - 2 and i ge 1;
    if assigned P`faces_known and P`faces_known le i then
        return true,P`faces_indices[i];
    end if;
    return false,_;
end function;

// Computes the indices of vertices for the i-faces of a polytope P.
// Note: This function is for polytopes ONLY. The indices given correspond to
// the sequence of vertices of P.
// Note: i must be in the range 1 <= i <= Dimension(P) - 2.
function faces_compute_indices(P,i)
    // Basic sanity checks
    assert i le Dimension(P) - 2 and i ge 1;
    // Perhaps we already know the result?
    if not assigned P`faces_known then
        P`faces_known:=Dimension(P) - 1;
    elif P`faces_known le i then
        return P`faces_indices[i];
    end if;
    // We need the indices of the (i+1)-faces to work with
    faces:=i eq Dimension(P) - 2 select amb_facet_indices(P)
                                   else $$(P,i + 1);
    // Partition the (i+1)-faces into simplices and non-simplices. Simplices are
    // much better because we know their relative facets.
    faces_indices:=&join {PowerSet(PowerSet(Integers())) | Subsets(S,i + 1) :
                                                      S in faces | #S eq i + 2};
    // For the non-simplicial faces we need to compute the dimension of each
    // pair-wise intersections of the (i+1)-faces, and keep the i-dim ones
    faces:={PowerSet(Integers()) | S : S in faces | #S ne i + 2};
    if #faces ne 0 then
        verts:=Vertices(P);
        for face in {&meet S : S in Subsets(faces,2)} diff faces_indices do
            if #face gt i then
                v:=verts[Representative(face)];
                if Rank(Matrix(Rationals(),
                             [Ambient(P) | verts[j] - v : j in face])) eq i then
                    Include(~faces_indices,face);
                end if;
            end if;
        end for;
    end if;
    // Record the data and return the indices of the i-faces
    P`faces_known:=i;
    if not assigned P`faces_indices then
        P`faces_indices:=[PowerSequence(PowerSet(Integers()))|];
    end if;
    P`faces_indices[i]:=Setseq(faces_indices);
    return P`faces_indices[i];
end function;

// Returns the sequence of i-faces of the polytope P.
// Note: This function performs the necessary computation for polytopes ONLY,
// and is more efficient that the more general polyhedron case.
// Note: i must be in the range 1 <= i <= Dimension(P) - 2.
function faces_compute_polytope(P,i)
    // Basic sanity checks
    assert i le Dimension(P) - 2 and i ge 1;
    // Get the data we'll need to create the i-faces
    vertices:=Vertices(P);
    faceindices:=faces_compute_indices(P,i);
    faces:=[PowerStructure(TorPol)|];
    // We want to reuse as much data as possible, so first we walk through
    // those (i+1)-faces that already know their facet polytopes
    bool,iplus1faces:=faces_known(P,i);
    if bool then
        for j in [1..#iplus1faces] do
            if assigned iplus1faces[j]`amb_facets then
                // Create the map between the vertices of this (i+1)-face and P
                m:=mapping_of_sequences(Vertices(iplus1faces[j]),vertices);
                // Start working through the facets of this face
                facetidxs:=amb_facet_indices(iplus1faces[j]);
                for k in [1..#facetidxs] do
                    idx:=Index(faceindices,
                                       {Integers() | m[l] : l in facetidxs[k]});
                    // If the face is already known, exchange it, otherwise
                    // record it
                    if IsDefined(faces,idx) then
                        iplus1faces[j]`amb_facets[k]:=faces[idx];
                    else
                        faces[idx]:=iplus1faces[j]`amb_facets[k];
                    end if;
                end for;
            end if;
        end for;
    end if;
    // Now we create the i-faces that haven't been computed
    for j in [1..#faceindices] do
        if not IsDefined(faces,j) then
            faces[j]:=Polytope([Ambient(P) | vertices[k] : k in faceindices[j]]:
                                                             areVertices:=true);
        end if;
    end for;
    // Finally we update those (i+1)-faces that don't know their facet polytopes
    if bool then
        for j in [1..#iplus1faces] do
            if not assigned iplus1faces[j]`amb_facets then
                // Create the map between the vertices of this (i+1)-face and P
                m:=mapping_of_sequences(Vertices(iplus1faces[j]),vertices);
                // Do we need to teach this face what its facet indices are?
                if not assigned iplus1faces[j]`amb_facet_idxs then
                    vertidxs:={Integers() | Index(vertices,v) :
                                                 v in Vertices(iplus1faces[j])};
                    iplus1faces[j]`amb_facet_idxs:=[PowerSet(Integers()) |
                          {Index(m,l) : l in indices} : indices in faceindices |
                          indices subset vertidxs];
                end if;
                // Tell it the facet polytopes
                iplus1faces[j]`amb_facets:=[PowerStructure(TorPol) |
                   faces[Index(faceindices,{Integers() | m[l] : l in indices})]:
                   indices in amb_facet_indices(iplus1faces[j])];
            end if;
        end for;
    end if;
    // Return the i-faces
    return faces;
end function;

// Returns the sequence of i-faces of the polyhedron P.
// Note: i must be in the range 1 <= i <= Dimension(P) - 2.
function faces_compute_polyhedron(P,i)
    // Basic sanity checks
    assert i le Dimension(P) - 2 and i ge 1;
    // We perform the calculation on the normalised cone
    faces:=[PowerStructure(TorPol)|];
    for F in Faces(NormalisedCone(P),i + 1) do
        PF:=Polyhedron(F);
        if not IsEmpty(PF) then
            Append(~faces,ChangeAmbient(PF,Ambient(P)));
        end if;
    end for;
    // Return the data
    return faces;
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the faces, but we do copy the face indices.
procedure faces_apply_translation(P,CP,Q)
    if assigned P`faces_indices then
        CP`faces_indices:=P`faces_indices;
        if assigned P`faces_known then
            CP`faces_known:=P`faces_known; end if;
        if assigned P`faces_lattice then
            CP`faces_lattice:=P`faces_lattice; end if;
    end if;
    if assigned P`faces_f_vector then
        CP`faces_f_vector:=P`faces_f_vector; end if;
    if assigned P`faces_h_vector then
        CP`faces_h_vector:=P`faces_h_vector; end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the faces, but we do copy the face indices.
procedure faces_apply_negation(P,CP)
    if assigned P`faces_indices then
        CP`faces_indices:=P`faces_indices;
        if assigned P`faces_known then
            CP`faces_known:=P`faces_known; end if;
        if assigned P`faces_lattice then
            CP`faces_lattice:=P`faces_lattice; end if;
    end if;
    if assigned P`faces_auts then
        CP`faces_auts:=P`faces_auts; end if;
    if assigned P`faces_f_vector then
        CP`faces_f_vector:=P`faces_f_vector; end if;
    if assigned P`faces_h_vector then
        CP`faces_h_vector:=P`faces_h_vector; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the faces, but we do copy the face indices.
procedure faces_apply_dilation(P,CP,k)
    if assigned P`faces_indices then
        CP`faces_indices:=P`faces_indices;
        if assigned P`faces_known then
            CP`faces_known:=P`faces_known; end if;
        if assigned P`faces_lattice then
            CP`faces_lattice:=P`faces_lattice; end if;
    end if;
    if assigned P`faces_auts then
        CP`faces_auts:=P`faces_auts; end if;
    if assigned P`faces_f_vector then
        CP`faces_f_vector:=P`faces_f_vector; end if;
    if assigned P`faces_h_vector then
        CP`faces_h_vector:=P`faces_h_vector; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the faces, but we do copy the face indices.
procedure faces_change_ambient(P,CP,L)
    if assigned P`faces_indices then
        CP`faces_indices:=P`faces_indices;
        if assigned P`faces_known then
            CP`faces_known:=P`faces_known; end if;
        if assigned P`faces_lattice then
            CP`faces_lattice:=P`faces_lattice; end if;
    end if;
    if assigned P`faces_auts then
        CP`faces_auts:=P`faces_auts; end if;
    if assigned P`faces_f_vector then
        CP`faces_f_vector:=P`faces_f_vector; end if;
    if assigned P`faces_h_vector then
        CP`faces_h_vector:=P`faces_h_vector; end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
// Note: We deliberately don't bother copying across the polyhedral descriptions
// of the faces, but we do copy the face indices.
procedure faces_change_to_maximal(P,CP,emb,trans)
    if assigned P`faces_indices then
        CP`faces_indices:=P`faces_indices;
        if assigned P`faces_known then
            CP`faces_known:=P`faces_known; end if;
        if assigned P`faces_lattice then
            CP`faces_lattice:=P`faces_lattice; end if;
    end if;
    if assigned P`faces_f_vector then
        CP`faces_f_vector:=P`faces_f_vector; end if;
    if assigned P`faces_h_vector then
        CP`faces_h_vector:=P`faces_h_vector; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Faces(P::TorPol) -> SeqEnum[SeqEnum[TorPol]]
{A sequence of sequences of polyhedra, where the (i + 1)-th sequence contains the i-dimensional faces of the polyhedron P}
    return [Faces(P,i) : i in [0..Dimension(P)]];
end intrinsic;

intrinsic Faces(P::TorPol,i::RngIntElt) -> SeqEnum[TorPol]
{The sequence of i-dimensional faces of the polyhedron P}
    // Get the easy cases out of the way
    d:=Dimension(P);
    if i gt d or i lt -1 then return [PowerStructure(TorPol)|];
    elif i eq -1 then return [EmptyPolyhedron(Ambient(P))];
    elif i eq d then return [P];
    elif i eq d - 1 then return Facets(P); end if;
    // If necessary, calculate the face data
    if not assigned P`faces_seq then
        P`faces_seq:=[PowerSequence(PowerStructure(TorPol))|];
    end if;
    if not IsDefined(P`faces_seq,i + 1) then
        if i eq 0 then
            P`faces_seq[1]:=[PowerStructure(TorPol) |
                                Polytope([v] : areVertices:=true) :
                                v in Vertices(P)];
        else
            P`faces_seq[i+1]:=IsPolytope(P) select faces_compute_polytope(P,i)
                                            else faces_compute_polyhedron(P,i);
        end if;
    end if;
    // Return the sequence of faces
    return P`faces_seq[i+1];
end intrinsic;

intrinsic Edges(P::TorPol) -> SeqEnum[TorPol]
{The sequence of edges of the polyhedron P}
    return Faces(P,1);
end intrinsic;

intrinsic FaceIndices(P::TorPol,i::RngIntElt) -> SeqEnum[SetEnum[RngIntElt]]
{A sequence of sets describing the i-dimensional faces of the polytope P. The j-th set gives the indices of the vertices of P which define the j-th i-dimensional face of P.}
    // Sanity checks
    require IsPolytope(P): "Polyhedron must be a polytope";
    // Some dimensions are special cases...
    d:=Dimension(P);
    if i gt d or i lt -1 then return [PowerSet(Integers())|];
    elif i eq -1 then return [PowerSet(Integers()) | {Integers()|}];
    elif i eq d then return [PowerSet(Integers()) | {1..NumberOfVertices(P)}];
    elif i eq d - 1 then return amb_facet_indices(P);
    elif i eq 0 then return [PowerSet(Integers()) | {i} :
                                               i in [1..NumberOfVertices(P)]];
    else return faces_compute_indices(P,i); end if;
end intrinsic;

intrinsic EdgeIndices(P::TorPol) -> SeqEnum[SetEnum[RngIntElt]]
{A sequence of sets describing the edges of the polytope P}
    require IsPolytope(P): "Polyhedron must be a polytope";
    return FaceIndices(P,1);
end intrinsic;

intrinsic NumberOfFaces(P::TorPol,i::RngIntElt) -> RngIntElt
{The number of i-dimensional faces of the polyhedron P}
    // Get the easy cases out of the way
    d:=Dimension(P);
    if i gt d or i lt -1 then return 0;
    elif i eq d or i eq -1 then return 1;
    elif i eq d - 1 then return NumberOfFacets(P);
    elif i eq 0 then return NumberOfVertices(P); end if;
    // Is the f-vector assigned?
    if assigned P`faces_f_vector then
        return P`faces_f_vector[i+2];
    end if;
    // We'll have to do some work
    if IsPolytope(P) then
        // We try to avoid doing a calculation if we can...
        if i gt 1 and d le 5 and IsSmooth(P) then
            bool,idxs:=faces_indices_known(P,i);
            if bool then
                return #idxs;
            else
                f:=fVector(P);
                return f[i+2];
            end if;
        else
            return #faces_compute_indices(P,i);
        end if;
    else
        // THINK: Surely the normalised cone can answer this question directly?
        return #faces_compute_polyhedron(P,i);
    end if;
end intrinsic;

intrinsic NumberOfEdges(P::TorPol) -> RngIntElt
{The number of edges of the polyhedron P}
    return NumberOfFaces(P,1);
end intrinsic;    

intrinsic Graph(P::TorPol) -> GrphUnd
{The graph of the face lattice of the polyhedron P. The vertices of the graph are labeled by the dimension of the corresponding face of P.}
    if not assigned P`faces_lattice then
        // Build the face lattice as a sequence S of sequences of sets, where
        // S[i+1][j] is the set of indices of (i-1)-faces of P that are facets
        // of the j-th i-face. Note the shift in the index i in S!
        if IsPolytope(P) then
            P`faces_lattice:=[PowerSequence(PowerSet(Integers())) |
                [PowerSet(Integers()) | {Integers() | j : j in [1..#subfaces] |
                subfaces[j] subset face} : face in FaceIndices(P,i)]
                where subfaces:=FaceIndices(P,i - 1) : i in [0..Dimension(P)]];
        else
            // THINK: Surely the normalised cone can answer this question?
            P`faces_lattice:=[PowerSequence(PowerSet(Integers())) |
                [PowerSet(Integers()) | {Integers() | j : j in [1..#subfaces] |
                subfaces[j] subset face} : face in Faces(P,i)]
                where subfaces:=Faces(P,i - 1) : i in [0..Dimension(P)]];
        end if;
    end if;
    // Build the graph from the face lattice
    offset:=[Integers() | 0,1];
    for i in [1..#P`faces_lattice] do
        offset[i + 2]:=offset[i + 1] + #P`faces_lattice[i];
    end for;
    labels:=[-1] cat &cat[PowerSequence(Integers()) | [i - 1 :
                   j in [1..#P`faces_lattice[i]]] : i in [1..#P`faces_lattice]];
    edges:={{j + offset[i + 1],k + offset[i]} : k in P`faces_lattice[i][j],
                     j in [1..#P`faces_lattice[i]], i in [1..#P`faces_lattice]};
    G:=Graph<#labels | edges>;
    AssignVertexLabels(~G,labels);
    // Return the graph
    return G;
end intrinsic;

intrinsic AutomorphismGroup(P::TorPol) -> GrpMat
{The automorphism group of the polyhedron P}
    if not assigned P`faces_auts then
        // Get the labeled face graph and compute the automorphism group
        G:=labeled_graph(P);
        Gp:=AutomorphismGroup(G);
        // Note the vertices and number of vertices
        vrts:=Vertices(P);
        nv:=#vrts;
        // Extract the subgroup of automorphisms on P, and the corresponding
        // elements in GL(n,Z)
        src:=Transpose(Matrix(Rationals(),vrts));
        subGp:=sub<Gp | Identity(Gp)>;
        gl:=GL(Dimension(Ambient(P)),Integers());
        autGp:=sub<gl | Identity(gl)>;
        for elt in Gp do
            if not elt in subGp then
                // We want to extract the maps on the vertices
                vrtmp:=[Integers() | i : i in Eltseq(elt)[1..nv]];
                bool,M:=IsConsistent(src,Transpose(Matrix(Rationals(),
                                     [Universe(vrts) | vrts[i] : i in vrtmp])));
                if bool then
                    bool,M:=IsCoercible(gl,RowSequence(Transpose(M)));
                    if bool then
                        autGp:=sub<gl | autGp,M>;
                        subGp:=sub<Gp | subGp,elt>;
                    end if;
                end if;
            end if;
        end for;
        // Record the automorphism group
        P`faces_auts:=autGp;
    end if;
    // Return the automorphism group
    return P`faces_auts;
end intrinsic;

intrinsic IsFace(P::TorPol,F::TorPol) -> BoolElt
{True iff F is a face of the polyhedron P}
    // Do the cheap tests first
    if Ambient(F) ne Ambient(P) then
        return false; end if;
    if IsPolytope(P) and not IsPolytope(F) then
        return false; end if;
    Fverts:=Seqset(Vertices(F));
    Pgens:=Seqset(amb_get_fp_generating_points(P));
    if not Fverts subset Pgens then
        return false; end if;
    Hs:=amb_partition_halfspaces_by_task(P);
    if not &or[points_on_halfspace_boundary(H,Fverts) : H in Hs] then
        // It's possible that F eq P
        return F eq P;
    end if;
    // Now we have to actually do a little work
    _,Ss:=amb_partition_halfspaces_by_task(F);
    if not &and[v in Fverts : v in Pgens | in_embedded_lattice(F,v)] then
        return false; end if;
    // If P is a polytope then we now know that F is a face
    if IsPolytope(P) then
        return true; end if;
    // The final check is a real drag...
    face:=ce_normalised_cone(F,ce_get_embedding(P),ce_get_origin(P));
    return IsFace(ce_get_cone(P),face);
end intrinsic;

intrinsic fVector(P::TorPol) -> SeqEnum[RngIntElt]
{The f-vector (f_-1,f_0,...,f_d) of the d-dimensional polyhedron P}
    if not assigned P`faces_f_vector then
        d:=Dimension(P);
        // There are some special cases in which we know the f-vector.
        if d le 2 then
            case d:
                when -1:
                    P`faces_f_vector:=[Integers() | 1];
                when 0:
                    P`faces_f_vector:=[Integers() | 1,1];
                when 1:
                    P`faces_f_vector:=[Integers() | 1,2,1];
                when 2:
                    n:=NumberOfVertices(P);
                    P`faces_f_vector:=[Integers() | 1,n,n,1];
            end case;
        // For low-dimensional smooth polytopes we know the answer. See:
        // G.Hegedus and A.M.Kasprzyk, "The boundary volume of a lattice
        // polytope", arXiv:1002.2815v2 [math.CO]
        elif d le 5 and IsSmooth(P) then
            case d:
                when 3:
                    n:=NumberOfVertices(P);
                    P`faces_f_vector:=[Integers() | 1, n, 3*n-6, 2*n-4, 1];
                when 4:
                    n:=NumberOfVertices(P);
                    m:=NumberOfEdges(P) + n;
                    P`faces_f_vector:=[Integers()|1, n, m-n, 2*m-4*n, m-2*n, 1];
                when 5:
                    n:=NumberOfVertices(P);
                    m:=NumberOfEdges(P) + n;
                    P`faces_f_vector:=[Integers() | 1, n, m-n, 4*m-14*n+20,
                                                    5*m-20*n+30, 2*m-8*n+12, 1];
            end case;
        // Otherwise we'll have to do some calculations
        else
            P`faces_f_vector:=[Integers() | NumberOfFaces(P,i) : i in [-1..d]];
        end if;
    end if;
    return P`faces_f_vector;
end intrinsic;

intrinsic fPolynomial(P::TorPol) -> RngUPolElt
{The f-polynomial of the polyhedron P}
    f:=fVector(P);
    R:=PolynomialRing(Rationals());
    x:=R.1;
    return &+[R | f[i] * x^(#f - i) : i in [1..#f]];
end intrinsic;

intrinsic hVector(P::TorPol) -> SeqEnum[RngIntElt]
{The h-vector of the simplicial polytope P}
    if not assigned P`faces_h_vector then
        require IsPolytope(P) and IsSimplicial(P):
            "The polyhedron must be a simplicial polytope";
        d:=Dimension(P);
        f:=fVector(P);
        P`faces_h_vector:=[&+[Binomial(d-j,d-i) * (-1)^(i-j) * f[j-1+2] :
                                                    j in [0..i]] : i in [0..d]];
    end if;
    return P`faces_h_vector;
end intrinsic;

intrinsic hPolynomial(P::TorPol) -> SeqEnum[RngIntElt]
{The h-polynomial of the simplicial polytope P}
    require IsPolytope(P) and IsSimplicial(P):
            "The polyhedron must be a simplicial polytope";
    h:=hVector(P);
    R:=PolynomialRing(Rationals());
    x:=R.1;
    return &+[R | h[i] * x^(#h - i) : i in [1..#h]];
end intrinsic;
