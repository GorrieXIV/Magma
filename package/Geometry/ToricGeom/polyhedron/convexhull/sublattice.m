freeze;

/////////////////////////////////////////////////////////////////////////
// sublattice.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42129 $
// $Date: 2013-02-16 06:27:29 +1100 (Sat, 16 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for dealing with the pull-back of the finite part P of a
// polyhedron into a sublattice L' such that P is of maximal dimension
// in L'.
/////////////////////////////////////////////////////////////////////////
// Notes
// =====
// A polytope P in a lattice L is not, in general, of maximal dimension.
// It's much easier to work with a maximal dimensional polytope, thus we
// construct a sublattice L' -> L embedding via:
//    L' \rightarrow L
//    u  \mapsto     emb(u) + trans
// where 'trans' is a translation, and 'emb' a lattice map.
//
// Note that as described this procedure isn't well defined! It's entirely
// possible for the subspace containing P to NOT contain any lattice points.
// For example, the triangle:
//    P = conv{ (1/2,1,0), (1/2,0,1), (1/2,-1,-1) }.
// When this is the case we translate P so that it is contained in some
// sublattice of L (in practice we translate the first vertex to the origin)
// and proceed from there. But we have to be careful to note that we've done
// this, since concepts such as volume are defined relative to the sublattice
// L'. Thus we set "sub_is_lattice" to be false to alert us to this case.
//
// This file contains only functions intended for internal use.
/////////////////////////////////////////////////////////////////////////

import "../../lattice/hyperplane.m": to_hyperplane, hyperplane_translation, hyperplane_negation, hyperplane_change_ambient;
import "../../lattice/lattice.m": lattice_from_cache;
import "../faces/support.m": amb_get_fp_generating_points;

declare attributes TorPol:
    sub_hyperplanes,        // The hyperplanes cutting out the subspace
    sub_is_lattice,         // True iff the containing subspace is a lattice
    sub_origin,             // The translation ('trans' above)
    sub_embedding;          // The embedding map ('emb' above)

/////////////////////////////////////////////////////////////////////////
// Constructing the sublattice L'
/////////////////////////////////////////////////////////////////////////

// Creates the embedding L' in L such that the finite part of the polyhedron P
// into the pulled back to L' is of maximal dimension.
// Note: Also sets the dimension of the finite part of P.
procedure create_lattice_embedding(P)
    // First we shift the generating points to the origin to find the dimension
    S:=amb_get_fp_generating_points(P);
    v:=Representative(S);
    L:=Universe(S);
    M:=Matrix([L | s - v : s in S]);
    P`fp_dimension:=Rank(M);
    // Is this dimension less than the ambient dimension?
    if P`fp_dimension ne Dimension(L) then
        // Calculate the equations of the hyperplanes cutting out the subspace
        // containing S
        normals:=[Dual(L) | Eltseq(n) : n in Basis(Kernel(Transpose(M)))];
        heights:=[Rationals() | v * n : n in normals];
        // Normalise this data to make everything integral
        for i in [1..#normals] do
            r:=LCM([Integers() | Denominator(c) : c in Eltseq(normals[i])] cat
                                      [Integers() | Denominator(heights[i])]);
            normals[i] *:= r;
            heights[i] *:= r;
        end for;
        ChangeUniverse(~heights,Integers());
        // Is the target zero dimensional?
        if P`fp_dimension eq 0 then
            // Yes -- build the zero map
            P`sub_is_lattice:=IsIntegral(v);
            emb:=ZeroMap(lattice_from_cache(0),L);
            S:=[Zero(Domain(emb))];
        else
            // No -- we find out whether this cuts out a sublattice in L           
            bool,translation,K:=IsConsistent(Transpose(Matrix(Integers(),
                                          normals)),Matrix(1,#heights,heights));
            if bool then
                // If we're here then this does generate a sublattice
                P`sub_is_lattice:=true;
                // Create the lattice map
                v:=L ! Eltseq(translation);
                _,emb:=Sublattice(ChangeUniverse(Basis(K),L));
            else
                // If we're here then this doesn't cut out a sublattice
                P`sub_is_lattice:=false;
                K:=Kernel(Transpose(Matrix(Integers(),normals)));
                // Create the lattice map
                emb:=LatticeMap(lattice_from_cache(P`fp_dimension),
                                                  ChangeUniverse(Basis(K),L));
            end if;
            // Pull the points across
            S:=[Domain(emb) | (u - v) @@ emb : u in S];
        end if;
        // Save the details
        P`sub_hyperplanes:=[CartesianProduct(Dual(L),Integers()) |
                     to_hyperplane(normals[i],heights[i]) : i in [1..#heights]];
        P`sub_origin:=v;
        P`sub_embedding:=emb;
    else
        // This is already maximal -- use the identity map
        P`sub_hyperplanes:=[CartesianProduct(Dual(L),Integers())|];
        P`sub_is_lattice:=true;
        P`sub_origin:=Zero(L);
        P`sub_embedding:=IdentityMap(L);
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure fp_emb_apply_translation(P,CP,Q)
    if assigned P`sub_hyperplanes then
        CP`sub_hyperplanes:=[Universe(P`sub_hyperplanes) |
                          hyperplane_translation(H,Q) : H in P`sub_hyperplanes];
    end if;
    if assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P)) then
        if assigned P`sub_origin then
            CP`sub_origin:=P`sub_origin; end if;
        if assigned P`sub_is_lattice then
            CP`sub_is_lattice:=P`sub_is_lattice; end if;
        if assigned P`sub_embedding then
            CP`sub_embedding:=P`sub_embedding; end if;
    else
        if assigned P`sub_origin then
            CP`sub_origin:=P`sub_origin + Q; end if;
        if assigned P`sub_is_lattice and IsIntegral(Q) then
            CP`sub_is_lattice:=P`sub_is_lattice; end if;
        if assigned P`sub_embedding and IsIntegral(Q) then
            CP`sub_embedding:=P`sub_embedding; end if;
    end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure fp_emb_apply_negation(P,CP)
    if assigned P`sub_hyperplanes then
        CP`sub_hyperplanes:=[Universe(P`sub_hyperplanes) |
                               hyperplane_negation(H) : H in P`sub_hyperplanes];
    end if;
    if assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P)) then
        if assigned P`sub_origin then
            CP`sub_origin:=P`sub_origin; end if;
        if assigned P`sub_is_lattice then
            CP`sub_is_lattice:=P`sub_is_lattice; end if;
        if assigned P`sub_embedding then
            CP`sub_embedding:=P`sub_embedding; end if;
    else
        if assigned P`sub_origin then
            CP`sub_origin:=-P`sub_origin; end if;
        if assigned P`sub_is_lattice then
            CP`sub_is_lattice:=P`sub_is_lattice; end if;
        if assigned P`sub_embedding then
            L:=Ambient(P);
            neg:=hom<L -> L | -IdentityMatrix(Integers(),Dimension(L))>;
            CP`sub_embedding:=P`sub_embedding * neg;
        end if;
    end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure fp_emb_apply_dilation(P,CP,k)
    if assigned P`sub_hyperplanes then
        if assigned P`fp_dimension and
            P`fp_dimension eq Dimension(Ambient(P)) then
            CP`sub_hyperplanes:=P`sub_hyperplanes;
        else
            CP`sub_hyperplanes:=[Universe(P`sub_hyperplanes) |
                   to_hyperplane(H[1],H[2] * k) : H in P`sub_hyperplanes];
        end if;
    end if;
    if assigned P`fp_dimension and P`fp_dimension eq Dimension(Ambient(P)) then
        if assigned P`sub_origin then
            CP`sub_origin:=P`sub_origin; end if;
        if assigned P`sub_is_lattice then
            CP`sub_is_lattice:=P`sub_is_lattice; end if;
        if assigned P`sub_embedding then
            CP`sub_embedding:=P`sub_embedding; end if;
    else
        if assigned P`sub_origin then
            CP`sub_origin:=k * P`sub_origin;
            if IsIntegral((k - 1) * P`sub_origin) then
                if assigned P`sub_is_lattice then
                    CP`sub_is_lattice:=P`sub_is_lattice; end if;
                if assigned P`sub_embedding then
                    CP`sub_embedding:=P`sub_embedding; end if;
            end if;
         end if;
    end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure fp_emb_change_ambient(P,CP,L)
    if assigned P`sub_is_lattice then
        CP`sub_is_lattice:=P`sub_is_lattice; end if;
    if assigned P`sub_origin then
        CP`sub_origin:=L ! P`sub_origin; end if;
    if assigned P`sub_embedding then
        mve:=hom<Ambient(P) -> L | IdentityMatrix(Integers(),Dimension(L))>;
        CP`sub_embedding:=P`sub_embedding * mve;
    end if;
    if assigned P`sub_hyperplanes then
        CP`sub_hyperplanes:=[CartesianProduct(Dual(L),Integers()) |
                       hyperplane_change_ambient(H,L) : H in P`sub_hyperplanes];
    end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure fp_emb_change_to_maximal(P,CP,emb,trans)
    CP`sub_origin:=Zero(Domain(emb));
    CP`sub_hyperplanes:=[CartesianProduct(Dual(Domain(emb)),Integers())|];
    CP`sub_is_lattice:=true;
    CP`sub_embedding:=IdentityMap(Domain(emb));
end procedure;

/////////////////////////////////////////////////////////////////////////
// Access functions for the embedding L' -> L
/////////////////////////////////////////////////////////////////////////

// Returns the lattice L'
function fp_emb_lattice(P)
    if not assigned P`sub_embedding then
        create_lattice_embedding(P);
    end if;
    return Domain(P`sub_embedding);
end function;

// Returns the dimension of the lattice L'
function fp_emb_lattice_dimension(P)
    if not assigned P`fp_dimension then
        create_lattice_embedding(P);
    end if;
    return P`fp_dimension;
end function;

// Returns the translation and embedding to map points from L' into L
function fp_emb_map(P)
    if not assigned P`sub_origin or not assigned P`sub_embedding then
        create_lattice_embedding(P);
    end if;
    return P`sub_origin,P`sub_embedding;
end function;

// Returns the hyperplanes that cut out the subspace containing the finite part
// of P
function fp_emb_hyperplanes(P)
    if not assigned P`sub_hyperplanes then
        create_lattice_embedding(P);
    end if;
    return P`sub_hyperplanes;
end function;

// True iff the embedding of L' into L is a lattice embedding -- i.e. there
// exists a volume form for the image of L' in L
function fp_emb_has_volume_form(P)
    if not assigned P`sub_is_lattice then
        create_lattice_embedding(P);
    end if;
    return P`sub_is_lattice;
end function;

// Returns the generating points of the finite part of P pulled-back to L'
function fp_emb_pullback_of_generating_points(P)
    trans,emb:=fp_emb_map(P);
    return [Domain(emb) | (u - trans) @@ emb :
                                        u in amb_get_fp_generating_points(P)];
end function;

/////////////////////////////////////////////////////////////////////////
// Translating between L and L'
/////////////////////////////////////////////////////////////////////////

// True iff the point v in L lies in the subspace containing the finite part
// of P (i.e. in the image of L').
function in_embedded_lattice(P,u)
    for hyperplane in fp_emb_hyperplanes(P) do
        if u * hyperplane[1] ne hyperplane[2] then return false; end if;
    end for;
    return true;
end function;

// Converts the point v in L' to the corresponding point in L.
function embedded_lattice_to_ambient_lattice(P,u)
    trans,emb:=fp_emb_map(P);
    return emb(u) + trans;
end function;

// Attempts to pull-back the point v in L to a point in L'.
// Returns true and the pull-back if possible, false otherwise.
function ambient_lattice_to_embedded_lattice(P,u)
    if not in_embedded_lattice(P,u) then return false,_; end if;
    trans,emb:=fp_emb_map(P);
    return (u - trans) @@ emb;
end function;

// Maps the hyperplane H in L to L' via the dual of the embedding map.
function ambient_hyperplane_to_embedded_hyperplane(P,H)
    trans,emb:=fp_emb_map(P);
    dual:=Dual(emb);
    return to_hyperplane(dual(H[1]),H[2] - H[1] * trans);
end function;
