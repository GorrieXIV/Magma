freeze;

/////////////////////////////////////////////////////////////////////////
// properties.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 48810 $
// $Date: 2014-11-01 22:14:16 +1100 (Sat, 01 Nov 2014) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating properties of polyhedra.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// Contains intrinsics to answer questions: "is this a simplex?", "is this
// smooth?", etc. Most of them only apply to polytopes. See the note
// at the start of attributes.m for an attempt to explain what I consider
// the distinction to be between attributes and properties.
//
// There is a certain ambiguity as to how to define concepts such as
// "reflexive", "smooth", "Fano", and "Gorenstein index" when the
// polytope is not maximal. I have decided that a necessary prerequisite
// is that the polytope is maximal; this can be easily changed if people
// object and offer up a good definition.
/////////////////////////////////////////////////////////////////////////

import "../lattice/hyperplane.m": halfspace_gorenstein_contribution, point_on_halfspace_boundary;
import "../cone/generators.m": is_generated_at_height_1;
import "convexhull/neighbourlygraph.m": ng_facets_containing_point;
import "convexhull/convexhull.m": fp_get_dimension, fp_facet_indices, fp_get_pullback_halfspaces;
import "faces/support.m": amb_has_volume_form, amb_get_halfspaces, amb_partition_halfspaces_by_task, amb_neighbourly_graph, amb_get_fp_generating_points, amb_are_fp_generating_points_vertices;

declare attributes TorPol:
    dimension,              // The dimension of the polyhedron
    is_empty,               // Is this poluhedron empty?
    is_polytope,            // Is this polyhedron a polytope?
    is_affine,              // Is this an affine linear space?
    is_integral,            // Are the vertices integral?
    is_simplicial,          // Is this polytope simplicial?
    is_simple,              // Is this polyhedron simple?
    is_smooth,              // Is this polytope smooth?
    is_fano,                // Is this polytope Fano?
    gorenstein_index;       // If this polytope is Fano, this is Gorenstein idx

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Input: A sequence of hyperplanes.
// Output: True iff their intersection contains an integral point. If true,
// also returns such a point.
function intersection_has_integral_point(Hs)
    M:=Transpose(Matrix(Integers(),[H[1] : H in Hs]));
    h:=Matrix(1,#Hs,[Integers() | H[2] : H in Hs]);
    try
        v:=Solution(M,h);
    catch e
        return false,_;
    end try;
    return true,Dual(Parent(Representative(Hs)[1])) ! Eltseq(v);
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure props_apply_translation(P,CP,Q)
    if assigned P`dimension then
        CP`dimension:=P`dimension; end if;
    if assigned P`is_polytope then
        CP`is_polytope:=P`is_polytope; end if;
    if assigned P`is_affine then
        CP`is_affine:=P`is_affine; end if;
    if assigned P`is_integral and IsIntegral(Q) then
        CP`is_integral:=P`is_integral; end if;
    if assigned P`is_simplicial then
        CP`is_simplicial:=P`is_simplicial; end if;
    if assigned P`is_simple then
        CP`is_simple:=P`is_simple; end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure props_apply_negation(P,CP)
    if assigned P`dimension then
        CP`dimension:=P`dimension; end if;
    if assigned P`is_polytope then
        CP`is_polytope:=P`is_polytope; end if;
    if assigned P`is_affine then
        CP`is_affine:=P`is_affine; end if;
    if assigned P`is_integral then
        CP`is_integral:=P`is_integral; end if;
    if assigned P`is_simplicial then
        CP`is_simplicial:=P`is_simplicial; end if;
    if assigned P`is_simple then
        CP`is_simple:=P`is_simple; end if;
    if assigned P`is_smooth then
        CP`is_smooth:=P`is_smooth; end if;
    if assigned P`is_fano then
        CP`is_fano:=P`is_fano; end if;
    if assigned P`gorenstein_index then
        CP`gorenstein_index:=P`gorenstein_index; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure props_apply_dilation(P,CP,k)
    if assigned P`dimension then
        CP`dimension:=P`dimension; end if;
    if assigned P`is_polytope then
        CP`is_polytope:=P`is_polytope; end if;
    if assigned P`is_affine then
        CP`is_affine:=P`is_affine; end if;
    if assigned P`is_integral and P`is_integral and IsIntegral(k) then
        CP`is_integral:=P`is_integral; end if;
    if assigned P`is_simplicial then
        CP`is_simplicial:=P`is_simplicial; end if;
    if assigned P`is_simple then
        CP`is_simple:=P`is_simple; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure props_change_ambient(P,CP,L)
    if assigned P`dimension then
        CP`dimension:=P`dimension; end if;
    if assigned P`is_polytope then
        CP`is_polytope:=P`is_polytope; end if;
    if assigned P`is_affine then
        CP`is_affine:=P`is_affine; end if;
    if assigned P`is_integral then
        CP`is_integral:=P`is_integral; end if;
    if assigned P`is_simplicial then
        CP`is_simplicial:=P`is_simplicial; end if;
    if assigned P`is_simple then
        CP`is_simple:=P`is_simple; end if;
    if assigned P`is_smooth then
        CP`is_smooth:=P`is_smooth; end if;
    if assigned P`is_fano then
        CP`is_fano:=P`is_fano; end if;
    if assigned P`gorenstein_index then
        CP`gorenstein_index:=P`gorenstein_index; end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure props_change_to_maximal(P,CP,emb,trans)
    CP`dimension:=Dimension(Domain(emb));
    if assigned P`is_polytope then
        CP`is_polytope:=P`is_polytope; end if;
    if assigned P`is_affine then
        CP`is_affine:=P`is_affine; end if;
    if assigned P`is_integral then
        CP`is_integral:=P`is_integral; end if;
    if assigned P`is_simplicial then
        CP`is_simplicial:=P`is_simplicial; end if;
    if assigned P`is_simple then
        CP`is_simple:=P`is_simple; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Properties of polytopes and polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic Dimension(P::TorPol) -> BoolElt
{The dimension of the polyhedron P}
    if not assigned P`dimension then
        fp_dim:=fp_get_dimension(P);
        if IsPolytope(P) then
            P`dimension:=fp_dim;
        elif fp_dim eq 0 then
            P`dimension:=Dimension(InfinitePart(P));
        else
            V:=amb_get_fp_generating_points(P);
            u:=Representative(V);
            gens:=[v - u : v in V] cat RGenerators(InfinitePart(P));
            P`dimension:=Rank(Matrix(gens));
        end if;
    end if;
    return P`dimension;
end intrinsic;

intrinsic ContainsZero(P::TorPol) -> BoolElt
{True iff the polyhedron P contains the origin strictly in its interior}
    return IsInInterior(Zero(Ambient(P)),P);
end intrinsic;

intrinsic IsEmpty(P::TorPol) -> BoolElt
{True iff the polyhedron P is empty}
    if not assigned P`is_empty then
        P`is_empty:=IsEmpty(amb_get_fp_generating_points(P));
    end if;
    return P`is_empty;
end intrinsic;

intrinsic IsAffineLinear(P::TorPol) -> BoolElt
{True iff the polyhedron P is an affine linear space}
    if not assigned P`is_affine then
        P`is_affine:=false;
        if not IsEmpty(P) and not IsPolytope(P) then
            IP:=InfinitePart(P);
            if IsLinearSpace(IP) then
                gens:=amb_get_fp_generating_points(P);
                u:=Representative(gens);
                P`is_affine:=&and[v - u in IP : v in gens];
            end if;
        end if;
    end if;
    return P`is_affine;
end intrinsic;

intrinsic IsLinearSpace(P::TorPol) -> BoolElt
{True iff the polyhedron P is a linear space}
    return IsAffineLinear(P) and ContainsZero(P);
end intrinsic;

intrinsic IsPointed(P::TorPol) -> BoolElt
{True iff the polyhedron P is pointed (i.e. if it is empty or has a vertex)}
    return IsEmpty(P) or (not IsAffineLinear(P) and NumberOfVertices(P) gt 0);
end intrinsic;

intrinsic IsPolytope(P::TorPol) -> BoolElt
{True iff P is a polytope}
    if not assigned P`is_polytope then
        if assigned P`ip_cone then
            P`is_polytope:=IsZero(P`ip_cone);
        else
            P`is_polytope:=true;
        end if;
    end if;
    return P`is_polytope;
end intrinsic;

intrinsic IsMaximumDimensional(P::TorPol) -> BoolElt
{True iff the dimension of the polyhedron P equals the dimension of the ambient lattice}
    return Dimension(P) eq Dimension(Ambient(P));
end intrinsic;

intrinsic IsIntegral(P::TorPol) -> BoolElt
{True iff the vertices of the polyhedron P are at integral coordinates in the underlying toric lattice or, if P contains lines, iff the smallest dimensional non-trivial faces of P are generated by integral points}
    if not assigned P`is_integral then
        if IsAffineLinear(P) then
            // The polyhedron is an affine linear space
            P`is_integral:=amb_has_volume_form(P);
        elif not IsEmpty(amb_get_fp_generating_points(P)) then
            // The polyhedron is pointed -- we want to avoid computing the
            // vertices unless absolutely necessary
            if IsIntegral(amb_get_fp_generating_points(P)) then
                P`is_integral:=true;
            else
                if amb_are_fp_generating_points_vertices(P) then
                    P`is_integral:=false;
                else
                    P`is_integral:=IsIntegral(Vertices(P));
                end if;
            end if;
        else
            // The polyhedron contains lines, but isn't a linear space
            if IsIntegral(amb_get_fp_generating_points(P)) then
                P`is_integral:=true;
            else
                // This is a bit of a faff. We need to see if we can replace
                // each of the generators by an equivalent integral point.
                Hs:=amb_get_halfspaces(P);
                P`is_integral:=&and[intersection_has_integral_point(
                          [H[1] : H in Hs | point_on_halfspace_boundary(H,v)]) :
                          v in amb_get_fp_generating_points(P)];
            end if;
        end if;
    end if;
    return P`is_integral;
end intrinsic;

intrinsic IsIntegrallyClosed(P::TorPol) -> BoolElt
{True iff the polytope P is integrally closed (i.e. every lattice point in k*P can be written as the sum of k lattice points in P, for all k) }
    // Sanity check
    require IsPolytope(P): "The polyhedron must be a polytope";
    // Fetch the cone over P
    C:=NormalisedCone(P);
    // Perhaps we already know the \Z generators?
    if assigned C`Zgens then
        grading:=Grading(C);
        return &and[v * grading eq 1 : v in ZGenerators(C)];
    end if;
    // Ensure that the cone is of maximum dimension
    if not IsMaximumDimensional(C) then
        lin:=LinearSpanEquations(C);
        CC,psi:=ConeInSublattice(C);
        if assigned CC`Zgens then
            gens:=ZGenerators(CC);
            grading:=Grading(CC);
            bool:=&and[v * grading eq 1 : v in gens];
        else
            bool,gens:=is_generated_at_height_1(CC);
        end if;
        if bool then
            C`Zgens:=Sort(Image(psi,gens));
        end if;
    else
        bool,gens:=is_generated_at_height_1(C);
        if bool then
            C`Zgens:=gens;
        end if;
    end if;
    return bool;
end intrinsic;

intrinsic IsPerfectlyCentered(P::TorPol) -> BoolElt
{True iff the polyhedron P is a polytope containing the origin strictly in its interior, such that for any nonempty face F of P the intersection relint(F) with the (outer) normal cone is nonempty.}
    if not IsPolytope(P) or not ContainsZero(P) then
        return false;
    end if;
    Hs,n:=Inequalities(P);
    for i in [1..n] do
        ray:=Ambient(P) ! ((Hs[i][2] / Norm(Hs[i][1])) * Hs[i][1]);
        if not &and[ray * Hs[j][1] gt Hs[j][2] : j in [1..n] | j ne i] then
            return false;
        end if;
    end for;
    return true;
end intrinsic;

intrinsic IsFano(P::TorPol) -> BoolElt
{True iff the polyhedron P is a Fano polytope (i.e. of maximum dimension, containg the origin strictly in its interior, with primitive lattice vertices)}
    if not assigned P`is_fano then
        P`is_fano:=IsPolytope(P) and IsMaximumDimensional(P) and
                    ContainsZero(P) and &and[IsPrimitive(v) : v in Vertices(P)];
    end if;
    return P`is_fano;
end intrinsic;

intrinsic IsSimplex(P::TorPol) -> BoolElt
{True iff the polyhedron P is a simplex}
    return IsPolytope(P) and NumberOfVertices(P) eq fp_get_dimension(P) + 1;
end intrinsic;

intrinsic IsSimplicial(P::TorPol) -> BoolElt
{True iff the polyhedron P is a simplicial polytope}
    if not assigned P`is_simplicial then
        if not IsPolytope(P) then
            P`is_simplicial:=false;
        else
            d:=fp_get_dimension(P);
            if d le 2 then
                P`is_simplicial:=true;
            else
                P`is_simplicial:=&and[#F eq d : F in fp_facet_indices(P)];
            end if;
        end if;
    end if;
    return P`is_simplicial;
end intrinsic;

intrinsic IsSimple(P::TorPol) -> BoolElt
{True iff the polyhedron P is simple}
    if not assigned P`is_simple then
        _,sub:=amb_partition_halfspaces_by_task(P);
        d:=Dimension(P) + #sub;
        ng:=amb_neighbourly_graph(P);
        P`is_simple:=&and[#ng_facets_containing_point(ng,v) eq d :
                                                            v in Vertices(P)];
    end if;
    return P`is_simple;
end intrinsic;

intrinsic IsSmooth(P::TorPol) -> BoolElt
{True iff the polyhedron P is a smooth polytope}
    if not assigned P`is_smooth then
        if IsFano(P) and IsSimplicial(P) then
            vertices:=Vertices(P);
            P`is_smooth:=&and[AreGenerators(
                                [Universe(vertices) | vertices[i] : i in F]) :
                                F in fp_facet_indices(P)];
        else
            P`is_smooth:=false;
        end if;
    end if;
    return P`is_smooth;
end intrinsic;

intrinsic IsReflexive(P::TorPol) -> BoolElt
{True iff the polyhedron P is a reflexive polytope}
    if not assigned P`gorenstein_index and not IsFano(P) then
        return false;
    end if;
    return GorensteinIndex(P) eq 1;
end intrinsic;

intrinsic GorensteinIndex(P::TorPol) -> RngIntElt
{The Gorenstein index of the Fano polytope P}
    if not assigned P`gorenstein_index then
        require IsFano(P):
            "The polyhedron must be a Fano polytope";
        if Dimension(P) eq 0 then
            P`gorenstein_index:=1;
        else
            Hs:=fp_get_pullback_halfspaces(P);
            P`gorenstein_index:=LCM([Integers() |
                               halfspace_gorenstein_contribution(H) : H in Hs]);
        end if;
    end if;
    return P`gorenstein_index;
end intrinsic;

intrinsic IsFlag(P::TorPol) -> BoolElt
{True iff the simplicial poytope P is flag}
    require IsPolytope(P) and IsSimplicial(P):
        "The polyhedron must be a simplicial polytope";
    S:=&join[SequenceToSet(FaceIndices(P,i)) : i in [1..Dimension(P) - 1]];
    n:=NumberOfVertices(P);
    found:={PowerSet(Integers())|};
    for i in [2..n] do
        for s in Subsets({1..n},i) do
            if not s in S then
                minimal:=true;
                for ss in found do
                    if ss subset s then
                        minimal:=false;
                        break;
                    end if;
                end for;
                if minimal then
                    if i gt 2 then
                        return false;
                    else
                        Include(~found,s);
                    end if;
                end if;
            end if;
        end for;
    end for;
    return true;
end intrinsic;
