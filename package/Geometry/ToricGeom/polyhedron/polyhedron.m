freeze;

/////////////////////////////////////////////////////////////////////////
// polyhedron.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 49861 $
// $Date: 2015-02-22 20:41:20 +1100 (Sun, 22 Feb 2015) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for creating and printing polyhedra.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": remove_repetitions, bounding_box;
import "../utilities/strings.m": seq_calc_widths, seq_to_aligned_string, seq_to_string;
import "../cone/generators.m": are_R_generators_minimal;
import "../lattice/hyperplane.m": to_halfspace, halfspace_gorenstein_contribution, point_on_halfspace_boundary;
import "../lattice/lattice.m": lattice_from_cache;
import "../lattice/point.m": lattice_vector_to_row_matrix, row_matrix_to_lattice_vector;
import "../lattice/gradedlattice.m": default_origin;
import "convexhull/neighbourlygraph.m": ng_build_from_facets;
import "attributes.m": attr_apply_translation, attr_apply_negation, attr_apply_dilation, attr_change_ambient, attr_change_to_maximal;
import "properties.m": props_apply_translation, props_apply_negation, props_apply_dilation, props_change_ambient, props_change_to_maximal;
import "convexhull/sublattice.m": fp_emb_has_volume_form, fp_emb_apply_translation, fp_emb_apply_negation, fp_emb_apply_dilation, fp_emb_change_ambient, fp_emb_change_to_maximal;
import "faces/support.m": amb_has_volume_form, amb_get_fp_generating_points, amb_are_fp_generating_points_vertices, amb_partition_halfspaces_by_task, amb_apply_translation, amb_apply_negation, amb_apply_dilation, amb_change_ambient, amb_change_to_maximal;
import "faces/faces.m": faces_apply_translation, faces_apply_negation, faces_apply_dilation, faces_change_ambient, faces_change_to_maximal;
import "convexhull/convexhull.m": fp_get_dimension, fp_apply_translation, fp_apply_negation, fp_apply_dilation, fp_change_ambient, fp_change_to_maximal;
import "triangulation.m": triangulation_apply_translation, triangulation_apply_negation, triangulation_apply_dilation, triangulation_change_ambient, triangulation_change_to_maximal;
import "latticepoints/latticepoints.m": pts_apply_translation, pts_apply_negation, pts_change_ambient, pts_change_to_maximal;
import "latticepoints/ehrhart.m": ehrhart_apply_translation, ehrhart_apply_negation, ehrhart_change_ambient, ehrhart_change_to_maximal;
import "coneembedding.m": ce_default_embedding, ce_get_embedding, ce_get_cone;
import "polar.m": polar_apply_negation, polar_apply_dilation, polar_change_ambient;

declare type TorPol;
declare attributes TorPol:
    max_dim_poly,           // The maximum dimensional version of P, s.t. P =...
    max_dim_emb,            //  emb(PP) +...
    max_dim_trans,          //  translation.
    compact_part,           // The compact part of P
    hash_value,             // The hash value of this polyhedron
    description;            // A special description string for this polyhedron

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns a new polytope equal to P, where the pullback of emb + trans gives
// a maximum dimensional polyhedron. Note: Does not check that the affine
// embedding really does yeild a maximum dimensional copy of P.
function create_maximum_dimensional(P,emb,trans)
    // Transfer the data across
    CP:=New(TorPol);
    attr_change_to_maximal(P,CP,emb,trans);
    props_change_to_maximal(P,CP,emb,trans);
    amb_change_to_maximal(P,CP,emb,trans);
    fp_emb_change_to_maximal(P,CP,emb,trans);
    fp_change_to_maximal(P,CP,emb,trans);
    triangulation_change_to_maximal(P,CP,emb,trans);
    pts_change_to_maximal(P,CP,emb,trans);
    ehrhart_change_to_maximal(P,CP,emb,trans);
    faces_change_to_maximal(P,CP,emb,trans);
    // Return the new polyhedron, along with the affine embedding
    return CP,emb,trans;
end function;

// True iff the weights lambda are reduces and irreducible.
function reduced_and_irreducible(lambda)
    for i in [1..#lambda] do
        if GCD(Remove(lambda,i)) ne 1 then
            return false;
        end if;
    end for;
    return true;
end function;

// Returns (as a sequence of sequences) the corners of the hyper-box with
// "bottom-left" corner 'min' and "top-right" corner 'max'.
procedure all_corners_recurse(min,max,~T,pt)
    idx:=#pt;
    if idx eq #min then
        Append(~T,pt);
    else
        $$(min,max,~T,Append(pt,min[idx + 1]));
        if min[idx + 1] ne max[idx + 1] then
            $$(min,max,~T,Append(pt,max[idx + 1]));
        end if;
    end if;
end procedure;

function all_corners(min,max)
    T:=[PowerSequence(Rationals())|];
    all_corners_recurse(min,max,~T,[Rationals()|]);
    return T;
end function;

// Adds the description string to the given polyhedron
procedure polyhedron_add_description(P,desc)
    error if Type(P) ne TorPol,
        "polyhedron_add_description: Argument 1 must be a polyhedron";
    error if Type(desc) ne MonStgElt,
        "polyhedron_add_description: Argument 2 must be a string";
    while #desc gt 0 and
        (desc[#desc] eq "\n" or desc[#desc] eq "\t" or desc[#desc] eq " ") do
        desc:=desc[1..#desc - 1];
    end while;
    if #desc eq 0 then return; end if;
    if assigned P`description then
        P`description cat:= "\n" cat desc;
    else
        P`description:=desc;
    end if;
end procedure;

// Returns true iff the two non-pointed polyhedra are equal. Assumes that
// the infinite parts are already known to be equal.
function are_nonpointed_polyhedra_equal(P1,P2)
    v1:=amb_get_fp_generating_points(P1);
    v2:=amb_get_fp_generating_points(P2);
    if Seqset(v1) eq Seqset(v2) then return true; end if;
    h1:=amb_partition_halfspaces_by_task(P1);
    h2:=amb_partition_halfspaces_by_task(P2);
    if #h1 ne #h2 then return false; end if;
    for v in v1 do
        Hs:=[H : H in h1 | point_on_halfspace_boundary(H,v)];
        found:=false;
        for u in v2 do
            found:=&and[point_on_halfspace_boundary(H,u) : H in Hs];
            if found then break; end if;
        end for;
        if not found then return false; end if;
    end for;
    for v in v2 do
        Hs:=[H : H in h2 | point_on_halfspace_boundary(H,v)];
        found:=false;
        for u in v1 do
            found:=&and[point_on_halfspace_boundary(H,u) : H in Hs];
            if found then break; end if;
        end for;
        if not found then return false; end if;
    end for;
    return true;
end function;

/////////////////////////////////////////////////////////////////////////
// Printing and hash value
/////////////////////////////////////////////////////////////////////////

intrinsic PrintNamed(P::TorPol,level::MonStgElt,name::MonStgElt)
{The description of the polyhedron P}
    // We get the empty polyhedron out of the way as a special case
    if IsEmpty(P) then
        if level eq "Maximal" then
            Sprintf("Empty polyhedron in %o",Ambient(P));
        else
            printf "Empty polyhedron";
        end if;
        // Output any description
        if level ne "Minimal" and assigned P`description then
            printf "\n" cat P`description;
        end if;
        return;
    end if;
    // First we collect together the strings we'll need
    prefix:="    ";
    // Create the main strings
    if (amb_are_fp_generating_points_vertices(P) or assigned P`amb_ng) and
       NumberOfVertices(P) ne 0 then
        gens:=Vertices(P);
        num:=#gens;
        if num eq 1 then
            numstr:="one vertex";
        else
            numstr:=Sprintf("%o vertices", num);
        end if;
    else
        gens:=amb_get_fp_generating_points(P);
        num:=#gens;
        if num eq 1 then
            numstr:="one generator";
        else
            numstr:=Sprintf("%o generators", num);
        end if;
    end if;
    if level ne "Minimal" and num ne 0 and
      (level eq "Maximal" or num le 10) then
        V:=[PowerSequence(Rationals()) | Eltseq(v) : v in gens];
        widths:=seq_calc_widths(V);
    end if;
    infstr:="";
    if not IsPolytope(P) and level ne "Minimal" then
        gens:=RGenerators(InfinitePart(P));
        if #gens ne 0 and (level eq "Maximal" or #gens le 10) then
            C:=[PowerSequence(Rationals()) | Eltseq(n) : n in gens];
            Cwidths:=seq_calc_widths(C);
            if assigned widths then
                for i in [1..#widths] do
                    if widths[i] lt Cwidths[i] then
                        widths[i]:=Cwidths[i];
                    end if;
                end for;
            else
                widths:=Cwidths;
            end if;
            if #gens eq 1 then
                infstr:=" given by a cone with one ";
            else
                infstr:=Sprintf(" given by a cone with %o ", #gens);
            end if;
            if are_R_generators_minimal(InfinitePart(P)) then
                infstr cat:= "minimal ";
            end if;
            if #gens eq 1 then
                infstr cat:= "generator:\n";
            else
                infstr cat:= "generators:\n";
            end if;
        end if;
    end if;
    // Output the sequences
    if assigned V then
        numstr cat:= Sprintf(":\n%o%o", prefix, seq_to_aligned_string(V,
                                                    widths, "(", ",", prefix));
    end if;
    if assigned C then
        infstr cat:= Sprintf("%o%o", prefix,
                           seq_to_aligned_string(C, widths, "(", ",", prefix));
    end if;
    // Create any extra strings
    if level eq "Maximal" then
        ambient:=Sprintf("in %o ", Ambient(P));
        extra:="";
        newline:=false;
        if (assigned P`Ehrhart_coeffs and IsDefined(P`Ehrhart_coeffs,1)) or
           assigned P`points then
            num:=NumberOfPoints(P);
            extra:=Sprintf("containing %o points", num);
            if assigned P`points and num gt 0 and num le 10 then
                pts:=[PowerSequence(Integers()) | Eltseq(pt) : pt in Points(P)];
                widths:=seq_calc_widths(pts);
                extra cat:= Sprintf(":\n%o%o", prefix,
                          seq_to_aligned_string(pts, widths, "(", ",", prefix));
                newline:=true;
            end if;
        end if;
        if assigned P`amb_num_facets then
            if #extra ne 0 then
                if newline then
                    extra cat:= "\nand ";
                    newline:=false;
                else
                    extra cat:= " and ";
                end if;
            end if;
            extra cat:= Sprintf("with %o facets", P`amb_num_facets);
            if assigned P`amb_facet_idxs and P`amb_num_facets le 10 and
               IsPolytope(P) then
                extra cat:= " given by indices:\n";
                for i in [1..P`amb_num_facets] do
                    extra cat:= prefix cat
                                seq_to_string(P`amb_facet_idxs[i],"[",",");
                    if i ne P`amb_num_facets then
                        extra cat:= ",\n";
                    end if;
                end for;
                newline:=true;
            end if;
        end if;

    else
        ambient:="";
        extra:="";
    end if;
    // Now output the data to screen
    if IsPolytope(P) then
        desc:="";
        if assigned P`is_simplicial and P`is_simplicial then
            if assigned P`is_smooth and P`is_smooth then
                desc cat:= "regular ";
            else
                desc cat:= "simplicial ";
            end if;
        end if;
        if assigned P`gorenstein_index and P`gorenstein_index eq 1 then
            if not (assigned P`is_smooth and P`is_smooth) then
                desc cat:= "reflexive ";
            end if;
        end if;
        if assigned P`is_fano and P`is_fano then
            desc cat:= "Fano ";
        end if;
        if name eq "$" then
            printf "%o-dimensional %opolytope %owith %o",
                                            Dimension(P), desc, ambient, numstr;
        else
            printf "%o-dimensional %opolytope %o %owith %o",
                                      Dimension(P), desc, name, ambient, numstr;
        end if;
        if #extra gt 0 then
            printf "\n%o.", extra;
        end if;
    else
        if assigned V then
            numstr cat:= "\n";
        else
            numstr cat:= " ";
        end if;
        if name eq "$" then
            printf "%o-dimensional polyhedron %owith %o-dimensional finite part with %o", Dimension(P), ambient, fp_get_dimension(P), numstr;
        else
            printf "%o-dimensional polyhedron %o %owith %o-dimensional finite part with %o", Dimension(P), name, ambient, fp_get_dimension(P), numstr;
        end if;
        printf "and %o-dimensional infinite part%o", Dimension(InfinitePart(P)),
                                                                        infstr;
    end if;
    // Output any description
    if level eq "Maximal" and assigned P`description then
        printf "\n" cat P`description;
    end if;
end intrinsic;

intrinsic Hash(P::TorPol) -> RngIntElt
{The hash value of the polyhedron}
    // This is annoying, since we can't really guarantee what data has been
    // processed, and it seems stupid to calculate too much simply for a
    // hash value. It's also nice to have something invariant under lattice
    // automorphisms. We opt for the Gorenstein heights of the facets.
    if not assigned P`hash_value then
        indices:=[Integers() | halfspace_gorenstein_contribution(halfspace) :
                        halfspace in amb_partition_halfspaces_by_task(P)];
        P`hash_value:=Hash(Sort(indices));
    end if;
    return P`hash_value;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Comparison of polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic 'eq'(P1::TorPol, P2::TorPol) -> BoolElt
{True iff the polyhedra P1 and P2 are equal}
    if Ambient(P1) ne Ambient(P2) then
        return false; end if;
    if IsEmpty(P1) then
        return IsEmpty(P2); end if;
    if IsPolytope(P1) then
        if not IsPolytope(P2) then
            return false; end if;
        if Dimension(P1) ne Dimension(P2) then
            return false; end if;
        return Seqset(Vertices(P1)) eq Seqset(Vertices(P2));
    else
        if IsPolytope(P2) then
            return false; end if;
        if InfinitePart(P1) ne InfinitePart(P2) then
            return false; end if;
        if Dimension(P1) ne Dimension(P2) then
            return false; end if;
        if IsPointed(P1) then
            if not IsPointed(P2) then
                return false; end if;
            return Seqset(Vertices(P1)) eq Seqset(Vertices(P2));
        else
            if IsPointed(P2) then
                return false; end if;
            return are_nonpointed_polyhedra_equal(P1,P2);
        end if;
    end if;
end intrinsic;

intrinsic 'subset'(P1::TorPol, P2::TorPol) -> BoolElt
{True iff the polyhedron P1 is a subset of the polyhedron P2}
    if Ambient(P1) ne Ambient(P2) then
        return false; end if;
    if IsEmpty(P1) then
        return true; end if;
    if IsPolytope(P2) then
        if not IsPolytope(P1) then
            return false; end if;
        if Dimension(P1) gt Dimension(P2) then
            return false; end if;
        return &and[v in P2 : v in amb_get_fp_generating_points(P1)];
    else
        if not IsPolytope(P1) and not InfinitePart(P1) subset InfinitePart(P2)
            then return false; end if;
        return &and[v in P2 : v in amb_get_fp_generating_points(P1)];
    end if;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Intersection of polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic 'meet'(P1::TorPol, P2::TorPol) -> TorPol
{The polyhedron given by the intersection of the polyhedra P1 and P2}
    require Ambient(P1) eq Ambient(P2):
                "Arguments must lie in the same lattice";
    if IsEmpty(P1) then return P1; end if;
    if IsEmpty(P2) then return P2; end if;
    I1:=Inequalities(P1);
    I2:=Inequalities(P2);
    return PolyhedronWithInequalities(
                [Dual(Ambient(P1)) | ineq[1] : ineq in I1] cat
                [Dual(Ambient(P1)) | ineq[1] : ineq in I2],
                [Integers() | ineq[2] : ineq in I1] cat
                [Integers() | ineq[2] : ineq in I2]);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Arithmetic of polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic '+'(Q::TorLatElt, P::TorPol) -> TorPol
{}
    return P+Q;
end intrinsic;

intrinsic '-'(Q::TorLatElt, P::TorPol) -> TorPol
{}
    return (-P)+Q;
end intrinsic;

intrinsic '-'(P::TorPol, Q::TorLatElt) -> TorPol
{}
    return P+(-Q);
end intrinsic;

intrinsic '+'(P::TorPol, Q::TorLatElt) -> TorPol
{The translation of the polyhedra P by Q}
    require Ambient(P) eq Parent(Q): "Arguments must lie in the same lattice";
    if IsEmpty(P) then return P; end if;
    if IsZero(Q) then return P; end if;
    CP:=New(TorPol);
    // Set the data we can
    attr_apply_translation(P,CP,Q);
    props_apply_translation(P,CP,Q);
    amb_apply_translation(P,CP,Q);
    fp_emb_apply_translation(P,CP,Q);
    fp_apply_translation(P,CP,Q);
    triangulation_apply_translation(P,CP,Q);
    pts_apply_translation(P,CP,Q);
    ehrhart_apply_translation(P,CP,Q);
    faces_apply_translation(P,CP,Q);
    // Return the translated polyhedron
    return CP;
end intrinsic;

intrinsic '+'(Q::TorLatElt, C::TorCon) -> TorPol
{}
    return C+Q;
end intrinsic;

intrinsic '+'(C::TorCon, Q::TorLatElt) -> TorPol
{The translation of the cone C by Q}
    require Ambient(C) eq Parent(Q): "Arguments must lie in the same lattice";
    return ConeToPolyhedron(C) + Q;
end intrinsic;

intrinsic '+'(C::TorCon, P::TorPol) -> TorPol
{}
    return P+C;
end intrinsic;

intrinsic '+'(P::TorPol, C::TorCon) -> TorPol
{The Minkowski sum of the polyhedron P and the cone C}
    require Ambient(P) eq Ambient(C): "Arguments must lie in the same lattice";
    if IsEmpty(P) then return P; end if;
    // Create the graded lattice
    L,emb:=GradedToricLattice(Ambient(P));
    // Move the generators into the lattice
    origin:=default_origin(L,1);
    gens:=[L | emb(v) + origin : v in amb_get_fp_generating_points(P)];
    inf:=emb(RGenerators(InfinitePart(P))) cat emb(RGenerators(C));
    // Create the polyhedron
    return Polyhedron(Cone(gens cat inf));
end intrinsic;

intrinsic '+'(P::TorPol, Q::TorPol) -> TorPol
{The Minkowski sum of the polyhedra P and Q}
    require Ambient(P) eq Ambient(Q): "Arguments must lie in the same lattice";
    if IsEmpty(P) then return P; end if;
    if IsEmpty(Q) then return Q; end if;
    if P eq Q then return 2 * P; end if;
    // First calculate the finite part
    fpGens:=[Ambient(P) | q + p : p in amb_get_fp_generating_points(P),
                                  q in amb_get_fp_generating_points(Q)];
    if IsPolytope(P) and IsPolytope(Q) then
        return Polytope(fpGens);
    end if;
    // Now calculate the infinite part
    if not IsPolytope(P) then
        emb:=ce_get_embedding(P);
        origin:=ScalarLattice().1 @@ LatticeMap(Grading(ce_get_cone(P)));
        gens:=emb(RGenerators(InfinitePart(P)));
        if not IsPolytope(Q) then
            gens cat:= emb(RGenerators(InfinitePart(Q)));
        end if;
    else
        emb:=ce_get_embedding(Q);
        origin:=ScalarLattice().1 @@ LatticeMap(Grading(ce_get_cone(Q)));
        gens:=emb(RGenerators(InfinitePart(Q)));
    end if;
    // Finally, package it all together
    gens cat:= [Codomain(emb) | emb(v) + origin : v in fpGens];
    return Polyhedron(Cone(gens));
end intrinsic;

intrinsic '-'(P::TorPol) -> TorPol
{The negation -P of the polyhedra P}
    if IsEmpty(P) then return P; end if;
    CP:=New(TorPol);
    // Set the data we can
    attr_apply_negation(P,CP);
    props_apply_negation(P,CP);
    amb_apply_negation(P,CP);
    fp_emb_apply_negation(P,CP);
    fp_apply_negation(P,CP);
    triangulation_apply_negation(P,CP);
    pts_apply_negation(P,CP);
    ehrhart_apply_negation(P,CP);
    polar_apply_negation(P,CP);
    faces_apply_negation(P,CP);
    // Return the negation
    return CP;
end intrinsic;

intrinsic '*'(k::RngIntElt, P::TorPol) -> TorPol
{}
    return (Rationals() ! k) * P;
end intrinsic;

intrinsic '*'(k::FldRatElt, P::TorPol) -> TorPol
{The dilation kP of the polyhedron P}
    if IsEmpty(P) then return P; end if;
    if k eq 1 then return P; end if;
    if k lt 0 then
        if k eq -1 then
            return -P;
        else
            return (-k) * (-P);
        end if;
    end if;
    if k eq 0 then
        if IsPolytope(P) then
            return Polytope([Zero(Ambient(P))]);
        else
            return Polyhedron(NormalisedCone(P):level:=0);
        end if;
    end if;
    CP:=New(TorPol);
    // Set the data we can
    attr_apply_dilation(P,CP,k);
    props_apply_dilation(P,CP,k);
    amb_apply_dilation(P,CP,k);
    fp_emb_apply_dilation(P,CP,k);
    fp_apply_dilation(P,CP,k);
    triangulation_apply_dilation(P,CP,k);
    polar_apply_dilation(P,CP,k);
    faces_apply_dilation(P,CP,k);
    // Return the dilated polyhedron
    return CP;
end intrinsic;

intrinsic '*'(P1::TorPol, P2::TorPol) -> TorPol
{The direct product of the polyhedra, lying in the direct sum of their ambient toric lattices}
    L,embL1,embL2:=DirectSum(Ambient(P1),Ambient(P2));
    if IsPolytope(P1) and IsPolytope(P2) then
        return Polytope([L | v1 + v2 :
                             v1 in embL1(amb_get_fp_generating_points(P1)),
                             v2 in embL2(amb_get_fp_generating_points(P2))]);
    else
        // Create the graded lattice
        L,emb:=GradedToricLattice(L);
        // Move the generators into the lattice
        gens1:=[L | (embL1 * emb)(v) :
                            v in amb_get_fp_generating_points(P1)];
        gens2:=[L | (embL2 * emb)(v) :
                            v in amb_get_fp_generating_points(P2)];
        inf1:=(embL1 * emb)(RGenerators(InfinitePart(P1)));
        inf2:=(embL2 * emb)(RGenerators(InfinitePart(P2)));
        // Compute the product
        origin:=default_origin(L,1);
        gens:=[L | v1 + v2 + origin : v1 in gens1, v2 in gens2];
        inf:=[L | r1 + r2 : r1 in inf1, r2 in inf2];
        // Create the polyhedron
        return Polyhedron(Cone(gens cat inf));
    end if;
end intrinsic;

intrinsic '*'(P::TorPol,M::Mtrx) -> TorLatElt
{The product P * M of a polyhedron P with a square matrix M}
    L:=Ambient(P);
    dim:=Dimension(L);
    require NumberOfRows(M) eq NumberOfColumns(M) and
            NumberOfRows(M) eq dim:
        Sprintf("Argument 2 must be a %o x %o (square) matrix",dim,dim);
    require CoefficientRing(M) cmpeq Integers() or
            CoefficientRing(M) cmpeq Rationals():
        "Argument 2 must have integral or rational entries";
    if IsEmpty(P) then return P; end if;
    if CoefficientRing(M) cmpeq Integers() then
        M:=ChangeRing(M,Rationals());
    end if;
    // If this is a polytope we can simply take the image of the vertices
    if IsPolytope(P) then
        gens:=[L | row_matrix_to_lattice_vector(L,
                     lattice_vector_to_row_matrix(v) * M) :
                     v in amb_get_fp_generating_points(P)];
        if amb_are_fp_generating_points_vertices(P) and Rank(M) eq dim then
            return Polytope(gens : areVertices:=true);
        else
            return Polytope(gens);
        end if;
    end if;
    // Otherwise we need to use the cone embedding
    LL,emb:=GradedToricLattice(L);
    origin:=default_origin(LL,1);
    C:=Cone([LL | emb(row_matrix_to_lattice_vector(L,
                    lattice_vector_to_row_matrix(v) * M)) + origin :
                    v in amb_get_fp_generating_points(P)]
        cat [LL | emb(row_matrix_to_lattice_vector(L,
                    lattice_vector_to_row_matrix(gen) * M)) :
                    gen in RGenerators(InfinitePart(P))]);
    return Polyhedron(C);
end intrinsic;

intrinsic '/'(P::TorPol, k::RngIntElt) -> TorPol
{}
    return P / (Rationals() ! k);
end intrinsic;

intrinsic '/'(P::TorPol, k::FldRatElt) -> TorPol
{The dilation (1/k)P of the polyhedron P}
    require not IsZero(k): "Argument 2 must be non-zero";
    if IsEmpty(P) then return P; end if;
    return (1/k) * P;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Change ambient lattice
/////////////////////////////////////////////////////////////////////////

intrinsic ChangeAmbient(P::TorPol, L::TorLat) -> TorPol
{A polyhedron equal to P except for lying in the ambient toric lattice L}
    // Sanity check
    if L eq Ambient(P) then return P; end if;
    require Dimension(L) eq Dimension(Ambient(P)): Sprintf("The dimension of the lattice (%o) must equal the dimension of the ambient of the polyhedron (%o)",Dimension(L),Dimension(Ambient(P)));
    // Is this the empty polyhedron?
    if IsEmpty(P) then return EmptyPolyhedron(L); end if;
    // Transfer the data across
    CP:=New(TorPol);
    attr_change_ambient(P,CP,L);
    props_change_ambient(P,CP,L);
    amb_change_ambient(P,CP,L);
    fp_emb_change_ambient(P,CP,L);
    fp_change_ambient(P,CP,L);
    triangulation_change_ambient(P,CP,L);
    pts_change_ambient(P,CP,L);
    ehrhart_change_ambient(P,CP,L);
    polar_change_ambient(P,CP,L);
    // Copy over any print data
    if assigned P`description then
        CP`description:=P`description;
    end if;
    // Return the new polyhedron
    return CP;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Creation of polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic Polyhedron(C::TorCon,phi::Map[TorLat,TorLat],v::TorLatElt) -> TorPol
{The polyhedron arising as the preimage of the cone C under the affine map phi + v}
    require Codomain(phi) eq Ambient(C):
        "Argument 2 must map from a toric lattice into the ambient of the cone";
    require v in Ambient(C):
        "Argument 3 must lie in the same toric lattice as the cone";
    require IsIntegral(v): Sprintf("Argument 3: %o must be a lattice point",v);
    // Create the graded lattice
    grL:=GradedToricLattice(Domain(phi));
    // Build the map
    M:=VerticalJoin(Matrix([v]),DefiningMatrix(phi));
    grphi:=hom<grL -> Codomain(phi) | M>;
    // Return the resulting polyhedron
    return Polyhedron(C @@ grphi);
end intrinsic;

intrinsic Polyhedron(C::TorCon,H::TorLatElt,h::RngIntElt) -> TorPol
{}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    // Reduce H to a primitive lattice point and scale h accordingly
    if not IsPrimitive(H) then
        den:=Denominator(H);
        H *:= den;
        h *:= den;
        num:=GCD(Eltseq(H));
        if num ne 1 then
            H /:= num;
            h /:= num;
        end if;
    end if;
    bool,h:=IsCoercible(Integers(),h);
    // Sanity check on h
    require bool:
        "The hyperplane at the given height does not cut out a sublattice";
    // Get the embedding and the origin
    emb:=KernelEmbedding(H);
    origin:=(ScalarLattice().1 * h) @@ LatticeMap(H);
    // Return the resulting polyhedron
    return Polyhedron(C,emb,origin);
end intrinsic;

intrinsic Polyhedron(C::TorCon,H::TorLatElt,h::FldRatElt) -> TorPol
{The polyhedron arising as the intersection of the cone C with the hyperplane H at height h}
    // Sanity check on H
    require IsInDual(H,Ambient(C)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    // Reduce H to a primitive lattice point and scale h accordingly
    if not IsPrimitive(H) then
        den:=Denominator(H);
        H *:= den;
        h *:= den;
        num:=GCD(Eltseq(H));
        if num ne 1 then
            H /:= num;
            h /:= num;
        end if;
    end if;
    bool,h:=IsCoercible(Integers(),h);
    // Sanity check on h
    require bool:
        "The hyperplane at the given height does not cut out a sublattice";
    // Get the embedding and the origin
    emb:=KernelEmbedding(H);
    origin:=(ScalarLattice().1 * h) @@ LatticeMap(H);
    // Return the resulting polyhedron
    return Polyhedron(C,emb,origin);
end intrinsic;

intrinsic Polyhedron(C::TorCon : level:=1) -> TorPol
{The polyhedron arising as the intersection of the cone C with the hyperplane at height one (can be changed via 'level')}
    // Sanity check
    if Type(level) ne RngIntElt then
        bool,level:=IsCoercible(Integers(),level);
        require bool: "'level' must be an integer value";
    end if;
    // Perhaps the polyhedron is cached on the cone?
    if level eq 1 and assigned C`height_1_slice then
        return C`height_1_slice;
    end if;
    // Get the grading from the cone (which in turn gets it from the lattice)
    grad:=Grading(C);
    // Build the embedding and origin
    embedding:=ce_default_embedding(C);
    zero:=default_origin(C,level);
    // Deal with negative generators
    gens_minus:=[Ambient(C)| v : v in RGenerators(C) | level * (v * grad) lt 0];
    if not IsEmpty(gens_minus) then
        C:=C meet ConeWithInequalities([PrimitiveLatticeVector(level * grad)]);
    end if;
    // Get the generators for the finite part
    gens_plus:=[Ambient(C) | v : v in MinimalRGenerators(C) |
                                                       level * (v * grad) gt 0];
    // Is this an empty polyhedron?
    if IsEmpty(gens_plus) then
        return EmptyPolyhedron(Domain(embedding));
    end if;
    // Get the generators for the infinite part
    gens_zero:=[Ambient(C) | v : v in MinimalRGenerators(C) | v * grad eq 0];
    // Create the polyhedron
    P:=New(TorPol);
    P`ce_cone:=C;
    P`ce_embedding:=embedding;
    P`ce_height:=level;
    P`ce_origin:=zero;
    P`ambient:=Domain(embedding);
    P`fp_are_vertices:=true;
    P`amb_fp_generators:=[Domain(embedding) |
               ((level / (v * grad)) * v - zero) @@ embedding : v in gens_plus];
    P`amb_are_vertices:=true;
    if not IsEmpty(gens_zero) then
        P`ip_cone:=Cone(gens_zero @@ embedding);
        P`ip_cone`are_Rgens_minimal:=true;
        if not IsEmpty(LinearSubspaceGenerators(P`ip_cone)) then
            P`amb_are_vertices:=false;
        end if;
    end if;
    // Should we cache this polyhedron on the cone?
    if level eq 1 then
        C`height_1_slice:=P;
    end if;
    // Return the polyhedron
    return P;
end intrinsic;

intrinsic Polyhedron(S::SetEnum[TorLatElt]) -> TorPol
{}
    require not IsNull(S): "Illegal null sequence";
    return Polytope(SetToSequence(S));
end intrinsic;

intrinsic Polyhedron(S::SeqEnum[TorLatElt]) -> TorPol
{}
    require not IsNull(S): "Illegal null sequence";
    return Polytope(S);
end intrinsic;

intrinsic Polyhedron(S::SeqEnum[SeqEnum[RngIntElt]]) -> TorPol
{}
    require not IsNull(S): "Illegal null sequence";
    return Polytope(S);
end intrinsic;

intrinsic Polyhedron(S::SeqEnum[SeqEnum[FldRatElt]]) -> TorPol
{The polytope defined by taking the convex hull of the sequence of vectors S}
    require not IsNull(S): "Illegal null sequence";
    return Polytope(S);
end intrinsic;

intrinsic Polytope(S::SetEnum[TorLatElt]) -> TorPol
{}
    require not IsNull(S): "Illegal null sequence";
    return Polytope(SetToSequence(S));
end intrinsic;

intrinsic Polytope(S::SeqEnum[TorLatElt] : areVertices:=false) -> TorPol
{}
    require not IsNull(S): "Illegal null sequence";
    // Is this the empty polyhedron?
    if IsEmpty(S) then return EmptyPolyhedron(Universe(S)); end if;
    // Sanity checks
    require Type(areVertices) eq BoolElt: "'areVertices' must be a boolean";
    // Remove any repetitions from the points (but try to maintain the order)
    remove_repetitions(~S);
    // Create the polytope
    P:=New(TorPol);
    P`amb_fp_generators:=S;
    P`is_polytope:=true;
    P`ambient:=Universe(S);
    if areVertices then
        P`fp_are_vertices:=true;
        P`amb_are_vertices:=true;
    end if;
    // Return the polytope
    return P;
end intrinsic;

intrinsic Polytope(S::SeqEnum[SeqEnum[RngIntElt]]: areVertices:=false) -> TorPol
{}
    require not IsEmpty(S): "Polytope must have at least one vertex";
    dim:=#S[1];
    require &and[#v eq dim:v in S]: "Vectors must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,L);
    return Polytope(S : areVertices:=areVertices);
end intrinsic;

intrinsic Polytope(S::SeqEnum[SeqEnum[FldRatElt]]: areVertices:=false) -> TorPol
{The polytope defined by taking the convex hull of the sequence of vectors S}
    require not IsEmpty(S): "Polytope must have at least one vertex";
    dim:=#S[1];
    require &and[#v eq dim:v in S]: "Vectors must be of the same dimension";
    L:=lattice_from_cache(dim);
    ChangeUniverse(~S,L);
    return Polytope(S : areVertices:=areVertices);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Useful constructions
/////////////////////////////////////////////////////////////////////////

intrinsic Polyhedron(P::TorPol,H::TorLatElt,h::RngIntElt) -> TorPol
{}
    require IsInDual(H,Ambient(P)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    I:=Inequalities(P);
    return PolyhedronWithInequalities([Parent(H) | HH[1] : HH in I] cat [H,-H],
                                     [Integers() | HH[2] : HH in I] cat [h,-h]);
end intrinsic;

intrinsic Polyhedron(P::TorPol,H::TorLatElt,h::FldRatElt) -> TorPol
{The polyhedron arising as the intersection of the polyhedron P with the hyperplane H at height h}
    require IsInDual(H,Ambient(P)):
        "Argument 2 must lie in the dual to the ambient of argument 1";
    d:=Denominator(h);
    return Polyhedron(P,d * H,Numerator(h));
end intrinsic;

intrinsic StandardSimplex(d::RngIntElt) -> TorPol
{The d-dimensional simplex given by the standard basis and the origin}
    require d gt 0: "The dimension must be a positive integer";
    return StandardSimplex(lattice_from_cache(d));
end intrinsic;

intrinsic StandardSimplex(L::TorLat) -> TorPol
{The simplex given by the standard basis of the toric lattice L and the origin}
    if Dimension(L) eq 0 then return EmptyPolyhedron(L); end if;
    return Polytope([Zero(L)] cat Basis(L) : areVertices:=true);
end intrinsic;

intrinsic BoxPolytope(d::RngIntElt) -> TorPol
{The d-dimensional cube [0,1]^d}
    require d gt 0: "The dimension must be a positive integer";
    return BoxPolytope(lattice_from_cache(d));
end intrinsic;

intrinsic BoxPolytope(L::TorLat) -> TorPol
{The d-dimensional cube [0,1]^d in the toric lattice L}
    if Dimension(L) eq 0 then return EmptyPolyhedron(L); end if;
    verts:=SetToSequence(Subsequences({0,1},Dimension(L)));
    Sort(~verts);
    ChangeUniverse(~verts,L);
    return Polytope(verts : areVertices:=true);
end intrinsic;

intrinsic CrossPolytope(d::RngIntElt) -> TorPol
{The d-dimensional cross-polytope}
    require d gt 0: "The dimension must be a positive integer";
    return CrossPolytope(lattice_from_cache(d));
end intrinsic;

intrinsic CrossPolytope(L::TorLat) -> TorPol
{The maximum dimensional cross-polytope in the toric lattice L}
    if Dimension(L) eq 0 then return EmptyPolyhedron(L); end if;
    return Polytope([L | L.i : i in [1..Dimension(L)]] cat
                    [L | -L.i : i in [1..Dimension(L)]] : areVertices:=true);
end intrinsic;

intrinsic CyclicPolytope(d::RngIntElt,n::RngIntElt) -> TorPol
{The cyclic polytope generated by n points in d-dimensional space}
    require d gt 0: "The dimension must be a positive integer";
    return CyclicPolytope(lattice_from_cache(d),n);
end intrinsic;

intrinsic CyclicPolytope(L::TorLat,n::RngIntElt) -> TorPol
{The cyclic polytope generated by n points in the toric lattice L}
    if n eq 0 then return EmptyPolyhedron(L); end if;
    d:=Dimension(L);
    return Polytope([L | [Integers() | i^j : j in [1..d]] : i in [1..n]] :
                                                            areVertices:=true);
end intrinsic;

intrinsic ConeToPolyhedron(C::TorCon) -> TorPol
{The cone C realised as a polyhedron}
    L,emb:=GradedToricLattice(Ambient(C));
    return Polyhedron(Cone(emb(RGenerators(C)) cat [default_origin(L,1)]));
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::SeqEnum[RngIntElt],h::RngIntElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HyperplaneToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::SeqEnum[RngIntElt],h::FldRatElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HyperplaneToPolyhedron(v,h);
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::SeqEnum[FldRatElt],h::RngIntElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HyperplaneToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::SeqEnum[FldRatElt],h::FldRatElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HyperplaneToPolyhedron(v,h);
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::TorLatElt,h::RngIntElt) -> TorPol
{}
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HyperplaneToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HyperplaneToPolyhedron(v::TorLatElt,h::FldRatElt) -> TorPol
{The hyperplane v * u = h realised as a polyhedron}
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    // Get the generators for the hyperplane
    u,K:=Solution(Transpose(Matrix(Rationals(),[v])),Matrix(1,1,[h]));
    L:=Dual(Parent(v));
    u:=L ! Eltseq(u);
    gens:=[L | Eltseq(gen) : gen in Basis(K)];
    LL,emb:=GradedToricLattice(L);
    // Move the generators into the graded lattice and create the cone
    C:=Cone([emb(u) + default_origin(LL,1)] cat
            [LL | emb(gen) : gen in gens] cat [LL | -emb(gen) : gen in gens]);
    // Return the polyhedron
    return Polyhedron(C);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::SeqEnum[RngIntElt],h::RngIntElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HalfspaceToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::SeqEnum[RngIntElt],h::FldRatElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HalfspaceToPolyhedron(v,h);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::SeqEnum[FldRatElt],h::RngIntElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HalfspaceToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::SeqEnum[FldRatElt],h::FldRatElt) -> TorPol
{}
    require not IsEmpty(v): "Argument 1 must not be empty";
    v:=Dual(lattice_from_cache(#v)) ! v;
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HalfspaceToPolyhedron(v,h);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::TorLatElt,h::RngIntElt) -> TorPol
{}
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    return HalfspaceToPolyhedron(v,Rationals() ! h);
end intrinsic;

intrinsic HalfspaceToPolyhedron(v::TorLatElt,h::FldRatElt) -> TorPol
{The halfspace v * u >= h realised as a polyhedron}
    require not IsZero(v): "Argument 1 cannot be the zero vector";
    // Get the generators for the supporting hyperplane
    u,K:=Solution(Transpose(Matrix(Rationals(),[v])),Matrix(1,1,[h]));
    L:=Dual(Parent(v));
    u:=L ! Eltseq(u);
    gens:=[L | Eltseq(gen) : gen in Basis(K)];
    LL,emb:=GradedToricLattice(L);
    // Move the generators into the graded lattice and create the cone
    origin:=default_origin(LL,1);
    C:=Cone([emb(u) + origin] cat [emb(L ! v)] cat
            [LL | emb(gen) : gen in gens] cat [LL | -emb(gen) : gen in gens]);
    // Return the polyhedron
    return Polyhedron(C);
end intrinsic;

intrinsic FixedSubspaceToPolyhedron(G::GrpMat) -> TorPol
{}
    n:=NumberOfRows(Representative(G));
    require G subset GL(n,Integers()) or G subset SL(n,Integers()):
        Sprintf("The group must be a subgroup of GL(%o,Z) or of SL(%o,Z)",n);
    return FixedSubspaceToPolyhedron(lattice_from_cache(n),G);
end intrinsic;

intrinsic FixedSubspaceToPolyhedron(L::TorLat,G::GrpMat) -> TorPol
{The subspace (realised as a polyhedron) fixed by the action of the matrix group G on the toric lattice L. G should be a subgroup of either GL(n,Z) or of SL(n,Z), where n is the dimension of L.}
    n:=Dimension(L);
    require G subset GL(n,Integers()) or G subset SL(n,Integers()):
        Sprintf("The group must be a subgroup of GL(%o,Z) or of SL(%o,Z)",n);
    // Collect together the normals describing the hyperplanes fixed by the
    // generators of G
    norms:=[Dual(L)|];
    for g in Generators(G) do
        M:=RowSequence(g);
        for i in [1..#M] do
            M[i][i] -:= 1;
            Append(~norms,M[i]);
        end for;
    end for;
    // Finally return the polyhedron generated by these inequalities
    norms cat:= [Dual(L) | -u : u in norms];
    return PolyhedronWithInequalities(norms,ZeroSequence(Integers(),#norms));
end intrinsic;

intrinsic RandomPolytope(L::TorLat,n::RngIntElt,k::RngIntElt) -> TorPol
{A random polytope in the toric lattice L, generated by n points whose coefficients lie between -k and k}
    require n ge 0: "Argument 2 must be a non-negative integer";
    d:=Dimension(L);
    if k le 0 then k:=-k; end if;
    return Polytope([L | [Random(2 * k) - k : i in [1..d]] : j in [1..n]]);
end intrinsic;

intrinsic RandomPolytope(d::RngIntElt,n::RngIntElt,k::RngIntElt) -> TorPol
{A random polytope in a d-dimensional toric lattice, generated by n points whose coefficients lie between -k and k}
    require d ge 1:
        "The dimension of the ambient toric lattice must be greater than zero";
    require n ge 0: "Argument 2 must be a non-negative integer";
    if n eq 0 then return EmptyPolyhedron(lattice_from_cache(d)); end if;
    if k le 0 then k:=-k; end if;
    return Polytope([PowerSequence(Integers()) |
                              [Random(2 * k) - k : i in [1..d]] : j in [1..n]]);
end intrinsic;

intrinsic PolytopeOfProjectiveSpace(d::RngIntElt) -> TorPol
{}
    require d ge 1: "The dimension must be at least one";
    return PolytopeOfWPS(lattice_from_cache(d),[Integers() | 1 : i in [0..d]]);
end intrinsic;

intrinsic PolytopeOfProjectiveSpace(L::TorLat) -> TorPol
{A simplex whose spanning fan corresponds to projective space P^d}
    d:=Dimension(L);
    require d ge 1: "The dimension must be at least one";
    return PolytopeOfWPS(L,[Integers() | 1 : i in [0..d]]);
end intrinsic;

intrinsic PolytopeOfWPS(d::RngIntElt) -> TorPol
{A simplex whose spanning fan corresponds to projective space P^d}
    require d ge 1: "The dimension must be at least one";
    return PolytopeOfWPS(lattice_from_cache(d),[Integers() | 1 : i in [0..d]]);
end intrinsic;

intrinsic PolytopeOfWPS(lambda::SeqEnum[RngIntElt]) -> TorPol
{}
    dim:=#lambda - 1;
    require dim ge 1: "The sequence of weights must be of length at least two";
    return PolytopeOfWPS(lattice_from_cache(dim),lambda);
end intrinsic;

intrinsic PolytopeOfWPS(L::TorLat,lambda::SeqEnum[RngIntElt]) -> TorPol
{A simplex whose spanning fan corresponds to weighted projective space P(lambda)}
    // Sanity check on the input
    dim:=#lambda - 1;
    require dim ge 1:
        "The sequence of weights must be of length at least two";
    require reduced_and_irreducible(lambda):
        "The weights must be reduced and irreducible";
    require dim eq Dimension(L):
        Sprintf("The ambient lattice must be of dimension %o",dim);
    // Calculate the coprime values
    d:=ZeroSequence(Integers(),dim + 1);
    d[1]:=lambda[1];
    for i in [1..dim] do
        d[i + 1]:=GCD(d[i],lambda[i + 1]);
    end for;
    // Set the easy values
    row:=ZeroSequence(Integers(),dim);
    v:=[PowerSequence(Integers()) | row : i in [1..dim + 1]];
    for i in [1..dim] do
        v[i + 1][i]:=d[i] div d[i + 1];
    end for;
    // Now set the more difficult values
    c:=[Integers()|];
    for i in [2..dim] do
        // Set the final c value
        c[i + 1]:=d[i] div d[i + 1];
        kappa:=Integers() ! (c[i + 1] * lambda[i + 1]);
        // Step backwards through each column setting the value
        for j in [i - 1..1 by -1] do
            // Reduce the values of d[j], kappa, and lambda[j + 1] as much
            // as possible
            gcd:=GCD(d[j + 1],kappa);
            nd:=d[j] div gcd;
            nk:=kappa div gcd;
            nl:=lambda[j + 1] div gcd;
            // Start searching for integer solutions
            k:=nk div nd;
            while (nd * k - nk) mod nl ne 0 do
                k +:= 1;
            end while;
            c[j + 1]:=(nd * k - nk) div nl;
            // Set the entry
            v[j + 1][i]:=c[j + 1];
            // Increase the value of kappa accordingly
            kappa +:= c[j + 1] * lambda[j + 1];
        end for;
    end for;
    // Finally set the first vertex
    for i in [1..dim] do
        for j in [1..dim] do
            v[1][i] -:= v[j + 1][i] * lambda[j + 1];
        end for;
        v[1][i] div:= lambda[1];
    end for;
    // Return the polytope
    ChangeUniverse(~v,L);
    return Polytope(v : areVertices:=true);
end intrinsic;

intrinsic PolyhedronWithInequalities(A::SeqEnum[SeqEnum[RngIntElt]],
    c::SeqEnum[RngIntElt]) -> TorPol
{}
    require not IsEmpty(A): "Polyhedron must have at least one inequality";
    dim:=#A[1];
    require &and[#u eq dim:u in A]:"Inequalities must be of the same dimension";
    D:=Dual(lattice_from_cache(dim));
    ChangeUniverse(~A,D);
    return PolyhedronWithInequalities(A,c);
end intrinsic;

intrinsic PolyhedronWithInequalities(A::SeqEnum[SeqEnum[FldRatElt]],
    c::SeqEnum[RngIntElt]) -> TorPol
{}
    require not IsEmpty(A): "Polyhedron must have at least one inequality";
    dim:=#A[1];
    require &and[#u eq dim:u in A]:"Inequalities must be of the same dimension";
    D:=Dual(lattice_from_cache(dim));
    ChangeUniverse(~A,D);
    return PolyhedronWithInequalities(A,c);
end intrinsic;

intrinsic PolyhedronWithInequalities(A::SeqEnum[TorLatElt],
    c::SeqEnum[RngIntElt]) -> TorPol
{The polyhedron defined by Ai*v >= ci for each Ai,ci in A,c}
    require not IsNull(A): "Illegal null sequence";
    require #A eq #c: "Sequences must be of the same length";
    L,emb:=GradedToricLattice(Universe(A));
    return Polyhedron(ConeWithInequalities([L |
                                [-c[i]] cat Eltseq(A[i]) : i in [1..#A]]));
end intrinsic;

intrinsic EmptyPolyhedron(d::RngIntElt) -> TorPol
{The empty polyhedron in a d-dimensional toric lattice}
    require d gt 0: "The dimension must be a positive integer";
    return EmptyPolyhedron(lattice_from_cache(d));
end intrinsic;

intrinsic EmptyPolyhedron(L::TorLat) -> TorPol
{The empty polyhedron in the given toric lattice L}
    if not assigned L`empty_polytope then
        P:=New(TorPol);
        P`has_lattice_point:=false;
        P`is_empty:=true;
        P`dimension:=-1;
        P`fp_dimension:=-1;
        P`fp_triangulation:={PowerSet(Integers())|};
        P`fp_volume:=0;
        P`amb_fp_generators:=[L|];
        P`amb_are_vertices:=true;
        P`amb_num_facets:=0;
        if Dimension(L) ne 0 then
            P`amb_ng:=ng_build_from_facets([L|],
                  {to_halfspace(Dual(L).1,1,-1),to_halfspace(Dual(L).1,-1,-1)});
        else
            P`amb_ng:=ng_build_from_facets([L|],{});
        end if;
        P`is_simplicial:=true;
        P`is_smooth:=true;
        L`empty_polytope:=P;
    end if;
    return L`empty_polytope;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Constructions from existing polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic PolyhedronInSublattice(P::TorPol) -> TorPol,Map[TorLat,TorLat],TorLatElt
{The polyhedron of maximal dimension given by the intersection of the toric lattice containing the polyhedron P with an affine sublattice of dimension equal to the dimension of P. Also gives the affine embedding as a lattice embedding and translation.}
    if not assigned P`max_dim_poly then
        if IsMaximumDimensional(P) then
            return P,IdentityMap(Ambient(P)),Zero(Ambient(P));
        end if;
        // Check that there exists a sublattice such that P is maximal
        require not IsEmpty(P) and amb_has_volume_form(P):
            "There does not exist an affine sublattice in which the polyhedron is of maximum dimension";
        // Calculate the affine sublattice containing P
        _,Hs:=amb_partition_halfspaces_by_task(P);
        trans,K:=Solution(Transpose(Matrix(Integers(),[H[1][1] : H in Hs])),
                          Matrix(1,#Hs,[Integers() | H[1][2] : H in Hs]));
        trans:=Ambient(P) ! Eltseq(trans);
        L,emb:=Sublattice([Ambient(P) | Eltseq(v) : v in Basis(K)]);
        // Create the maximum dimensional version of P
        P`max_dim_poly:=create_maximum_dimensional(P,emb,trans);
        P`max_dim_emb:=emb;
        P`max_dim_trans:=trans;
    end if;
    return P`max_dim_poly,P`max_dim_emb,P`max_dim_trans;
end intrinsic;

intrinsic CompactPart(P::TorPol) -> TorPol
{The polytope defined by taking the convex hull of the vertices of the polyhedron P. If P is not pointed then gives a (non-unique) polytope Q such that Q + infinite part equals P.}
    if not assigned P`compact_part then
        if IsPolytope(P) then return P; end if;
        if IsPointed(P) then
            P`compact_part:=Polytope(Vertices(P) : areVertices:=true);
        else
            P`compact_part:=Polytope(amb_get_fp_generating_points(P));
        end if;
    end if;
    return P`compact_part;
end intrinsic;

intrinsic BoundingBox(P::TorPol) -> TorPol,TorLatElt,TorLatElt
{The smallest polytope Q that is a hyper-box and contains the polytope P. Also gives the bottom-left and top-right corners of the box.}
    require IsPolytope(P): "The argument must be a polytope";
    // Build the corners of the box
    min,max:=bounding_box([PowerSequence(Rationals()) | Eltseq(v) :
                                        v in amb_get_fp_generating_points(P)]);
    B:=ChangeUniverse(all_corners(min,max), Ambient(P));
    // Return the polytope
    return Polytope(B : areVertices:=true), Ambient(P) ! min, Ambient(P) ! max;
end intrinsic;

