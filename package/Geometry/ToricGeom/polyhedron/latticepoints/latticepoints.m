freeze;

/////////////////////////////////////////////////////////////////////////
// latticepoints.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38137 $
// $Date: 2012-04-13 00:14:20 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating lattice points in the finite-part of P.
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": bounding_box, knapsack_repeats;
import "../../lattice/lattice.m": lattice_from_cache;
import "../../lattice/hyperplane.m": cmp_hyperplane_and_point;
import "../convexhull/sublattice.m": fp_emb_map, fp_emb_lattice;
import "../convexhull/convexhull.m": fp_get_pullback_vertices, fp_get_pullback_halfspaces;
import "../faces/support.m": amb_has_volume_form;
import "../polyhedron.m": create_maximum_dimensional;
import "../coneembedding.m": ce_get_cone, ce_get_height;
import "ehrhart.m": number_of_points;
import "dim1.m": dim_1_points, dim_1_number_of_points, dim_1_boundary_points, dim_1_number_of_boundary_points, dim_1_interior_points, dim_1_number_of_interior_points;
import "dim2.m": dim_2_number_of_points, dim_2_boundary_points, dim_2_number_of_boundary_points, dim_2_number_of_interior_points;
import "reflexive.m": points_in_reflexive;
import "simplex.m": points_in_simplex;
import "simplicial.m": points_in_simplicialcomplex;

declare attributes TorPol:
    points,                     // The lattice points in P
    interior_points,            // The lattice points strictly in P
    num_interior_points,        // The number of interior lattice points
    boundary_points,            // The boundary points of P
    num_boundary_points,        // The number of boundary lattice points
    integral_part;              // The integral part of P

/////////////////////////////////////////////////////////////////////////
// Local functions for general dimension
/////////////////////////////////////////////////////////////////////////

// 'num' is the number of points to search for; if you don't know, set to -1.
// THINK: This is a very clumsy way of finding the points -- one alternative
// is to emulate what we do with Z-generators of cones. When P is simplicial
// and contains the origin we can compute the fundamental domain over each face
// and very easily calculate the interior points in the original lattice.
procedure general_points_recurse(P,min,max,idx,pt,~pts,~num)
    if idx lt #min then
        for i in [Ceiling(min[idx])..Floor(max[idx])] do
            if num eq 0 then break; end if;
            $$(P,min,max,idx+1,Append(pt,i),~pts,~num);
        end for;
    else
        min:=Ceiling(min[idx]);
        max:=Floor(max[idx]);
        hs:=fp_get_pullback_halfspaces(P);
        v:=fp_emb_lattice(P) ! Append(pt,min);
        minvec:=[Integers()|cmp_hyperplane_and_point(h[1],v) * h[2] : h in hs];
        if &and[sgn ge 0 : sgn in minvec] then
            inP:=true;
            Append(~pts,v);
            num-:=1;
            if num eq 0 then return; end if;
        else
            inP:=false;
        end if;
        if max eq min then return; end if;
        v:=fp_emb_lattice(P) ! Append(pt,max);
        maxvec:=[Integers()|cmp_hyperplane_and_point(h[1],v) * h[2] : h in hs];
        if &and[sgn ge 0 : sgn in maxvec] then
            Append(~pts,v);
            num-:=1;
            if num eq 0 then return; end if;
            if inP then
                for i in [min + 1..max - 1] do
                    Append(~pts,fp_emb_lattice(P) ! Append(pt,i));
                    num-:=1;
                    if num eq 0 then return; end if;
                end for;
                return;
            end if;
        end if;
        if &or[minvec[i] lt 0 : i in [1..#hs] | minvec[i] eq maxvec[i]] then
            return;
        end if;
        differences:=[Integers() | i : i in [1..#hs] | minvec[i] ne maxvec[i]];
        for i in [min + 1..max - 1] do
            v:=fp_emb_lattice(P) ! Append(pt,i);
            vec:=[Integers() | cmp_hyperplane_and_point(hs[i][1],v) * hs[i][2] :
                                                              i in differences];
            vinP:=&and[sgn ge 0 : sgn in vec];
            if vinP then
                Append(~pts,v);
                num-:=1;
                if num eq 0 then return; end if;
                inP:=true;
            elif inP then
                return;
            end if;
        end for;
    end if;
end procedure;

function general_points(P,num)
    if assigned P`has_lattice_point and not P`has_lattice_point then
        return {Ambient(P)|}; end if;
    if not amb_has_volume_form(P) then
        return {Ambient(P)|}; end if;
    // We do the calculation in the "finite part" lattice L'
    pts:=[fp_emb_lattice(P)|];
    min,max:=bounding_box([Eltseq(v) : v in fp_get_pullback_vertices(P)]);
    general_points_recurse(P,min,max,1,[Integers()|],~pts,~num);
    // Now we need to lift the points back into the ambient lattice L
    trans,emb:=fp_emb_map(P);
    return {Ambient(P) | emb(u) + trans : u in pts};
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure pts_apply_translation(P,CP,Q)
    if IsIntegral(Q) then
        if assigned P`points then
            CP`points:={Ambient(P) | v + Q : v in P`points}; end if;
        if assigned P`interior_points then
            CP`interior_points:={Ambient(P) | v + Q : v in P`interior_points};
        end if;
        if assigned P`boundary_points then
            CP`boundary_points:={Ambient(P) | v + Q : v in P`boundary_points};
        end if;
        if assigned P`num_interior_points then
            CP`num_interior_points:=P`num_interior_points; end if;
        if assigned P`num_boundary_points then
            CP`num_boundary_points:=P`num_boundary_points; end if;
        if assigned P`integral_part then
            if P ne P`integral_part then
                CP`integral_part:=P`integral_part + Q;
            else
                CP`integral_part:=CP;
            end if;
        end if;
    end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure pts_apply_negation(P,CP)
    if assigned P`points then
        CP`points:={Ambient(P) | -v : v in P`points}; end if;
    if assigned P`interior_points then
        CP`interior_points:={Ambient(P) | -v : v in P`interior_points}; end if;
    if assigned P`boundary_points then
        CP`boundary_points:={Ambient(P) | -v : v in P`boundary_points}; end if;
    if assigned P`num_interior_points then
        CP`num_interior_points:=P`num_interior_points; end if;
    if assigned P`num_boundary_points then
        CP`num_boundary_points:=P`num_boundary_points; end if;
    if assigned P`integral_part then
        if P ne P`integral_part then
            CP`integral_part:=-P`integral_part;
        else
            CP`integral_part:=CP;
        end if;
    end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure pts_change_ambient(P,CP,L)
    if assigned P`points then
        CP`points:=ChangeUniverse(P`points,L); end if;
    if assigned P`interior_points then
        CP`interior_points:=ChangeUniverse(P`interior_points,L); end if;
    if assigned P`boundary_points then
        CP`boundary_points:=ChangeUniverse(P`boundary_points,L); end if;
    if assigned P`num_interior_points then
        CP`num_interior_points:=P`num_interior_points; end if;
    if assigned P`num_boundary_points then
        CP`num_boundary_points:=P`num_boundary_points; end if;
    if assigned P`integral_part then
        if P ne P`integral_part then
            CP`integral_part:=ChangeAmbient(P`integral_part,L);
        else
            CP`integral_part:=CP;
        end if;
    end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure pts_change_to_maximal(P,CP,emb,trans)
    L:=Domain(emb);
    if assigned P`points then
        CP`points:={L | (v - trans) @@ emb : v in P`points}; end if;
    if assigned P`interior_points then
        CP`interior_points:={L | (v - trans) @@ emb : v in P`interior_points};
    end if;
    if assigned P`boundary_points then
        CP`boundary_points:={L | (v - trans) @@ emb : v in P`boundary_points};
    end if;
    if assigned P`num_interior_points then
        CP`num_interior_points:=P`num_interior_points; end if;
    if assigned P`num_boundary_points then
        CP`num_boundary_points:=P`num_boundary_points; end if;
    if assigned P`integral_part then
        if P ne P`integral_part then
            CP`integral_part:=
                    create_maximum_dimensional(P`integral_part,emb,trans);
        else
            CP`integral_part:=CP;
        end if;
    end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Lattice points
/////////////////////////////////////////////////////////////////////////

intrinsic Points(P::TorPol) -> SetEnum[TorLatElt]
{The integral lattice points in the polytope P}
    if not assigned P`points then
        require IsPolytope(P): "Polyhedron must be a polytope";
        if amb_has_volume_form(P) then
            d:=Dimension(P);
            if d lt 0 then
                P`points:={Ambient(P)|};
            elif d eq 0 then
                pt:=Representative(Vertices(P));
                P`points:=IsIntegral(pt) select {Ambient(P) | pt}
                                           else {Ambient(P)|};
            elif d eq 1 then
                P`points:=dim_1_points(P);
            elif IsReflexive(P) then
                if IsSmooth(P) then
                    pts:=SequenceToSet(Vertices(P));
                    Include(~pts,Zero(Ambient(P)));
                    P`points:=pts;
                else
                    P`points:=points_in_reflexive(P);
                end if;
            elif IsIntegral(P) and IsSimplex(P) then
                P`points:=points_in_simplex(P);
            elif IsIntegral(P) and ContainsZero(P) then
                P`points:=points_in_simplicialcomplex(P);
            else
                if assigned P`Ehrhart_coeffs and
                    IsDefined(P`Ehrhart_coeffs,1) then
                    P`points:=general_points(P,P`Ehrhart_coeffs[1]);
                else
                    P`points:=general_points(P,-1);
                end if;
            end if;
            // If we've found a lattice point and a non-lattice representative
            // is set, update the representative point to be a lattice point
            if assigned P`representative and not IsIntegral(P`representative)
                and #P`points gt 0 then
                P`representative:=Representative(P`points);
            end if;
        else
            P`points:={Ambient(P)|};
        end if;
    end if;
    return P`points;
end intrinsic;

intrinsic NumberOfPoints(P::TorPol) -> RngIntElt
{The number of integral lattice points in the polytope P}
    if not assigned P`Ehrhart_coeffs or not IsDefined(P`Ehrhart_coeffs,1) then
        if not assigned P`Ehrhart_coeffs then
            P`Ehrhart_coeffs:=[Integers()|];
        end if;
        if assigned P`points then
            P`Ehrhart_coeffs[1]:=#P`points;
        elif assigned P`num_interior_points and
            assigned P`num_boundary_points then
            P`Ehrhart_coeffs[1]:=P`num_interior_points + P`num_boundary_points;
        else
            require IsPolytope(P): "Polyhedron must be a polytope";
            if not amb_has_volume_form(P) then
                P`Ehrhart_coeffs[1]:=0;
            elif IsSmooth(P) then
                P`Ehrhart_coeffs[1]:=NumberOfVertices(P) + 1;
            elif assigned P`fp_decomposition then
                P`Ehrhart_coeffs[1]:=number_of_points(P);
            else
                d:=Dimension(P);
                if d lt 0 then
                    P`Ehrhart_coeffs[1]:=0;
                elif d eq 0 then
                    pt:=Representative(fp_get_pullback_vertices(P));
                    P`Ehrhart_coeffs[1]:=IsIntegral(pt) select 1 else 0;
                elif d eq 1 then
                    P`Ehrhart_coeffs[1]:=dim_1_number_of_points(P);
                elif d eq 2 and IsIntegral(P) then
                    P`Ehrhart_coeffs[1]:=dim_2_number_of_points(P);
                elif d eq 3 then
                    // The dimension 3 dichotomy -- the threshold 9.5 is from
                    // experimental evidence with random polytopes
                    min,max:=bounding_box([Eltseq(v) :
                                             v in fp_get_pullback_vertices(P)]);
                    vol:=(&*[max[i] - min[i] : i in [1..#max]])^(1/3);
                    if vol ge 9.5 then
                        P`Ehrhart_coeffs[1]:=number_of_points(P);
                    else
                        P`Ehrhart_coeffs[1]:=#Points(P);
                    end if;
                elif d eq 4 then
                    // The dimension 4 dichotomy -- the threshold 16.5 is from
                    // experimental evidence with random polytopes
                    min,max:=bounding_box([Eltseq(v) :
                                             v in fp_get_pullback_vertices(P)]);
                    vol:=(&*[max[i] - min[i] : i in [1..#max]])^(1/4);
                    if vol ge 16.5 then
                        P`Ehrhart_coeffs[1]:=number_of_points(P);
                    else
                        P`Ehrhart_coeffs[1]:=#Points(P);
                    end if;
                else
                    // For dimension > 4 we default to Barvinok's algorithm;
                    // THINK: It might we worth estimating thresholds in these
                    // cases too
                    P`Ehrhart_coeffs[1]:=number_of_points(P);
                end if;
            end if;
        end if;
    end if;
    return P`Ehrhart_coeffs[1];
end intrinsic;

intrinsic InteriorPoints(P::TorPol) -> SetEnum[TorLatElt]
{The integral lattice points in the strict interior of the polytope P}
    if not assigned P`interior_points then
        require IsPolytope(P): "Polyhedron must be a polytope";
        if amb_has_volume_form(P) then
            d:=Dimension(P);
            if d le 0 then
                P`interior_points:={Ambient(P)|};
            elif d eq 1 then
                P`interior_points:=dim_1_interior_points(P);
            else
                if IsReflexive(P) then
                    P`interior_points:={Ambient(P) | Zero(Ambient(P))};
                elif assigned P`boundary_points then
                    P`interior_points:=Points(P) diff P`boundary_points;
                else
                    P`interior_points:={Ambient(P) | pt : pt in Points(P) |
                                                            IsInInterior(pt,P)};
                end if;
            end if;
        else
            P`interior_points:={Ambient(P)|};
        end if;
    end if;
    return P`interior_points;
end intrinsic;

intrinsic NumberOfInteriorPoints(P::TorPol) -> RngIntElt
{The number of integral lattice points in the strict interior of the polytope P}
    if not assigned P`num_interior_points then
        if not assigned P`interior_points then
            require IsPolytope(P): "Polyhedron must be a polytope";
            if amb_has_volume_form(P) then
                d:=Dimension(P);
                if d le 0 then
                    P`num_interior_points:=0;
                elif d eq 1 then
                    P`num_interior_points:=dim_1_number_of_interior_points(P);
                elif d eq 2 and IsIntegral(P) then
                    P`num_interior_points:=dim_2_number_of_interior_points(P);
                else
                    // In the general case we try to exploit whatever data we
                    // might already know
                    if IsReflexive(P) then
                        P`num_interior_points:=1;
                    elif assigned P`Ehrhart_gen_func and IsIntegral(P) then
                        P`num_interior_points:=EhrhartCoefficient(P,-1)*(-1)^d;
                    else
                        P`num_interior_points:=#InteriorPoints(P);
                    end if;
                end if;
            else
                P`num_interior_points:=0;
            end if;
        else
            P`num_interior_points:=#InteriorPoints(P);
        end if;
    end if;
    return P`num_interior_points;
end intrinsic;

intrinsic BoundaryPoints(P::TorPol) -> SetEnum[TorLatElt]
{The integral lattice points on the boundary of the polytope P}
    if not assigned P`boundary_points then
        require IsPolytope(P): "Polyhedron must be a polytope";
        if amb_has_volume_form(P) then
            d:=Dimension(P);
            if d le 0 then
                P`boundary_points:={Ambient(P)|};
            elif d eq 1 then
                P`boundary_points:=dim_1_boundary_points(P);
            elif d eq 2 and IsIntegral(P) then
                P`boundary_points:=dim_2_boundary_points(P);
            else
                if assigned P`points then
                    if assigned P`interior_points then
                        P`boundary_points:=P`points diff P`interior_points;
                    else
                        P`boundary_points:={Ambient(P) | pt : pt in P`points |
                                                            IsOnBoundary(pt,P)};
                    end if;
                else
                    P`boundary_points:=&join[Points(F) : F in Facets(P)];
                end if;
            end if;
        else
            P`boundary_points:={Ambient(P)|};
        end if;
    end if;
    return P`boundary_points;
end intrinsic;

intrinsic NumberOfBoundaryPoints(P::TorPol) -> RngIntElt
{The number of integral lattice points on the boundary of the polytope P}
    if not assigned P`num_boundary_points then
        if not assigned P`boundary_points then
            require IsPolytope(P): "Polyhedron must be a polytope";
            if amb_has_volume_form(P) then
                d:=Dimension(P);
                if d le 0 then
                    P`num_boundary_points:=0;
                elif d eq 1 then
                    P`num_boundary_points:=dim_1_number_of_boundary_points(P);
                elif d eq 2 and IsIntegral(P) then
                    P`num_boundary_points:=dim_2_number_of_boundary_points(P);
                else
                    // In the general case we try to exploit whatever data we
                    // might already know
                    if IsReflexive(P) then
                        P`num_boundary_points:=NumberOfPoints(P) - 1;
                    elif assigned P`Ehrhart_gen_func and IsIntegral(P) then
                        P`num_boundary_points:=NumberOfPoints(P) -
                                               NumberOfInteriorPoints(P);
                    else
                        P`num_boundary_points:=#BoundaryPoints(P);
                    end if;
                end if;
            else
                P`num_boundary_points:=0;
            end if;
        else
            P`num_boundary_points:=#BoundaryPoints(P);
        end if;
    end if;
    return P`num_boundary_points;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Fixed points
/////////////////////////////////////////////////////////////////////////

intrinsic FixedPoints(P::TorPol,G::GrpMat) -> SetEnum[TorLatElt]
{The integral lattice points in the polyhedron P fixed by the action of the matrix group G acting on the ambient toric lattice. G should be a subgroup of either GL(n,Z) or of SL(n,Z), where n is the dimension of the lattice.}
    n:=Dimension(Ambient(P));
    require G subset GL(n,Integers()) or G subset SL(n,Integers()):
        Sprintf("The group must be a subgroup of GL(%o,Z) or of SL(%o,Z)",n);
    // If there's no volume form this is trivial
    if not amb_has_volume_form(P) then
        return {Ambient(P)|}; end if;
    // Collect together the normals describing the hyperplanes fixed by the
    // generators of G
    norms:=[Dual(Ambient(P))|];
    for g in Generators(G) do
        M:=RowSequence(g);
        for i in [1..#M] do
            M[i][i] -:= 1;
            Append(~norms,M[i]);
        end for;
    end for;
    // If we know the points of P then this is just a simple evaluation check...
    if assigned P`points then
        return {Ambient(P) | v : v in P`points | &and[v * u eq 0 : u in norms]};
    // ...otherwise we create the fixed subspace and intersect
    else
        norms cat:= [Dual(Ambient(P)) | -u : u in norms];
        H:=PolyhedronWithInequalities(norms,ZeroSequence(Integers(),#norms));
        fixed:=P meet H;
        // Assert that this region is a polytope
        require IsPolytope(fixed):
            "The set of integral lattice points in the polygon fixed by the group action is infinite";
        // Return the points
        return Points(fixed);
    end if;
end intrinsic;
    
/////////////////////////////////////////////////////////////////////////
// Integral part
/////////////////////////////////////////////////////////////////////////

intrinsic IntegralPart(P::TorPol) -> TorPol
{The polyhedron defined by taking the convex hull of the integral points in the polyhedron P}
    if not assigned P`integral_part then
        // Get the easy case out of the way first
        if IsIntegral(P) then return P; end if;
        // Is P empty, a polytope or a polyhedron?
        if not amb_has_volume_form(P) then
            P`integral_part:=EmptyPolyhedron(Ambient(P));
        elif IsPolytope(P) then
            P`integral_part:=Polytope(Points(P));
        else
            C:=ce_get_cone(P);
            height:=ce_get_height(P);
            // If P is naturally embedded at height 1, this is easy
            if height eq 1 then
                grading:=Grading(C);
                zgens:=[Ambient(C) | gen : gen in ZGenerators(C : level:=1) |
                                                            gen * grading le 1];
                if IsEmpty(zgens) then
                    P`integral_part:=EmptyPolyhedron(Ambient(P));
                else
                    CC:=Cone(zgens);
                    origin:=ScalarLattice().1 @@ LatticeMap(grading);
                    // Create the polyhedron
                    P`integral_part:=Polyhedron(CC);
                end if;
            else
                grading:=Grading(C);
                zgens:=[Ambient(C) | gen : gen in ZGenerators(C:level:=height) |
                                                       gen * grading le height];
                if IsEmpty(zgens) then
                    P`integral_part:=EmptyPolyhedron(Ambient(P));
                else
                    zgens_gradings:=[Integers() | gen * grading : gen in zgens];
                    S:=Exclude(Setseq(Seqset(zgens_gradings)),0);
                    SS:=knapsack_repeats(S,height);
                    new:=[[Ambient(C)|] :  i in [1..Maximum(S)]];
                    for i in [1..#zgens] do
                        if not IsZero(zgens_gradings[i]) then
                            Append(~new[zgens_gradings[i]],zgens[i]);
                        end if;
                    end for;
                    L:=lattice_from_cache(#S);
                    Csmall:=Cone([L | &+[L.Index(S,a) : a in s] : s in SS]);
                    M:=[{*S[i]^^e[i] : i in [1..#e] *} where e is Eltseq(v) :
                                               v in MinimalRGenerators(Csmall)];
                    new_cone:=[Ambient(C)|r:r in RGenerators(C)|r*grading eq 0];
                    for i in M do
                        this_type:=[Zero(Ambient(C))];
                        for j in Set(i) do
                            here:=[Multiplicity(i,j) * zgen : zgen in new[j] ];
                            this_type:=[v + w :v in this_type, w in here];
                        end for;
                        new_cone cat:= this_type;
                    end for;
                    new_cone:=Cone(new_cone);
                    P`integral_part:=Polyhedron(new_cone: level:=height);
                end if;
            end if;
        end if; 
        // The integral part of the integral part is itself, of course
        P`integral_part`integral_part:=P`integral_part;
    end if;
    return P`integral_part;
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Nonvanishing form
/////////////////////////////////////////////////////////////////////////

intrinsic NonvanishingForm(P::TorPol) -> TorLatElt
{A point u in the toric lattice dual to the ambient of the polyhedron P such that u * v is non-zero for all non-zero v in P}
    // Set the data we'll need
    D:=Dual(Ambient(P));
    d:=Dimension(Ambient(P));
    zero:=Zero(Ambient(P)) in P;
    // Split into cases -- polytope and polyhedron
    if IsPolytope(P) then
        // If the points are known then we can use the lattice-points version
        if assigned P`points then
            if zero then
                return NonvanishingForm(Exclude(P`points,Zero(Ambient(P))));
            else
                return NonvanishingForm(P`points);
            end if;
        end if;
        // The algorithm in the polytope case is deterministic
        i:=0;
        while true do
            u:=PrimitiveLatticeVector(D ! [Integers() | i^j : j in [0..d - 1]]);
            if zero then
                if NumberOfPoints(Polyhedron(P,u,0)) eq 1 then
                    return u;
                end if;
            else
                if not HasIntegralPoint(Polyhedron(P,u,0)) then
                    return u;
                end if;
            end if;
            i+:=1;
        end while;
    else
        // Sanity check -- if P isn't strictly convex then it had better not
        // contain the origin
        require IsStrictlyConvex(InfinitePart(P)) or not zero:
            "No non-vanishing form exists for this polyhedron";
        // The algorithm in the polyhedron case is non-deterministic
        i:=1;
        while true do
            u:=PrimitiveLatticeVector(D ! [Integers() |
                                          Random(2 * i) - i : j in [0..d - 1]]);
            if not IsZero(u) then
                Q:=Polyhedron(P,u,0);
                if IsPolytope(Q) then
                    if zero then
                        if NumberOfPoints(Q) eq 1 then return u; end if;
                    else
                        if not HasIntegralPoint(Q) then return u; end if;
                    end if;
                end if;
                i+:=1;
            end if;
        end while;
    end if;
end intrinsic;
