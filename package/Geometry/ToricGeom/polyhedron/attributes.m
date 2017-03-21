freeze;

/////////////////////////////////////////////////////////////////////////
// attributes.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27450 $
// $Date: 2010-06-18 10:39:58 +1000 (Fri, 18 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Intrinsics for returning attributes of polyhedra.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// The distinction between attributes and properties isn't totally clear,
// but I'm assuming that it is approximately as follows:
//  * if the question it's answering is of the form "is it true that...?"
//    then it is a property of P;
//  * if, however, the question is more a request ("give me the...") then
//    I regard it as an attribute.
// For example, the intrinsic "IsSimplicial(P)" belongs in properties.m,
// and the intrinsic "Ambient(P)" belongs in attributes.m.
/////////////////////////////////////////////////////////////////////////

import "../lattice/gradedlattice.m": default_origin;
import "../lattice/point.m": nonvanishing_form;
import "../lattice/hyperplane.m": point_on_halfspace_boundary;
import "latticepoints/ehrhart.m": reduce_to_univariate;
import "latticepoints/latticepoints.m": general_points;
import "properties.m": intersection_has_integral_point;
import "faces/support.m": amb_has_volume_form, amb_get_fp_generating_points, amb_get_halfspaces, amb_decomposition_of_cone_at_vertex;

declare attributes TorPol:
    ambient,            // The ambient toric lattice of P
    has_lattice_point,  // Is there an integral lattice point in P?
    representative,     // A point in P, chosen to be integral if cheap
    codegree,           // The codegree of P (if known)
    ip_cone;            // The infinite part of P

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Works very hard to return an integral point in P if possible. Otherwise
// returns a rational point.
function integral_representative(P)
    // First we see what Representative can offer us
    if not IsIntegral(Representative(P)) and
        (not assigned P`has_lattice_point or P`has_lattice_point) then
        // Search for a point amongst the generators of the finite part
        for pt in amb_get_fp_generating_points(P) do
            if IsIntegral(pt) then
                P`representative:=pt;
                return P`representative;
            end if;
        end for;
        // If we're here then the easy check failed
        if IsPolytope(P) then
            // If P is a polytope we make use of the Points() intrinsic
            if assigned P`points then
                if #P`points eq 0 then
                    P`has_lattice_point:=false;
                else
                    P`representative:=Representative(P`points);
                end if;
            else
                pts:=general_points(P,1);
                if #pts eq 0 then
                    P`has_lattice_point:=false;
                    P`points:={Ambient(P)|};
                else
                    P`representative:=Representative(pts);
                end if;
            end if;
        else
            // If P is a polyhedron, is the integral part already known?
            if assigned P`integral_part then
                if IsEmpty(P`integral_part) then
                    P`has_lattice_point:=false;
                else
                    P`representative:=Representative(P`integral_part);
                end if;
            else
                // We try looking in the convex hull of the generators
                if Dimension(CompactPart(P)) gt 0 then
                    pts:=general_points(P,1);
                    if #pts ne 0 then
                        P`representative:=Representative(pts);
                        return P`representative;
                    end if;
                end if;
                // If P contains lines then we might be able to work on the
                // quotient
                if not IsPointed(P) then
                    L,quot:=Quotient(LinearSpanGenerators(InfinitePart(P)));
                    LL,emb:=GradedToricLattice(L);
                    origin:=default_origin(LL,1);
                    C:=Cone([LL | emb(quot(v)) + origin :
                                v in amb_get_fp_generating_points(P)] cat
                            [LL | emb(quot(gen)) :
                                gen in RGenerators(InfinitePart(P))]);
                    PP:=Polyhedron(C);
                    v:=integral_representative(PP) @@ quot;
                    if IsIntegral(v) then
                        P`representative:=v;
                        return P`representative;
                    end if;
                end if;
                // No luck? We'll have to compute the integral part
                if IsEmpty(IntegralPart(P)) then
                    P`has_lattice_point:=false;
                else
                    P`representative:=Representative(P`integral_part);
                end if;
            end if;
        end if;
    end if;
    // We've done all we can, so return what we have
    return P`representative;
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Applies the translation by the vector Q to the data of P, storing the results
// that can be adjusted in CP.
procedure attr_apply_translation(P,CP,Q)
    if assigned P`ambient then
        CP`ambient:=P`ambient; end if;
    if assigned P`has_lattice_point and IsIntegral(Q) then
        CP`has_lattice_point:=P`has_lattice_point; end if;
    if assigned P`representative and IsIntegral(P`representative) and
        IsIntegral(Q) then
        CP`representative:=Q + P`representative; end if;
    if assigned P`codegree and IsIntegral(Q) then
        CP`codegree:=P`codegree; end if;
    if assigned P`ip_cone then
        CP`ip_cone:=P`ip_cone; end if;
end procedure;

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure attr_apply_negation(P,CP)
    if assigned P`ambient then
        CP`ambient:=P`ambient; end if;
    if assigned P`has_lattice_point then
        CP`has_lattice_point:=P`has_lattice_point; end if;
    if assigned P`representative then
        CP`representative:=-P`representative; end if;
    if assigned P`codegree then
        CP`codegree:=P`codegree; end if;
    if assigned P`ip_cone then
        CP`ip_cone:=-P`ip_cone; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure attr_apply_dilation(P,CP,k)
    if assigned P`ambient then
        CP`ambient:=P`ambient; end if;
    if assigned P`has_lattice_point and P`has_lattice_point and
        IsIntegral(k) then
        CP`has_lattice_point:=true; end if;
    if assigned P`representative and IsIntegral(P`representative) and
        IsIntegral(k * P`representative) then
        CP`representative:=k * P`representative; end if;
    if assigned P`codegree and IsIntegral(k) then
        if Abs(k) ge P`codegree then
            CP`codegree:=1;
        else
            CP`codegree:=Ceiling(P`codegree / Abs(k));
        end if;
    end if;
    if assigned P`ip_cone then
        CP`ip_cone:=P`ip_cone; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure attr_change_ambient(P,CP,L)
    CP`ambient:=L;
    if assigned P`has_lattice_point then
        CP`has_lattice_point:=P`has_lattice_point; end if;
    if assigned P`representative then
        CP`representative:=L ! P`representative; end if;
    if assigned P`codegree then
        CP`codegree:=P`codegree; end if;
    if assigned P`ip_cone then
        CP`ip_cone:=ChangeAmbient(P`ip_cone,L); end if;
end procedure;

// Adjusts the data of P to reflect the given maximum embedding data, storing
// the results in CP.
procedure attr_change_to_maximal(P,CP,emb,trans)
    CP`ambient:=Domain(emb);
    if assigned P`has_lattice_point then
        CP`has_lattice_point:=P`has_lattice_point; end if;
    if assigned P`representative then
        CP`representative:=(P`representative - trans) @@ emb; end if;
    if assigned P`ip_cone then
        CP`ip_cone:=P`ip_cone @@ emb; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Attributes of polytopes and polyhedra
/////////////////////////////////////////////////////////////////////////

intrinsic Ambient(P::TorPol)-> TorLat
{The ambient toric lattice of the polyhedron P}
    if not assigned P`ambient then
        if assigned P`representative then
            P`ambient:=Parent(P`representative);
        elif assigned P`ip_cone then
            P`ambient:=Ambient(P`ip_cone);
        elif assigned P`sub_embedding then
            P`ambient:=Codomain(P`sub_embedding);
        elif assigned P`amb_fp_generators then
            P`ambient:=Universe(P`amb_fp_generators);
        else
            require false: "No ambient defined for this polyhedron";
        end if;
    end if;
    return P`ambient;
end intrinsic;

intrinsic InfinitePart(P::TorPol) -> TorCon
{The infinite part of the polyhedron P}
    if not assigned P`ip_cone then
        P`ip_cone:=ZeroCone(Ambient(P));
    end if;
    return P`ip_cone;
end intrinsic;

intrinsic HasIntegralPoint(P::TorPol) -> BoolElt
{True iff the polyhedron P contains an integral lattice point}
    if not assigned P`has_lattice_point then
        // Check that P lies in a sublattice
        if not amb_has_volume_form(P) then
            P`has_lattice_point:=false;
        // Perhaps we already know an integral representative?
        elif IsIntegral(Representative(P)) then
            P`has_lattice_point:=true;
        // Some new data may have been collected since the representative was
        // chosen, so we do a few simple rechecks:
        // Maybe we now know the integral part?
        elif assigned P`integral_part then
            P`has_lattice_point:=not IsEmpty(P`integral_part);
        // Do we know the points?
        elif assigned P`points then
            P`has_lattice_point:=#P`points gt 0;
        elif assigned P`Ehrhart_coeffs and IsDefined(P`Ehrhart_coeffs,1) then
            P`has_lattice_point:=P`Ehrhart_coeffs[1] gt 0;
        // How about an interior point?
        elif assigned P`num_interior_points and P`num_interior_points gt 0 then
            P`has_lattice_point:=true;
        elif assigned P`interior_points and #P`interior_points gt 0 then
            P`has_lattice_point:=true;
        // A boundary point?
        elif assigned P`num_boundary_points and P`num_boundary_points gt 0 then
            P`has_lattice_point:=true;
        elif assigned P`boundary_points and #P`boundary_points gt 0 then
            P`has_lattice_point:=true;
        // OK, no luck with the rechecks. Now we'll have to do some work:
        // If this is a polytope we simply count the number of points
        elif IsPolytope(P) then
            P`has_lattice_point:=NumberOfPoints(P) ne 0;
        // If this polyhedron contains lines then we quotient out by them and
        // ask for integral points in the resulting polyhedron. Note that we
        // don't need to worry about the case where P is an affine subspace
        // because Representative() takes care of that (since it's easy)
        elif not IsPointed(P) then
            L,quot:=Quotient(LinearSpanGenerators(InfinitePart(P)));
            LL,emb:=GradedToricLattice(L);
            origin:=default_origin(LL,1);
            C:=Cone([LL | emb(quot(v)) + origin :
                        v in amb_get_fp_generating_points(P)] cat
                    [LL | emb(quot(gen)) :gen in RGenerators(InfinitePart(P))]);
            PP:=Polyhedron(C);
            P`has_lattice_point:=HasIntegralPoint(PP);
        // Otherwise we need to check the generating function explicitly (note
        // that our construction assumes that P is pointed)
        else
            // Get the decomposition of the supporting cones into univariate
            // cones and associated numerators. This data is in the form
            // <N,D,E>, where the corresponding function is
            //      E * x^N / &*[1 - x^DD : DD in D],
            // where E is +1 or -1, and x = (x_1,...,x_d), d = #N.
            decomp:=&cat[amb_decomposition_of_cone_at_vertex(P,v) :
                                                              v in Vertices(P)];
            // Get a non-vanishing form on the rays
            lambda:=nonvanishing_form(
                             SequenceToSet(&cat[triple[2] : triple in decomp]));
            // Reduce the decomposition from multivariate to univariate form
            genfuncs:=reduce_to_univariate(decomp,lambda);
            // Now we need to find a suitable root of unity to miss the poles
            k:=Maximum([Integers() | &+triple[2] : triple in genfuncs]) + 1;
            // Test at the root of unity
            R:=PolynomialRing(Rationals());
            t:=R.1;
            f:=t^k - 1;
            S:=[pair[1] : pair in Factorisation(f)];
            degs:=[Degree(poly) : poly in S];
            f:=S[Index(degs,Maximum(degs))];
            RR<a>:=quo<R | f>;
            value:=&+[triple[3] * Evaluate(Power(t,triple[1]) /
                        &*[t^DD - 1 : DD in triple[2]],a) : triple in genfuncs];
            P`has_lattice_point:=value ne 0;
        end if;
    end if;
    return P`has_lattice_point;
end intrinsic;

intrinsic Representative(P::TorPol) -> TorLatElt
{A representative element of the polyhedron P}
    if not assigned P`representative then
        require not IsEmpty(P): "The polyhedron must not be empty";
        S:=amb_get_fp_generating_points(P);
        // Does P lie in a sublattice?
        if not amb_has_volume_form(P) then
            P`representative:=Representative(S);
        // Maybe we know that the integral part is empty?
        elif assigned P`integral_part and IsEmpty(P`integral_part) then
            P`representative:=Representative(S);
        // Maybe we've calculated that there aren't any lattice points?
        elif assigned P`has_lattice_point and not P`has_lattice_point then
            P`representative:=Representative(S);
        // Perhaps we already know the points in P?
        elif assigned P`points then
            if #P`points gt 0 then
                P`representative:=Representative(P`points);
            else
                P`representative:=Representative(S);
            end if;
        elif assigned P`Ehrhart_coeffs and IsDefined(P`Ehrhart_coeffs,1) and
            P`Ehrhart_coeffs[1] eq 0 then
            P`representative:=Representative(S);
        // What about for the strict interior?
        elif assigned P`interior_points and #P`interior_points gt 0 then
            P`representative:=Representative(P`interior_points);
        // Or for the boundary?
        elif assigned P`boundary_points and #P`boundary_points gt 0 then
            P`representative:=Representative(P`boundary_points);
        else
            // Is one of the generating points integral?
            found:=false;
            for s in S do
                if IsIntegral(s) then
                    P`representative:=s;
                    found:=true;
                    break;
                end if;
            end for;
            if not found then
                // Is the origin in P? (Note that we've left this until now
                // because 'in' forces the support to be calculated.)
                if Zero(Ambient(P)) in P then
                    P`representative:=Zero(Ambient(P));
                else
                    // If P contains a line then we may be able to coax an
                    // integral point out of it without too much trouble
                    if IsAffineLinear(P) then
                        found,v:=intersection_has_integral_point(
                                           [H[1] : H in amb_get_halfspaces(P)]);
                        if found then
                            P`representative:=v; end if;
                    elif not IsPointed(P) then
                        Hs:=amb_get_halfspaces(P);
                        for v in S do
                            subHs:=[H[1] : H in Hs |
                                              point_on_halfspace_boundary(H,v)];
                            found,u:=intersection_has_integral_point(subHs);
                            if found then
                                P`representative:=u;
                                break;
                            end if;
                        end for;
                    end if;
                    // Finally, we give up and use a (non-integral) generator
                    if not found then
                        P`representative:=Representative(S);
                    end if;
                end if;
            end if;
        end if;
    end if;
    return P`representative;
end intrinsic;

intrinsic Degree(P::TorPol) -> RngIntElt
{The degree of the integral polytope P}
    // Sanity checks
    require IsPolytope(P) and IsIntegral(P):
        "The polyhedron must be an integral polytope";
    // Return the answer
    return Dimension(P) + 1 - Codegree(P);
end intrinsic;

intrinsic Codegree(P::TorPol) -> RngIntElt
{The codegree of the integral polytope P (i.e. the smallest dilation k such that kP contains an interior lattice point)}
    if not assigned P`codegree then
        // Sanity checks
        require IsPolytope(P) and IsIntegral(P):
            "The polyhedron must be an integral polytope";
        // Compute it
        if ContainsZero(P) then
            P`codegree:=1;
        else
            k:=1;
            while NumberOfInteriorPoints(k * P) eq 0 do
                k +:= 1;
            end while;
            P`codegree:=k;
        end if;
    end if;
    return P`codegree;
end intrinsic;
