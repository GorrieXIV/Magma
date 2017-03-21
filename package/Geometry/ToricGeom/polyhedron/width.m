freeze;

/////////////////////////////////////////////////////////////////////////
// width.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk and Benjamin Nill
/////////////////////////////////////////////////////////////////////////
// Calculates the lattice width of a polytope.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": bounding_box;
import "faces/support.m": amb_get_fp_generating_points;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns the lattice width of P with respect to the form u
function compute_width(P,u)
    heights:=[Rationals() | v * u : v in amb_get_fp_generating_points(P)];
    return Maximum(heights) - Minimum(heights);
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Width(P::TorPol,u::TorLatElt) -> FldRatElt
{The width of the polytope P with respect to the dual lattice element u}
    // Sanity check
    require IsPolytope(P): "The polyhedron must be a polytope";
    require IsMaximumDimensional(P):
        "The polytope must be of maximum dimension in the ambient lattice";
    require IsInDual(u,Ambient(P)):
        "The point must lie in the dual to the ambient lattice of the polytope";
    // Return the result
    return compute_width(P,u);
end intrinsic;

intrinsic Width(P::TorPol) -> FldRatElt,SetEnum[TorLatElt]
{The minimum lattice width of a polytope P, along with the set of all forms that give that width}
    // Sanity check
    require IsPolytope(P): "The polyhedron must be a polytope";
    require IsMaximumDimensional(P):
        "The polytope must be of maximum dimension in the ambient lattice";
    // If the polytope doesn't contain the origin then we translate
    if not ContainsZero(P) then
        if assigned P`interior_points and #P`interior_points ne 0 then
            bary:=Representative(P`interior_points);
        else
            gens:=amb_get_fp_generating_points(P);
            bary:=&+gens / #gens;
        end if;
        P:=P - bary;
    end if;
    // Choose a small form and compute the lattice width -- we use the bounding
    // box of P to help with this choice
    d:=Dimension(Ambient(P));
    min,max:=bounding_box([PowerSequence(Rationals()) | Eltseq(v) :
                                        v in amb_get_fp_generating_points(P)]);
    dif:=[Rationals() | max[i] - min[i] : i in [1..d]];
    i:=Index(dif,Minimum(dif));
    D:=Dual(Ambient(P));
    u:=D.i;
    c:=compute_width(P,u);
    // Compute the norm of the largest sphere contained in P
    r:=Minimum([Rationals() | I[2]^2 / Norm(I[1]) : I in Inequalities(P)]);
    // Compute the minimum width and the set of minimum width forms
    minwidth:=c;
    S:=[D|];
    LL:=Lattice(IdentityMatrix(Integers(),d));
    PP:=ShortVectorsProcess(LL,c^2 / (4 * r));
    while not IsEmpty(PP) do
        u:=Eltseq(NextVector(PP));
        if GCD(u) eq 1 then
            u:=D ! u;
            c:=compute_width(P,u);
            if c lt minwidth then
                minwidth:=c;
                S:=[D | u];
            elif c eq minwidth then
                Append(~S,u);
            end if;
        end if;
    end while;
    // Append the negations
    S cat:= [D | -v : v in S];
    // Return the result
    return Rationals() ! minwidth,SequenceToSet(S);
end intrinsic;
