freeze;

/////////////////////////////////////////////////////////////////////////
// polar.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27125 $
// $Date: 2010-06-04 12:14:46 +1000 (Fri, 04 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating the polar polyhedron.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// Recall that Q* = Q***. We use the 'is_polar' flag to note whether
// this polyhedron P is already known to be the polar of some Q. If so,
// then the above result tells us that P=P**, so we can set the polar
// of P* to be P.
/////////////////////////////////////////////////////////////////////////

import "faces/support.m": amb_get_halfspaces;

declare attributes TorPol:
    is_polar,           // True iff this is the polar polyhedron of some Q
    polar;              // The polar polyhedron of P

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Constructs the polar polytope from the half-space description of P
// Note: Assumes that P is a maximum dimensional polytope containing the
// origin in it's strict interior.
function get_polar_polytope(P)
    // Get the half-spaces defining P
    halfspaces:=amb_get_halfspaces(P);
    assert &and[halfspace[2] eq -1 : halfspace in halfspaces];
    // Create the vertex set
    verts:=[Dual(Ambient(P)) | halfspace[1][1] / (-halfspace[1][2]) :
                                                       halfspace in halfspaces];
    // Finally note that P = Q* and return Q
    P`is_polar:=true;
    // THINK: Might want to copy across more data to Q
    return Polytope(verts : areVertices:=true);
end function;

// Returns the polar polyhedron for P
function get_polar_polyhedron(P)
    if IsPolytope(P) and IsMaximumDimensional(P) and ContainsZero(P) then
        return get_polar_polytope(P);
    else
        return Polyhedron(Dual(NormalisedCone(P)));
    end if;
end function;

/////////////////////////////////////////////////////////////////////////
// Mappings
/////////////////////////////////////////////////////////////////////////

// Note: We don't copy across the polar polyhedron because we want to avoid
// infinite recursion. If you feel that it's worth putting in a fix to allow
// the polar to be transfered, please go ahead.

// Applies the negation -P to the data of P, storing the results that can be
// adjusted in CP.
procedure polar_apply_negation(P,CP)
    if assigned P`is_polar then
        CP`is_polar:=P`is_polar; end if;
end procedure;

// Applies the dilation kP to the data of P, storing the results that can be
// adjusted in CP.
procedure polar_apply_dilation(P,CP,k)
    if assigned P`is_polar and P`is_polar and ContainsZero(P) then
        CP`is_polar:=true; end if;
end procedure;

// Adjusts the data of P to reflect the change of ambient to L, storing the
// results in CP.
procedure polar_change_ambient(P,CP,L)
    if assigned P`is_polar then
        CP`is_polar:=P`is_polar; end if;
end procedure;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Polar(P::TorPol) -> TorPol
{The polar dual to the polyhedron P}
    if not assigned P`polar then
        // First we create the polar Q=P*
        Q:=get_polar_polyhedron(P);
        Q`is_polar:=true;
        P`polar:=Q;
        // Can we set any properties of the dual?
        if assigned P`is_simplicial and P`is_simplicial then
            Q`is_simple:=true; end if;
        // If we're already a polar polyhedron, then the polar of Q is P
        if assigned P`is_polar and P`is_polar then
            Q`polar:=P;
        end if;
    end if;
    return P`polar;
end intrinsic;

intrinsic Dual(P::TorPol) -> TorPol
{If P is a polytope of maximum dimension containing the origin in its strict interior, then this is the corresponding polar polytope}
    require IsPolytope(P) and IsMaximumDimensional(P):
        "The polyhedron must be a polytope of maximum dimension";
    require ContainsZero(P):
        "The polytope must contain the origin in its strict interior";
    return Polar(P);
end intrinsic;
