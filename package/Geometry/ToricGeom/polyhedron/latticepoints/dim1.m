freeze;

/////////////////////////////////////////////////////////////////////////
// dim1.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38140 $
// $Date: 2012-04-13 00:18:58 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for calculating lattice points in one dimension.
/////////////////////////////////////////////////////////////////////////

import "../convexhull/convexhull.m": fp_get_pullback_vertices;
import "../convexhull/sublattice.m": fp_emb_map;

/////////////////////////////////////////////////////////////////////////
// Local functions for dimension 1
/////////////////////////////////////////////////////////////////////////

// Returns the points of P.
function dim_1_points(P)
    trans,emb:=fp_emb_map(P);
    V:=fp_get_pullback_vertices(P);
    u:=Representative(Eltseq(V[1]));
    v:=Representative(Eltseq(V[2]));
    if IsIntegral(V[1]) then
        if v - u lt 0 then
            k:=Floor(u - v);
            W:=-Universe(V).1;
        else
            k:=Floor(v - u);
            W:=Universe(V).1;
        end if;
        return {Ambient(P) | emb(V[1] + i * W) + trans : i in [0..k]};
    elif IsIntegral(V[2]) then
        if u - v lt 0 then
            k:=Floor(v - u);
            W:=-Universe(V).1;
        else
            k:=Floor(u - v);
            W:=Universe(V).1;
        end if;
        return {Ambient(P) | emb(V[2] + i * W) + trans : i in [0..k]};
    else
        if u lt v then
            u:=Ceiling(u);
            if u gt v then return {Ambient(P)|}; end if;
            k:=Floor(v - u);
            W:=Universe(V).1;
            U:=u * W;
            return {Ambient(P) | emb(U + i * W) + trans : i in [0..k]};
        else
            v:=Ceiling(v);
            if v gt u then return {Ambient(P)|}; end if;
            k:=Floor(u - v);
            W:=Universe(V).1;
            V:=v * W;
            return {Ambient(P) | emb(V + i * W) + trans : i in [0..k]};
        end if;
    end if;
end function;

// Returns the number of points in P.
function dim_1_number_of_points(P)
    V:=fp_get_pullback_vertices(P);
    u:=Representative(Eltseq(V[1]));
    v:=Representative(Eltseq(V[2]));
    if IsIntegral(V[1]) then
        return Floor(Abs(v - u)) + 1;
    elif IsIntegral(V[2]) then
        return Floor(Abs(v - u)) + 1;
    else
        if u lt v then
            u:=Ceiling(u);
            return u gt v select 0 else Floor(v - u);
        else
            v:=Ceiling(v);
            return v gt u select 0 else Floor(u - v);
        end if;
    end if;
end function;

// Returns the boundary points in P.
function dim_1_boundary_points(P)
    V:=Vertices(P);
    if IsIntegral(V[1]) then
        return IsIntegral(V[2]) select SequenceToSet(V) else {Universe(V)|V[1]};
    end if;
    return IsIntegral(V[2]) select {Universe(V) | V[2]} else {Universe(V)|};
end function;

// Returns the number boundary points in P.
function dim_1_number_of_boundary_points(P)
    V:=fp_get_pullback_vertices(P);
    if IsIntegral(V[1]) then
        return IsIntegral(V[2]) select 2 else 1;
    end if;
    return IsIntegral(V[2]) select 1 else 0;
end function;

// Returns the interior points of P.
function dim_1_interior_points(P)
    trans,emb:=fp_emb_map(P);
    V:=fp_get_pullback_vertices(P);
    u:=Representative(Eltseq(V[1]));
    v:=Representative(Eltseq(V[2]));
    if IsIntegral(V[1]) then
        if v - u lt 0 then
            k:=Floor(u - v);
            W:=-Universe(V).1;
        else
            k:=Floor(v - u);
            W:=Universe(V).1;
        end if;
        if IsIntegral(V[2]) then
            return {Ambient(P) | emb(V[1] + i * W) + trans : i in [1..k-1]};
        else
            return {Ambient(P) | emb(V[1] + i * W) + trans : i in [1..k-1]};
        end if;
    elif IsIntegral(V[2]) then
        if u - v lt 0 then
            k:=Floor(v - u);
            W:=-Universe(V).1;
        else
            k:=Floor(u - v);
            W:=Universe(V).1;
        end if;
        return {Ambient(P) | emb(V[2] + i * W) + trans : i in [1..k]};
    else
        if u lt v then
            u:=Ceiling(u);
            if u gt v then return {Ambient(P)|}; end if;
            k:=Floor(v - u);
            W:=Universe(V).1;
            U:=u * W;
            return {Ambient(P) | emb(U + i * W) + trans : i in [0..k]};
        else
            v:=Ceiling(v);
            if v gt u then return {Ambient(P)|}; end if;
            k:=Floor(u - v);
            W:=Universe(V).1;
            V:=v * W;
            return {Ambient(P) | emb(V + i * W) + trans : i in [0..k]};
        end if;
    end if;
end function;

// Returns the number of interior points in P.
function dim_1_number_of_interior_points(P)
    // Perhaps this is easy?
    if assigned P`Ehrhart_coeffs and IsDefined(P`Ehrhart_coeffs,1) then
        return P`Ehrhart_coeffs[1] - dim_1_number_of_boundary_points(P);
    end if;
    // We need to do a little work
    V:=fp_get_pullback_vertices(P);
    u:=Representative(Eltseq(V[1]));
    v:=Representative(Eltseq(V[2]));
    if IsIntegral(V[1]) then
        num:=Floor(Abs(v - u));
        return IsIntegral(V[2]) select num - 1 else num;
    elif IsIntegral(V[2]) then
        return Floor(Abs(v - u));
    else
        if u lt v then
            u:=Ceiling(u);
            return u gt v select 0 else Floor(v - u);
        else
            v:=Ceiling(v);
            return v gt u select 0 else Floor(u - v);
        end if;
    end if;
end function;
