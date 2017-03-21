freeze;

/////////////////////////////////////////////////////////////////////////
// reflexive.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38189 $
// $Date: 2012-04-16 17:50:59 +1000 (Mon, 16 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the lattice points in a reflexive polytope.
/////////////////////////////////////////////////////////////////////////
// Calculates the Ehrhart data for a reflexive polytope of
// dimension <= 5.
// See: G.Hegedus and A.M.Kasprzyk, "The boundary volume of a lattice
// polytope", arXiv:1002.2815v2 [math.CO].
/////////////////////////////////////////////////////////////////////////

import "../../utilities/functions.m": points_in_simplex;
import "../../lattice/lattice.m": lattice_get_Zlattice;
import "../triangulation.m": calculate_triangulation_of_boundary;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// True iff the weights match those of a known terminal Gorenstein w.p.s.
function is_known_terminal_wps(wts)
    wset:=SequenceToSet(wts);
    if 1 in wset then
        // Check for projective space
        if #wset eq 1 then return true; end if;
        // The low dimensional cases
        d:=#wts - 1;
        if d le 3 then
            return false;
        elif d eq 4 then
            return Sort(wts) eq [1,1,1,1,2];
        elif d eq 5 then
            wts:=Sort(wts);
            return wts eq [1,1,1,1,2,2] or wts eq [1,1,2,2,3,3] or
                   wts eq [1,1,1,2,3,4];
        end if; 
    end if;
    // No luck
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// Point functions
/////////////////////////////////////////////////////////////////////////

// Special case function to return the points of P when P is a w.p.s.
function points_in_wps(P)
    // Recover the weights
    d:=Dimension(P);
    verts:=Vertices(P);
    wts:=Eltseq(Basis(Kernel(Matrix(verts)))[1]);
    // Create the initial set of points
    pts:=SequenceToSet(verts);
    Include(~pts,Zero(Ambient(P)));
    // We can spot PP^n, and also know the reflexive terminal cases in low dim
    if is_known_terminal_wps(wts) then return pts; end if;
    // We proceed cone by cone, ignoring the smooth cases
    for i in [1..#wts] do
        r:=wts[i];
        if r ne 1 then
            // Extract the generators for the i-th cone
            M:=Matrix(Rationals(),Remove(verts,i)) / r;
            // Create the fundamental domain
            F:=AbelianGroup([Integers() | r : j in [1..d]]);
            G,emb:=sub< F | &+[Cwts[j] * F.j : j in [1..d]] >
                                                      where Cwts:=Remove(wts,i);
            // Extract the points at height 1
            for g in G do
                pt:=Eltseq(emb(g));
                if &+pt eq r then
                    Include(~pts,Vector(Rationals(),pt) * M);
                end if;
            end for;
        end if;
    end for;
    // Return the points
    return pts;
end function;

// Special case function to return the points of P when P = Dual(PP^n).
function points_in_dual_proj_space(P)
    d:=Dimension(P) + 1;
    V:=Matrix([v / d : v in Vertices(P)]);
    return {Ambient(P) | Vector(pt) * V : pt in points_in_simplex(d,d)};
end function;

// Returns the set of lattice points in the given reflexive polytope P.
function points_in_reflexive(P)
    // If this is a simplex then we have a few special cases we can deal with
    verts:=Vertices(P);
    d:=Dimension(P);
    if #verts eq d + 1 then
        // If this is (genuine) w.p.s. then we use a different approach
        idx:=Index(verts);
        if idx eq 1 then
            return points_in_wps(P);
        end if;
        // If this is Dual(PP^n) then we special-case it
        if idx eq (d + 1)^(d - 1) and Volume(P) eq (d + 1)^d then
            return points_in_dual_proj_space(P);
        end if;
    end if;
    // Create the initial set of points
    pts:=SequenceToSet(verts);
    Include(~pts,Zero(Ambient(P)));
    // Fetch the ZZ-module to work with
    R:=lattice_get_Zlattice(Ambient(P));
    // Start working through the cones of the boundary triangulation
    calculate_triangulation_of_boundary(P);
    for F in P`fp_boundary_triang do
        // Is this cone smooth? If so, we can ignore it.
        M:=Matrix(Rationals(),[verts[i] : i in F]);
        r:=Abs(Determinant(M));
        if r ne 1 then
            // Create the mapping matrix
            Minv:=r * M^-1;
            M /:= r;
            // Calculate the generators
            quolat,proj:=quo<R | [Eltseq(verts[i]) : i in F]>;
            gens:=[Eltseq(Vector(Rationals(),Eltseq(g)) * Minv) :
                             g in Generators(TorsionSubmodule(quolat)) @@ proj];
            ChangeUniverse(~gens,PowerSequence(Integers()));
            // Create the fundamental domain
            A:=AbelianGroup([Integers() | r : i in [1..d]]);
            G,emb:=sub< A | [&+[g[i] * A.i : i in [1..d]] : g in gens] >;
            // Extract the points at height 1
            for g in G do
                pt:=Eltseq(emb(g));
                if &+pt eq r then
                    Include(~pts,Vector(Rationals(),pt) * M);
                end if;
            end for;
        end if;
    end for;
    // Return the points
    return pts;
end function;

/////////////////////////////////////////////////////////////////////////
// Ehrhart functions
/////////////////////////////////////////////////////////////////////////

// Returns the delta vector for the given reflexive polytope P.
function calculate_reflexive_ehrhart_delta(P)
    case Dimension(P):
        when 1:
            delta:=[Integers() | 1,1];
        when 2:
            delta:=[Integers() | 1, NumberOfPoints(P) - 3, 1];
        when 3:
            n:=NumberOfPoints(P) - 4;
            delta:=[Integers() | 1, n, n, 1];
        when 4:
            cs:=EhrhartCoefficients(P,2);
            n:=cs[2];
            m:=cs[3];
            delta:=[Integers() | 1, n-5, m-5*n+10, n-5, 1];
        when 5:
            cs:=EhrhartCoefficients(P,2);
            n:=cs[2];
            m:=cs[3];
            delta:=[Integers() | 1, n-6, m-6*n+15, m-6*n+15, n-6, 1];
    end case;
    return delta;
end function;

// Assignes the data needed to compute the Ehrhart generating function when P
// is a reflexive polytope of dimension <= 5. Returns the rational generating
// function.
function calculate_reflexive_ehrhart_data(P)
    // First we create the delta vector
    delta:=calculate_reflexive_ehrhart_delta(P);
    P`Ehrhart_delta:=delta;
    // Create the rational generating function
    R:=PolynomialRing(Rationals());
    t:=R.1;
    k:=#delta;
    P`Ehrhart_gen_func:=&+[delta[i] * t^(i - 1) : i in [1..k]] / (1 - t)^k;
    // Return it
    return P`Ehrhart_gen_func;
end function;
