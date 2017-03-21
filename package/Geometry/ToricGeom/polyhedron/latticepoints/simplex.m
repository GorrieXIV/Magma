freeze;

/////////////////////////////////////////////////////////////////////////
// simplex.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38141 $
// $Date: 2012-04-13 00:21:50 +1000 (Fri, 13 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Calculates the lattice points in an integral simplex.
/////////////////////////////////////////////////////////////////////////
// Calculates the Ehrhart data for an integral simplex.
// Experiments show that this is faster than the general Barvinok
// implementation when the dimension >= 5.
/////////////////////////////////////////////////////////////////////////

import "../../lattice/lattice.m": lattice_get_Zlattice_of_dim;
import "../convexhull/sublattice.m": fp_emb_map;
import "../convexhull/convexhull.m": fp_get_pullback_vertices;

/////////////////////////////////////////////////////////////////////////
// Point functions
/////////////////////////////////////////////////////////////////////////

// Returns the lattice points in the integral simplex P.
function points_in_simplex(P)
    // Move to the equivalent maximum dimensional polytope
    verts:=fp_get_pullback_vertices(P);
    trans,Lemb:=fp_emb_map(P);
    // We turn this into a Gorenstein Q-factorial cone
    d:=#verts;
    rays:=[Append(Eltseq(v),1) : v in verts];
    M:=Matrix(Rationals(),rays);
    r:=Abs(Determinant(M));
    // If the cone is smooth, there's nothing to do
    if r eq 1 then return SequenceToSet(Vertices(P)); end if;
    // Fetch the ZZ-module to work with
    R:=lattice_get_Zlattice_of_dim(d);
    // Create the mapping matrix
    Minv:=r * M^-1;
    M /:= r;
    // Calculate the generators
    quolat,proj:=quo<R | rays>;
    gens:=[Eltseq(Vector(Rationals(),Eltseq(g)) * Minv) :
                     g in Generators(TorsionSubmodule(quolat)) @@ proj];
    ChangeUniverse(~gens,PowerSequence(Integers()));
    // Create the fundamental domain
    A:=AbelianGroup([Integers() | r : i in [1..d]]);
    G,emb:=sub< A | [&+[g[i] * A.i : i in [1..d]] : g in gens] >;
    // Extract the points at height 1
    pts:=SequenceToSet(Vertices(P));
    for g in G do
        pt:=Eltseq(emb(g));
        if &+pt eq r then
            // Pull back the points to the ambient of P
            u:=Prune(Eltseq(Vector(Rationals(),pt) * M));
            Include(~pts,Lemb(u) + trans);
        end if;
    end for;
    // Return the points
    return pts;
end function;

/////////////////////////////////////////////////////////////////////////
// Ehrhart functions
/////////////////////////////////////////////////////////////////////////

// Returns the delta vector for the given integral simplex.
function calculate_simplex_ehrhart_delta(P)
    box:=BoxElements(NormalisedCone(P));
    sums:=[Integers() | &+pt : pt in box];
    delta:=[Integers() | #[0 : height in sums | height eq i] :
                                                        i in [0..Dimension(P)]];
    return delta;
end function;

// Assignes the data needed to compute the Ehrhart generating function when P
// is an integral simplex. Returns the rational generating function.
function calculate_simplex_ehrhart_data(P)
    // First we create the delta vector
    delta:=calculate_simplex_ehrhart_delta(P);
    P`Ehrhart_delta:=delta;
    // Create the rational generating function
    R:=PolynomialRing(Rationals());
    t:=R.1;
    k:=#delta;
    P`Ehrhart_gen_func:=&+[delta[i] * t^(i - 1) : i in [1..k]] / (1 - t)^k;
    // Return it
    return P`Ehrhart_gen_func;
end function;
