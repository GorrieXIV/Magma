freeze;

/////////////////////////////////////////////////////////////////////////
// barvinok.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 26138 $
// $Date: 2010-04-22 15:15:50 +1000 (Thu, 22 Apr 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Functions for implementing Barvinok's algorithm for lattice point
// enumeration.
/////////////////////////////////////////////////////////////////////////
// Note
// ====
// The intention is to compute a generating function for the lattice
// points inside a cone C. Wlog we may assume that C is of maximal
// dimension and simplicial.
//
// Barvinok's algorithm decomposes a maximal simplicial cone C into a
// signed sum of regular (unimodular) cones Ci, such that the sum of the
// generating functions for the Ci, along with the appropriate signs,
// gives the generating function for C.
/////////////////////////////////////////////////////////////////////////

import "triangulation.m": cone_simplicial_subdivision;

/////////////////////////////////////////////////////////////////////////
// Barvinok's decomposition algorithm
/////////////////////////////////////////////////////////////////////////

// Input: A cone C, not necessarily simplicial or of maximum dimension.
// Output: A list of unimodular cones given by their rays (as a matrix), and
// signs. This data is presented as a sequence
//  [<rays1,sgn1>, <rays2,sgn2>, ...],
// where the Ci=Cone(RowSequence(raysi)) are the cones of the decomposition of
// C, and sgni indicates the sign of the contribution the generating function.
// Also returns an embedding emb:Ambient(Ci) -> Ambient(C).
// Important note: Does not cast the rays into Ambient(Ci). Of course, you
// can recover this ambient as the domain of the embedding emb.
// Important note: Does not keep track of inclusion/exclusion of
// lower-dimensional faces. You'll have to compute that from the data, or
// use Brion's polarisation trick.
function barvinok_cone_decomposition(C)
    // First ensure that C is of maximum dimension
    C,emb:=ConeInSublattice(C);
    // For each cone in a simplicial subdivision of C, calculate the
    // decomposition
    if IsSimplicial(C) then
        decomp:=Barvinok(Matrix(Rays(C)));
    else
        decomp:=&cat[Barvinok(Matrix(CC)):CC in cone_simplicial_subdivision(C)];
    end if;
    // Return the results
    return decomp,emb;
end function;
