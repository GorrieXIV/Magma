freeze;

/////////////////////////////////////////////////////////////////////////
// lattice.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38311 $
// $Date: 2012-04-24 04:50:53 +1000 (Tue, 24 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Decomposes an integral polygon into its possible lattice Minkowski
// decompositions. We say that P = Q + R is a "lattice Minkowski sum" if
//  i) it is a Minkowski sum;
//  ii) P \cap \Z^n \subset (Q \cap \Z^n) + (R \cap \Z^n).
// In fact condition (ii) can easily be seen to be an equality.
/////////////////////////////////////////////////////////////////////////

import "decomposition.m": minkowski_pairs, line_decomposition;
import "../database/reverse/dim3_reflexive_facet.m": reflexive_dim3_facet_to_id, reflexive_dim3_facet, reflexive_dim3_lattice_minkowski;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a sequence of decompositions, removes duplicates
function distinct_decompositions(decomps,zero)
    // Merge all 0-dimensional polytopes occuring in each decomposition, and
    // prune the origin if it's there
    for i in [1..#decomps] do
        pt:=zero;
        decomp:=[PowerStructure(TorPol)|];
        for P in decomps[i] do
            if Dimension(P) eq 0 then
                pt +:= Representative(Vertices(P));
            else
                Append(~decomp,P);
            end if;
        end for;
        if not IsZero(pt) then
            Append(~decomp,Polytope([pt] : areVertices:=true));
        end if;
        decomps[i]:=decomp;
    end for;
    // Assign an ID to each polytope in the decompositions
    polys:=SetToIndexedSet(SequenceToSet(&cat decomps));
    // Create the set of IDs
    decomps:={PowerSequence(Integers()) | Sort([Index(polys,P) : P in decomp]) :
                                                             decomp in decomps};
    // Flip them back to polytopes
    return [PowerSequence(PowerStructure(TorPol)) | [polys[i] : i in decomp] :
                                                             decomp in decomps];
end function;

// Given a Minkowski decomposition "pair" of P, returns true iff it is a
// lattice decomposition.
function is_lattice_decomposition(P,pair)
    // Extract the polytopes
    Q,R:=Explode(pair);
    // First check that there are enough points
    if NumberOfPoints(Q) * NumberOfPoints(R) lt NumberOfPoints(P) then
        return false;
    end if;
    // Now we do the more serious check
    return #{Ambient(P) | q + r : q in Points(Q), r in Points(R)} eq
                                                            NumberOfPoints(P);
end function;

// It's possible the polygon P is equivalent to a facet of a reflexive 3-tope.
// If so, we have the decomposition stored in a look-up table.
function is_reflexive3_facet(P)
    // Which facet ID would it be equivalent to if it was?
    bool,id:=reflexive_dim3_facet_to_id(P);
    if not bool then return false,_; end if;
    // Fetch the vertices for that ID and try to construct the map.
    verts:=reflexive_dim3_facet(id);
    PP,emb,trans1:=PolyhedronInSublattice(P);
    ChangeUniverse(~verts,Ambient(PP));
    bool,phi,trans2:=IsEquivalent(Polytope(verts : areVertices:=true),PP);
    if not bool then return false,_; end if;
    // Compute the final translation
    trans:=emb(trans2) + trans1;
    // Map the decomposition into the correct space
    decomps:=[PowerSequence(PowerStructure(TorPol))|];
    for decomp in reflexive_dim3_lattice_minkowski(id) do
        point:=false;
        newDecomp:=[PowerStructure(TorPol)|];
        // Add the component
        for verts in decomp do
            Q:=Polytope(ChangeUniverse(verts,Ambient(PP)) : areVertices:=true);
            QQ:=Image(emb,Image(phi,Q));
            if not point and Dimension(QQ) eq 0 then
                QQ +:= trans;
                point:=true;
            end if;
            Append(~newDecomp,QQ);
        end for;
        // Add the translation if necessary
        if not point and not IsZero(trans) then
            Append(~newDecomp,Polytope([trans] : areVertices:=true));
        end if;
        Append(~decomps,newDecomp);
    end for;
    // Return success
    return true,decomps;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic LatticeMinkowskiDecomposition(P::TorPol) -> SeqEnum[SeqEnum[TorPol]]
{The possible lattice Minkowski decompositions of the integral polytope P}
    // Sanity checks
    require IsPolytope(P) and IsIntegral(P):
        "The polyhedron must be an integral polytope";
    // Get the dimension 0 and 1 cases out of the way
    if Dimension(P) eq 0 then
        return [[P]];
    elif Dimension(P) eq 1 then
        return line_decomposition(P);
    elif Dimension(P) eq 2 then
        // This might be a polygon the answer might be in a look-up table
        bool,decomp:=is_reflexive3_facet(P);
        if bool then return decomp; end if;
    end if;
    // Compute the possible lattice Minkowski pairs.
    pairs:=[PowerSequence(PowerStructure(TorPol)) | pair :
                 pair in minkowski_pairs(P) | is_lattice_decomposition(P,pair)];
    // Seperate out the pairs containing a 0-dimensional component
    zerodim:=[Universe(pairs) | pair : pair in pairs |
                            Dimension(pair[1]) eq 0 or Dimension(pair[2]) eq 0];
    pairs:=[Universe(pairs) | pair : pair in pairs |
                           Dimension(pair[1]) ne 0 and Dimension(pair[2]) ne 0];
    // If P was lattice indecomposable then we don't need to do any more work
    zero:=Zero(Ambient(P));
    if #pairs eq 0 then
        return distinct_decompositions(zerodim,zero);
    end if;
    // For each pair we compute all possible decompositions
    result:=[Universe(pairs)|];
    polys:=SetToIndexedSet(SequenceToSet(&cat pairs));
    decomps:=[PowerSequence(Universe(pairs)) | $$(Q) : Q in polys];
    for pair in pairs do
        // Extract the polytopes and fetch their ids
        Q,R:=Explode(pair);
        idx1:=Index(polys,Q);
        idx2:=Index(polys,R);
        // Now modge the decompositions together
        result cat:= [comp1 cat comp2 :
                                comp1 in decomps[idx1], comp2 in decomps[idx2]];
    end for;
    // Return the decomposition -- we need to take the time to remove duplicates
    return distinct_decompositions(result,zero);
end intrinsic;
