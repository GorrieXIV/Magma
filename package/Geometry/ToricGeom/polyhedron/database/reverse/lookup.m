freeze;

/////////////////////////////////////////////////////////////////////////
// lookup.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38043 $
// $Date: 2012-04-01 01:05:07 +1100 (Sun, 01 Apr 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// A public interface to the reverse look-up tables.
/////////////////////////////////////////////////////////////////////////

import "dim3_smooth.m": smooth_dim3_to_id,smooth_dim3_id_to_ids;
import "dim3_reflexive.m": reflexive_dim3_to_id,reflexive_dim3_id_to_ids;
import "dim3_terminal.m": terminal_dim3_to_id,terminal_dim3_id_to_ids;
import "dim3_canonical.m": canonical_dim3_to_id;

declare attributes TorPol:
    db_ids;         // The sequence of database ids

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic DatabaseID( P::TorPol ) -> SeqEnum
{Looks up the integral polytope P in the databases of polytopes. Matching entries are given as a tuple <database name, database id>. Possible database names are "smooth3", "reflexive3", "terminal3", and "canonical3".}
    if not assigned P`db_ids then
        // Sanity check
        require IsPolytope(P) and IsIntegral(P):
            "The polyhedron must be a lattice polytope";
        ids:=[];
        // Handle the three-dimensional case
        if Dimension(P) eq 3 and IsIntegral(P) then
            P:=PolyhedronInSublattice(P);
            // Is this a Fano polytope?
            if IsFano(P) then
                if IsSmooth(P) then
                    bool,id:=smooth_dim3_to_id(P);
                    require bool: id;
                    ids cat:= smooth_dim3_id_to_ids(id);
                elif IsReflexive(P) then
                    bool,id:=reflexive_dim3_to_id(P);
                    require bool: id;
                    ids cat:= reflexive_dim3_id_to_ids(id);
                elif NumberOfPoints(P) eq NumberOfVertices(P) + 1 then
                    bool,id:=terminal_dim3_to_id(P);
                    require bool: id;
                    ids cat:= terminal_dim3_id_to_ids(id);
                elif NumberOfInteriorPoints(P) eq 1 then
                    bool,id:=canonical_dim3_to_id(P);
                    require bool: id;
                    Append(~ids,<"canonical3",id>);
                end if;
            end if;
        end if;
        // Save the result
        P`db_ids:=ids;
    end if;
    // Return the result
    return P`db_ids;
end intrinsic;
