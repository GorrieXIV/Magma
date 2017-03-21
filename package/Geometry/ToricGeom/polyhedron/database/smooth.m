freeze;

/////////////////////////////////////////////////////////////////////////
// smooth.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 38017 $
// $Date: 2012-03-30 05:06:51 +1100 (Fri, 30 Mar 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Database of smooth Fano polytopes of dimension <= 8.
// Dimensions <= 6 are grouped together in the "smoothfano" database (1.1MB).
// Dimension 7 is in the "smoothfano7" database (6.3MB).
// Dimension 8 is in the "smoothfano8" database (85.2MB).
/////////////////////////////////////////////////////////////////////////
// * The classification of the smooth Fano polytopes is from:
//    M. Obro, "An algorithm for the classification of smooth Fano
//    polytopes", arXiv:0704.0049v1.
/////////////////////////////////////////////////////////////////////////

import "../polyhedron.m": polyhedron_add_description;
import "grdb.m": GRDB_search_root;
import "read.m": ID_to_block, read_packed_vertices;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true along with the vertices of the corresponding smooth polytope
// upon success, false along with an error message otherwise.
function vertices_of_smooth_fano( ID )
    block, line := ID_to_block( ID, 250 );
    bool, verts := read_packed_vertices( "smoothfano", block, line );
    return bool, verts;
end function;

// Returns true along with the vertices of the corresponding smooth polytope
// of dimension 7 upon success, false along with an error message otherwise.
function vertices_of_smooth_fano_dim_7( ID )
    block, line := ID_to_block( ID, 722 );
    bool, verts := read_packed_vertices( "smoothfano7", block, line );
    return bool, verts;
end function;

// Returns true along with the vertices of the corresponding smooth polytope
// of dimension 8 upon success, false along with an error message otherwise.
function vertices_of_smooth_fano_dim_8( ID )
    block, line := ID_to_block( ID, 7498 );
    bool, verts := read_packed_vertices( "smoothfano8", block, line );
    return bool, verts;
end function;

/////////////////////////////////////////////////////////////////////////
// Smooth Fano polytopes
/////////////////////////////////////////////////////////////////////////

intrinsic PolytopeSmoothFano( ID::RngIntElt ) -> TorPol
{The smooth Fano polytope with given database ID in the range 1..830783}
    // Is the ID within the database range?
    require ID ge 1 and ID le 830783: "The ID must be in the range 1..830783";
    // Create the list of vertices
    if ID le 8635 then
        bool, vertices := vertices_of_smooth_fano( ID );
    elif ID le 80891 then
        bool, vertices := vertices_of_smooth_fano_dim_7( ID - 8635 );
    else
        bool, vertices := vertices_of_smooth_fano_dim_8( ID - 80891 );
    end if;
    if not bool then
        // We couldn't access the database file
        require false: vertices;
    end if;
    // Return the polytope
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polytope has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of smooth " cat
        "Fano polytopes.\n    " cat GRDB_search_root( "toricsmooth" ) cat 
        "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopeSmoothFanoDim4( ID::RngIntElt ) -> TorPol
{The smooth Fano 4-dimensional polytope with given database ID in the range 1..124}
    require ID ge 1 and ID le 124: "The ID must be in the range 1..124";
    return PolytopeSmoothFano( ID + 23 );
end intrinsic;

intrinsic PolytopeSmoothFanoDim5( ID::RngIntElt ) -> TorPol
{The smooth Fano 5-dimensional polytope with given database ID in the range 1..866}
    require ID ge 1 and ID le 866: "The ID must be in the range 1..866";
    return PolytopeSmoothFano( ID + 147 );
end intrinsic;

intrinsic PolytopeSmoothFanoDim6( ID::RngIntElt ) -> TorPol
{The smooth Fano 6-dimensional polytope with given database ID in the range 1..7622}
    require ID ge 1 and ID le 7622: "The ID must be in the range 1..7622";
    return PolytopeSmoothFano( ID + 1013 );
end intrinsic;

intrinsic PolytopeSmoothFanoDim7( ID::RngIntElt ) -> TorPol
{The smooth Fano 7-dimensional polytope with given database ID in the range 1..72256}
    require ID ge 1 and ID le 72256: "The ID must be in the range 1..72256";
    bool, vertices := vertices_of_smooth_fano_dim_7( ID );
    if not bool then
        // We couldn't access the database file
        require false: vertices;
    end if;
    // Return the polytope
    ID +:= 8635;
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polytope has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of smooth " cat
        "Fano polytopes.\n    " cat GRDB_search_root( "toricsmooth" ) cat 
        "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopeSmoothFanoDim8( ID::RngIntElt ) -> TorPol
{The smooth Fano 8-dimensional polytope with given database ID in the range 1..749892}
    require ID ge 1 and ID le 749892: "The ID must be in the range 1..749892";
    bool, vertices := vertices_of_smooth_fano_dim_8( ID );
    if not bool then
        // We couldn't access the database file
        require false: vertices;
    end if;
    // Return the polytope
    ID +:= 80891;
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polytope has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of smooth " cat
        "Fano polytopes.\n    " cat GRDB_search_root( "toricsmooth" ) cat 
        "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;
