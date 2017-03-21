freeze;

/////////////////////////////////////////////////////////////////////////
// dim2.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 40228 $
// $Date: 2012-10-05 21:02:19 +1000 (Fri, 05 Oct 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Database of two-dimensional Fano polytopes.
/////////////////////////////////////////////////////////////////////////
// * The classification of the toric log del Pezzo surfaces is from:
//    A.M. Kasprzyk, M. Kreuzer, B. Nill, "On the combinatorial
//    classification of toric log del Pezzo surfaces", LMS Journal of
//    Computation and Mathematics, 13 (2010), 33-46.
// * The classification of the l-reflexive surfaces is from:
//    A.M. Kasprzyk, B. Nill, "Reflexive polytopes of higher index and
//    the number 12", Electronic Journal of Combinatorics, 19 (2012),
//    no. 3, P9.
// * The classification of small polygons is from:
//    G. Brownm A.M. Kasprzyk, "Small polygons and toric codes",
//    Journal of Symbolic Computation (2012),
//    doi:10.1016/j.jsc.2012.07.001.
/////////////////////////////////////////////////////////////////////////

import "../polyhedron.m": polyhedron_add_description;
import "grdb.m": GRDB_search_root;
import "read.m": ID_to_block, read_packed_vertices;
import "reverse/dim3_canonical_facet.m": canonical_dim3_facet;

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Returns true along with the vertices of the corresponding log del Pezzo
// polygon upon success, false along with an error message otherwise.
function vertices_of_ldp( ID )
    block, line := ID_to_block( ID, 250 );
    bool, verts := read_packed_vertices( "ldp", block, line );
    return bool, verts;
end function;

// Returns true along with the vertices of the corresponding l-reflexive
// polygon upon success, false along with an error message otherwise.
function vertices_of_lreflexive( ID )
    block, line := ID_to_block( ID, 500 );
    bool, verts := read_packed_vertices( "lreflexive2", block, line );
    return bool, verts;
end function;

// Returns true along with the vertices of the corresponding small polygon
// upon success, false along with an error message otherwise.
function vertices_of_smallpolygon( ID )
    block, line := ID_to_block( ID, 4861 );
    bool, verts := read_packed_vertices( "smallpolygons", block, line );
    return bool, verts;
end function;

// Returns the smallest value of k such that the small polygon with given
// ID fits instide a [0,k] x [0,k] box.
function smallest_box( ID )
    if ID le 2 then
        return 1;
    elif ID le 17 then
        return 2;
    elif ID le 148 then
        return 3;
    elif ID le 1517 then
        return 4;
    elif ID le 15359 then
        return 5;
    elif ID le 144544 then
        return 6;
    elif ID le 1249439 then
        return 7;
    end if;
    error "The ID must be in the range 1..1249439";
end function;

/////////////////////////////////////////////////////////////////////////
// Dimension 2
/////////////////////////////////////////////////////////////////////////

intrinsic PolytopeLDP( ID::RngIntElt ) -> TorPol
{The LDP-polygon with given database ID in the range 1..15346}
    // Is the ID within the database range?
    require ID ge 1 and ID le 15346: "The ID must be in the range 1..15346";
    // Create the list of vertices
    bool, vertices := vertices_of_ldp( ID );
    require bool: vertices;
    // Return the polytope
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polygon has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of " cat
        "toric log del Pezzo surfaces.\n    " cat
        GRDB_search_root("toricldp") cat "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopelReflexiveDim2( ID::RngIntElt ) -> TorPol
{The l-reflexive polygon with given database ID in the range 1..41458}
    // Is the ID within the database range?
    require ID ge 1 and ID le 41458: "The ID must be in the range 1..41458";
    // Create the list of vertices
    bool, vertices := vertices_of_lreflexive( ID );
    require bool: vertices;
    // Return the polytope
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polygon has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of " cat
        "l-reflexive polygons.\n    " cat
        GRDB_search_root("toriclr2") cat "ID=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopeSmallPolygon( ID::RngIntElt ) -> TorPol,RngIntElt
{The polygon P with given database ID in the range 1..1249439. Also gives the smallest value of k such that P fits inside a [0,k] x [0,k] box (after possible translation and change of basis). The database contains all polygons for 1 <= k <= 7.}
    // Is the ID within the database range?
    require ID ge 1 and ID le 1249439: "The ID must be in the range 1..1249439";
    // Create the list of vertices
    bool, vertices := vertices_of_smallpolygon( ID );
    require bool: vertices;
    // What value should k take?
    k := smallest_box( ID );
    // Return the polytope
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polygon has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of " cat
        "small polygons.\n    " cat
        GRDB_search_root("boxpoly") cat "id=" cat IntegerToString( ID ) );
    return P,k;
end intrinsic;

intrinsic PolytopeReflexiveFanoDim2( ID::RngIntElt ) -> TorPol
{The reflexive Fano polygon with given database ID in the range 1..16}
    // Is the ID within the database range?
    require ID ge 1 and ID le 16: "The ID must be in the range 1..16";
    // Return the polygon
    return PolytopeCanonicalFanoDim2( ID );
end intrinsic;

intrinsic PolytopeCanonicalFanoDim2( ID::RngIntElt ) -> TorPol
{The canonical Fano polygon with given database ID in the range 1..16}
    // Is the ID within the database range?
    require ID ge 1 and ID le 16: "The ID must be in the range 1..16";
    // Create the list of vertices
    vertices := case< ID |
        1:  [ [ 0, 1], [ 1, 1], [ 1, 0], [ 0,-1], [-1,-1], [-1, 0] ],
        2:  [ [ 0, 1], [ 1, 1], [ 1,-1], [-1,-1], [-1, 0] ],
        3:  [ [ 0, 1], [ 1, 1], [ 1,-1], [ 0,-1], [-1, 0] ],
        4:  [ [ 0, 1], [ 1, 1], [ 0,-1], [-1,-1], [-1, 0] ],
        5:  [ [ 0, 1], [ 1, 1], [ 1,-1], [-2,-1] ],
        6:  [ [ 0, 1], [ 2, 1], [ 0,-1], [-2,-1] ],
        7:  [ [ 0, 1], [ 1, 1], [ 1,-2], [-1, 0] ],
        8:  [ [ 0, 1], [ 1, 1], [ 0,-1], [-2,-1] ],
        9:  [ [ 0, 1], [ 1, 1], [-1,-2], [-1, 0] ],
        10: [ [ 0, 1], [ 1, 1], [ 0,-1], [-1, 0] ],
        11: [ [ 0, 1], [ 1, 1], [ 0,-1], [-1,-1] ],
        12: [ [ 0, 1], [ 3, 1], [-3,-2] ],
        13: [ [ 0, 1], [ 4, 1], [-2,-1] ],
        14: [ [ 0, 1], [ 2, 1], [-3,-2] ],
        15: [ [ 0, 1], [ 2, 1], [-1,-1] ],
        16: [ [ 0, 1], [ 1, 1], [-1,-2] ],
        default: 0 >;
    // Return the polygon
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polygon has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of toric " cat
        "log del Pezzo surfaces.\n    " cat GRDB_search_root( "toricldp" ) cat 
        "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopeTerminalFanoDim2( ID::RngIntElt ) -> TorPol
{The terminal Fano polygon with given database ID in the range 1..5}
    // Is the ID within the database range?
    require ID ge 1 and ID le 5: "The ID must be in the range 1..5";
    // Return the polygon
    return PolytopeSmoothFanoDim2( ID );
end intrinsic;

intrinsic PolytopeSmoothFanoDim2( ID::RngIntElt ) -> TorPol
{The smooth Fano polygon with given database ID in the range 1..5}
    // Is the ID within the database range?
    require ID ge 1 and ID le 5: "The ID must be in the range 1..5";
    // Create the list of vertices
    vertices := case< ID |
        1: [ [ 1, 0], [ 0, 1], [-1, 1], [ 1,-1], [-1, 0] ],
        2: [ [ 1, 0], [ 0, 1], [-1, 1], [ 1,-1], [-1, 0], [ 0,-1] ],
        3: [ [ 1, 0], [ 0, 1], [-1, 1], [ 0,-1] ],
        4: [ [ 1, 0], [ 0, 1], [-1, 0], [ 0,-1] ],
        5: [ [ 1, 0], [ 0, 1], [-1,-1] ],
        default: 0 >;
    // Return the polygon
    P := Polytope( vertices : areVertices:=true );
    polyhedron_add_description( P, "This polygon has ID = " cat
        IntegerToString( ID ) cat " in the Graded Ring Database of smooth " cat
        "Fano polytopes.\n    " cat GRDB_search_root( "toricsmooth" ) cat 
        "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

intrinsic PolytopeCanonicalFanoDim3Facet( ID::RngIntElt ) -> TorPol
{The (2-dimensional) facets of the canonical Fano 3-dimensional polytopes, up to affine equivalence. The facets are indexed 1..4248.}
    // Is the ID within the database range?
    require ID ge 1 and ID le 4248: "The ID must be in the range 1..4248";
    // Create and return the facet
    P:=Polytope( canonical_dim3_facet(ID) : areVertices:=true );
// THINK:
//    polyhedron_add_description( P, "This polygon has ID = " cat
//        IntegerToString( ID ) cat " in the Graded Ring Database of " cat
//        "facets of canonical Fano threefolds.\n    " cat
//        GRDB_search_root( "????????" ) cat "id=" cat IntegerToString( ID ) );
    return P;
end intrinsic;

// Note: The following intrinsic is used by external code. Please do not remove!
intrinsic InternalPolytopeCanonicalFanoDim3Facet( ID::RngIntElt )
    -> SeqEnum[SeqEnum[RngIntElt]]
{The vertices of the (2-dimensional) facets of the canonical Fano 3-dimensional polytopes, up to affine equivalence. The facets are indexed 1..4248. By construction, the vertices are given in affine normal form.}
    // Is the ID within the database range?
    require ID ge 1 and ID le 4248: "The ID must be in the range 1..4248";
    // Return the vertices of the facet
    return canonical_dim3_facet(ID);
end intrinsic;
