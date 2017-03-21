freeze;

/////////////////////////////////////////////////////////////////////////
// palp.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 36857 $
// $Date: 2012-01-09 07:02:03 +1100 (Mon, 09 Jan 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Author: Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Output a polytope in PALP file format. For more details see:
//  http://hep.itp.tuwien.ac.at/~kreuzer/CY/CYpalp.html
/////////////////////////////////////////////////////////////////////////

import "../../utilities/strings.m": seq_to_string;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic WritePolytopeToPALP( P::TorPol, F::MonStgElt )
{Writes the integral polytope P to the file F in PALP's file format}
    // Sanity checks
    require IsPolytope(P): "The polyhedron must be a polytope";
    require not IsEmpty(P): "The polytope must be non-empty";
    require IsIntegral(P): "The polytope must be integral";
    require IsMaximumDimensional(P):
        "The dimension of the polytope must equal the dimension of the ambient lattice";
    // Output the header
    fprintf F, "%o %o\n", NumberOfVertices(P), Dimension(P);
    // Output the vertices
    for v in Vertices(P) do
        fprintf F, "%o\n", seq_to_string(Eltseq(v),"","");
    end for;
end intrinsic;
