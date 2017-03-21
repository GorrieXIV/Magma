freeze;

/////////////////////////////////////////////////////////////////////////
// map.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 27125 $
// $Date: 2010-06-04 12:14:46 +1000 (Fri, 04 Jun 2010) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Extends the application of maps between toric lattices to polyhedra.
/////////////////////////////////////////////////////////////////////////

import "../lattice/gradedlattice.m": default_origin;
import "faces/support.m": amb_are_fp_generating_points_vertices, amb_get_fp_generating_points;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

intrinsic Preimage(phi::Map[TorLat,TorLat],P::TorPol) -> TorPol
{The preimage of the polyhedron P under the toric lattice map phi}
    require Ambient(P) eq Codomain(phi): "Polyhedron must lie in the codomain";
    dphi:=Dual(phi);
    ineqs:=Inequalities(P);
    return PolyhedronWithInequalities([Codomain(dphi)| dphi(H[1]) : H in ineqs],
                                      [Integers() | H[2] : H in ineqs]);
end intrinsic;

intrinsic '@@'(P::TorPol,phi::Map[TorLat,TorLat]) -> TorPol
{The preimage of the polyhedron P under the toric lattice map phi}
    require Ambient(P) eq Codomain(phi): "Polyhedron must lie in the codomain";
    return Preimage(phi,P);
end intrinsic;

intrinsic Image(phi::Map[TorLat,TorLat],P::TorPol) -> TorPol
{The image of the polyhedron P under the toric lattice map phi}
    require Ambient(P) eq Domain(phi): "Polyhedron must lie in the domain";
    // If this is a polytope we can simply take the image of the vertices
    if IsPolytope(P) then
        if amb_are_fp_generating_points_vertices(P) and
           Rank(DefiningMatrix(phi)) eq Dimension(Domain(phi)) then
            return Polytope(Image(phi,amb_get_fp_generating_points(P)) :
                                                            areVertices:=true);
        else
            return Polytope(Image(phi,amb_get_fp_generating_points(P)));
        end if;
    end if;
    // Otherwise we need to use the cone embedding
    LL,emb:=GradedToricLattice(Codomain(phi));
    origin:=default_origin(LL,1);
    C:=Cone([LL | emb(phi(v)) + origin : v in amb_get_fp_generating_points(P)]
                cat [LL | emb(phi(gen)) : gen in RGenerators(InfinitePart(P))]);
    return Polyhedron(C);
end intrinsic;

intrinsic '@'(P::TorPol,phi::Map[TorLat,TorLat]) -> TorPol
{The image of the polyhedron P under the toric lattice map phi}
    require Ambient(P) eq Domain(phi): "Polyhedron must lie in the domain";
    return Image(phi,P);
end intrinsic;
