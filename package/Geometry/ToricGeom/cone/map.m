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
// Extends the application of maps between toric lattices to cones.
/////////////////////////////////////////////////////////////////////////

import "../lattice/map.m": space_map;
import "../lattice/gradedlattice.m": impose_grading;
import "../polyhedron/coneembedding.m": ce_get_embedding, ce_get_origin;
import "../polyhedron/attributes.m": integral_representative;
import "cone.m": create_raw_cone;
import "generators.m": cone_has_inequalities;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

/*
intrinsic PreimagePolyhedron(v::TorLatElt, phi::Map[TorLat,TorLat], C::TorCon)
    -> TorLatElt
{Phi is a toric lattice map L1 -> L2, C a cone in L1, and v an element in L2. Gives the polyhedron which is the intersection of preimage of v and C.}
    require v in Codomain(phi):
        "Argument 1 must lie in the codomain of Argument 2";
    require Ambient(C) cmpeq Domain(phi):
        "Argument 3 must lie in the domain of Argument 2";
    w:=v @@ phi;
    kernel:=LinearConeGenerators(KernelBasis(phi));
    Cw:=Cone(Append(kernel,w));
    CCw,emb:=ConeInSublattice(Cw);
    grading:=emb(Representative(MinimalInequalities(CCw)));
    level:=grading * w;
    CC:=C meet Cw;
    impose_grading(L: grading:=grading); 
    P:=Polyhedron(CC : level:=level);
    emb:=ce_get_embedding(P);
    origin:=ce_get_origin(P);
    // THINK: This is not correct:
    PP:=Polyhedron([Codomain(emb) | emb(p) + origin : p in Vertices(P)] :
                                                             areVertices:=true);
    return PP;
end intrinsic;
*/
intrinsic Preimage(v::TorLatElt, phi::Map[TorLat,TorLat], C::TorCon)
    -> TorLatElt
{Phi is a toric lattice map L1 -> L2, C a cone in L1, and v an element in L2. If v is contained in phi(C), then gives w in C such that phi(w) = v (if possible, w is chosen to be integral). Otherwise gives the preimage of w under phi.}
    require v in Codomain(phi):
        "Argument 1 must lie in the codomain of argument 2";
    require Ambient(C) cmpeq Domain(phi):
        "Argument 3 must lie in the domain of argument 2";
    w:=v @@ phi;
    if w in C then
        return w;
    end if;
    kernel:=Cone(LinearConeGenerators(KernelBasis(phi)));
    Cw:=(kernel + Cone(w));
    CCw,emb:=ConeInSublattice(Cw); 
    CC:=(C @@ emb) meet CCw;
    kernel:=kernel @@ emb;
    if CC subset kernel then
        return w;
    end if;
    grading:=Representative(MinimalInequalities(CCw));
    level:=grading * (w @@ emb);
    if IsIntegral(level) then
        impose_grading(Domain(emb): grading:=grading);
        P:=Polyhedron(CC : level:=level);
        emb2:=ce_get_embedding(P);
        origin:=ce_get_origin(P);
        return emb(emb2(integral_representative(P)) + origin);
    end if;
    for r in RGenerators(CC) do
        prod:= grading * r;
        if prod ne 0 then
            return emb((level / prod) * r);
        end if;
    end for;
end intrinsic;

intrinsic Preimage(phi::Map[TorLat,TorLat],C::TorCon) -> TorCon
{The preimage of the cone C under the toric lattice map phi}
    require Ambient(C) cmpeq Codomain(phi): "Cone must lie in the codomain";
    return C @@ phi;
end intrinsic;

intrinsic '@@'(C::TorCon,phi::Map[TorLat,TorLat]) -> TorCon
{The preimage of the cone C under the toric lattice map phi}
    require Ambient(C) cmpeq Codomain(phi): "Cone must lie in the codomain";
    if IsIdentity(phi) then 
        return C;
    end if;
    CC:=create_raw_cone(Domain(phi));
    if assigned C`Rgens then
        lat_phi:=space_map(phi);
        if &and[(Codomain(lat_phi) ! Eltseq(v)) in Image(lat_phi) :
                                                    v in RGenerators(C)] then 
            ker:=KernelBasis(phi);    
            CC`Rgens:=RGenerators(C) @@ phi cat
            LinearConeGenerators(ker);
            if IsEmpty(ker) then
                if assigned C`is_simplicial then 
                    CC`is_simplicial:=IsSimplicial(C);
                end if;
            end if;
        else
            _:=Inequalities(C);
        end if;
    end if;   
    if cone_has_inequalities(C) then
        DD:=Dual(CC);
        DD`Rgens:=Inequalities(C) * phi; 
    end if;
    return CC;
end intrinsic;

intrinsic Image(phi::Map[TorLat,TorLat],C::TorCon) -> TorCon
{The image of the cone C under the toric lattice map phi}
    require Ambient(C) cmpeq Domain(phi): "Cone must lie in the domain";
    if IsIdentity(phi) then 
        return C;
    end if;
    return Dual(Dual(C) @@ Dual(phi));
end intrinsic;

intrinsic '@'(C::TorCon,phi::Map[TorLat,TorLat]) -> TorCon
{The image of the cone C under the toric lattice map phi}
    require Ambient(C) cmpeq Domain(phi): "Cone must lie in the domain";
    return Image(phi, C);
end intrinsic;
