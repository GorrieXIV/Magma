freeze;

/////////////////////////////////////////////////////////////////////////
// fanconstruction.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 43195 $
// $Date: 2013-05-17 20:35:03 +1000 (Fri, 17 May 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Constructions of toric fans from polyhedra.
/////////////////////////////////////////////////////////////////////////

import "coneembedding.m": ce_get_cone, ce_normalised_cone, ce_get_embedding, ce_get_origin;
import "faces/support.m": amb_get_fp_generating_points, edge_facet_indices;

declare attributes TorPol:
    dual_fan,                   // The fan dual to P
    dual_fan_projection,        // The dual of the embedding
    dual_fan_divisor;           // If P arises as a polyhedron of sections of D,
                                // then it remembers D; It is used to ensure
                                // the order of rays of the dual fan is correct.
                                // Also if D is ample, then the dual fan will be
                                // the fan of the variety of D. 

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Given a polytope P, returns a sequence of supporting cones corresponding to
// the edges of P. Note that each of these cones will contain a 1-dimensional
// subspace, as determined by the edge. The cones are returned in the same order
// as the edges of P.
function supporting_edge_cones(P)
    // Sanity check
    error if not IsPolytope(P), "The polyhedron must be a polytope.";
    // Collect the data we need
    efidxs:=edge_facet_indices(P);
    fidxs:=FacetIndices(P);
    eidxs:=EdgeIndices(P);
    verts:=Vertices(P);
    // Start building the cones
    Cs:=[];
    for i in [1..#efidxs] do
        i1,i2:=Explode(SetToSequence(eidxs[i]));
        u:=verts[i1];
        v:=verts[i2] - u;
        pts:=[v,-v] cat &cat[[verts[j] - u : j in fidxs[f]] : f in efidxs[i]];
        Append(~Cs,Cone(pts));
    end for;
    return Cs;
end function;

/////////////////////////////////////////////////////////////////////////
// Intrinsics
/////////////////////////////////////////////////////////////////////////

// N.B. Alias for DualFan
intrinsic NormalFan(P::TorPol) -> TorFan
{The normal fan of the polyhedron P}
    if not assigned P`dual_fan then
        require not IsEmpty(P): "The polyhedron must not be empty";
    end if;
    F,proj:=DualFan(P);
    return F,proj;
end intrinsic;

intrinsic NormalEdgeCones(P::TorPol) -> SeqEnum[TorCon]
{The (outer) normal cones of the edges of the polyhedron P. The cones are given in the same order as the edges of P.}
    if IsPolytope(P) then
        return [Dual(C) : C in supporting_edge_cones(P)];
    else
        return [NormalCone(P,E) : E in Edges(P)];
    end if;
end intrinsic;

// N.B. Alias for DualFaceInDualFan, however we duplicate the code to avoid
// repeating the expensive IsFace check
intrinsic NormalCone(P::TorPol,F::TorPol) -> TorCon
{The (outer) normal cone of the face F of the polyhedron P}
    emb:=ce_get_embedding(P);
    face:=ce_normalised_cone(F,emb,ce_get_origin(P));
    cone:=ce_get_cone(P);
    require IsFace(cone,face): "Argument 2 must be a face of argument 1";
    supp:=SupportingHyperplane(cone,face);
    fan,phi:=NormalFan(P);
    return Face(fan,Cone(phi(supp * emb)));
end intrinsic;

intrinsic DualFan(P::TorPol) -> TorFan
{The normal fan of the polyhedron P}
    if not assigned P`dual_fan then
        require not IsEmpty(P): "The polyhedron must not be empty";
        // If P was constructed from a divisor, and the variety knows its
        // NefCone, then it is cheap to check if D was ample. 
        if assigned P`dual_fan_divisor           
           and assigned Variety(P`dual_fan_divisor)`nef_cone 
           and IsAmple(P`dual_fan_divisor) then
            D:=P`dual_fan_divisor;
            P`dual_fan:=Fan(Variety(D));
            P`dual_fan_projection:=IdentityMap(Ambient(P`dual_fan));
        else 
            // THINK: This can be done now without the cone, I guess.
            cone:=ce_get_cone(P);
            lin:=LinearSpanEquations(cone) * ce_get_embedding(P);
            if IsEmpty(lin) then
                embedding:=IdentityMap(Ambient(P));
            else
                _,embedding:=Quotient(lin);
                embedding:=Dual(embedding);
            end if;
            cone1,phi:=ConeInSublattice(cone);
            grading:=Grading(cone) * phi;
            rays:=[Dual(Ambient(cone1)) | r : r in MinimalInequalities(cone1) |
                           Rank(Matrix([grading,r])) eq 2];
            cone_indices:=[PowerSequence(Integers()) |
                           [Integers() | i : i in [1..#rays] | v*rays[i] eq 0] :
                           v in [Ambient(cone1) | w :
                           w in MinimalRGenerators(cone1) | w * grading ne 0]];
            rays:=(rays @@ Dual(phi)) * (embedding * ce_get_embedding(P));
            // If P is a polyhedron of sections of some divisor, then it is
            // worth ordering the rays in the same order as in the original fan.
            if assigned P`dual_fan_divisor then 
	        D:=P`dual_fan_divisor;
                rays2:=Dual(embedding)(PureRays(Fan(Variety(D))));
                bijection:=[Integers() | i: r in rays2 |
                                        not IsZero(i) where i is Index(rays,r)];
                bijection cat:=[i:  i in [1..#rays]| not i in bijection];
                rays:=rays[bijection];
                inverse:=[Index(bijection,i) : i in [1..#rays]];
                cone_indices:=[PowerSequence(Integers()) |
			  [Integers()|inverse[i] : i in cone ] : cone in cone_indices];
            end if;
            // If P is a polyhedron of sections of some divisor, then perhaps
            // they are the same fans?
            if assigned D and
               Dimension(Ambient(P)) eq Dimension(Domain(embedding))
               and rays eq rays2  and {Seqset(c) : c in cone_indices} eq
               Seqset(ConeIndices(Fan(Variety(D)))) then
                F:=Fan(Variety(D));
                P`dual_fan_divisor`is_ample:=true;
            else
                if IsEmpty(rays) then
                    F:=ZeroFan(Dual(Domain(embedding)));
                else
                    F:=Fan(rays,cone_indices :
                             define_fan:=true, min_rays:=true, max_cones:=true);
                end if;
            end if;
            P`dual_fan:=F;
            P`dual_fan_projection:=Dual(embedding);
        end if; 
    end if;
    return P`dual_fan, P`dual_fan_projection;
end intrinsic;

intrinsic DualFaceInDualFan(P::TorPol,F::TorPol) -> TorCon
{The (outer) normal cone of the face F of the polyhedron P}
    emb:=ce_get_embedding(P);
    face:=ce_normalised_cone(F,emb,ce_get_origin(P));
    cone:=ce_get_cone(P);
    require IsFace(cone,face): "Argument 2 must be a face of argument 1";
    supp:=SupportingHyperplane(cone,face);
    fan,phi:=DualFan(P);
    return Face(fan,Cone(phi(supp * emb)));
end intrinsic;

intrinsic SpanningFan(P::TorPol) -> TorFan
{The fan spanning the faces of the polytope P, where the origin lies strictly in the interior of P}
    require IsPolytope(P) and ContainsZero(P):
        "The polyhedron must be a polytope containing the origin in its interior";
    return Fan(Vertices(P),
                [PowerSequence(Integers()) | Setseq(f) : f in FacetIndices(P)] :
                define_fan:=true, min_rays:=true, max_cones:=true,
                is_complete:=true);
end intrinsic;
