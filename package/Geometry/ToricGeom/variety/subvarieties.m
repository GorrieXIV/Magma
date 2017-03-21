freeze;

/////////////////////////////////////////////////////////////////////////
// subvarieties.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 42133 $
// $Date: 2013-02-17 00:52:42 +1100 (Sun, 17 Feb 2013) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////
// Creation of affine patches and subvarieties of toric varieties.
/////////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": variables_of_scheme, remove_repetitions;
import "../fan/fan.m": construct_fan_from_rays, internal_cone_indices, known_cones;

declare attributes TorLat:
    big_torus_cache;        // The big tori associated with this lattice
    
declare attributes TorVar:
    big_torus_embedding,    // The embedding of the big torus in X
    affine_patches_cache,   // Cache of affine patches
    coord_subvars_cache;    // Cache of coordinate subvarieties

/////////////////////////////////////////////////////////////////////////
// Local functions
/////////////////////////////////////////////////////////////////////////

// Checks if ToricAffinePatch(X,S) has already been created.
// S is a set of integers, a subset of PureRayIndices(Fan(X)), the set of those
// variables that are non-zero. If the patch is already there, then returns the
// map from patch to X. If the patch is not yet there returns false.
function affine_patch_check_cache(X,S)
    if not assigned X`affine_patches_cache then
        X`affine_patches_cache:=AssociativeArray(PowerSet(Integers()));
    end if;
    if IsDefined(X`affine_patches_cache,S) then
        return X`affine_patches_cache[S];
    elif IsEmpty(S)  then 
        return ToricIdentityMap(X);
    elif Seqset(PureRayIndices(Fan(X))) eq S then
        _, psi:=BigTorus(X);
        return psi;
    end if;
    return false;
end function;

// Checks if CoordinateSubvariety(X,S) has already been created.
// S is a set of integers, a subset of PureRayIndices(Fan(X)), the set of ALL
// those variables that are zero. If the coordinate subvaiety is already there,
// then returns the map from the subvariety to X. If the coordinate subvariety
// is not yet there returns false.
function coordinate_subvariety_check_cache(X,S)
    if not assigned X`coord_subvars_cache then
        X`coord_subvars_cache:=AssociativeArray(PowerSet(Integers()));
     end if;
    if IsDefined(X`coord_subvars_cache,S) then
        return X`coord_subvars_cache[S];
    elif IsEmpty(S)  then 
        return ToricIdentityMap(X);
    end if;
    return false;
end function;

/////////////////////////////////////////////////////////////////////////
// Affine patches
/////////////////////////////////////////////////////////////////////////

intrinsic ToricAffinePatch(X::TorVar,i::RngIntElt) -> TorVar, TorMap
{The affine patch of X corresponding to i-th cone of fan of X}
    // Sanity checks
    require IsField(BaseRing(X)): "Base ring must be a field";
    requirerange i, 1, #Cones(Fan(X));
    // Identify the patch
    cone:=Cone(Fan(X),i);
    Ri:=Sort(Setseq(ConeIndices(Fan(X), cone)) cat VirtualRayIndices(Fan(X)));
    S:={i : i in PureRayIndices(Fan(X)) | not i in Ri};
    psi:=affine_patch_check_cache(X, S);
    // if it is not yet there, then create it:
    if psi cmpeq false then 
        R:=[Ambient(cone) | rays[i] : i in Ri] where rays is Rays(Fan(X)); 
        bool,F:=construct_fan_from_rays(R,[cone] : max_cones:=true);
        require bool: F;
        A:=ToricVariety(BaseRing(X),F);
        psi:=ToricVarietyMap(A,X);
        psi`is_regular:=true;
        X`affine_patches_cache[S]:=psi;
    end if;
    return Domain(psi), psi;
end intrinsic;

intrinsic ToricAffinePatch(X::TorVar,S::[RngMPolElt]) -> TorVar, TorMap
{The toric variety, obtained from X with monomials from sequence S set to be non-zero}
    // Sanity check
    require IsField(BaseRing(X)): "Base ring must be a field";
    require not IsNull(S): "Illegal null sequence";
    require &and[IsMonomial(f) : f in S]:
        "Argument 2 must be a sequence of monomials";
    require Universe(S) cmpeq CoordinateRing(X):
        "Argument 2 must be a sequence of monomials from the Cox ring of argument 1";
    // convert the monomials into indices
    vars:=variables_of_scheme(X);
    indexes:=[Index(vars, s[1]) : s in &cat[Factorisation(ss): ss in S]];
    remove_repetitions(~indexes);
    // create the patch
    patch, psi:=ToricAffinePatch(X,indexes);
    return patch, psi;
end intrinsic;

intrinsic ToricAffinePatch(X::TorVar,S::[RngIntElt]) -> TorVar, TorMap
{The toric variety, obtained from X with variables with indices S set to be non-zero.}
    // Sanity checks
    require IsField(BaseRing(X)): "Base ring must be a field";
    require &and[s ge 1 and s le Length(X) : s in S]: 
        "Argument 2 must be a sequence of integers in range",[1..Length(X)];
    // check if we already have the patch:
    F:=Fan(X);
    S:={s : s in S | not s in VirtualRayIndices(F)};
    psi:= affine_patch_check_cache(X, S);
    // if we do not have the patch yet, then create it:
    if psi cmpeq false then 
        _:=AllCones(F);
        all_cones:=known_cones(F);
        faces_indices:=[internal_cone_indices(F,i): i in [1..#all_cones]];
        cones:=[c : c in faces_indices| not &or[i in c : i in S]];
        cones:=[c : c in cones | not &or[c subset cc : cc in exc] 
                        where exc is Exclude(cones,c)];
        indices:=[Index(faces_indices, c) : c in cones];
        cs:=all_cones[indices];
        R:=Rays(F)[Sort(Setseq(&join cones join Seqset(VirtualRayIndices(F))))];
        bool,FF:=construct_fan_from_rays(R,cs : max_cones:=true);
        require bool: FF;
        XX:=ToricVariety(BaseRing(X),FF);
        psi:=ToricVarietyMap(XX,X);
        psi`is_regular:=true;
        X`affine_patches_cache[S]:=psi;
    end if;
    return Domain(psi), psi;
end intrinsic;

intrinsic BigTorus(k::Rng, N::TorLat) -> TorVar
{The big torus associated with a toric lattice N}
    // Sanity checks
    require IsField(k): "Argument 1 must be a field"; 
    // Is the torus in the cache?
    if not assigned N`big_torus_cache then
        N`big_torus_cache:=[];
    end if;
    for X in N`big_torus_cache do
        if BaseRing(X) cmpeq k then
            return X;
        end if;
    end for;
    // We need to create the torus
    F:=ZeroFan(N);
    T:=ToricVariety(k,F);
    Append(~N`big_torus_cache,T);
    return T;
end intrinsic;

intrinsic BigTorus(X::TorVar) -> TorVar, TorMap, TorMap
{The big torus of X, together with its embedding into X and the rational map from X to torus}
    if not assigned X`big_torus_embedding then
        // Sanity check
        k:=BaseRing(X);
        require IsField(k): "Base ring must be a field";
        // Create the torus
        N:=OneParameterSubgroupsLattice(X);
        T := BigTorus(k, N);
        X`big_torus_embedding:=ToricVarietyMap(T,X);
        X`big_torus_embedding`is_regular:=true;
    end if;
    return Domain(X`big_torus_embedding), X`big_torus_embedding,
    Inverse(X`big_torus_embedding);
end intrinsic;

/////////////////////////////////////////////////////////////////////////
// Coordinate subvarieties
/////////////////////////////////////////////////////////////////////////

intrinsic CoordinateSubvariety(X::TorVar,S::[RngMPolElt]) -> TorVar, TorMap
{The toric variety, obtained from X with monomials from sequence S set to be zero}
    // Sanity checks
    require IsField(BaseRing(X)): "Base ring must be a field";
    require not IsNull(S): "Illegal null sequence";
    require &and[IsMonomial(f) and TotalDegree(f) eq 1 : f in S]:
        "Argument 2 must be a sequence of variables";
    require Universe(S) cmpeq CoordinateRing(X):
        "Argument 2 must be a sequence of variables from the Cox ring of argument 1";
    // convert polynomials into indices:    
    vars:=variables_of_scheme(X);
    indexes:=[Index(vars, s) : s in S];
    // Create the subvariety
    patch, psi:=CoordinateSubvariety(X,indexes);
    return patch, psi;
end intrinsic;

intrinsic CoordinateSubvariety(X::TorVar,S::[RngIntElt]) -> TorVar, TorMap
{The toric variety, obtained from X with variables with indices S set to be zero}
    // Sanity check
    require IsField(BaseRing(X)): "Base ring must be a field";
    require &and[s ge 1 and s le Length(X) : s in S]:
        "Argument 2 must be a sequence of integers in range ",[1..Length(X)];
    // preliminary check if we already have this coordinate subvariety:
    psi:=coordinate_subvariety_check_cache(X, Seqset(S));
    if not psi cmpeq false then 
        return Domain(psi), psi;
    end if;
    // Ensure that all the rays have been calculated for the fan
    F:=Fan(X);
    _:=AllRays(F);
    // Construct the cone spanned by rays with indices S
    C:=Cone(F,S : extend:=true, in_fan:=false);
    // Construct relevant open subset (we get rid of all strata that do not
    // intersect desired locus) and check if the input makes sense
    relevant_cones:=[CC : CC in Cones(F) | C subset CC];
    require C in F: "Given arguments define empty subscheme.";
    // check again if we already have the subvariety:
    newS:=ConeIndices(F,C);
    if newS ne Seqset(S) then
        psi:= coordinate_subvariety_check_cache(X, newS);
        if not psi cmpeq false then 
            return Domain(psi), psi;
        end if;
    end if;
    // now we need to do the real work:
    indices:=[Integers() | i : i in [1..Length(X)] |
                    not &or[R in MinimalRGenerators(CC) : CC in relevant_cones]  
                    where R is Ray(F,i)];
    aff,psi1:=ToricAffinePatch(X,indices);
    // We calculate the coordinate subvariety
    FF:=Fan(aff);
    FFF,phi:=NormalFan(FF,C);
    XXX:=ToricVariety(BaseRing(X),FFF);
    var:=variables_of_scheme(XXX);
    SS:=[FamilyOfMultivaluedSections(CoordinateRing(XXX))|];
    for i in [1..Length(aff)] do
        r:=Ray(FF,i);
        rr:=phi * r;
        v:=PrimitiveLatticeVector(rr);
        j:=Index(Rays(FFF),v);
        if j eq 0 then
            if IsZero(v) then
                Append(~SS, 0);
            else
                Append(~SS,1);
            end if;
        else
            Append(~SS, MultivaluedSection(var[j],v / rr));
        end if;
    end for;
    psi2:=ToricVarietyMap(XXX,aff,SS: relevant:=true, homogeneous:=true);
    psi2`is_description_good:=true;
    psi2`is_regular:=true;
    psi:=psi2*psi1;
    X`coord_subvars_cache[newS]:=psi;
    return  XXX, psi;
end intrinsic;
