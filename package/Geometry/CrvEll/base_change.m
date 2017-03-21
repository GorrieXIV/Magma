freeze;

/* 
This is antiquated "lift" syntax for base extensions, which should 
migrate to BaseExtend syntax; best to implement a special type for 
isogenies, or morphisms in geometry.  --David
*/

intrinsic LiftIsogeny(m::Map, K::Rng) -> Map
    {Base extension of the isogeny m to the base ring K}
    S1 := Eltseq(Domain(m));
    S2 := Eltseq(Codomain(m));
    require CanChangeUniverse(S1, K) : "Unable to base extend to given ring";
    require CanChangeUniverse(S2, K) : "Unable to base extend to given ring";
    E1 := BaseExtend(Domain(m), K);
    E2 := BaseExtend(Codomain(m), K);
    PK := ChangeRing(Parent(IsogenyMapPhiMulti(m)), K);
    psi := PK!IsogenyMapPsiMulti(m);
    phi := PK!IsogenyMapPhiMulti(m);
    omg := PK!IsogenyMapOmega(m);
    return Isogeny(E1, E2, psi, phi, omg);
end intrinsic;

intrinsic LiftIsomorphism(m::Map, K::Rng) -> Map
    {Base extension of the isomorphism m to the base ring K}
    S := IsomorphismData(m);
    require CanChangeUniverse(S, K) : "Unable to base extend to given ring";
    E1 := BaseExtend(Domain(m), K);
    E2 := BaseExtend(Codomain(m), K);
    return Isomorphism(E1, E2, ChangeUniverse(S, K));
end intrinsic;

