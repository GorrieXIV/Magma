freeze;

// Compatibility routines with old versions

intrinsic IsEllipticCurve(C::CrvHyp) -> BoolElt, CrvEll, MapIsoSch, MapIsoSch
{Given a hyperelliptic curve, the function decides whether C has degree 3.
When true, the function also returns $C$ as an elliptic curve, 
and isomorphisms between the two.
This function is deprecated and will be removed in a later release.
Instead, use Degree(C) eq 3, and EllipticCurve(C).}
    // This was a bit strange, because if C is a CrvHyp 
    // then it is automaticlly nonsingular.
    // Therefore, the function is just testing whether Degree(C) equals 3.
    
    // if Genus(C) ne 1 or not IsOdd(Degree(C)) then 
    if Degree(C) ne 3 then
       return false, _, _, _; 
    end if;
    E, f := EllipticCurve(C);
    return true, E, f, Inverse(f);
end intrinsic;

intrinsic IsogeniesAreEqual(m1::Map, m2::Map) -> BoolElt
{True iff m1 and m2 are equal isogenies.  This function is deprecated
and will be removed in a future release -- use 'eq' instead.}
    return m1 eq m2;
end intrinsic;

