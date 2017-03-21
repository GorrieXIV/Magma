freeze;

/*
Construct the plane curve, of type Crv, with input any curve of
special type: CrvRat, CrvCon, CrvEll, CrvHyp, or CrvMod.
*/

intrinsic PlaneCurve(C::CrvPln) -> CrvPln
    {Construct the plane curve, of type Crv, in the same ambient
    space, given input any plane curve of special type: CrvRat,
    CrvCon, CrvEll, CrvHyp, or CrvMod.}
    if Type(C) eq Crv then return C; end if;
    return Curve(Ambient(C),Polynomial(C));
end intrinsic;
