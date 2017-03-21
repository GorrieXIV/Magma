freeze;


intrinsic IsHolzerReduced(p::Pt) -> BoolElt
    {For a point p on a conic, returns true if and only if the
    image of the point on the Legendre model satifies the bound
    of Holzer's Theorem.}
    require Type(Scheme(p)) eq CrvCon and 
        Type(Ring(Parent(p))) in {RngInt,FldRat}:
        "Argument must be a point on a conic over the rationals.";
    return IsReduced(p);
end intrinsic;
