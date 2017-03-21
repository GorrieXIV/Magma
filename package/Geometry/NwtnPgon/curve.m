freeze;

intrinsic NewtonPolygon(C::Crv) -> NwtnPgon
{Returns the Newton Polygon of the affine curve C.}
    require IsAffine(C): "Argument must be an affine curve";
    return NewtonPolygon(Polynomial(C));
end intrinsic;

