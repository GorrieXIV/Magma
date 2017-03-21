freeze;

intrinsic Matrix(f::MapSch) -> Mtrx
    {The matrix determining the linear map f, followed
    by the image of the origin, if f is an affine map.}
    funs := DefiningPolynomials(f);
    require &and[
       IsHomogeneous(f) and TotalDegree(f) in {1,-1} : f in funs ] :
       "Argument must be defined by a homogeneous linear transformation.";
    R := CoordinateRing(Ambient(Domain(f)));
    mons := [ R.i : i in [1..Rank(R)] ];
    M := Matrix(Length(Codomain(f)), &cat[ [
        MonomialCoefficient(f,x) : f in funs ] : x in mons ]);
    return M;
end intrinsic;


