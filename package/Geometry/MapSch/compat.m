freeze;

intrinsic DefiningEquations(m::MapSch) -> SeqEnum
    {The defining polynomials of the scheme map f.}
    return DefiningPolynomials(m);
end intrinsic;
