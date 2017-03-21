freeze;

// Replaced by the single syntax IsNonsingular

intrinsic IsNonSingular(X::Sch : FullCheck := false) -> BoolElt
{ True iff X is nonsingular (strictly, smooth over the base ring). If FullCheck
  is false (the default), it is assumed that X is equidimensional. Otherwise the
  potentially expensive decomposition into equidimensional components is
  performed and the Jacobi criterion applied to each component.}
    return IsNonsingular(X : FullCheck := FullCheck);
end intrinsic;

intrinsic IsNonSingular(X::Sch,p::Pt) -> BoolElt
{True iff p is a nonsingular point of X, or of the scheme in which it lies if no scheme argument is given}
    return not IsSingular(X,p);
end intrinsic;

intrinsic IsNonSingular(p::Pt) -> BoolElt
{"} // "
    return not IsSingular(p);
end intrinsic;

// Replaced by DefiningPolynomial(s).

intrinsic DefiningEquation(X::Sch) -> RngMPolElt
    {The defining polynomial of the scheme X (which must be given by a single equation)}
    require IsHypersurface(X) : "Argument must be a hypersurface.";
    return DefiningPolynomial(X);
end intrinsic;

intrinsic Equation(X::Sch) -> RngMPolElt
    {"} // "
    require IsHypersurface(X) : "Argument must be a hypersurface.";
    return DefiningPolynomial(X);
end intrinsic;

intrinsic Polynomial(X::Sch) -> RngMPolElt
    {"} // "
    require IsHypersurface(X) : "Argument must be a hypersurface.";
    return DefiningPolynomial(X);
end intrinsic;

intrinsic DefiningEquations(X::Sch) -> RngMPolElt
    {The defining polynomials of the scheme X}
    return DefiningPolynomials(X);
end intrinsic;

intrinsic Equations(X::Sch) -> RngMPolElt
    {"} // "
    return DefiningPolynomials(X);
end intrinsic;

intrinsic Polynomials(X::Sch) -> RngMPolElt
    {"} // "
    return DefiningPolynomials(X);
end intrinsic;

// Replaced by DefiningIdeal

intrinsic Ideal(X::Sch) -> RngMPol
    {Same as DefiningIdeal}
    return DefiningIdeal(X);
end intrinsic;

