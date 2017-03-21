freeze;

/*
intrinsic MonomialBasis(Q::RngMPolRes) -> []
{Return the basis of monomials of the finite quotient Q}

    require HasFiniteDimension(Q): "Quotient must have finite dimension";

    V, f := VectorSpace(Q);
    return [V.i@@f: i in [1 .. Dimension(V)]];

end intrinsic;
*/
