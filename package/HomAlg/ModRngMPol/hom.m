freeze;

/*
AKS, March 2007.
*/

/*
intrinsic '*'(s::RngElt, h::ModMPolHom) -> ModMPolHom
{The homomorphism obtained by multiplying h by the scalar s}
    l, s := IsCoercible(CoefficientRing(h), s);
    require l: "Scalar is not coercible into coefficient ring";
    return Homomorphism(Domain(h), Codomain(h), s*Matrix(h));
end intrinsic;

intrinsic '*'(h::ModMPolHom, s::RngElt) -> ModMPolHom
{The homomorphism obtained by multiplying h by the scalar s}
    l, s := IsCoercible(CoefficientRing(h), s);
    require l: "Scalar is not coercible into coefficient ring";
    return Homomorphism(Domain(h), Codomain(h), s*Matrix(h));
end intrinsic;
*/
