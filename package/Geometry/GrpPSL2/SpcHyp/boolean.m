freeze;

intrinsic IsCusp(x::SpcHypElt) -> BoolElt
    {Returns true if and only if the element x of the upper half
    plane is a cusp}
    if not assigned x`is_cusp then x`is_cusp := false;
    end if;
    return x`is_cusp;
end intrinsic;

intrinsic IsExact(x::SpcHypElt) -> BoolElt
    {Returns true if and only if the element x of the upper half
    plane is a cusp or defined by an element in some number field}
    return x`is_exact;
end intrinsic;


intrinsic IsReal(z::SpcHypElt) -> BoolElt
    {Returns true if and only if z is a cuspidal element.}
    return Imaginary(z) eq 0;
end intrinsic;

intrinsic IsInfinite(z::SpcHypElt) -> BoolElt
    {Returns true if and only if z is the cusp at infinity.}
    return z eq Parent(z)!Infinity();
end intrinsic;
