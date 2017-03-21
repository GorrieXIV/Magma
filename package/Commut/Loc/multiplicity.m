freeze;

function get_number(f, include_f)
    R := Parent(f);
    n := Rank(R);
    L := Localization(R);
    f := L!f;

    B := [Derivative(f, i): i in [1 .. n]];
    if include_f then
	Append(~B, f);
    end if;
    I := Ideal(B);

    // I; Groebner(I); "Standard:", I;

    if Dimension(I) gt 0 then
	return Infinity();
    end if;

    return Dimension(Generic(I)/I);
end function;

intrinsic MilnorNumber(f::RngMPolElt) -> RngIntElt
{The Milnor number of f.}

    require IsField(BaseRing(Parent(f))): "Base ring must be a field";
    return get_number(f, false);

end intrinsic;

intrinsic TjurinaNumber(f::RngMPolElt) -> RngIntElt
{The Tjurina number of f.}

    require IsField(BaseRing(Parent(f))): "Base ring must be a field";
    return get_number(f, true);

end intrinsic;
