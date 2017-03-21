freeze;

intrinsic '&+'(S::SetMulti) -> .
{The sum (counting multiplicities) of all elements of S}
    require not IsNull(S): "Illegal null set";
    U := Universe(S);
    s := U ! 0;
    for x in Set(S) do
	s := s + Multiplicity(S, x)*x;
    end for;
    return s;
end intrinsic;

intrinsic '&*'(S::SetMulti) -> .
{The product (counting multiplicities) of all elements of S}
    require not IsNull(S): "Illegal null set";
    U := Universe(S);
    s := U ! 1;
    for x in Set(S) do
	s := s * x^Multiplicity(S, x);
    end for;
    return s;
end intrinsic;
