freeze;

intrinsic Factorization(r::RngValElt) -> SeqEnum, RngValElt
{Factorization of an element of a valuation ring};

    v := Valuation(r);
    if v gt 0 then
	S := [<Parent(r)!(1/FieldOfFractions(Parent(r)).1), v>];
	u := r/S[1][1]^v;
    else
	S := [];
	u := r;
    end if;
    return S, u;
end intrinsic;
