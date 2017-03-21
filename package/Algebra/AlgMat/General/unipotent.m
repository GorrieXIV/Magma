freeze;

/*
Ops on nilpotent/unipotent matrices.
*/

intrinsic Exp(X::AlgMatElt) -> AlgMatElt
{The exponential of the nilpotent matrix X};

    R := BaseRing(X);
    require IsExact(R): "Base ring is not exact";
    
    is_nil, deg := IsNilpotent(X);
    require is_nil : "Matrix must be nilpotent";

    exp := 1 + X;
    term := X;
    for i in [2 .. deg-1] do
        require IsUnit(R!i): "Term denominator not invertible";
        term *:= X/i;
        exp +:= term;
    end for;

    return exp;

end intrinsic;

intrinsic Log(X::AlgMatElt) -> AlgMatElt
{The logarithm of the unipotent matrix X};

    R := BaseRing(X);
    require IsExact(R): "Base ring is not exact";

    is_uni, deg := IsUnipotent(X);
    require is_uni : "Matrix must be unipotent";

    X0 := 1 - X;
    term := -X0;
    log := term;
    for i in [2 .. deg-1] do
        term *:= X0;
        require IsUnit(R!i): "Term denominator not invertible";
        log +:= (R!i)^-1*term;
    end for;

    return log;

end intrinsic;
