freeze;

function get_fact(x)
    NF, Nu := Factorization(Numerator(x));
    DF, Du := Factorization(Denominator(x));
    return Sort(NF cat [<t[1], -t[2]>: t in DF]), Nu/Du;
end function;

/******************************************************************************/

intrinsic QuotientFactorization(x::FldRatElt) -> [], FldRatElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;

intrinsic QuotientFactorization(x::FldFunRatUElt) -> [], RngUPolElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;

intrinsic QuotientFactorization(x::FldFunRatMElt) -> [], RngMPolElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;

/******************************************************************************/

intrinsic FactorizationOfQuotient(x::FldRatElt) -> [], FldRatElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;

intrinsic FactorizationOfQuotient(x::FldFunRatUElt) -> [], RngUPolElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;

intrinsic FactorizationOfQuotient(x::FldFunRatMElt) -> [], RngMPolElt
{The factorization of the quotient x}
    require x ne 0: "Argument must be non-zero";
    return get_fact(x);
end intrinsic;
