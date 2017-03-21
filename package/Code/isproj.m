freeze;

intrinsic IsProjective(C::Code) -> BoolElt
{Return true iff the code C is projective.  NB: For additive codes, this
is with respect to the alphabet, not the coefficient field.  See also
IsAdditiveProjective}
    require Type(C) ne CodeQuantum : "Not defined for quantum codes";

    Gt := Transpose(GeneratorMatrix(C));
    n := Length(C);
    columns := { Normalize(Gt[j]) : j in [1..n] };
    return #columns eq n and 0 notin columns;
end intrinsic;

intrinsic IsAdditiveProjective(C::CodeAdd) -> BoolElt
{Return true iff the additive code C is projective over its coefficient field}
    G := GeneratorMatrix(C);
    n := Length(C);
    k := Nrows(G);
    F := CoefficientRing(C);
    K := Alphabet(C);
    columns := { AdditiveCode<K,F,k | [G[i,j] : i in [1..k]]> : j in [1..n] };
    return #columns eq n and not exists{v : v in columns | Dimension(v) eq 0};
end intrinsic;

