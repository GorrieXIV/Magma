freeze;

intrinsic Evaluate(FQ::[RngSLPolElt], PQ::[RngElt]) -> []
{Evaluate sequence of polynomials FQ at PQ}
    // return [Evaluate(f, PQ): f in FQ];

    S := Universe(FQ);
    InitializeEvaluation(S, PQ);
    return [Evaluate(f): f in FQ];
end intrinsic;
