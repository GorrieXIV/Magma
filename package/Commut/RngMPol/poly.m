freeze;

/*******************************************************************************
			    Homogeneous tests
*******************************************************************************/

intrinsic IsHomogeneous(S::{[GenMPolElt]}) -> BoolElt
{Return whether all the polynomials in set/sequence S are homogeneous
w.r.t. the grading of their parent.}

    return forall{f: f in S | IsHomogeneous(f)};
end intrinsic;

/*******************************************************************************
			    Denominator handling
*******************************************************************************/

intrinsic ClearDenominators(f::RngMPolElt) -> RngMPolElt, RngElt
{Clear the denominators of f (multiply by common denominator L) and return
the cleared polynomial and L.}

    L := LCM([Denominator(x): x in Coefficients(f)]);
    return L*f, L;

end intrinsic;

intrinsic ClearDenominators(Q::[RngMPolElt]) -> []
{Clear the denominators of the elements of Q.}

    return [ClearDenominators(f): f in Q];

end intrinsic;
