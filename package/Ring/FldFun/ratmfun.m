freeze;

/*
This should have some check that the function field comes
from a curve, but there is not boolean test.
*/
    
intrinsic ProjectiveRationalFunction(f::FldFunFracSchElt) -> FldFunRatMElt
    {An element mapping to f, in the rational function field of
    the ambient space containing the (projective) scheme X
    whose function field is the parent of f.}
    X := Scheme(Parent(f));
    assert IsProjective(X);
    num,den := IntegralSplit(f,X);
    assert den ne 0;
    return num/den;
end intrinsic;

intrinsic Evaluate(f::FldFunRatMElt, elts::SeqEnum) -> RngElt
    {Evaluates the rational function f at the elements in elts}
    require #elts eq Rank(Parent(f)) : 
      "Number of elements in 2nd argument sequence != number of variables";
    num := Evaluate(Numerator(f),elts);
    den := Evaluate(Denominator(f),elts);
    require (den ne 0) or (num ne 0):
          "Cannot evaluate function with zero denominator "
            * "in this case";
    return ((den eq 0) select Infinity() else num/den);
end intrinsic;
