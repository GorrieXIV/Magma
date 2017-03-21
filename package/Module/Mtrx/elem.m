freeze;

intrinsic ElementaryDivisorsMultiset(X::Mtrx) -> {**}
{The elementary divisors of X as a multiset}
    return SequenceToMultiset(ElementaryDivisors(X));
end intrinsic;

intrinsic ElementaryDivisorsMultiset(X::MtrxSprs) -> {**}
{The elementary divisors of X as a multiset}
    return SequenceToMultiset(ElementaryDivisors(X));
end intrinsic;
