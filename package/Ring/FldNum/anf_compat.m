
freeze;

intrinsic MergeFields(K1::FldAlg, K2::FldAlg) -> SeqEnum
{Returns a list with all possible fields L such that L = K1 K2 might hold}
    return CompositeFields(K1, K2);
end intrinsic;

intrinsic IsSubfield(Q::FldRat, K::FldAlg) -> BoolElt, Map
{Always true}
  return true, Coercion(Q,K);
end intrinsic;

intrinsic 'subset'(K::FldRat, L::FldAlg) -> BoolElt
{Always true}
    return true;
end intrinsic;

intrinsic 'subset'(K::FldAlg, L::FldAlg) -> BoolElt
{True iff K is a subfield of L.}
    is_sub, _ := IsSubfield(K,L);
    return is_sub;
end intrinsic;
