freeze;

intrinsic Decomposition(K::FldRat, p::RngIntElt) -> SeqEnum
{}
    require IsPrime(p) : "Argument 2 must be a prime element.";
    return [ <Abs(p), 1> ];
end intrinsic;

intrinsic Decomposition(K::FldRat, p::Infty) -> SeqEnum
{The (trivial) decomposition of p into places of the rationals}
    return [ <Abs(p), 1> ];
end intrinsic;

intrinsic Valuation(I::RngOrdFracIdl, p::PlcNumElt) -> RngIntElt
{The valuation of the ideal I at a finite place p}
    return Min([Valuation(x, p) : x in Generators(I)]);
end intrinsic;

intrinsic InfinitePlaces(K::FldRat) -> SeqEnum
{}
    return [ Infinity() ];
end intrinsic;

intrinsic InfinitePlaces(Z::RngInt) -> SeqEnum
{}
    return [ Infinity() ];
end intrinsic;

intrinsic LocalDegree(p::PlcNumElt) -> RngIntElt
  {The local degree of p, ie. the degree of the completion}
  return InertiaDegree(p)*RamificationIndex(p);
end intrinsic;

intrinsic RamificationIndex(p::PlcNumElt) -> RngIntElt
  {}
  if IsFinite(p) then
    return RamificationDegree(Ideal(p));
  elif IsReal(p) then
    return 1;
  else
    return 2;
  end if;
end intrinsic;

intrinsic DecompositionGroup(p::PlcNumElt) -> GrpPerm
  {The decompostion group of p, ie. the subgroup fixing p}
  if IsFinite(p) then
    return DecompositionGroup(Ideal(p));
  end if;
  K := NumberField(p);
  G, _, mG := AutomorphismGroup(K);
  if IsReal(p) then
    return sub<G|>;
  end if;
  // now the place is complex, the field is normal, so
  // - the primitive element is totally complex
  // - there better be an element in G of order 2
  pe := PrimitiveElement(K);
  c := ComplexConjugate(Conjugates(pe)[1]);
  cc := [];
  for u in [x : x in G |Order(x) eq 2] do
    if Abs(c - Conjugates(pe @(u@mG))[1]) le 10^-15 then
      Append(~cc, u);
    end if;
  end for;
  assert #cc eq 1;
  return sub<G|cc>;
end intrinsic;

intrinsic DecompositionGroup(p::RngIntElt) -> GrpPerm
  {}
  require p eq 0 or IsPrime(p):
    "the number must be 0 (for the infinite prime) or a prime";
  
  return AutomorphismGroup(Rationals());
end intrinsic;

