freeze;

import "schur_index.m": Schur_index;
import "extensions.m": schur_index_extn;

intrinsic SchurIndex(c::AlgChtrElt) -> RngIntElt
{The Schur index of c over the rationals}
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    m := Schur_index(c:Easy := true);
    return m;
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::FldRat) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    return SchurIndex(c);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::FldCycElt) -> RngIntElt
{The Schur index of c over the extension of the rationals given by
the cyclotomic field elements e}
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    q := SchurIndices(c);
    return schur_index_extn(c, q, [e]);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::FldRatElt) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    return SchurIndex(c);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::FldCyc) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    q := SchurIndices(c);
    return schur_index_extn(c, q, [PrimitiveElement(e)] : real := CyclotomicOrder(e) le 2);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::AlgChtrElt) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    real := Schur(e,2) ne 0;
    if real then
	/* e could be rational */
	if Degree(Universe(Eltseq(e))) eq 1 then
	    return SchurIndex(c);
	end if;
    end if;
    q := SchurIndices(c);
    return schur_index_extn(c, q, Eltseq(e) : real := real);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::SeqEnum[FldRatElt]) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    return SchurIndex(c);
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, e::SeqEnum[FldCycElt]) -> RngIntElt
{"} // "
    require Norm(c) eq 1: "Character must be absolutely irreducible";
    q := SchurIndices(c);
    return schur_index_extn(c, q, Minimize(e));
end intrinsic;

intrinsic SchurIndex(c::AlgChtrElt, K::FldAlg) -> RngIntElt
  {The Schur index of c over K}
  require Norm(c) eq 1: "Character must be absolutely irreducible";
  return Lcm([Integers()|x[2] : x in SchurIndices(c, K)]);
end intrinsic;

intrinsic SchurIndices(c::AlgChtrElt) -> SeqEnum
{The Schur indices of c over the completions of the rationals}
  require Norm(c) eq 1: "Character must be absolutely irreducible";
   m, q := Schur_index(c);
    Sort(~q, func<x,y|x[1]-y[1]>);
    return q;
end intrinsic;

intrinsic SchurIndices(c::AlgChtrElt, Q::FldRat) -> []
  {"} // "
  require Norm(c) eq 1: "Character must be absolutely irreducible";
  return SchurIndices(c);
end intrinsic;

intrinsic SchurIndices(C::FldAlg, s::SeqEnum, K::FldAlg) -> []
{The Schur indices of a character over the completions of the 
number field K. The character has character field C and SchurIndices s.}

  if Type(BaseField(K)) ne FldRat then
     K := AbsoluteField(K);
  end if;

  KC := Compositum(K, C);
  S := [];
  for l in s do
    p := l[1];
    if p eq 0 then
      PK := InfinitePlaces(K);
      PC := InfinitePlaces(C);
      PKC := InfinitePlaces(KC);
      extend := function(x)
        fl := exists(y){y: y in PKC | Extends(y, x)};
        assert fl;
        return y;
      end function;
      restrict := function(x)
        fl := exists(y){y: y in PC | Extends(x, y)};
        assert fl;
        return y;
      end function;
    else
      PK := [x[1] : x in Decomposition(K, p)];
      PC := [x[1] : x in Decomposition(C, p)];
      PKC := [x[1] : x in Decomposition(KC, p)];
      extend := function(x)
        O := Order(Ideal(PKC[1]));
        ix := O!!Ideal(x);
        fl := exists(y){y: y in PKC | ix subset Ideal(y)};
        assert fl;
        return y;
      end function;
      restrict := function(x)
        O := Order(Ideal(x));
        ix := Ideal(x);
        fl := exists(y){y: y in PC | (O!!Ideal(y)) subset ix};
        assert fl;
        return y;
      end function;
    end if;
    PKC := [extend(x) : x in PK];
    PC := [restrict(x) : x in PKC];
    for oo in [1..#PK] do
      d := l[2] div Gcd(l[2], LocalDegree(PKC[oo]) div LocalDegree(PC[oo]));
      if d ne 1 then
        Append(~S, <PK[oo], d>);
      end if;
    end for;
  end for;
  return S;
end intrinsic;

intrinsic SchurIndices(c::AlgChtrElt, K::FldAlg) -> []
  {The Schur indices of c over the completions of the number field K}

  require Norm(c) eq 1: "Character must be absolutely irreducible";
  C := CharacterField(c);
  if C eq RationalField() then C := CyclotomicField(1); end if;
  s := SchurIndices(c);
  return SchurIndices(C, s, K);
end intrinsic;
