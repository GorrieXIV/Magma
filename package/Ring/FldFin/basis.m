freeze;

intrinsic Basis(F::FldFin) -> SeqEnum
{Returns a basis of F that matches Eltseq}
  return [F.1^i : i in [0..Degree(F)-1]];
end intrinsic;

intrinsic Basis(F::FldFin, E::FldFin) -> SeqEnum
{Returns a basis of F over E that matches Eltseq}
  return [x^i : i in [0..Degree(F) div Degree(E)-1]] where x := Generator(F, E);
end intrinsic;

intrinsic Flat(e::FldFinElt) -> SeqEnum
{Returns the coefficients over the prime field}
  return Eltseq(e, PrimeField(Parent(e)));
end intrinsic;

intrinsic AbsoluteBasis(F::FldFin) -> SeqEnum
{Returns a basis over the prime field that matches Flat}
  return Basis(F, PrimeField(F));
end intrinsic;
