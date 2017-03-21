freeze;

intrinsic PrimeFactors(x::RngIntElt) -> SeqEnum
{The prime factors of x}
return [f[1] : f in Factorization(x)]; end intrinsic;

intrinsic Denominator(x::RngIntElt) -> RngIntElt
  {The denominator of the integer x}
  return 1;
end intrinsic;

intrinsic Numerator(x::RngIntElt) -> RngIntElt
  {The numerator of the integer x}
  return x;
end intrinsic;

intrinsic GaussianIntegerRing() -> RngQuad
{The ring of Gaussian integers (the maximal order of the quadratic field Q(i))}
    return MaximalOrder(QuadraticField(-1));
end intrinsic;

intrinsic GaussianIntegers() -> RngQuad
{The ring of Gaussian integers (the maximal order of the quadratic field Q(i))}
    return MaximalOrder(QuadraticField(-1));
end intrinsic;

intrinsic EisensteinIntegerRing() -> RngQuad
{The ring of Eisenstein integers (the maximal order of the quadratic field
Q(Sqrt(-3)))}
    return MaximalOrder(QuadraticField(-3));
end intrinsic;

intrinsic EisensteinIntegers() -> RngQuad
{The ring of Eisenstein integers (the maximal order of the quadratic field
Q(Sqrt(-3)))}
    return MaximalOrder(QuadraticField(-3));
end intrinsic;

intrinsic Round(x::FldComElt) -> RngQuadElt
{The nearest Gaussian integer to x};
    return GaussianIntegerRing() !
	[Round(Real(x)), Round(Imaginary(x))];
end intrinsic;

intrinsic Intseq(n::RngIntElt) -> SeqEnum
{The base 10 representation of n};
    return Intseq(n, 10);
end intrinsic;

intrinsic Seqint(Q::[RngIntElt]) -> RngIntElt
{The number whose base 10 representation is Q};
    return Seqint(Q, 10);
end intrinsic;

/* It's not necessary to also define IntegerToSequence and
   SequenceToInteger since they are defined to be identical
   to Intseq and Seqint in bind/i.b and bind/s.b.*/

////////////////////////////////////////////////////////////////////////////////

intrinsic Floor(x::RngIntElt) -> RngIntElt
  {Returns x}
  return x;
end intrinsic;

intrinsic Ceiling(x::RngIntElt) -> RngIntElt
  {"} // "
  return x;
end intrinsic;

intrinsic ContinuedFraction(x::RngIntElt) -> SeqEnum
  {"} // "
  return [x];
end intrinsic;

intrinsic BestApproximation(x::RngIntElt, k::RngIntElt) -> FldRatElt
  {"} // "
  return x/1;
end intrinsic;

////////////////////////////////////////////////////////////////////////////////

// these functions are for compatibility with number field functionality,
//  ==> use the default relevant to that context

PREC := GetKantPrecision();

intrinsic Conjugates(a::FldRatElt : Precision:=PREC) -> SeqEnum
{Return the sequence of conjugates of a}
  return [ RealField(Precision)! a ];
end intrinsic;

intrinsic Conjugates(a::RngIntElt : Precision:=PREC) -> SeqEnum
{"} // "
  return [ RealField(Precision)! a ];
end intrinsic;

intrinsic Evaluate(x::FldRatElt, p::Infty : Precision:=PREC) -> FldReElt
  {"} // "
  return RealField(Precision)! x;
end intrinsic;

intrinsic Evaluate(x::RngIntElt, p::Infty : Precision:=PREC) -> FldReElt
  {"} // "
  return RealField(Precision)! x;
end intrinsic;

