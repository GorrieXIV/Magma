freeze;

/****************************************************************************
loclib.m

November 2002, Nils Bruin

Library of helper functions over local rings.

******************************************************************************/

import "loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate;

intrinsic Monomials(f::RngUPolElt)->SeqEnum
  {The monomials of F as a sequence}
  R:=Parent(f);
  return [R!([0:j in [1..i]]cat [1]):i in [0..Degree(f)]];
end intrinsic;

intrinsic MyPrimitivePart(P::.)->.
  {Primitive Part}
  //PrimitivePart for polynomials over locals presently sucks. This routine
  //does a much better job. May change in the future?
  
  return ShiftVal(P,-MinValuation(P));
end intrinsic;

intrinsic RowSequence(M::Mtrx)->SeqEnum
  {A sequence of sequences representing rows}
  r := NumberOfRows(M);
  // get universe right for case with no rows 
  return [ PowerSequence(BaseRing(M)) | Eltseq(M[i]) : i in [1..r] ];
end intrinsic;

function MonicGcd(F,G)
  //F and G should be polynomials over a local ring and have unit leading
  //coefficient.
  v:=Minim([MinPrec(F),MinPrec(G)]);
  if v eq Infinity() then
    v:=BaseRing(Parent(F))`DefaultPrecision;
  end if;
  pi:=UniformizingElement(BaseRing(Parent(F)));
  F:=FlattenPrecision(F+O(pi^v));
  G:=FlattenPrecision(G+O(pi^v));
  assert Valuation(f) eq 0 and RelativePrecision(f) ge 1
                                 where f:=LeadingCoefficient(F);
  assert Valuation(g) eq 0 and RelativePrecision(g) ge 1
                                 where g:=LeadingCoefficient(G);
  M:=SylvesterMatrix(F,G);
  r:=NumberOfRows(M);
  E,T:=EchelonForm(M);
  assert Valuation(Determinant(T)) eq 0;
  E:=Matrix(r,r,[c+O(pi^v):c in Eltseq(E)]);
  assert exists(l){l : l in Reverse(RowSequence(E)) |
           exists{c:c in l| RelativePrecision(c) ne 0}};
  return StripPrecisionlessTerms(Parent(F)!Reverse(l));
end function;

intrinsic MyGCD(F::RngUPolElt,G::RngUPolElt)->RngUPolElt
  {Hopefully reliably computes gcd of two polynomials over a local field}
  R:=Parent(F);
  K:=BaseRing(R);
  require ISA(Type(K),FldPad):
     "Have to have polynomials over local field";

  //let's try and use GCD on the new locals:
  if ISA(Type(K),FldPad) then
    return GCD(F,G);
  end if;

  pi:=UniformizingElement(K);
  f:=ShiftVal(F,-MinValuation(F));
  g:=ShiftVal(G,-MinValuation(G));
  X:=R.1;
  while Valuation(LeadingCoefficient(f)) ne 0 or
        Valuation(LeadingCoefficient(g)) ne 0 do
    X:=ShiftVal(X,-1);
    f:=Evaluate(F,X);
    f:=ShiftVal(f,-MinValuation(f));
    g:=Evaluate(G,X);
    g:=ShiftVal(g,-MinValuation(g));
  end while;
  //now f and g are monic and with integral coefficients.
  O:=IntegerRing(K);
  Ox:=PolynomialRing(O);
  h:=MonicGcd(Ox!f,Ox!g);
  return MyPrimitivePart(Evaluate(h,R.1/Eltseq(X)[2]));
end intrinsic;  

intrinsic LongDivision(N::RngUPolElt,D::RngUPolElt)->RngUPolElt,RngUPolElt
  {Returns quotient and remainder}
  require RelativePrecision(LeadingCoefficient(D)) ge 1:
    "Leading coefficient of D must be invertible";
  Rng:=Parent(N);
  X:=Rng.1;
  if Degree(N) lt Degree(D) then
    return Rng!0,N;
  end if;
  Q1:=LeadingCoefficient(N)/LeadingCoefficient(D)*X^(Degree(N)-Degree(D));
  R1:=StripPrecisionlessTerms(N-Q1*D);
  Q2,R2:=LongDivision(R1,D);
  return Q1+Q2,R2;
end intrinsic;

intrinsic SquarefreePart(F::RngUPolElt)->RngUPolElt
{Return the squarefree part of f, which is the largest (normalized)
divisor g of f which is squarefree.}

  /*
  Removes GCD(F,dF) from F. For a polynomial over a local ring, this
  routine is conveniently overloaded to do the operation over the field
  of fractions and scale back the result to something with integral
  coefficients.
  */
  K:=BaseRing(Parent(F));
  if Degree(F) le 1 then
    return F;
  end if;
  if ISA(Type(K),RngPad) then
    H:=SquarefreePart(Polynomial(FieldOfFractions(K),F));
    H:=Polynomial(K,ShiftVal(H,-MinValuation(H)));
  elif ISA(Type(K),FldPad) then
    H,R:=LongDivision(F,MyGCD(F,Derivative(F)));
    assert R eq 0;
  else
    if Characteristic(Parent(F)) eq 0 then
	g:=GCD(F,Derivative(F));
	//assert F mod g eq 0;
	H:=F div g;
	H := Normalize(H);
    else
	L := SquarefreeFactorization(F);
	return &*[t[1]: t in L];
    end if;
  end if;
  if Degree(H) eq Degree(F) then
    return F;
  else
    return H;
  end if;
end intrinsic;

