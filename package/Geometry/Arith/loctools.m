freeze;

/****************************************************************************
loctools.m

January 2003, Nils Bruin

library of *functions* helpful for working with locals

To use these routines:

import "loctools.m": Minim, Maxim, IntNInf, MinValuation, MinPrec, ShiftVal,
       StripPrecisionlessTerms, FlattenPrecision, pAdicEvaluate,
       CoefficientByExponentVector;

******************************************************************************/
function Minim(L)
//  {Computes minimum}
  M:=Infinity();
  for a in L do
    if ISA(Type(Universe(L)),Cop) then
      if Retrieve(a) lt M then
        M:=Retrieve(a);
      end if;
    else
      if a lt M then
        M:=a;
      end if;
    end if;
  end for;
  return M;
end function;

function Maxim(L)
//  {Computes maximum}
  M:=-Infinity();
  for a in L do
    if ISA(Type(Universe(L)),Cop) then
      if Retrieve(a) gt M then
        M:=Retrieve(a);
      end if;
    else
      if a gt M then
        M:=a;
      end if;
    end if;
  end for;
  return M;
end function;

function IntNInf()
//  {Structure that contains both the integers and infinity}
  return cop<PowerStructure(Infty),Integers()>;
end function;

function MinValuation(f)
//  {The minimum valuation of the coefficients of f}
  if ISA(Type(f),SeqEnum) then
    return Min([Valuation(c):c in f]); // MW 23 Apr 2012
    return Minim([IntNInf()|Valuation(c):c in f]); 
  elif ISA(Type(f),RngUPolElt) or ISA(Type(f),RngMPolElt) then  
    return Min([Valuation(c):c in Coefficients(f)]); // MW 23 Apr 2012
    return Minim([IntNInf()|Valuation(c):c in Coefficients(f)]);
  else
    error "Argument not supported";
  end if;
end function;

function MinPrec(f)
//  {The minimum absolute precision in the coefficients of f}
  if ISA(Type(f),SeqEnum) then if #f eq 0 then return Infinity(); end if;
    return Min([AbsolutePrecision(c):c in f]); // MW 23 Apr 2012
    return Minim([IntNInf()|AbsolutePrecision(c):c in f]); 
  elif ISA(Type(f),RngUPolElt) or ISA(Type(f),RngMPolElt) then  
    return Min([AbsolutePrecision(c):c in Coefficients(f)]); // MW 23 Apr 2012
    return Minim([IntNInf()|AbsolutePrecision(c):c in Coefficients(f)]);
  else
    error "Argument not supported";
  end if;
end function;

function ShiftVal(F,v)
//  {Shift content}
  if F cmpeq 0 then
    return F;
  end if;
  R:=BaseRing(Parent(F));
  pi:=UniformizingElement(R);
  cf:=Coefficients(F);
  mn:=Monomials(F);
  if v lt 0 then
    cf:=[c div pi^(-v):c in cf];
  else
    cf:=[c*pi^v:c in cf];
  end if;
  return &+[cf[i]*mn[i]:i in [1..#mn]];
end function;

function StripPrecisionlessTerms(P)
//  {Equate precisionless terms to 0}
  //nice to get polynomials that lost all precision to actually compare 0.
  cf:=Coefficients(P);
  if forall{c:c in cf| RelativePrecision(c) eq 0} then
    //#cf eq 0 then
    return Zero(Parent(P));
  else
    return &+[cf[i]*mn[i]:i in [1..#cf]|RelativePrecision(cf[i]) ne 0] where mn:=Monomials(P);
  end if;
end function;

function CoefficientByExponentVector(P,v)
  error if #v ne Rank(Parent(P)),
    "Vector must be of length equal to the rank of the polynomial ring";
  cfs:=Coefficients(P);
  mons:=[Exponents(m):m in Monomials(P)];
  if exists(i){i: i in [1..#mons] | mons[i] eq v} then
    return cfs[i];
  else
    return BaseRing(Parent(P))!0;
  end if;
end function;

intrinsic MonomialCoefficient(f::RngMPolElt,v::[RngIntElt])->RngElt
  {Returns the coefficient in f of the monomial defined by the exponent vector
  v}
  require #v eq Rank(Parent(f)):"Vector must be of length equal to the rank of the polynomial ring";
  return CoefficientByExponentVector(f,v);
end intrinsic;

function FlattenPrecision(P)
//  {flatten the absolute precision on the coefficients of P}
  //It's not always a good idea to have different precisions floating around on
  //the coefficients of a polynomial. This one flattens the precision to
  //the lowest value.
  cf:=Coefficients(P);
  mn:=Monomials(P);
  pi:=UniformizingElement(BaseRing(Parent(P)));
  minprec:=MinPrec(P);
  if minprec eq Infinity() then
    return P;
  else
    cf:=[c+O(pi^minprec):c in cf];
    return &+[cf[i]*mn[i]:i in [1..#cf]];
  end if;
end function;

function pAdicEvaluate(P,v)
  return cf[1]+&+[cf[i]*v^(i-1):i in [2.. #cf]] where cf:=Coefficients(P);
end function;
