freeze;


/*******************************************************************

  L-Series of elliptic curves twisted by Artin representations
  L-Series of hyperelliptic curves twisted by Artin representations
  
  implements
    intrinsic LSeries(E::CrvEll[FldRat], A::ArtRep: Precision:=0)
    intrinsic LSeries(C::CrvHyp[FldRat], A::ArtRep: Precision:=0)
  
  version 2: Tim and Vladimir Dokchitser, Aug 2010
  version 3: TD, Nov 2014 - all the hard bits moved into Galois 
    representations machinery. Now supports arbitrary reduction types
    for elliptic curves, and hyperelliptic curves C with no additive pieces
    at the ramified primes of A

*******************************************************************/


Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
procedure Swap(~A,i,j) t:=A[i]; A[i]:=A[j]; A[j]:=t; end procedure;


function LocalFactorCA(C,A,p: prec:=0)
  if prec eq 0 then prec:=Precision(ComplexField()); end if;
  //Adual:=Field(A)!!ComplexConjugate(Character(A));
  //Agr:=GaloisRepresentation(Adual,p);
  for padicprec in [20,40,80,300] do
    try
      Agr:=GaloisRepresentation(A,p: Minimize:=true, Precision:=padicprec);  
      Cgr:=GaloisRepresentation(C,p: Minimize:=true, Precision:=padicprec);                                          
      ACgr:=Agr*Cgr;
      return ConductorExponent(ACgr),EulerFactor(ACgr: R:=PR(ComplexField(prec)));  
    catch e
      s:=e`Object;
    end try;
  end for;
  error "LocalFactor(C,A) failed: "*s;
end function;


function TwistedLSeries(C,A,Precision,LCseries,LCAseries)
  ch:=Character(A);
  if IsZero(ch) then  return LSeries(1: Precision:=Precision);
  elif IsOne(ch) then return LCseries(C);
  elif (Degree(ch) eq 1) and (Order(ch) eq 2) then
    K:=Kernel(A);
    D:=Discriminant(Integers(K));
    CD:=QuadraticTwist(C,D);
    return LCseries(CD);
  elif IsIrreducible(ch) then
    commonramification:=PrimeDivisors(GCD(Conductor(C),Conductor(A)));
    LC:=LCseries(C);
    LA:=LSeries(A: Precision:=Precision);
    L:=TensorProduct(LC,LA,[<p,cond,loc>
      where cond,loc:=LocalFactorCA(C,A,p: prec:=Precision)    
      : p in commonramification]: Precision:=Precision);          
        //! will cause precision issues if precision increased later 
  else
    dec:=Decomposition(A);
    dec:=&cat([[d[1]: i in [1..d[2]]]: d in dec]);
    L:=&*[LCAseries(C,a): a in dec];
  end if;
  L`parent:=<C,"tensor",A>;
  L`name:="twist of " cat Sprint(C) cat " by " cat Sprint(A);
  return L;
end function;


intrinsic LSeries(E:: CrvEll[FldRat], A:: ArtRep: Precision:=0) -> LSer
{L-series L(E,A,s) of an elliptic curve E/Q twisted by an Artin representation A}
  require BaseField(E) cmpeq Q:
    "Elliptic curve must be defined over the rationals";
  LE:=func<E|LSeries(E: Precision:=Precision)>;
  LEA:=func<E,A|LSeries(E,A: Precision:=Precision)>;
  return TwistedLSeries(E,A,Precision,LE,LEA);
end intrinsic;


intrinsic LSeries(C:: CrvHyp[FldRat], A:: ArtRep: Precision:=0, LocalData:=[* *]) -> LSer
{L-series L(C,A,s) of a hyperelliptic curve C/Q twisted by an Artin representation A}
  require BaseField(C) cmpeq Q:
    "Hyperelliptic curve must be defined over the rationals";
  LC:=func<C|LSeries(C: Precision:=Precision, LocalData:=LocalData)>;
  LCA:=func<C,A|LSeries(C,A: Precision:=Precision, LocalData:=LocalData)>;
  return TwistedLSeries(C,A,Precision,LC,LCA);
end intrinsic;


