freeze;

/************************************************************************
  weil_polynomials.m 

  Auxiliary routines to handle characteristic polynomials of the Frobenius 
  on etale cohomology.  (These routines are primarily designed to be used 
  for Picard group computations.)

  Stephan Elsenhans, March 2011

************************************************************************/

declare verbose WeilPolynomials, 2;

intrinsic HasAllRootsOnUnitCircle(f :: RngUPolElt) -> BoolElt
{We check that all complex roots of the rational polynomial f are of
 absolute value 1. The computation is based on a resolvent construction
 and does not involve floating-point computations.}

 vprintf WeilPolynomials,2:"Running absolute value of roots test\n";

 r := PolynomialRing(RationalField());
 f1 := r!f;
 f1 := f1 div Gcd(f1,Derivative(f1));
 f1 := f1 div Gcd(f1, r.1^2 - 1);
 if Degree(f1) eq 0 then
  vprintf WeilPolynomials,2:"Passed\n";  
  return true;
 end if;
 if Degree(f1) mod 2 eq 1 then
  vprintf WeilPolynomials,2:"Failed\n";  
  return false;
 end if;
 
 n := Degree(f1) div 2;
 res := 0; /* Construct resolvent res such that res(t + 1/t) * t^n = f1  */
 akt := f1;
 for i := n to 0 by -1 do
  c0 := MonomialCoefficient(akt, r.1^(i + n));
  res := res + c0 * r.1^i;
  akt := akt - c0 * r.1^(n-i) * (r.1^2 + 1)^i; /*  res, akt; */
 end for; 
 if akt ne 0 then /* Func eq not satisfied -- Roots not in pairs z , 1/z */
  vprintf WeilPolynomials,2:"Function equation not satisfied.\n";  
  return false;
 end if; /* res,akt; */
/* All roots of res: real in [-2,2]. Check using Sturms chain thm */
 res := res div Gcd(res,Derivative(res));
 sc := [res, Derivative(res)];
 while Degree(sc[#sc]) gt 0 do
  Append(~sc,-(sc[#sc -1] mod sc[#sc]));
 end while;
 vm2 := [Evaluate(akt,-2) : akt in sc];
 vm2 := [akt : akt in vm2 | akt ne 0];
 vp2 := [Evaluate(akt,2) : akt in sc];
 vp2 := [akt : akt in vp2 | akt ne 0]; /* vm2, vp2; */
 scm := 0;
 scp := 0;
 for i := 1 to #vm2 - 1 do
  if Sign(vm2[i]) ne Sign(vm2[i+1]) then scm := scm + 1; end if;
 end for;
 for i := 1 to #vp2 - 1 do
  if Sign(vp2[i]) ne Sign(vp2[i+1]) then scp := scp + 1; end if;
 end for; /* scm, scp; */
 if scm - scp eq Degree(res) then vprintf WeilPolynomials,2:"Passed\n";  
  return true; end if;
 vprintf WeilPolynomials,2:"Failed\n"; return false;
end intrinsic;

intrinsic FrobeniusTracesToWeilPolynomials
(tr :: SeqEnum, q :: RngIntElt, i :: RngIntElt, deg :: RngIntElt: 
 KnownFactor := 1) -> SeqEnum
{A list of all possible characteristic polynomials of degree 'deg'
 of the Frobenius x -> x^q on H^i computed from the Frobenius traces. 
 If a factor of the polynomial is known it can be added as KnownFactor. }

 qt := PolynomialRing(RationalField()); t := qt.1;
 require (KnownFactor ne 0):"Known factor can not be zero.";
 rem_deg := deg - Degree(qt!KnownFactor);

 require (i mod 2 eq 0) or (deg mod 2 eq 0): "Dim or Degree must be even.";
 require (#tr ge (rem_deg div 2)): "Too few traces or known factors given.";  

/* With known fact, sub the powsums of its roots from initial given powsums */ 
 if Degree(qt!KnownFactor) gt 0 then
  co_known := Coefficients(qt!KnownFactor / LeadingCoefficient(KnownFactor));
  ps_known := ElementarySymmetricToPowerSums
    (CoefficientsToElementarySymmetric(co_known) cat [0 : k in [1..#tr]]);
  sf := PowerSumToCoefficients([tr[i] - ps_known[i] : i in [1..#tr]]);
 else
  sf := PowerSumToCoefficients(tr);
 end if;
 
/* sf are the known coefficientens of the polynomial we want to construct */
 if #sf gt rem_deg+1 then
/* Check that all coefficients of monomials with negative degree are zero */
  if not &and [sf[i] eq 0 : i in [1..#sf - (rem_deg+1)]] then 
   vprint WeilPolynomials,1: "Traces force the Weil polynomial to have higher degree.";
   return [];
  end if;
 end if;
/* rem_deg; */
 cnt := (rem_deg-1) div 2;
 pol1 := 0; pol2 := 0;
 for j := 0 to cnt do 
  pol1 := pol1 + t^(rem_deg - j) * sf[#sf - j];
  pol2 := pol2 + t^j * sf[#sf - j] * q^(rem_deg * i div 2 - j * i); 
 end for;
 if rem_deg mod 2 eq 0 then
   pol2 := pol2 +  t^(rem_deg - rem_deg div 2) * sf[#sf - rem_deg div 2]; 
 end if;
 if i mod 2 eq 1 then /* Cohomology of odd dim -- only the "+"-sign possible */
  pol := pol1 + pol2;
  if &and[MonomialCoefficient(pol,t^(rem_deg-j)) eq sf[#sf - j] :
	  j in [1..Min(#sf-1,rem_deg)]] then 
  return [(pol) * qt!KnownFactor];
  else
   return []; /* Enough data to get a contradiction with the func equation */
  end if;
 end if;

/* Cohomology of even dimension -- both signs are possible. */
 pol := pol1 + pol2; /* Test "+" sign: absval of roots and all known coeff */
 res := []; /* pol;  */
 if HasAllRootsOnUnitCircle(Evaluate(pol,q^(i div 2) * t)) and 
    &and[MonomialCoefficient(pol,t^(rem_deg-j)) eq sf[#sf - j] :
	 j in [1..Min(#sf-1,rem_deg)]] then 
    Append(~res,qt!KnownFactor * pol); end if; 
 
 pol := pol1 - pol2; /* Test the "-" sign */ /* pol;  */
 if HasAllRootsOnUnitCircle(Evaluate(pol,q^(i div 2) * t)) and 
    &and[MonomialCoefficient(pol,t^(rem_deg-j)) eq sf[#sf - j] :
	 j in [1..Min(#sf-1,rem_deg)]] then 
    Append(~res,qt!KnownFactor * pol); end if; 
 return res;
end intrinsic;

intrinsic WeilPolynomialToRankBound(f::RngUPolElt, q::RngIntElt) -> RngIntElt
{Given a Weil polynomial f this routine counts the number of roots that are
 q*zeta for  zeta a root of unity. This is an upper bound for the geometric
 Picard rank of a surface over F_q. }

 require f ne 0: "Zero-polynomial can not be handeld.\n";
 rb := 0;
 rem := Evaluate(f,Parent(f).1*q); /* Tate-Twist */
 d := 1;
 repeat
  if EulerPhi(d) le Degree(rem) then
   a := Gcd(rem,Parent(rem)! CyclotomicPolynomial(d));
   while Degree(a) gt 0 do 
    rb := rb + Degree(a);
    rem := rem div a;
    a := Gcd(rem,Parent(rem).1^d - 1);
   end while;
  end if;
  d := d + 1;
 until (d ge 3) and /* EulerPhi(d') > Degrer(rem) for all d' >= d */
 (d ge Degree(rem) * (Exp(0.577217)*Log(Log(d)) + 3 / Log(Log(d))) ); 
 vprintf WeilPolynomials,1:"Loop bound %o\n",d;  
  return rb;
end intrinsic;

intrinsic ArtinTateFormula
(f :: RngUPolElt, q :: RngIntElt, h20 :: RngIntElt) -> RngIntElt, RngIntElt
{Given a polynomial f that is the characteristic polynomial of the Frobenius
 on H^2 of a surface with given Hodge number h^2,0 over F_q, this function
 returns the arithmetic Picard rank and the value of #Br * discriminant for
 the surface, as predicted by the Artin-Tate conjecture.}
  require f ne 0: "Zero-polynomial can not be handeld.\n";
 f1 := PolynomialRing(Rationals())!Evaluate(f,Parent(f).1 * q); /* The Tate twist */
 f1 := f1 / LeadingCoefficient(f1);
 rk := 0;
 while Evaluate(f1,1) eq 0 do
  rk := rk + 1;
  f1 := f1 div (Parent(f1).1 - 1); 
 end while;
 return rk, Evaluate(f1,1) * q^h20;
end intrinsic;


intrinsic WeilPolynomialOverFieldExtension
(f :: RngUPolElt, d :: RngIntElt) -> RngUPolElt
{Given a Weil polynomial f this returns a polynomial of the same degree, 
 whose roots are the dth powers r^d of the roots r of f}
 return Parent(f)!CharacteristicPolynomial(CompanionMatrix(f)^d);
end intrinsic;

intrinsic CheckWeilPolynomial
(f :: RngUPolElt, q :: RngIntElt, h20 :: RngIntElt: SurfDeg := -1) -> BoolElt
{Given a polynomial f this routine tests whether f satisfies several
 properties that  must hold for the characteristic polynomial of the Frobenius
 on H^2 of a surface  whose Hodge number h^\{2,0\} is h20.
 If the degree of the surface is specified, additional tests are done. 
 (For information about the tests being done, set the verbose flag
 'WeilPolynomials' to level 1)}
 
 require (Degree(f) gt 0) : "Polynomial is constant or zero.";  
 require (Degree(f) ge 2*h20) : "Degree must be at least 2*h^2,0.";  
  f1 := PolynomialRing(RationalField())!f;
 f1 := f1 / LeadingCoefficient(f1); 

 /* Roots are algebraic integers */
 if &or [not (c in IntegerRing()) : c in Coefficients(f1) ] then
  vprintf WeilPolynomials,1:"Roots are not integral.\n";
  return false;
 end if;

/* Roots are l-adic units for l <> p */
 if AbsoluteValue(Evaluate(f1,0)) ne q^Degree(f) then 
  vprintf WeilPolynomials,1:"Roots are not l-adic units for l <> p.\n";
  return false;
 end if;
 f2 := Evaluate(f1,q * Parent(f1).1); /* Tate twist */
 f2 := f2 div LeadingCoefficient(f2); 

/* Functional equation and absolute value of roots test.
   Weil's conjecture -- proven by Deligne */
 if not HasAllRootsOnUnitCircle(f2) then 
  vprintf WeilPolynomials,1:"Roots are not of absoulute value %o.\n",q;
  return false;
 end if;

/* Katz's conjecture -- proven by Mazur / Ogus */
 if LCM([Denominator(a) : a in Coefficients(f2)]) gt q^h20 then 
  vprintf WeilPolynomials,1:"Newton polygon is below the Hodge polygon.\n";
  return false;
 end if;

 r1,d1 := ArtinTateFormula(f,q,h20);
 r2,d2 := ArtinTateFormula(WeilPolynomialOverFieldExtension(f,2),q^2,h20);

/* Field extension for Weil-polynomials */
 if (r1 eq r2) and (not IsSquare(d1*d2)) then 
  vprintf WeilPolynomials,1:"Field ext in the Artin-Tate formula failed.\n";
  return false;
 end if;

/* Compare known and predicted Picard group */
 if SurfDeg gt 0 then 
  if (r1 eq 1) and (not IsSquare(SurfDeg * d1)) then
   vprintf WeilPolynomials,1:
    "Arithmetic Picard rank is 1 but hyperplane section is not in Pic.\n";
   return false;
  end if;
 end if;

/* I don't know more theorems on etale / crystalline / fppf cohomology. */
 vprintf WeilPolynomials,1:"All tests passed.\n";
 return true;
end intrinsic;



