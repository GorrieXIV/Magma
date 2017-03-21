freeze;

// June 2005
// Alexa van der Waall

// July 2009
// Alexa van der Waall

// This file is based on M.van Hoeij. - Formal solutions and factorization
// of differential operators with power series coefficients, 1997
// It contains routines relating to the factorisation of differential
// operators over a Laurent series ring, allowing 
// finding factors over finite extensions of the Laurent series ring.
// The file is a follow up on the one called factorisationLocal.m.

// Some improvements for the future.
// Write intrinisc Has(Scalar)ProjectiveDerivation, that currently is
//  a function.
// Try not to use Truncation , but do truncation as map to a 
//   polynomial ring. In this way everything can be
//   done for finite precision Laurent series rings.
// RightHand Factors uses the locallclm construction that sometimes fails,
//  but really should not. For now it just returns an operator and the message
//  false. 
// A.W.


import "localfactorisation.m" :
  LossInPrecisionInFactorisation,
  IsShiftedByRingElt,
  FactorWRTNewtPolSlope,
  FactorisationForStandardScaledOperator;
import  "locallclm.m" :
  LCLMOverSeries;

declare verbose RicattiFactor, 2;
declare verbose SemiRegularParts, 2;
declare verbose RightHandFactors, 2;


////////////////////////////////////////////////////////////////////
//                                                                //
//                       Relative precsion                        //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
intrinsic RelativePrecisionOfDerivation(R::RngDiffOp) -> RngElt
  {The relative precision of the derivation of an operator ring
   over a Laurent series ring.}
  // It returns the relative precision of the Derivation(R)(F.1). 
  F:=BaseRing(R);
  require IsDifferentialLaurentSeriesRing(F):
    "The operator ring is not defined over a differential Laurent series ring.";
  deriv:=F!Derivation(R)(F.1); 
  return RelativePrecision(deriv);
end intrinsic;  



////////////////////////////////////////////////////////////////////
//                                                                //
//                       General functions                        //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
function HasScalarProjectiveDerivationOverSeries(R)
  // input: The differential operator ring R over a differential Laurent series
  //        ring F=k((t)), or a differential Laurent series.
  // output: true iff R has derivation (c*t+O(*))*d/dt, where c is a constant.
  if Type(R) eq RngDiffOp then
    F:=BaseRing(R);
  else 
    assert Type(R) eq RngDiff;
    F:=R;
  end if; 
  assert IsDifferentialLaurentSeriesRing(F);
  derivtF:=(Derivation(R))(F.1);  
  c:=F!((1/F.1)*(derivtF));
  if IsWeaklyZero(c) then
    return false; 
  elif (Degree(c) eq 0) and (Valuation(c) eq 0) then
    return true; 
  else
    return false;
  end if;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                            Series Rings                        //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Do NOT make this one into an intrinsic.
function ChangePrecisionOfDerivationInPurelyRamifiedExtension(F,p)
  // (F::RngDiff,p::RngElt)  -> RngDiff, Map
  // {Returns a differential Laurent ring isomorphic to F,
  //   but whose derivation is has the desired relative precision p.
  //   The map is the isomorphism of F to the new field.}
  error if not IsDifferentialLaurentSeriesRing(F),
    "The differential ring must be a Laurent series ring.";   
  error if not HasScalarProjectiveDerivationOverSeries(F),
      "The derivation of the operator ring must be of the form c*t*d/dt.";
    // The latter is necesary, since then the valuation of D(F.1)^i is 
    // i itself again. This makes changing the precision easy. 
  if not p eq Infinity() then 
    bl, p:=IsCoercible(Integers(), p); 
    error if not bl,
      "Precision of derivation cannot be changed to an integer."; 
    error if not p gt 0,
      "Precision of derivation cannot be changed into a positive integer."; 
  end if;  
  K:=UnderlyingRing(F); 
  derivationF:=Derivation(F);
  b:=RelativePrecisionOfDerivation(F);
  newderivation:=map<K->K| x:-> ( Truncate(dx) 
      + (a cmpeq Infinity() select 0 else O((K.1)^a)
           where a:=AbsolutePrecision(x))
      // + (b cmpeq Infinity() select 0 else O((K.1)^(Valuation(dx)+p))
      //      where  b:=RelativePrecisionOfDerivation(F))
      + (b cmpeq Infinity() or (dx cmpeq 0) select 0 else O(K.1^(valdx+p))
           where valdx:=Valuation(dx))          
      where dx:=K!derivationF(x))>;  
  Fprime:=DifferentialRing(K,newderivation,ConstantRing(F));
  Fprime`IsDifferentialLSR:=true;    
  mpFtoFprime:=Coercion(F,K)*Coercion(K,Fprime);
  mpFtoFprime:=map<F->Fprime|x:->mpFtoFprime(x), y:-> y@@mpFtoFprime>;
  return Fprime, mpFtoFprime;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                   Purely ramified extensions                   //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
function IsPurelyRamifiedPolynomial(f) 
  // intrinsic IsPurelyRamifiedPolynomial(f::RngUPolElt) -> BoolElt, RngUPolElt
  // {If F[T] is the parent of f, returns true iff f is of the form 
  //  T^n -c*(F.1), for a positive integer n and c in ConstantRing(F).}
  // We do not allow c with relative precision less than the relative precision of F.
  // We do not allow an order term for c.
  // When the polynomial is indeed purely ramified, its truncated
  // version is returned if the coefficients are defined over a series ring.
  F:=BaseRing(Parent(f));
  isADF:= IsAlgebraicDifferentialField(F);
  isDLSR:= IsDifferentialLaurentSeriesRing(F);
  error if not (isADF or isDLSR),
     "Routine is implemented for polynomials over an algebraic differential",
     "field or a differential Laurent series ring.";
  error if not Characteristic(F) eq 0,
    "Routine only implemented for polynomials over a characteristic 0 field.";
  degf:=Degree(f);
  if degf lt 1 then
    return false, _;
  elif not IsMonic(f) then
    return false, _;
  end if;
    // Checking leading coefficient is not necessary anymore.
    // Check intermediate coefficients.
  setcoef:={F| Coefficient(f,i) :i in [1..degf-1]};
  if exists{v :v in setcoef | not IsZero(v)} then
    "Non-zero intermediate coefficient detected.";
    return false, _;
  end if;
    // Remains to check the constant coefficient.
    // This is a series element.
  constcoef:=Coefficient(f,0); 
  if IsWeaklyZero(constcoef) then
    return false, _;
  elif isADF then
    if IsCoercible(ConstantRing(F),constcoef/(F.1)) then
      return true, f;
    else
      return false, _;
    end if;
  else 
    assert isDLSR;
    if RelativePrecision(constcoef) lt RelativePrecision(F) then
      "The relative precision of the constant coefficient",
      "is less than the relative precision of the series ring.";
      return false, _;
    elif not(Valuation(constcoef) eq 1) then
      return false, _;
    // elif not IsWeaklyZero(constcoef-Coefficient(constcoef,1)*F.1) then
    elif not constcoef eq Coefficient(constcoef,1)*F.1 then
      return false, _;
    else 
    // Truncate is only of imporatance if we weaken the equality
    // of the constant term to be a weak equality.
      return true, Parent(f)![Truncate(v) :v in Eltseq(f)];
    end if;
  end if;
end function;


// ok
intrinsic PurelyRamifiedExtension(f::RngUPolElt[RngDiff]) -> RngDiff, Map
  {Creates a purely ramified extension of the differential base field F of 
   the purely ramified polynomial f.
   The inverse map returns 0 when undefined.}
  F:=BaseRing(f); 
  require Characteristic(F) eq 0:
    "Routine only implemented for differential ring of characteristic 0.";
  isADF:=IsAlgebraicDifferentialField(F);
  isDLSR:=IsDifferentialLaurentSeriesRing(F);
  require isADF or isDLSR:
    "The ring must be an algebraic differential field or a",
    "differential Laurent series ring.";
  if isADF then
    // require IsCoercible(ConstantField(F), (Derivation(F)(F.1))/(F.1)):
    //   "The derivation of the differential ring must be of the form c*t*d/dt.";
  else  
    require HasScalarProjectiveDerivationOverSeries(F):
      "The derivation of the differential ring must be of the form c*t*d/dt.";
    require RelativePrecisionOfDerivation(F) in 
      {Infinity(), RelativePrecision(F)}:
      "The derivation must have precision: infinite or ring precision.";
  end if; 
  bl, f:=IsPurelyRamifiedPolynomial(f);
  require bl:
    "The polynomial is not of the correct form.";
  if isADF then
    return ext<F|f>;
  end if;  
  n:=Degree(f);
  p:=n*RelativePrecision(F);
    // In general we need to change the precision of the derivation too.
  Fprime:=ChangeDerivation(F,1/n);
    // Change precision of Fprime in n*RelativePrecision(F).
    // This comes from the derivation of F, as it might have 
    // an order term coming from completion.   
  Fprime:=ChangePrecision(Fprime, p);
    // The precision of the derivation is another issue.
  Fprime:=ChangePrecisionOfDerivationInPurelyRamifiedExtension(Fprime,p);  
  Fprime`BaseField:=F;
  Fprime`IsDifferentialLSR:=true;
  a:=-Coefficient(Coefficient(f,0),1);  
  mp:=map< F->Fprime | x:->
        &+([Fprime|Coefficient(x,i)/(a^i)*Fprime.1^(i*n):i in Exponents(x)]) 
        + (b cmpeq Infinity() select 0 else O(Fprime.1^(n*b))
        where b:=AbsolutePrecision(x)),
        // inverse
        y :-> (exists {i:i in expy|not IsCoercible(Integers(),i/n)} 
        select 0 else 
        &+([F|Coefficient(y,i)*(a^Floor(i/n))*F.1^Floor(i/n):i in expy]) where 
        expy:=[j:j in Exponents(y)|not Coefficient(y,j) cmpeq 0])
        + (b cmpeq Infinity() select 0 else O(F.1^Ceiling(b/n))
        where b:=AbsolutePrecision(y)) >; 
  return Fprime, mp;
end intrinsic;

// ok
intrinsic PurelyRamifiedExtension(R::RngDiffOp,f::RngUPolElt) -> RngDiffOp, Map
   {If R =F[D], where F is a differential ring, returns 
    an operator ring over a purely ramified extension of  F, induced by f.}
  F:=BaseRing(R);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators over a characteristic 0 field.";
  isADF:=IsAlgebraicDifferentialField(F);
  isDLSR:=IsDifferentialLaurentSeriesRing(F);
  require isADF or isDLSR:  
    "The operator basering must be an algebraic differential field or a",
    "differential Laurent series ring.";      
  if isADF then
    require IsCoercible(ConstantField(F), (F!Derivation(R)(F.1))/(F.1)):
      "The derivation of the operator ring must be of the form c*t*d/dt.";
  else  
    require HasScalarProjectiveDerivationOverSeries(R):
      "The derivation of the operator ring must be of the form c*t*d/dt.";
    require RelativePrecisionOfDerivation(R) in 
      {Infinity(), RelativePrecision(F)}:
      "The derivation must have precision: infinite or ring precision.";
  end if;
  bl, seqf:=CanChangeUniverse(Eltseq(f), F);
  require bl:
    "The polynomial cannot be coerced over in the differential base ring.";  
  f:=PolynomialRing(F)!seqf;
  require IsPurelyRamifiedPolynomial(f):
    "The polynomial is not of the correct form.";
  Fext, mpFtoFext:=PurelyRamifiedExtension(f);    
  opmap:=LiftMap(mpFtoFext, R);
  return Codomain(opmap),opmap;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                        Ricatti Factor                          //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Used in the routine RicattiFactor, SemiRegularPart, RightHandFactor.
// May have to be converted to SlopeValuation.
function MinValsCoefsRHF(L)
  // Return the minimum of the slope valuations of the coefficients, when
  // it is negative, otherwise 0.
  assert ISA(Type(L), RngDiffOpElt);
  assert IsDifferentialSeriesRing(BaseRing(Parent(L)));
  seqL:={v :v in Eltseq(L)| not v cmpeq 0};
  if #seqL gt 0 then
    return Minimum([Valuation(v) :v in seqL] cat [0]);
  else 
    return 0;
  end if;
end function;      


// ok
function RicattiCase3_ConstFieldExt(R,C,pol,L,s,precval,exponent)
    vprint RicattiFactor,1:"Extension of the constant ring by", pol;
    assert BaseRing(Parent(pol)) eq C;
    Rext, mp:=ConstantFieldExtension(R,ext<C|pol>);
    Lext:=mp(L);
    assert Parent(Lext) eq Rext;
    Kext:=ConstantRing(BaseRing(Rext));
    P:=PolynomialRing(Kext);
    // Note that the polynomial we factor for has slope 1.
    return FactorWRTNewtPolSlope(Lext,s,(P.1-Kext.1)^exponent,precval), mp;               
end function;  

// ok
function RicattiCase4_ShiftByInteger(F,c,s,L)
  shiftterm:=c*(F.1)^(-s);
  vprint RicattiFactor,1:"Shifting of the operator by", shiftterm; 
  op, mp:=Translation(L, shiftterm);
  return op, mp, shiftterm;                
end function; 

// ok
function RicattiCase5_PureRamExt(F,c,s,L,precval,exponent)
  assert IsDifferentialLaurentSeriesRing(F);
  num:=Numerator(s);
  den:=Denominator(s);
  assert (num gt 0) and (den gt 0);  
  gcd, coefs:=XGCD([num, den]);
  assert gcd eq 1;
  a:=c^(-coefs[1]);
  b:=den*c^(coefs[2]);
  P:=PolynomialRing(F);
  rampol:=(P.1)^den -a*(F.1);
  vprint RicattiFactor,1:"Extension of the series ring by", rampol;
  _, mpFtoFext:=PurelyRamifiedExtension(rampol);
  mp:=LiftMap(mpFtoFext, Parent(L));
  Lext:=mp(L);
    // The problem is that the derivation might not be the standard one
    // but a multiple (by a constant (1/den)) of it.
    // We have to move to a standard scaled operator for factorisation
    // function to work.   
  error if LossInPrecisionInFactorisation(Lext),
    "The precision in the leading coefficient or in the derivation is",
    "too small.";
  sL, mptostandard:=Localization(Lext);
  Lstan:=MonicDifferentialOperator(sL);  
  Rstan:=Parent(Lstan);
  Kstan:=ConstantRing(BaseRing(Rstan));
  P:=PolynomialRing(Kstan);
  seqfactor:=FactorWRTNewtPolSlope(Lstan,den*s,(P.1-b)^exponent,den*precval);
    // Or is precval already enough? No, as the new ring needs to compute
    // with precision that is den times as much.         
    // Move back the standard scaled factor.
  rightfactor:=MonicDifferentialOperator(seqfactor[2]@@mptostandard);
  assert Parent(rightfactor) eq Parent(Lext);    
  return rightfactor, mp, rampol, den;           
end function;  

// ok
function RicattiFactor(L,Precision)
// intrinsic RicattiFactor(L::RngDiffOpElt:Precision:=-1) ->
//     RngDiffOpElt, Map, List
//  {If L is an operator in F[D], returns a first order right hand factor of 
//  L whose coefficients are in an algebraic extension E/F,
//  and the induced inclusion map.
//  The list contains all succesive irreducible polynomials used to obtain E/F.} 
  // Based on the algorithm in Section 5.1 of the article, for an operator
  // with only one slope.
  //
  // The routine should give at least precision non-negative terms
  // in each of the non-leading coefficients of a factor. In order to do so the
  // valuationprecision in the factorisation needs to be adjusted.
  // It is reset as the  given precision - the
  // minimal non-negative valuation of the coefficients of L.
  // It is subsequently multiplied by the denominator of the slope.
  // The Precision sets the precision of any of the series ring coefficient.
  // Precision -1 will lead to the lifting process proceeding until the
  // ring precision as an absolute precision is reached. In this
  // way we should have made sure that the exponential parts will be computed.
  R:=Parent(L);
  F:=BaseRing(R);
  // require Characteristic(F) eq 0:
  error if not  Characteristic(F) eq 0,
    "Routine only implemented for operators of characteristic 0.";
  // require IsDifferentialLaurentSeriesRing(F):
  error if not IsDifferentialLaurentSeriesRing(F),
    "The operator must be defined over a differential Laurent series ring."; 
  // require HasScalarProjectiveDerivationOverSeries(R):
  error if not HasScalarProjectiveDerivationOverSeries(R),
    "The derivation of the operator ring must be of the form c*t*d/dt.";      
  orderL:=WeakOrder(L);
  // require orderL ge 1:
  error if not orderL ge 1,
    "The weak degree of the operator should be at least 1.";
  // require IsWeaklyMonic(L):
  error if not IsWeaklyMonic(L),
    "The highest coefficient should be weakly equal to 1.";
  bl, Accuracy:=IsCoercible(Integers(), Precision);
  // require bl:
  error if not bl,
    "The set accuracy must be an integer."; 
  // require (Accuracy eq -1) or (Accuracy gt 0):
  error if not ((Accuracy eq -1) or (Accuracy gt 0)),
    "The set accuracy must be a positive integer or -1.";
  /*   
    // Code for when we allow the user to specify a slope via an option 
    // called Slope.
  bl, Slope:=IsCoercible(Rationals(), Slope);
  // require bl:
  error if not bl,
    "The set slope of the Newton Polygon must be rational.";
  // require (Slope eq -1) or (Slope ge 0):
  error if not ((Slope eq -1) or (Slope ge 0)),
    "The set slope of the Newton Polygon must be non-negative or -1.";  
  */  
      // Case 1 in the article. 
  if orderL eq 1 then 
    vprint RicattiFactor,2:"Case 1 of RicattiFactor algorithm."; 
    return L, Coercion(R,R), [* *];
  end if;  
  if not HasProjectiveDerivation(R) then
    // require not LossInPrecisionInFactorisation(L):
    error if LossInPrecisionInFactorisation(L),
      "The precision in the leading coefficient or in the derivation is",
      "too small.";
    Lstan, mptostandard:=Localization(L);
    Lstan:=MonicDifferentialOperator(Lstan);   
    Rstan:=Parent(Lstan); 
    // fact, mpRstantoRfact, list:=$$(Lstan:Precision:=Accuracy);
    fact, mpRstantoRfact, list:=$$(Lstan,Accuracy);
    Rfact:=Parent(fact);
    assert not IsWeaklyZero(LeadingCoefficient(fact));
    if Rstan eq Rfact then
      fact:=MonicDifferentialOperator(Inverse(mptostandard)(fact));
      return fact, Coercion(R,R), list;      
    else
      // The derivation of R is of the form c*t*d/dt.
      // We make an extension of R, called Rext,
      // relating to the extension Ffact/Fstan.
      c:=Coefficient((Derivation(R)(F.1))/F.1,0);
      C:=ConstantRing(BaseRing(Rfact));
      bl, c:=IsCoercible(C,c);
      assert bl;
      assert not IsWeaklyZero(c);
      Rext, mpRfacttoRext:=ChangeDerivation(Rfact, c);
      fact:=MonicDifferentialOperator(mpRfacttoRext(fact));
      mp:=mptostandard*mpRstantoRfact*mpRfacttoRext;
      mp:=map<R->Codomain(mp)| x:-> mp(x), y:->y@@mp>;
      return fact, mp, list;
    end if;
  end if;  
   // We do not allow Case 2b; we want 1 slope only.    
  np:=NewtonPolygon(L);
  slopes:=Slopes(np);
  vprint RicattiFactor,1:"All slope(s) of the Newton Polynomial:", slopes;
  /*  
    // Code for when we allow the user to specify a slope via an option 
    // called Slope.
  error if (Slope ge 0) and not exists {v :v in slopes | Slope cmpeq v},
    "The specified value of the slope does not occur as an actual slope.";
  error if (Slope cmpeq -1) and (#slopes gt 1),
    "Specify a value for the slope."; 
  if Slope ge 0 then
    s:=Slope;
  else  
    assert (Slope cmpeq -1) and (#slopes eq 1);
    s:=slopes[1];
  end if;   
  */
  // require #slopes eq 1:
  error if not #slopes eq 1,
    "Only operators whose Newton polynomial has precisely one slope allowed.";  
  bl, s:=IsCoercible(Rationals(), slopes[1]);
  assert bl;
  den := Denominator(s);
  assert GCD(Numerator(s), den) eq 1;
  npol:=NewtonPolynomial(Faces(np)[1]);  
  C:=ConstantRing(F);
  assert BaseRing(Parent(npol)) eq C;
  factors, const:=Factorisation(npol);
  vprint RicattiFactor,1:"Consider slope:", s;
  vprint RicattiFactor,1:"Factors of the Newton polynomial:", factors;
  // take the first factor.
  pol:=factors[1][1];
  exponent:=factors[1][2];
  degpol:=Degree(pol);
  assert IsMonic(pol);
  assert degpol eq Minimum([Degree(v[1]) :v in factors]);
  minvalscoefsL := MinValsCoefsRHF(L);
  relprecF:=Integers()!RelativePrecision(F);
    // precval is the precision we need for the right hand factor. It will
    // minimally be the absolute precision, and all exponential parts should
    // be obtained.
  if Accuracy gt 0 then
    precval:=Integers()!Accuracy-minvalscoefsL;
  else
    vprint RicattiFactor,2:"Ring precision as default precision taken.";
    precval:=relprecF-minvalscoefsL;
  end if; 
  vprint RicattiFactor,2:"Extending precision with:", -minvalscoefsL;
  vprint RicattiFactor,1:"Working with precision:", precval;
  if (s gt 0) and (#factors gt 1) then
      // Case 2c in the article.
      // do it for one of the factors, i.e. for pol.   
    vprint RicattiFactor,2:"Case 2c of RicattiFactor algorithm.";  
      // Perform Coprime index 1 factorisation.
      // Multiply precision by the denominator to obtain enough coefficient
      // precision.
    seqfactor:=FactorWRTNewtPolSlope(L,s,pol^exponent,den*precval);  
    // return $$(seqfactor[2]:Precision:=Accuracy);
    // return $$(seqfactor[2]:Precision:= precval+MinValsCoefsRHF(seqfactor[2]));
    return $$(seqfactor[2],precval+MinValsCoefsRHF(seqfactor[2]));
  elif (s eq 0) and ((#factors gt 1) or (exponent gt 1)) then
      // Case 2a in the article.
      // do it for one of the factors, i.e. for pol.
      // According to the coprime index 1 algorithm we have to 
      // put the exponent to 1 if the slope is 0.
    vprint RicattiFactor,2:"Case 2a of RicattiFactor algorithm.";  
    assert den eq 1;
    seqfactor:=FactorWRTNewtPolSlope(L,s,pol,precval);  
    // return $$(seqfactor[2]:Precision:=Accuracy); 
    // return $$(seqfactor[2]:Precision:=precval+MinValsCoefsRHF(seqfactor[2]));
    return $$(seqfactor[2],precval+MinValsCoefsRHF(seqfactor[2]));
  elif degpol gt 1 then
      // Case 3 in the article.
    vprint RicattiFactor,2:"Case 3 of RicattiFactor algorithm.";
    seqfactor, mp:=RicattiCase3_ConstFieldExt(R,C,pol,L,s,precval,exponent);
    // fact, g, list:=$$(seqfactor[2]:Precision:=Accuracy);
    // fact, g, list:=$$(seqfactor[2]:Precision:=precval+MinValsCoefsRHF(seqfactor[2]));
    fact, g, list:=$$(seqfactor[2],precval+MinValsCoefsRHF(seqfactor[2]));
    mp:=mp*g;
    mp:=map<R->Codomain(mp)| x:-> mp(x), y:->y@@mp>;
    return fact, mp, [* pol *] cat list;   
  else
    assert s gt 0;
    assert degpol eq 1;
    // get the root c.
    c:=-Coefficient(pol,0);
    bl, sint:=IsCoercible( Integers(),s);  
    if bl then
        // Case 4 in the article.
      vprint RicattiFactor,2:"Case 4 of RicattiFactor algorithm.";
      shiftL:=RicattiCase4_ShiftByInteger(F,c,sint,L); 
        // After shifting the lowest term will disappear as it 
        // is one of the monomials in the expansion we want to consider.
        // Therefore we can deduce the precision by 1 in the next step.
      // fact, g, list:=$$(shiftL:Precision:=Accuracy);
      // fact, g, list:=$$(shiftL:Precision:=precval+MinValsCoefsRHF(shiftL)-1);
      fact, g, list:=$$(shiftL,precval+MinValsCoefsRHF(shiftL)-1);
      Rshift:=Parent(fact);
      gen:=Coefficient((g(R!(F.1))),0);
      return Translation(fact, -c*(gen)^(-sint)),g, list;
    else  
        //Case 5 in the article.          
      vprint RicattiFactor,2:"Case 5 of RicattiFactor algorithm.";
      // The RicattiFactor5, already takes care of the denominator.
      rightfactor,mp,rampol,denval:=
        RicattiCase5_PureRamExt(F,c,s,L,precval,exponent);
      // fact, g, list:=$$(rightfactor:Precision:=Accuracy);
      // fact, g, list:=$$(rightfactor:Precision:=denval*precval+MinValsCoefsRHF(rightfactor));
      fact, g, list:=$$(rightfactor,denval*precval+MinValsCoefsRHF(rightfactor));
      mp:=mp*g;
      mp:=map<R->Codomain(mp)| x:-> mp(x), y:->y@@mp>;
      return fact, mp, [* rampol *] cat list; 
    end if;
  end if;
    // The following should not occur.
  "No Ricatti factor calculated.";
  return L, Coercion(R,R), [* *];  
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//               Semi-regular right hand factors                  //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
function AreAllShiftedByIntegers(S) 
  // Input: The factors of a polynomial.
  //        So S[i] = <factor, multiplicity of factor>.
  // Output: true iff every factor h is shifted by an integer from each
  //         other by an integer i(h), and the sequence of these integers,
  //         with respect to one fixed polynomial g, counted with multiplicities. 
  //         and the polynomial g. This polynomial g is choosen so that all 
  //         other ones are negative shifts.
  nrpols:=#S;
  assert nrpols gt 0;
  deg:={Degree(h[1]):h in S};
  if #deg gt 1 then 
    return false, _, _;
  end if; 
  deg:=Setseq(deg)[1];
  g:=S[1][1];
  if nrpols eq 1 then
    // Only one factor in S. It is shifted with 0 from itself.
    // Count 0 with multiplicity the number of times the 
    // factor occurs.
    return true, [Integers()| 0 :i in [1..S[1][2]]], g;
  end if;
  // First see if all polynomials are shifted from the first.
  seqintegers:=[Integers()| 0];
  polnumber:=1;
  shifted:=true;
  while (polnumber lt nrpols) and shifted do
    polnumber:=polnumber +1;
      // Determine if g(T)=h(T+i).
    bl, int:=IsShiftedByRingElt(g,S[polnumber][1],Integers());
    if bl then
      Append(~seqintegers, int);
    else
      shifted:=false;
    end if ;   
  end while; 
  if shifted then
    // Construct sequences of integers, including multiplicities.
    assert #seqintegers eq nrpols;
    maxint, index:=Maximum(seqintegers);
    pol:=S[index][1];
    seqintegers:=([Integers()|v-maxint :v in seqintegers]);  
    seqintegers:=[seqintegers[i] :j in [1..S[i][2]], i in [1..nrpols]];
    return true, seqintegers, pol;
  else
    return false, _, _;
  end if;
end function;

// ok
function LiftTransToDiffExt(trans, mp)
  // Input: trans, a translation map on differential operator ring R->R.
  //      extension map mp from R to Rext that send R.1 to a degree 1 operator.
  // Output: the lift of trans on Rext->Rext.
  R:=Domain(mp);
  Rext:=Codomain(mp);
  assert (Domain(trans) eq R) and (Codomain(trans) eq R);
  if (R eq Rext) then
    return trans;
  end if;  
    // first the image of R.1 under mp.
  mpD:=mp(R.1);
  assert Degree(mpD) eq 1;
  c:=Coefficient(mpD,1);
  a:=Coefficient(mpD,0);
  assert not IsWeaklyEqual(c,0);
    // Next the image of trans(R.1) under mp.
  mptransD:=(trans*mp)(R.1);
  assert (Degree(mptransD) eq 1);
  d:=Coefficient(mptransD,1);
  b:=Coefficient(mptransD,0);  
  assert not IsWeaklyEqual(d,0);
  ddivc:=d/c;
  edivc:=(b-a)/c;  
  cdivd:=c/d;
  fdivd:=(a-b)/d;
  return map<Rext->Rext| 
           L :-> (deg cmpeq -1 select (Rext!0) else
             &+([Coefficient(L,i)*(ddivc*Rext.1+edivc)^i :i in [0..deg]]) 
             where deg:=Degree(L)),
           L :->  (deg cmpeq -1 select (Rext!0) else
             &+([Coefficient(L,i)*(cdivd*Rext.1+fdivd)^i :i in [0..deg]]) 
             where deg:=Degree(L))>; 
end function;

// ok 
function SemiRegularParts(L,Precision)
// intrinsic SemiRegularParts(L::RngDiffOpElt:Precision:=-1) -> SeqEnum
//   {All semi-regular (right hand) parts of L modulo 
//    algebraic conjugation over the differential basefield of L.}
  // This code is base on the algorithm ``Semi-regular parts'' in
  //  Mark van Hoeij's paper (Section 8.4).
  // A returned sequence element is of the form:
  //  <Factor, map Parent(L) -> Parent(Rightfactor),
  //   list of successive ramification polynomials>. 
  // Note that the sum of the degrees of the semi-regular parts may not
  // add up to the degree of L.
  // The routine should give at least precision non-negative terms
  // in each of the non-leading coefficients of a factor. In order to do so the
  // valuationprecision in the factorisation needs to be adjusted.
  // It is reset as the  given precision - the
  // minimal non-negative valuation of the coefficients of L.
  // It is subsequently multiplied by the denominator of the slope.
  R:=Parent(L);
  F:=BaseRing(R);
  // require Characteristic(F) eq 0:
  error if not Characteristic(F) eq 0,
    "Routine only implemented for operators of characteristic 0.";
  // require IsDifferentialLaurentSeriesRing(F):
  error if not IsDifferentialLaurentSeriesRing(F),
    "The operator must be defined over a differential Laurent series ring."; 
  // require HasScalarProjectiveDerivationOverSeries(R):
  error if not HasScalarProjectiveDerivationOverSeries(R),
    "The derivation of the operator ring must be of the form c*t*d/dt."; 
  bl, Accuracy:=IsCoercible(Integers(), Precision);
  // require bl:
  error if not bl,
    "The set accuracy must be an integer.";
  // require (Accuracy ge -1) and (Accuracy ne 0):
  error if not ((Accuracy ge -1) and (Accuracy ne 0)),
    "The set accuracy must be a positive integer or -1.";      
  orderL:=WeakOrder(L);
  // require orderL ge 1:
  error if not orderL ge 1,
    "The weak degree of the operator should be at least 1.";   
  // require IsWeaklyMonic(L):
  error if not IsWeaklyMonic(L),
    "The highest coefficient should be weakly equal to 1.";
      // Case 1 in the article.
  if orderL eq 1 then 
    vprint SemiRegularParts,2:"Case 1 of SemiRegularParts algorithm."; 
    return [PowerStructure(Tup)|< L, Coercion(R,R) , [**]> ];
  end if;  
     // Move to series ring with standard derivation.
  listricfacts:=[PowerStructure(Tup)|];
  if not HasProjectiveDerivation(R) then
      "Non-standard derivation detected.";
    // require not LossInPrecisionInFactorisation(L):
    error if LossInPrecisionInFactorisation(L),
      "The precision in the leading coefficient or in the derivation is",
      "too small.";
      // It may be possible that some loss is precision may occur when
      // moving to the standard operator ring (I think). AW.)
    "Localizing the operator ring. Loss in precision may occur.";
    Lstan, mptostandard:=Localization(L);
      // Since R has a projective standard scale derivation, the map
      // should be trivial on F. 
    Lstan:=MonicDifferentialOperator(Lstan);   
    Rstan:=Parent(Lstan);   
    // list:= $$(Lstan:Precision:=Accuracy);
    list:= $$(Lstan,Accuracy);   
    for v in list do
      fact:=v[1];
      Rfact:=Parent(fact);
        // Rfact is an operator ring that respects the standard
        // derivation of Rstan by construction.
      assert not IsWeaklyZero(LeadingCoefficient(fact));  
      if Rstan eq Rfact then
        fact:=MonicDifferentialOperator(Inverse(mptostandard)(fact));
        Append(~listricfacts,<fact, Coercion(R,R), v[3]>); 
      else
          // Pull back to an extension of the original ring R.
          // We need to lift mptostandard and compute a diff op ring above
          // R, such that the derivation is c*t*d/dt on F.
          // Such a ring is Rext as follows.
        c:=Coefficient((Derivation(R)(F.1))/F.1,0);
        C:=ConstantRing(BaseRing(Rfact));
        bl, c:=IsCoercible(C,c);
        assert bl;
        assert not IsWeaklyZero(c);
        Rext, mpRfacttoRext:=ChangeDerivation(Rfact, c);
        fact:=MonicDifferentialOperator(mpRfacttoRext(fact));
        mp:=mptostandard*v[2]*mpRfacttoRext;
        mp:=map<R->Codomain(mp)| x:-> mp(x), y:->y@@mp>;
        Append(~listricfacts,<fact, mp, v[3]>); 
      end if;
    end for;
    return listricfacts;
  end if;  
  minvalscoefsL := MinValsCoefsRHF(L);
  relprecF:=Integers()!RelativePrecision(F);
    // precval is the precision we need for the right hand factor. It should
    // minimally become the absolute precision.
  if Accuracy gt 0 then
      // Old version: subtract 1 from accuracy only.
      // The precision of the valuation is enlarged to accomodate the
      // negative monomials.
    precval:=Integers()!Accuracy-minvalscoefsL;
  else
    precval:=relprecF-minvalscoefsL;
  end if;    
    // Case 2. in the article.
    // Use the LCLM algorithm to keep the semi-regular solution spaces apart.
    // The slope 0 will need special attention.   
    // 
    // We may want to add a setting if we are already convinced the L
    // is an LCLM part and omit the factorisation following.
    // factsL:=Factorisation(L:Precision:=Accuracy, Algorithm:="LCLM");
    // As we want proper precval monomials, rather then the number
    // obtained from a slope valuation we set the boolean in the next
    // function to true.
  factsL := FactorisationForStandardScaledOperator(L,precval,"LCLM",true);
  rightfacts:=[v[2] :v in factsL];
  nrright:=#rightfacts;
  if nrright gt 1 then
    vprint SemiRegularParts,2:"Case 2 of SemiRegularParts algorithm.";
    vprint SemiRegularParts,1:"Separate computations for the", nrright, 
                             "right factors from the factorisation algorithm." ;
    countright:=0;			     
    for rightfactor in rightfacts do
      countright:=countright+1;
      vprint SemiRegularParts,1:" ";
      vprint SemiRegularParts,1:"Computing the semi-regular part for the",
                                "right hand factor number:", countright;
      // list:=$$(rightfactor:Precision:=Accuracy);  
      // list:=$$(rightfactor:Precision:=precval+MinValsCoefsRHF(rightfactor));
      list:=$$(rightfactor,precval+MinValsCoefsRHF(rightfactor));
      listricfacts:=listricfacts cat list;
    end for;
    return listricfacts;
  end if;  
    // We are now in the situation that only one LCLM right hand factor exists.
  assert #rightfacts eq 1;
  rightfactor:=rightfacts[1];
  np:=NewtonPolygon(L);
  slopes:=Slopes(np);
  assert #slopes eq 1;
  bl, s:=IsCoercible(Rationals(), slopes[1]);
  assert bl; 
  npol:=NewtonPolynomial(Faces(np)[1]);  
  C:=ConstantRing(F);
  assert BaseRing(Parent(npol)) eq C;
  factors, const:=Factorisation(npol);
    // The next assertion is a result of the factorisation already performed.
  if s gt 0 then
    assert (#factors eq 1);
  end if;  
  vprint SemiRegularParts,1:"The slope of the operator:", s;
  vprint SemiRegularParts,1:"Factors of the Newton polynomial:", factors;
  pol:=factors[1][1];
  exponent:=factors[1][2];
  degpol:=Degree(pol);
  assert IsMonic(pol);
   // Case 3. in the article.
  if (s gt 0) and (#factors eq 1) and (degpol gt 1) then
    vprint SemiRegularParts,2:"Case 3 of SemiRegularParts algorithm.";
    seqfactor, mp:=RicattiCase3_ConstFieldExt(R,C,pol,L,s,precval,exponent);
    // list:= $$(seqfactor[2]:Precision:=Accuracy);   
    // list:= $$(seqfactor[2]:Precision:=precval+MinValsCoefsRHF(seqfactor[2]));
    list:= $$(seqfactor[2],precval+MinValsCoefsRHF(seqfactor[2]));
    for v in list do
      emb:=mp*v[2];
      emb:=map<R->Codomain(emb)| x:-> emb(x), y:->y@@emb>;      
      Append(~listricfacts, < v[1], emb, [* pol *] cat v[3]>);
     end for;
    return listricfacts;   
  end if;
  bl, sint:=IsCoercible( Integers(),s);
  c:=-Coefficient(pol,0);
    // Case 4. in the article.
  if (s gt 0) and bl and (#factors eq 1) and (degpol eq 1) then
    vprint SemiRegularParts,2:"Case 4 of SemiRegularParts algorithm.";
    shiftL, shiftmap, shiftterm:=RicattiCase4_ShiftByInteger(F,c,sint,L);
      // After shifting the lowest term will disappear as it 
      // is one of the monomials in the expansion we want to consider.
      // Therefore we can deduce the precision by 1 in the next step.
      // list:= $$(shiftL:Precision:=Accuracy);
    // list:= $$(shiftL:Precision:=precval+MinValsCoefsRHF(shiftL)-1);
    list:= $$(shiftL,precval+MinValsCoefsRHF(shiftL)-1);
    for v in list do 
      embmp:=v[2];  
      Rext:=Codomain(embmp);
      extshiftmap:=LiftTransToDiffExt(shiftmap, embmp);
      fact, _:=Translation(v[1], -BaseRing(Rext)!embmp(R!shiftterm));
      emb:=shiftmap*embmp*Inverse(extshiftmap);
      emb:=map<R->Codomain(emb)| x:-> emb(x), y:->y@@emb>;
      Append(~listricfacts, <fact, emb, v[3]>);
    end for;
    return listricfacts;
  end if;
    // Case 5. of the article.
  if (s gt 0) and (not bl) and (#factors eq 1) and (degpol eq 1) then 
    vprint SemiRegularParts,2:"Case 5 of SemiRegularParts algorithm.";
    rightfactor,mp,rampol,denval:=
        RicattiCase5_PureRamExt(F,c,s,L,precval,exponent);  
    // list:= $$(rightfactor:Precision:=Accuracy);
    // list:= $$(rightfactor:Precision:=denval*precval+MinValsCoefsRHF(rightfactor)); 
    list:= $$(rightfactor,denval*precval+MinValsCoefsRHF(rightfactor));
    for v in list do
      emb:=mp*v[2];
      emb:=map<R->Codomain(emb)| x:-> emb(x), y:->y@@emb>;
      Append(~listricfacts, <v[1], emb,  [* rampol *] cat v[3]>);
    end for; 
    return listricfacts;
  end if;
    // Remains only the integer shifted factors for s=0.
    // Case 6. of the article.
  assert s eq 0;
  bl, seqintegers, g:=AreAllShiftedByIntegers(factors);
  assert bl;
  assert not exists {v :v in seqintegers | v gt 0};
  assert IsMonic(g) and BaseRing(Parent(g)) eq C;
  vprint SemiRegularParts,2:"Case 6 of SemiRegularParts algorithm.";
  degg:=Degree(g);
  if degg eq 1 then
    hasextension:=false;
      // Shift with the root r of g.
    r:=F!(-Coefficient(g,0));
    vprint SemiRegularParts,1:"Shifting of the operator by:", r;
    Lshift, shiftmap:=Translation(L, r);
    assert Parent(Lshift) eq R;
    P:=PolynomialRing(C); 
  else 
    hasextension:=true;  
      // Make constant field extension before shifting.
    vprint SemiRegularParts,1:"Extension of the constant ring by:", g;  
    Rext, mp:=ConstantFieldExtension(R,ext<C|g>);
    Lext:=mp(L);
    Fext:=BaseRing(Rext);
    Kext:=ConstantRing(Fext);
    r:=Fext!(Kext.1);
      // Now shift with the root r of g.
    vprint SemiRegularParts,1:"Shifting of the operator by", r;
    Lshift, shiftmap:=Translation(Lext, r); 
    assert Parent(Lshift) eq Rext;
    P:=PolynomialRing(Kext);
  end if;
    // Perform coprime index 1 factorisation for h that is the product of
    // all integer shifts of P.1.
  h:=&*([P| (P.1-j):j in (seqintegers)]);
  vprint SemiRegularParts,1:"Factorisation w.r.t. Newton polynomial:", h;   
    // Since it factors all shifted by non-positive
    // integers, including 0, it will only factor w.r.t. slope P.1.
    // Therefore providing P.1 rather than h suffices?
    // seqfactor:=FactorWRTNewtPolSlope(Lshift,s,P.1,degg*precval);
    // seqfactor:=FactorWRTNewtPolSlope(Lshift,s,h,degg*precval);
    // This has to be the coprime index 1 factorisation (no LCLM).
    // Note also that the denominator of s=0 is 1.
  seqfactor:=FactorWRTNewtPolSlope(Lshift,s,h,precval);      
  list:=[PowerStructure(Tup)|
    <seqfactor[2], Coercion(W,W) where W:=Parent(seqfactor[2]) , [**]> ];
  listbeforeshift:=[PowerStructure(Tup)|]; 
  for v in list do 
    emb:=v[2]; 
    assert Domain(emb) eq Parent(seqfactor[2]);
    fact,_:=
      Translation(v[1], -BaseRing(Codomain(emb))!emb(Domain(emb)!r)); 
    extshiftmap:=LiftTransToDiffExt(shiftmap,emb);  
    emb:=shiftmap*emb*Inverse(extshiftmap);
    emb:=map<Domain(emb)->Codomain(emb)| x:-> emb(x), y:->y@@emb>;
    Append(~listbeforeshift, <fact, emb, v[3]>);
  end for;
  if not hasextension then
    return listbeforeshift;
  end if;
  for v in listbeforeshift do
    emb:=mp*v[2];
    emb:=map<R->Codomain(emb)| x:-> emb(x), y:->y@@emb>;
    Append(~listricfacts, < v[1], emb, [* g *] cat v[3]>);
  end for;
  return listricfacts;
    // The following should not happen.
  error true,
  "Calculation failed, bug in SemiRegularParts algorithm.";
  // return listricfacts;
end function;
 

////////////////////////////////////////////////////////////////////
//                                                                //
//                     Right hand factors                         //
//                                                                //
////////////////////////////////////////////////////////////////////


// ok
// Uses Coprime index 1 LCLM factorisation, Semi-regular parts, 
// and the Ricatti factor routine.
intrinsic RightHandFactors(L::RngDiffOpElt:Precision:=-1) -> SeqEnum, BoolElt
  {The list of monic right hand factors of L that correspond to its 
   semi-regular parts. 
   The second is true iff the right hand factor is proved irreducible.}
  // The routine should give at least precision non-negative terms
  // in each of the non-leading coefficients of a factor. In order to do so the
  // valuationprecision in the factorisation part needs to be adjusted.
  // It is reset as the  given precision - the
  // minimal non-negative valuation of the coefficients of L.
  // It is subsequently multiplied by the denominator of the slope.  
  R:=Parent(L);
  F:=BaseRing(R);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsDifferentialLaurentSeriesRing(F):
    "The operator must be defined over a differential Laurent series ring.";
  require not IsWeaklyZero(L):
    "The operator is weakly equal to 0.";
  relprecF := RelativePrecision(F);
  require relprecF gt 0:
    "The relative precision of the differential ring must be positive.";
  bl, Accuracy:=IsCoercible(Integers(), Precision);
  require bl:
    "The set accuracy must be an integer.";
  require (Accuracy ge -1) and (Accuracy ne 0):
    "The set accuracy must be a positive integer or -1.";  
  if not IsWeaklyMonic(L) then
    coef:=LeadingCoefficient(L);
    rhf, bl:=$$(MonicDifferentialOperator(L));
    return rhf, bl;
  end if;
  if not HasProjectiveDerivation(R) then
    "Non-standard derivation detected.";
    require not LossInPrecisionInFactorisation(L):
      "The precision in the leading coefficient or in the derivation is",
      "too small.";
      // It may be possible that some loss is precision may occur when
      // moving to the standard operator ring (I think). AW.)
    "Localizing the operator ring. Loss in precision may occur.";
    sL, mptostandard:=Localization(L);
    standardL:=MonicDifferentialOperator(sL);  
    rhf, bl:=$$(standardL); 
    rhf:=[R| v@@mptostandard :v in rhf];
    rhf:=[R|MonicDifferentialOperator(v) :v in rhf];
    return rhf, bl;
  end if;  
  assert HasProjectiveDerivation(R);
    // Compute first split up in LCLM algorithm. This will give a 
    // break up in right hand factors with no exponential parts in common.
    // Not all of these factors may be irreducible.
  minvalsL := MinValsCoefsRHF(L);
  if Accuracy gt 0 then
    accuracyL:=Accuracy;
  else
    accuracyL:=relprecF;
  end if;
    // We extend the precision so that all terms with a
    // negative valuation in the coefficient will be obtained.
  vprint RightHandFactors,1:"Computing coprime index 1 LCLM factors.";  
  seq, areirreducible:=
    FactorisationForStandardScaledOperator(L,(accuracyL-minvalsL),"LCLM",true);
    // Factorisation(L:Algorithm:="LCLM", Precision:=(accuracyL-minvalsL));
    // For pure slope valuation only do the following.
    // Factorisation(L:Algorithm:="LCLM", Precision:=accuracyL);
  vprint RightHandFactors,1:"Coprime index 1 LCLM factorisation completed.";
    // Every right term returned by Factorisation has one slope.
    // and belongs to an exponential part class.
    // The newton polynomial might still be reducible.
  rh:=[R| v[2] :v in seq];
  rhfactors:=[R|];
  vprint RightHandFactors,1:"The number of right hand factors from LCLM factorisation:", #rh;
  vprint RightHandFactors,2:"They are:", rh;
  vprint RightHandFactors,1:" ";
  foundall:=true;
  bls:=[];
  for r in rh do 
    assert Parent(r) eq R;
    indexr:=Index(rh,r);
    vprint RightHandFactors,1:"Calculations for LCLM right hand factor number:", indexr;
    if areirreducible[indexr] eq "true" then
      rhfactors:=rhfactors cat [r];
      bls[indexr]:=true;
      vprint RightHandFactors,1:"LCLM right hand factor is irreducible.";
      vprint RightHandFactors,1:" ";
    else     
      vprint RightHandFactors,1:"LCLM right hand factor may be reducible.";
        // Compute all semi-regular parts of r.
        // Then use these to compute all right hand factors 
        // over the base ring of L using an LCLM routine from .
      "Calculating semi-regular parts.";	
      accuracyr:=accuracyL - minvalsL;
      // listfacts:=SemiRegularParts(r:Precision:=accuracyr);
      // listfacts:=SemiRegularParts(r:Precision:=accuracyr+MinValsCoefsRHF(r));
      listfacts:=SemiRegularParts(r,accuracyr+MinValsCoefsRHF(r));
      srparts:=[* v[1] :v in listfacts *];
      embmaps:=[* v[2] :v in listfacts *];	
      extpols:=[* v[3] :v in listfacts *];
      vprint RightHandFactors,1:"The number of semi-regular parts of LCLM factor",indexr,"is:", #srparts;
      vprint RightHandFactors,1:" ";
      for i in [1..#srparts] do
           // Extend precision if necessary or compute only a few terms 
           // and lift to speed up calculations. This may be a better way
           // to write the LCLM function anyway.
        srpart:=srparts[i];   
        degsrpart:=Degree(srpart);
        vprint RightHandFactors,1:"Considering semi-regular part number:", i; 
        vprint RightHandFactors,2:"Degree of semi-regular part:", degsrpart;  
        if degsrpart eq 1 then;
          "Performing LCLM calculation on a semi-regular part.";      
          LC:=LCLMOverSeries(srpart, embmaps[i]); 
        else   
          "Computing a first order Ricatti factor.";
          pols := [v : v in extpols[i] | 
                       not CanChangeUniverse(Eltseq(v), BaseRing(Parent(v)))];
          if IsEmpty(pols) then
            multfactor := 1;
          else
            multfactor := &*[Degree(pol): pol in pols]; 
          end if;   
          accuracysrpart:=multfactor*(accuracyL-minvalsL)
                          +MinValsCoefsRHF(srpart);
          // ric, mp, _:=RicattiFactor(srpart:Precision:=accuracysrpart);
          ric, mp, _:=RicattiFactor(srpart,accuracysrpart); 
          "Performing LCLM calculation on the Ricatti factor.";
            // Hope this works.             
          LC:=LCLMOverSeries(ric,(embmaps[i])*mp);         
        end if;     
	if not IsWeaklyZero(LC) then
          vprint RightHandFactors,2:"The LCLM from the semi-regular part:", LC;
          assert Parent(LC) eq R;
	  leftLC, rem:=EuclideanRightDivision(L,LC);
	  assert IsWeaklyEqual(rem, R!0);
          if IsWeaklyEqual(LC, r) then
            LC:=r;
          end if;  
          rhfactors:=rhfactors cat [LC];
          bls[indexr]:=true;
	  vprint RightHandFactors,1:"Irreducible right hand factor",
            "of degree", Degree(LC), "found.";
	else
	  foundall:=false;
          bls[indexr]:=false;
          rhfactors:=rhfactors cat [r];
          vprint RightHandFactors,1:"LCLM calculation failed for semi-regular part.";
	end if;
        vprint RightHandFactors,1:" ";
      end for; 
    end if; 
  end for;
  if foundall and (&+[WeakDegree(v) :v in rhfactors] eq WeakDegree(L)) then
    vprint RightHandFactors,1:"Full set of irreducible right hand",
                               "factors obtained.";                                                      
  end if;
  return rhfactors, bls;
end intrinsic;


