freeze;

declare verbose DiffRng,1;

////////////////////////////////////////////////////////////////////
//                                                                //
//                 DIFFERENTIAL FIELDS AND RINGS                  //
//                                                                //
//               Original design and implementations              //
//                               by                               //
//                      Alexa van der Waall                       //
//                                                                // 
//                   Uses C-code implemented by                   //
//                       Nicole Sutherland                        //
//                                                                //
//              Additional design and implementations             //
//                               by                               //
//                           Nils Bruin                           //
//                               and                              //
//                       Nicole Sutherland                        //
//                                                                //
////////////////////////////////////////////////////////////////////



// General creation functions written in C
// These creation functions are DifferentialRing(Rng, Map, Rng) and 
// DifferentialField(FldFun, DiffFunElt)
// IT IS PROBABLY BEST TO EXPORT THE FOLLOWING 
// ROUTINE RationalDifferentialField INSTEAD OF THE MORE GENERAL
// DifferentialField(FldFun,DiffFunElt).
// AT LEAST THIS SEEMS EASIER FOR THE USER FOR NOW.


// READ ME.
//
// WHEN CREATING A (LAURENT) SERIES DIFFERENTIAL RING MAKE
// SURE THAT IT IS ALWAYS OF THE FORM C((x)) WHERE C IS THE DIFFERENTIAL
// CONSTANT RING AND X THE GENERATOR OF THE SERIES RING.
// THE ONLY ELEMENTS  THAT MAY HAVE NON-ZERO DERIVATIONS ARE THUS
// THE POWERS OF X.
//
// WHEN CREATING AN ALGEBRAIC DIFFERENTIAL FIELD MAKE
// SURE THAT IT IS ALWAYS OF THE FORM C(X) WHERE C IS THE DIFFERENTIAL
// CONSTANT RING AND X THE GENERATOR OF THE FIELD.
// THIS SHOULD BE THE CASE BY CONSTRUCTION VIA THE DIFFERENTIAL
// OF THE DERIVATION.



////////////////////////////////////////////////////////////////////
//                                                                //
//                        General Functions                       //
//                                                                // 
////////////////////////////////////////////////////////////////////


function MyNgens(K)
  if  Type(K) in {RngUPol, RngMPol, RngMPolRes, FldFunRat} then
    return Rank(K);
  elif Type(K) in {FldRat} then
    return 0;
  elif Type(K) in {FldFun, FldNum, RngDiff} then
    return Ngens(K); 
  elif Type(K) in 
      {RngSerPow, RngSerLaur, RngSerPuis} then
    return 1;
  else
    return "MyNgens is not defined for this type of ring.";
  end if;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////


declare attributes RngDiff:
  Generators,
  URGenerators,
  IsDifferentialLSR,
  BaseRingDiffLSRExtension;  


////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic DifferentialRing(R::Rng,D::Map,C::Rng) -> RngDiff
  {The ring R with derivation D and constant ring C.}
  // KEEP THIS INTRINSIC AS GENERAL AS POSSIBLE.
  // DO NOT ADD ANY RESTRICTIONS UNLESS IT IS REALLY GENERAL.
  // OTHERWISE WRITE A SEPARATE CREATION AS IS DONE FOR E.G.
  // RationalDifferentialField.
  return InternalDifferentialRing(R,D,C);
end intrinsic;

intrinsic RationalDifferentialField(C::Rng) -> RngDiff
  {Creates the algebraic differential field in one variable over
   the constant field C, with differential (1) d ($.1).}
  require IsField(C):
    "The given argument must be a field.";
  K:=RationalFunctionField(C:Type:=FldFun,Global:=false);
  dz:=Differential(K.1);
  F:=DifferentialField(K,dz);
  U:=UnderlyingRing(F);
  assert ISA(Type(U),FldFun);
  F`Generators:=[U.i: i in [1..Ngens(U)]];
  return F;
end intrinsic;

intrinsic DifferentialLaurentSeriesRing(C::Fld:Precision:=Infinity()) -> RngDiff
  {Creates the differential ring of the form F=C((t)), with derivation t*d/dt.}
     // The underlying ring is a Laurent series ring with infinite precision.
  require Characteristic(C) eq 0:
    "The characteristic of the given field should be 0.";
  bl, Prec:=IsCoercible(Integers(),Precision);
  require bl or Precision cmpeq Infinity():
    "The precision must be an integer or infinite";
  if bl then
      Precision := Prec;
  end if;
  require Precision ge 2:
    "The set precision must be a positive integer greater than 1.";
  if Precision eq Infinity() then
    LS:=LaurentSeriesRing(C);
  else
    LS:=LaurentSeriesRing(C:Precision:=Precision);
  end if;
  deriv := map<LS->LS| x:-> &+([LS|i*Coefficient(x,i)*LS.1^i: 
      i in Exponents(x)]) 
      + (b cmpeq Infinity() select 0 else O(LS.1^AbsolutePrecision(x))
      where b := RelativePrecision(x))>;   
  F := DifferentialRing(LS,deriv,C);
  F`IsDifferentialLSR := true;
  F`BaseRingDiffLSRExtension := C;
  return F;
end intrinsic;

// also write a code for finite precision LSR(K,p).


intrinsic AssignNames(~F::RngDiff, S::[MonStgElt])
  {}
  // Written by Nils Bruin.
  UF:=UnderlyingRing(F);
  if assigned F`URGenerators then
      // we split S in generators on "UF" and "BRUF", the BaseRing of U.
    BRUF:=BaseRing(UF);
    UFNames:=[S[i]: i in [1..#S] | i notin F`URGenerators];
    BRUFNames:=[S[i]: i in [1..#S] | i in F`URGenerators];
    AssignNames(~UF,UFNames);
    AssignNames(~BRUF,BRUFNames);
  else
    AssignNames(~UF, S);
  end if;
end intrinsic


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Membership and Equality                     //
//                                                                //
////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////
//                                                                //
//                      Predicates and Booleans                   //
//                                                                //
////////////////////////////////////////////////////////////////////
 
 
intrinsic IsAlgebraicDifferentialField(L::Rng) -> BoolElt
  {}
  if not(ISA(Type(L), RngDiff)) then
    return false;
  end if;
  if not(assigned L`IsAlgebraicFunctionField) then
    return false;
  else
    return L`IsAlgebraicFunctionField;
  end if;
end intrinsic;

intrinsic IsDifferentialField(L::Rng) -> BoolElt
  {}
  if not(ISA(Type(L), RngDiff)) then
    return false;
  end if;
  if not(assigned L`IsField) then
    return false;
  else
    return L`IsField;
  end if;
end intrinsic;

intrinsic IsDifferentialRing(L::Rng) -> BoolElt
  {}
  return ISA(Type(L), RngDiff);
end intrinsic;

intrinsic IsDifferentialSeriesRing(L::Rng) -> BoolElt
  {}
  if not (ISA(Type(L), RngDiff)) then
    return false;
  elif not ISA(Type(UnderlyingRing(L)), RngSer) then 
    return false;
  else
    return true;
  end if;
end intrinsic;

intrinsic IsDifferentialLaurentSeriesRing(L::Rng) -> BoolElt
  {}
  if not (ISA(Type(L), RngDiff)) then
    return false;
  elif not (assigned L`IsDifferentialLSR) then
    return false;
  else
    return L`IsDifferentialLSR;
  end if;
end intrinsic;

intrinsic IsDifferentialRingElement(x::RngElt) -> BoolElt
 {}
 return ISA(Type(x), RngDiffElt);
end intrinsic;

intrinsic IsOrderTerm(x::RngDiffElt) -> BoolElt
  {True iff x is an order term in a differential series ring.}
  F:=Parent(x);
  require IsDifferentialSeriesRing(F):
    "The element is not a differential series.";
  U := UnderlyingRing(F);
  return IsOrderTerm(U!x);
end intrinsic;

// ok
// Used in SlopeValuation and other factorisation codes.
// Can be done better for an algebraic differential ring using differentials.
intrinsic HasProjectiveDerivation(F::RngDiff) -> BoolElt
  {True iff F is a differential ring with derivation weakly of the form t*d/dt.}
  // input: The differential ring F.
  // output: true iff F (weakly) has derivation t*d/dt.
  isADF := IsAlgebraicDifferentialField(F);
  isDLSR := IsDifferentialLaurentSeriesRing(F);
  require isADF or isDLSR:
     "The differential ring must be an algebraic differential field or a",
     "differential Laurent series ring.";
  require Characteristic(F) eq 0:
    "Routine only implemented for a characteristic 0 field.";
  derivtF:=(Derivation(F))(F.1);  
  scalefunction:=F!((1/F.1)*(derivtF));
  return IsWeaklyEqual(scalefunction-(F!1), F!0);
end intrinsic;

// ok
intrinsic HasZeroDerivation(F::RngDiff) -> BoolElt
  {True iff the algebraic differential field or differential series
   ring F has (weak) zero derivation.}
  // input: A diff Laurent series ring F=k((t)), or a algebraic 
  //        differential ring k(z), where k is the differential
  //        constant field.
  // output: true iff F has zero derivation (+ order term) on t. 
  require IsAlgebraicDifferentialField(F) or IsDifferentialLaurentSeriesRing(F):
    "The input must be an algebraic differential field or",
    "a differential Laurent Series ring.";
  return IsWeaklyZero((Derivation(F))(F.1));
end intrinsic;

// IsWeaklyZero and IsWeaklyEqual is implemented in C.


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute Access Functions                  //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Differential(L::RngDiff) -> DiffFunElt
  {The differential assigned to L.}
  require IsAlgebraicDifferentialField(L):
    "The given argument is not an algebraic differential field.";
  return L`Differential;
end intrinsic;

intrinsic BaseRing(L::RngDiff) -> Rng
  {}
  require assigned L`BaseRing:
    "The ring does not have the proper attribute assigned.";
  return L`BaseRing;
end intrinsic;

intrinsic BaseField(L::RngDiff) -> Rng
  {}
  require assigned L`BaseRing:
    "The ring does not have the proper attribute assigned.";
  basering:=BaseRing(L);
  require IsField(basering):
    "The ring has a base ring that is not a field.";
  return basering;  
end intrinsic;

intrinsic ConstantRing(L::RngDiff) -> Rng
  {}
  require assigned L`ConstantRing or IsDifferentialLaurentSeriesRing(L):
    "The ring does not have the proper attribute assigned."; 
  if assigned L`ConstantRing then
    return L`ConstantRing;
  else
    return BaseRing(L);
  end if;
end intrinsic;

intrinsic ConstantField(L::RngDiff) -> Fld
  {}
  constants:=ConstantRing(L);
  require IsField(constants):
    "The ring has a constant ring that is not a field.";
  return constants;
end intrinsic;

intrinsic UnderlyingRing(L::RngDiff) -> Rng  
  {The underlying ring of L.}
  require assigned L`UnderlyingRing:
    "The ring does not have the proper attribute assigned.";
  return L`UnderlyingRing;
end intrinsic;

intrinsic UnderlyingField(L::RngDiff) -> Fld  
  {The underlying field of L.}
  underlyingring:=UnderlyingRing(L);
  require IsField(underlyingring):
    "The ring has a underlying ring that is not a field.";
  return underlyingring;
end intrinsic;

intrinsic Derivation(L::RngDiff) -> Map
{The derivation of L.}
    if assigned L`Derivation then
      deriv:=L`Derivation;
      domain:=Domain(deriv);
      codomain:=Codomain(deriv);
      derivation:= Coercion(L,domain)*deriv*Coercion(codomain,L);
      return map<L->L| x:-> derivation(x)>;
    end if;
    assert IsAlgebraicDifferentialField(L);
    return map<L -> L | 
                 e :-> L!(Differential(e)/L`Differential)>;
end intrinsic;

intrinsic Derivative(x::RngDiffElt) -> RngDiffElt
{The derivation of the parent of x, applied to x.}
    L:=Parent(x);
    return Derivation(L)(x);
end intrinsic;

procedure set_generators(F)
    assert not assigned F`Generators;
    U:=UnderlyingRing(F);
    F`Generators:=[(U.i): i in [1..MyNgens(U)]];
end procedure;

intrinsic Generators(F::RngDiff) -> SeqEnum
  {The list of generators of F. If there is no list assigned to F, one 
   is constructed by default from the UnderlyingRing(F).}
  if not(assigned F`Generators) then
    vprint DiffRng: "Assigning generators by default routine.";
    set_generators(F);
  end if;
  return ChangeUniverse(F`Generators, F);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                   Coercions                                    //
//                                                                // 
////////////////////////////////////////////////////////////////////


intrinsic Ngens(F::RngDiff) -> RngIntElt
  {}
  if not(assigned F`Generators) then
    set_generators(F);
  end if;
  return #(F`Generators);
end intrinsic;

intrinsic '.'(F::RngDiff,i::RngIntElt) -> RngDiffElt
  {}
  requirerange i, 1, Ngens(F);
  if not(assigned F`Generators) then
    set_generators(F);
  end if;
  return F!(F`Generators)[i];
end intrinsic;

intrinsic Name(F::RngDiff, i::RngIntElt) -> RngDiffElt
  {}
  requirerange i, 1, Ngens(F);
  return F.i;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Arithmetic and Functionality                //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic '^' (x::RngDiffElt,m::RngIntElt) -> RngDiffElt
   {}
   return Parent(x)!((UnderlyingRing(Parent(x))!x)^m);
end intrinsic;

intrinsic 'div' (x::RngDiffElt,y::RngDiffElt) -> RngDiffElt
   {}
   bl, answer:= IsDivisibleBy(x,y);
   require bl:  
     "Division is not exact";   
   return answer;
end intrinsic;

intrinsic '/' (x::RngDiffElt,y::RngDiffElt) -> RngDiffElt
   {}
   require IsField(Parent(x)): "only implemented for differential fields";
   require IsField(Parent(y)): "only implemented for differential fields";
   require not(IsZero(y)): "Division by zero.";
   bl,yinx:=IsCoercible(Parent(x),y);
   if bl then
     y:=yinx;
   else
     bl,xiny:=IsCoercible(Parent(y),x);
     require bl: "x and y must live in compatible differential fields";
     x:=xiny;
   end if;
   return x div y;
end intrinsic;


///////////////////////////////////////////////////////////////////
//                                                                //
//                       Structure Operations                     //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic ChangeDerivation(F::RngDiff,f::RngElt) 
    -> RngDiff, Map
  {Returns a differential field field isomorphic to F,
   but whose derivation is f*Derivation(F), with f not (weakly equal to) 0.
   The map is the isomorphism of F to the new field}
  bl, f :=IsCoercible(F,f);
  require bl eq true:
    "The second argument is not coercible in the differential ring.";
    // require IsIdentical(F,Parent(f)): 
    //   "The second argument must be an element of the differential field.";
  // require f ne F!0: 
  require not IsWeaklyZero(f):
    "The second argument must not be (weakly equal to) 0."; 
  K:=UnderlyingRing(F); 
  if IsAlgebraicDifferentialField(F) then
    wK:= Differential(F);
    wK:=1/(K!f)*wK;
      // Coercion in K, as the differential in a differential of K.
    Fprime:=DifferentialField(K,wK);
  else 
    derivationK:=Derivation(F);
    newderivation:=map<K->K | g:->(f)*(derivationK(g))>;
    Fprime:= DifferentialRing(K,newderivation,ConstantRing(F));
    if IsDifferentialLaurentSeriesRing(F) then
      Fprime`IsDifferentialLSR := true;
      Fprime`BaseRingDiffLSRExtension := F`BaseRingDiffLSRExtension;
    else 
      Fprime`IsDifferentialLSR := false;
    end if;  
    if assigned F`BaseField then
      Fprime`BaseField := F`BaseField;
    elif assigned F`BaseRing then
      Fprime`BaseRing := F`BaseRing;
    end if;
  end if;   
  mpFtoFprime:= Coercion(F,K)*Coercion(K,Fprime);
  mpFtoFprime:=map<F->Fprime|x:->mpFtoFprime(x), y:-> y@@mpFtoFprime>;
  return Fprime, mpFtoFprime;
end intrinsic;

intrinsic ChangeDifferential(F::RngDiff, df::DiffFunElt) -> RngDiff, Map
  {Returns the algebraic differential field, whose underlying ring is the one 
   of F, but with differential df.
   The map returned is the bijective map of F into the new algebraic 
   differential field.}
  require IsAlgebraicDifferentialField(F):
    "The given differential field must be an algebraic differential field.";
  require df in DifferentialSpace(F):
    "The differential is not a differential of the first argument.";
  require not df cmpeq Differential(F!0):
    "The differential must be non-zero.";
  f := Differential(F)/df;
    // differentials of F may be differentials of its underlying ring.
  assert (f in F) or (f in UnderlyingRing(F));
  return ChangeDerivation(F,F!f);  
end intrinsic;

// ok
intrinsic ChangePrecision(F::RngDiff,p::RngElt) -> RngDiff, Map
  {Returns a differential series ring isomorphic to F with relative precision p.
   The map returned is the induced map of F to the new field.}
  // No compensation for the order term, if present, is made. 
  require IsDifferentialLaurentSeriesRing(F):
    "The given ring must be a differential Laurent series ring.";  
  if not p eq Infinity() then 
    bl, p:=IsCoercible(Integers(),p);
    require bl:
      "The second argument is not coercible in the ring of integers.";
  end if;    
  require p gt 0:
    "The precision must be positive or infinite.";    
  K:=UnderlyingRing(F); 
  derivationK:=Derivation(F);
  Kprime:=ChangePrecision(K,p);
  newderivation:=map<Kprime->Kprime | g:-> Kprime!(K!derivationK(F!(K!g)))>;
  Fprime:=DifferentialRing(Kprime,newderivation,ConstantRing(F));
  Fprime`IsDifferentialLSR:=true;
  Fprime`BaseRingDiffLSRExtension := F`BaseRingDiffLSRExtension;
  if assigned F`BaseField then
    Fprime`BaseField := F`BaseField;
  elif assigned F`BaseRing then
    Fprime`BaseRing := F`BaseRing;
  end if;
  mpFtoFprime:=Coercion(F,K)*Coercion(K,Kprime)*Coercion(Kprime,Fprime);
  mpFtoFprime:=map<F->Fprime|x:->mpFtoFprime(x), y:-> y@@mpFtoFprime>;
  return Fprime, mpFtoFprime;
end intrinsic;

function DerivInConstFieldExtOfSeriesRing(F,UFext,x)
  // Input: A differential Laurent series ring F=C((t)), with constant ring
  //        C and underlying ring UF. 
  //        An algebraic extension UFext of UF, containing x.
  // Output: The derivation induced in UFext.
  assert IsDifferentialLaurentSeriesRing(F);
  if x eq  UFext!0 then
    return x;
  end if;  
  valx:=Valuation(x);
  eltseqx:=Eltseq(x);
  precisionx:=AbsolutePrecision(x);
  valdergen:=Valuation(Derivation(F)(F.1));
    // Compute the order term in the derivation of x.
  if precisionx cmpeq Infinity() then
    derivx:=UFext!0;
  else 
    derivx := ChangePrecision(UFext!0, valdergen+precisionx-1);
  end if;
   // Compute the derivation of the known part and add this to the order term.
  if #eltseqx eq 0 then
    return derivx;
  else 
    return derivx + &+([eltseqx[i]*UFext!Derivation(F)((F.1)^(valx+i-1))
                         :i in [1..#eltseqx]]);
  end if;
end function;

intrinsic ConstantFieldExtension(F::RngDiff, Cext::Fld) -> RngDiff, Map
  {Returns the field having the same structure as F, but
   whose constant field is the extension Cext of the constant field of F.}
     // Maybe do more if Cext eq C or Cmpeq C. 
     // Give inverse map for instance.
     // This is not yet implemented in "ConstantFieldExtension(FldFun)".
     // Need to implement Finite Fields.
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsAlgebraicDifferentialField(F) or 
          IsDifferentialLaurentSeriesRing(F):
    "The given argument is not an algebraic differential field nor a ",
    "differential Laurent series ring.";     
  K:=UnderlyingRing(F);
  C:=ConstantField(F);
  assert IsField(K); 
  require (not ISA(Type(C), RngSer)) and (not IsDifferentialSeriesRing(C)):
    "The constant ring must not be a series ring.";
  require ExistsCoveringStructure(C, Cext) : 
		"Argument 2 must extend the constant field of argument 1";
  require CoveringStructure(C, Cext) eq Cext : 
		"Argument 2 must extend the constant field of argument 1";   
  if IsAlgebraicDifferentialField(F) then		
    assert C eq ConstantField(K);		
    KK, phi:=ConstantFieldExtension(K,Cext);  
      // the one for FldFun. 
      // So phi goes from K to KK.
      // Find principal divisor. So find f in F with Df <>0.
      // My guess is using Separating element.  
    f:=SeparatingElement(F);   
    df:=Differential(f);
    assert not df eq Differential(F!0);
    w:=Differential(F); 
      // So w is the differential of F, df is another, principal one. 
      // Then w/df is an element of F.
      // Differential(phi(f@@nemb)) is the image of the differential df over KK.
      // In total wprime:=phi((w/df)@@nemb)*Differential(phi(f@@nemb)) 
      // gives the natural differential that is the image of w over FF.
    wKK:=phi((w/df))*Differential(phi(f));
    FF:= DifferentialField(KK,wKK); 
    mpFtoFF:= Coercion(F,K)*phi*Coercion(KK,FF);
    mpFtoFF:= map<F->FF| a:-> mpFtoFF(a), b:-> b@@mpFtoFF>;
    return FF, mpFtoFF;
  else
    assert IsDifferentialLaurentSeriesRing(F);
    assert C eq BaseRing(K);
    KK, mpKtoKK:=ChangeRing(K,Cext);
      // KK has the same precision as K.
    assert Cext eq CoefficientRing(KK);
    deriv:=map<KK->KK| x:->DerivInConstFieldExtOfSeriesRing(F,KK,x)>;
    FF := DifferentialRing(KK, deriv, Cext);
    FF`IsDifferentialLSR := true;
    FF`BaseRingDiffLSRExtension := F`BaseRingDiffLSRExtension;
    // FF`BaseRingDiffLSRExtension := Cext;
      // Embedding of F into FF.
    emb:=Coercion(F,K)*mpKtoKK*Coercion(KK,FF);
    mp:= map<F-> FF| x:-> emb(x), y:-> y@@emb>; 
      // Need check that y can be mapped back?
    return FF, mp;
  end if;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                          Element Operations                    //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Differential(x::RngDiffElt) -> FldFunElt
  {Returns the differential of an element in the algebraic differential field F,
   as a differential in the differential space of the underlying ring of F.}
     // As there is not a differential space for algebraic differential
     // fields F yet, we use the underlying ring of such F.
  F := Parent(x);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator ring is not defined over",
    "an algebraic differential field.";
  K := UnderlyingRing(F);
  assert ISA(Type(K), FldFun);
  return Differential(K!x);
end intrinsic;

intrinsic Eltseq(a::RngDiffElt) -> SeqEnum
  {Returns the coefficients over K, K must occur as a coefficient field.}
  F:=Parent(a);
  require IsAlgebraicDifferentialField(F) or IsDifferentialLaurentSeriesRing(F):
    "The argument is not an algebraic differential field element,",
    "nor a differential Laurent series.";
  UF:= UnderlyingRing(F);
  if IsAlgebraicDifferentialField(F) then
    bl, K := HasAttribute(F, "BaseField");
    require bl:
      "No basefield found.";
    seq:=Eltseq(UF!a);
    U := Universe(seq);
    require U eq UnderlyingRing(K):
      "No coercion in basefield possible.";
    return ChangeUniverse(seq, K);
  else 
    assert IsDifferentialLaurentSeriesRing(F);
    C := ConstantRing(F);
    assert BaseRing(UF) eq C;
    seq := Eltseq(UF!a);
    assert Universe(seq) eq C;
    return seq;
  end if;
end intrinsic; 

intrinsic MinimalPolynomial(a::RngDiffElt) -> RngUPolElt
  {The minimal polynomial of the field element a over the coefficient field.}
  F:=Parent(a);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";
  bl, K := HasAttribute(F, "BaseField");
  require bl:
      "No basefield found.";
  f:=MinimalPolynomial(UnderlyingRing(F)!a);
  P:=Parent(f);
  U:=UnderlyingRing(K);
  assert U eq BaseRing(P);
  _, mp :=ChangeRing(P,K);
  return mp(f);
end intrinsic;

intrinsic O(x::RngDiffElt) -> RngDiffElt
  {Returns O(x).}
  F:=Parent(x);
  require IsDifferentialSeriesRing(F):
    "The element is not a differential series.";
  return F!O(UnderlyingRing(F)!x);
end intrinsic;

intrinsic Truncate(x::RngDiffElt) -> RngDiffElt 
  {The known part of the differential series x.}
  F:=Parent(x);
  require IsDifferentialSeriesRing(F):
    "The element must be a differential series."; 
  return F!Truncate(UnderlyingRing(F)!x);
end intrinsic;

intrinsic Exponents(x::RngDiffElt) -> SeqEnum
  {The interval from the valuation of x to (including) the degree of x.} 
  F:=Parent(x);
  require IsDifferentialSeriesRing(F):
    "The element is not a differential series.";
  S := UnderlyingRing(F);
  require ISA(Type(S),RngSerPow) or ISA(Type(S),RngSerLaur):
    "The argument must be a differential power series or Laurent series.";  
  return Exponents(S!x);
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                    Matrices related to Diff. Rings             //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic WronskianMatrix(S::[RngDiffElt]) -> AlgMatElt
  {The Wronskian matrix of S=[y1,y2,...yn] over R.}
  R:=Universe(S);
  deriv:=Derivation(R);
  n:=#S;
  wronskianmat:=Matrix(R,1,n,S);
  row:=S;
  for i := 1 to n-1 do
    prevrow:=row;
    row:=[deriv(yi): yi in prevrow]; 
    wronskianmat:=
      VerticalJoin(wronskianmat,Matrix(R,1,n,row));
  end for;
  return wronskianmat;  
end intrinsic;

intrinsic WronskianDeterminant(S::[RngDiffElt]) -> RngDiffElt, AlgMatElt
  {The determinant of the Wronskian matrix of S=[y1,y2,...yn] over R and
   the Wronskian matrix itself.}
  R:=Universe(S);
  wronskianmat:=WronskianMatrix(S);
  return Determinant(wronskianmat), wronskianmat;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                  Field of Differential Constants               //
//    (the largest subfield on which the derivation is trivial)   //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic ExactConstantField(F::RngDiff) -> Fld, Map
  {The field of constants of the algebraic differential field F,
   together with the inclusion map to F.}
  // We make use of the fact that a differential acts trivially on
  // all indeterminates in all underlying fields of the last
  // transcendental extension in UnderlyingField(F)/C and the fact
  // that the differential of a FldDiff is non-trivial.
  require IsAlgebraicDifferentialField(F):
    "The given argument is not an algebraic differential field.";
    K:=UnderlyingRing(F);
    assert IsField(K);
    ECF, inclK := ExactConstantField(K);
    inclF:=inclK*Coercion(K,F);
    inclF:=map<ECF->F | x:-> inclF(x), y:->y@@inclF>;
    return ECF, inclF;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                 Algebraic Differential Fields                  //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic SeparatingElement(F::RngDiff) -> RngDiffElt
  {Returns the separating element of the algebraic differential field F.}
    // This is is the coerced SeparatingElement of the underlying field of F.
  require IsAlgebraicDifferentialField(F):
    "The given differential operator ring is not defined over",
    "an algebraic differential field.";
  K := UnderlyingRing(F);
  assert ISA(Type(K), FldFun);
  t := SeparatingElement(K);
  assert Parent(t) eq K;
  return F!t;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//               Algebraic Differential Extensions                //
//                                                                //
////////////////////////////////////////////////////////////////////


// In C the routine ``ext<|>'' for differential rings has been implemented.
// For now in symbols it is:
// ext<F::RngDiff|f::RngUPolElt> -> RngDiff, Map
// It returns:
//   {The algebraic differential field extension of F induced by f, together
//   with the inclusion map of F to the new field.}
// Two conditions must hold for the arguments.
// 1. F must be an AlgebraicDifferentialField.
// 2. The BaseRing of f must be F.


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Differential Ring Extensions                //
//                                                                //
////////////////////////////////////////////////////////////////////

// This section is mostly developped by Nils Bruin.

function ExtDerivToRngPol(P,deriv,L)
  //Written by Nils Bruin.
  //takes a polynomial ring (affine algebra) P with coefficient ring 
  // (PreimageRing that is the UnderlyingRing of) 
  // the differential ring (R with deriv: R->R)
  // together with a list L of length r=Rank(P) that specifies the images
  // of P.1,...,P.r under the extended deriv we create.
  // The return value is the extension of deriv to P, with the 
  // pre-described images.
  // Note that L need not take values in P. It could also be
  // FieldOfFractions(P) for instance.
  r:=Rank(P);
  function newderiv(f)
    res:=Universe(L)!0;
    for t in Terms(f) do
      c:=LeadingCoefficient(t);
      v:=Exponents(t);
      res:=res + (P!deriv(c))* LeadingMonomial(t);
      for j in [1..r] do
        if v[j] ne 0 then
          res := res +c*L[j]*v[j]*&*[P.i^( i eq j select v[j]-1 else v[i]):
                                                             i in [1..r]];
        end if;
      end for;
    end for;
    return res;
  end function;
  return map<P->Universe(L)| f:->newderiv(f)>;
end function;

intrinsic DifferentialRingExtension(L::[RngMPolElt]) -> RngDiff
  {The differential ring extension A = Universe(L) with deriv(A.i)=A!L[i],
   of the differential BaseRing of Universe(L).}
  // Based on code of Nils Bruin.
  P:=Universe(L);
  R:=BaseRing(P);
  r:=Rank(P);
  require IsDifferentialRing(R):
    "The coefficient ring of the given ring must be a differential ring.";
  require #L eq r:
    "The length of the sequence must be the rank of the given ring.";  
  UR:=UnderlyingRing(R);
  derivR:=Derivation(R);
  derivUR := Coercion(UR,R)*derivR*Coercion(R,UR);
  UP:=ChangeRing(P,UR);
  UL:=[UP| v: v in L];
  derivUP:=ExtDerivToRngPol(UP,derivUR,UL);
  ER :=DifferentialRing(UP,derivUP,ConstantRing(R));
  ER`BaseRing:=R;
  assert UnderlyingRing(ER) eq UP;
  ER`Generators:=[(P.i): i in [1..Rank(P)]];
  return ER;
end intrinsic;


///////////////////////////////////////////////////////////////////
//                                                                //
//                 Differential Field Extensions                  //
//                                                                //
////////////////////////////////////////////////////////////////////

// This section is mostly developped by Nils Bruin.

function ExtDerivToFoF(deriv)
  // By Nils Bruin.
  // Extends the map deriv of a ring P to its field of fractions.
  // This does not apply for rings of type RngMPolRes or RngDiff.
  P:=Domain(deriv);
  L:=FieldOfFractions(P);
  return map<L->L| f:->((deriv(num)*den-num*deriv(den))/den^2
                   where num:=Numerator(f)
                   where den:=Denominator(f))>;
end function;

intrinsic DifferentialFieldExtension(L::[RngMPolElt]) -> RngDiff
  {The differential field extension A=Q(Universe(L)) with deriv(A.i)=A!L[i],
   of the differential BaseRing of Universe(L)}
  // Based on code of Nils Bruin.
  P:=Universe(L);
  R:=BaseRing(P);
  r:=Rank(P);
  require IsDifferentialField(R):
    "The basering of the given ring must be a differential field.";
  require #L eq r:
    "The length of the sequence must be the rank of the given ring.";
  UR:=UnderlyingRing(R);  
  require not(ISA(Type(UR),RngMPolRes)) and not(ISA(Type(UR),RngDiff)):
    "Routine not implemented for BaseRing with this underlying type.";  
  derivR:=Derivation(R); 
  derivUR := Coercion(UR,R)*derivR*Coercion(R,UR);
  UP:=ChangeRing(P,UR);
  UL:=[UP| v: v in L];
  derivUP:=ExtDerivToRngPol(UP,derivUR,UL);
  derivFOFP:=ExtDerivToFoF(derivUP);
  FOFP:=Domain(derivFOFP);
    // This is indeed the field of ractions of P.
  assert not ISA(Type(FOFP),RngDiff);
  assert IsField(ConstantRing(R));
  ER := DifferentialRing(FOFP,derivFOFP,ConstantRing(R));
  ER`BaseField:=R;
  ER`Generators:=[FOFP|(P.i): i in [1..Rank(P)]];
  return ER;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                     Exponential extensions                     //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic ExponentialFieldExtension(F::RngDiff,f::RngDiffElt) -> RngDiff
  {Creates a differential extension F(E) of the field F, where E
   satisfies Derivation(E)=f*E.}
  require IsDifferentialField(F):
    "The first argument must be a differential field.";
  require Parent(f) eq F:
    "The second argument must be an element of the first.";
  P:=PolynomialRing(F,1);
  lst:=[P|f*(P.1)];
  return DifferentialFieldExtension(lst);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                     Logarithmic extensions                     //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic LogarithmicFieldExtension(F::RngDiff,f::RngDiffElt) -> RngDiff
  {Creates a differential extension F(L) of the field F, where L
   satisfies Derivation(L)=f.}
  require IsDifferentialField(F):
    "The first argument must be a differential field.";
  require Parent(f) eq F:
    "The second argument must be an element of the first.";
  P:=PolynomialRing(F,1);
  lst:=[P|f];
  return DifferentialFieldExtension(lst);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                        Quotient Rings                          //
//                                                                //
////////////////////////////////////////////////////////////////////

// This section is jointly developped with Nils Bruin.

// We consider a differential ideal as an ideal of its underlying ring
// until we have an own type, or something like ideal<|> for
// RngDiff's installed.
intrinsic IsDifferentialIdeal(R::RngDiff,I::RngMPol) -> BoolElt
  {True iff I can be coerced as a differential ideal of R.}
  P:=Generic(I);
  if not(P cmpeq UnderlyingRing(R)) then
    vprint DiffRng:"Ideal is not defined over the underlying ring.";
    return false;
  end if;
  for gen in Generators(I) do
    if not(P!(Derivation(R)(P!gen)) in I) then
      vprint DiffRng:"Ideal is not closed under derivation";
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic DifferentialIdeal(L::[RngDiffElt]) -> RngMPol
  {Returns the differential ideal I generated by L as an ideal 
   of the underlying ring of Universe(L).}
    // A differential ideal I of a RngDiff R is an ideal such that deriv(I)
    // is contained in I.
  R:=Universe(L); 
  U:=UnderlyingRing(R);
  require ISA(Type(U),RngMPol):
    "The underlying field must be of type RngMPol.";
  LU:=ChangeUniverse(L,U);
  I:= ideal<U|LU>; 
    // if the derivative of a term in I is already in the ideal, 
    // then we do not have to consider this term anymore.
    // Otherwise we add the derivative to the generators of the ideal
    // and have to check again if its derivative is in the ideal, etc.
    // We make a set J that contain all terms that have to be checked.
  checked:={U|};
  repeat
    J:=Generators(I);
    closed:=true;
    for term in J do
      if term notin checked then
        deriv:=U!(Derivation(R)(term)); 
        if deriv notin I then
          I:=I+ideal<U|deriv>;
          closed:=false;
        end if;
        Include(~checked,term);
      end if;
    end for;     
  until closed;
  return I;
end intrinsic;

intrinsic QuotientRing(R::RngDiff, I::RngMPol) -> RngDiff, Map
  {The differential quotient ring QR=R/I with deriv(QR.i)=QR!(deriv(R[i])), 
   together with the induced quotient map R -> QR.}
  // Based on code of Nils Bruin.
  P:=Generic(I);
  require P cmpeq UnderlyingRing(R):
    "The ideal must be an ideal of the underlying ring of the first argument.";
  require IsDifferentialIdeal(R,I):
    "The given argument is not a differential ideal.";
  r:=Ngens(R);
  QP, mapPtoQP:=quo<P|I>;  
  derivR:=Derivation(R);
  imagesR:=[derivR(g): g in Generators(R)];
  imagesQP:=ChangeUniverse(ChangeUniverse(imagesR,P),QP);
  derivQP:=ExtDerivToRngPol(QP,derivR,imagesQP);
  QR:=DifferentialRing(QP,derivQP,ConstantRing(R));
    // Ideal situation would be that ConstantRing(QR) 
    // is the image of ConstantRing(R) in R/I, instead of ConstantRing(R)
    // itself.
  if assigned R`BaseRing then
    QR`BaseRing:=BaseRing(R);
  end if;
  QR`Generators:=Generators(R);
  mapRtoQR:=Coercion(R,P)*mapPtoQP*Coercion(QP,QR);
  mapRtoQR:=map<R->QR| x:->mapRtoQR(x), y:->y@@mapRtoQR>; 
  return QR, mapRtoQR;  
end intrinsic; 


////////////////////////////////////////////////////////////////////
//                                                                //
//                  Rings and Fields of Fractions                 //
//                                                                //
////////////////////////////////////////////////////////////////////


// This section is mostly developped by Nils Bruin.

function IsRngMpolResRngOfFrac(A)
  // Returns true if the RngMPolRes A is its Ring Of Fractions,
  // otherwise false.
  I:=DivisorIdeal(A);
  R:=Generic(I);
  d,vr:=Dimension(I);
  if d eq 0 then
    return true;
  else
    return false;
  end if;
end function; 

function ALEXA_RingOfFractions(A)
  // Input: A is an RngMPolRes.
  // Output: The ring A[r^(-1): r in A is invertible], together with the 
  // inclusion map.}
  // Written by Nils Bruin.
  assert ISA(Type(A), RngMPolRes);
  if IsRngMpolResRngOfFrac(A) then
    return A, map<A->A| a:->a, a:->a>;
  end if;
  I:=DivisorIdeal(A);
  R:=Generic(I);
  d,vr:=Dimension(I);
  E,toE:=Extension(I,vr);
  Q,toQ:=quo<Generic(E)|E>;
  varvec:=[A.i:i in vr];
  AtoQ:=Coercion(A,R)*toE*toQ;
    // So Q is now the ring of quotients of A and AtoQ embeds A into Q;
    // The inverse of AtoQ is all wrong, though.
  inv:=function(q)
    C:=Coefficients(q);
    L:=Monomials(q);
    dn:=[Denominator(c): c in C];
    error if exists{d:d in dn| not(d eq 1)},
         "element is not recognisably integral";
    return &+[A|Evaluate(Numerator(C[i]),varvec)*(L[i]@@AtoQ): i in [1..#L]];
  end function;
  AtoQ:=map<A->Q|a:->AtoQ(a), q:->inv(q)>;
  return Q,AtoQ;
end function;

function MyNumDen(q)
  // Written by Nils Bruin
  // q is a RngMPolResElt with base field something having numerator and
  // denominator.
  C:=Coefficients(q);
  L:=Monomials(q);
  den:=#C eq 0 select 1 else LCM([Denominator(c):c in C]);
  num:=[Numerator(c)*(den div Denominator(c)):c in C];
  return &+[Parent(q)|num[i]*L[i]: i in [1..#C]],Parent(q)!den;
end function;

function ExtDerivRngMPolResToRoF(deriv)
  // Written by Nils Bruin.
  // Extends the derivation of a RngMPolRes to its ring of fractions.
  P:=Domain(deriv);
// Once general RingOfFractions is ready to go
// This should once again call RingOfFractions returning a RngFrac
// mpPtoL will be the coercion map from P into L
  L, mpPtoL:=ALEXA_RingOfFractions(P);
  return map<L->L| 
    f:->((mpPtoL(deriv(num@@mpPtoL))*den-num*mpPtoL(deriv(den@@mpPtoL)))/den^2
                   where num,den:=MyNumDen(f))>, mpPtoL;
end function;

// Have a look again at the ConstantRing, can this be optimalized?
function RingOfFracForURRngMPolRes(R) 
  // Based on code of Nils Bruin.
  // Input: R must be a RngDiff, whose UnderlyingRing UR is
  //        of type RngMPolRes.
  // Output: The differential ring R[r^(-1): r in R is invertible] of 
  //         fractions of R, together with the inclusion map.
  UR:=UnderlyingRing(R);
  if IsRngMpolResRngOfFrac(UR) then 
    return R, map<R->R| a:->a, a:->a>;
  end if;  
  C:=ConstantRing(R);
  assert IsField(C);
  I:=DivisorIdeal(R);
  bl:=IsField(CoefficientRing(I));
  if bl then
    derivR:=Derivation(R);
    assert (Domain(derivR) eq R) and (Codomain(derivR) eq R);
    derivUR:=Coercion(UR,R)*derivR*Coercion(R,UR);
    derivQUR, mapURtoQUR := ExtDerivRngMPolResToRoF(derivUR);
    QUR:=Domain(derivQUR);
    QR := DifferentialRing(QUR,derivQUR,C);
    if assigned R`BaseRing then
      QR`BaseRing:=BaseRing(R);
    end if;
    QR`Generators:=[QUR|mapURtoQUR(UR!gen): gen in Generators(R)];
    mapRtoQR:=Coercion(R,UR)*mapURtoQUR*Coercion(QUR,QR);
    mapRtoQR:=map<R->QR|x:->mapRtoQR(x),y:->y@@mapRtoQR>;
    return QR, mapRtoQR;
  else
    return false, "Not implemented yet for this kind of ring.";
  end if;
end function;

// Look at constant field, can this be optimalized?
intrinsic FieldOfFractions(R::RngDiff) ->  RngDiff, Map
  {The differential field of fractions of R, together
   with the inclusion map of R in the field.}
  // Based on code of Nils Bruin.
  require IsDomain(R):
    "The given ring must be a domain.";
  if IsField(R) then
    return R, map<R->R| a:->a, a:->a>;
  end if;  
  C:=ConstantRing(R);
  require IsField(C):
    "The differential ring must have a field as its constant ring";
  UR:=UnderlyingRing(R);
  if ISA(Type(UR),RngMPolRes) then
    F,mp:=RingOfFracForURRngMPolRes(R);
    assert IsField(F);
    I:=DivisorIdeal(UR);
    _, F`URGenerators :=Dimension(I);
    return F,mp;
  else 
    derivR:=Derivation(R);
    assert (Domain(derivR) eq R) and (Codomain(derivR) eq R);
    derivUR:=Coercion(UR,R)*derivR*Coercion(R,UR);  
    derivFOF:=ExtDerivToFoF(derivUR);
    FOFUR:=Domain(derivFOF);
      // Is the field of fractions of UR by construction.
    F:=DifferentialRing(FOFUR,derivFOF,C);
    if assigned R`BaseRing then
      F`BaseRing:=BaseRing(R);
    end if;
    F`Generators:=[FOFUR|UR!gen: gen in Generators(R)];
    mapFOFURtoF:=Coercion(FOFUR,F);
    mapRtoF:=map<R->F| x :-> mapFOFURtoF(FOFUR!(UR!x)), 
                     y :-> R!(UR!(y@@mapFOFURtoF))>;
    return F, mapRtoF;
  end if;
end intrinsic;


// This is the general one.
// Maybe export this one and not the FieldOfFractions?
intrinsic RingOfFractions(R::RngDiff) ->  RngDiff, Map
  {The differential ring R[r^(-1): r in R is invertible] of fractions of R, 
   together with the inclusion map.}
  // Based on code of Nils Bruin.
  C:=ConstantRing(R);
  require IsField(C):
    "The differential ring must have a field as its constant ring";
  UR:=UnderlyingRing(R);
  if ISA(Type(UR),RngMPolRes) then
    return RingOfFracForURRngMPolRes(R);
  elif IsDomain(R) then
    return FieldOfFractions(R);
  else 
    return false, "Not yet implemented for this type of ring.";
  end if;
end intrinsic;


////////////////////////////////////////////////////////////////////


/**
Further implementation ideas:

Coercion of the constant field and the exactconstantfield in the
  differential field. Same for rings.
Differential Space defined on the RngDiff instead on its underlying ring.
Differential on RngDiff itself instead on its underlying ring.
SeparatingElement on RngDiff itself.
ext<F|f>-symbol on FldDiff's, so not only on algebraic ones.
Subfield/ring coercion of BaseRing.
Function that lifts derivation given by DiffFld with differential.
**/



