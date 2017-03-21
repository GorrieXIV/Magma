freeze;

// also write a code for finite precision LSR(K,p).

import "singularities.m" : completion;


////////////////////////////////////////////////////////////////////
//                                                                //
//                             Precision                          //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic RelativePrecision(F::RngDiff) -> RngElt
   {Returns the relative precision of the underlying series ring of F.}
   require IsDifferentialSeriesRing(F):
     "The underlying ring must be a series ring.";
   return RelativePrecision(UnderlyingRing(F));
end intrinsic;

intrinsic RelativePrecisionOfDerivation(F::RngDiff) -> RngElt
  {Given a differential Laurent series ring F, returns the relative precision 
   of the derivation of F.1.}
   require IsDifferentialSeriesRing(F):
     "The argument is not a differential series ring.";
   return RelativePrecision(Derivation(F)(F.1));
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                              Places                            //
//                                                                //
////////////////////////////////////////////////////////////////////


// Code by Nils Bruin.
function LiftPlace(pl)
  //{Creates a degree 1 place above pl in Places(F), in the smallest field 
  //function field L allowing such a place. The second argument is the embedding of 
  // the function field of pl in L.}
  F := FunctionField(pl);
  assert ISA(Type(F), FldFun);
  assert pl in Places(F);
  if Degree(pl) eq 1 then
    return pl, Coercion(F,F);
  end if;
  t:=UniformizingElement(pl);
  zeroinextension := Evaluate(t,pl); 
  Cpl:=Parent(zeroinextension);
  Fpl, FtoFpl :=ConstantFieldExtension(F,Cpl);
  if Degree(F) ne Infinity() then
    Fr:=F;
    Fplr:=Fpl;
  else
    Fr:=RationalExtensionRepresentation(F);
    Fplr:=RationalExtensionRepresentation(Fpl);
  end if;
  Ofin:=MaximalOrderFinite(Fr);
  Oinf:=MaximalOrderInfinite(Fr);
  Ifin,Iinf:=Ideals(1*Places(Fr)!pl);
  Oplfin:=MaximalOrderFinite(Fplr);
  Oplinf:=MaximalOrderInfinite(Fplr);
  Iplfin:=ideal<Oplfin|[Fplr!(FtoFpl(F!f)):f in Generators(Ifin)]>;
  Iplinf:=ideal<Oplinf|[Fplr!(FtoFpl(F!f)):f in Generators(Iinf)]>;
  Liftedplace:=DivisorGroup(Fpl)!Divisor(Iplfin,Iplinf); 
    // degree1places:={P: P in Support(Liftedplace)| Degree(P) eq 1};
    // bl:=#degree1places ge 1;
  bl:=exists(degree1place){P: P in Support(Liftedplace)| Degree(P) eq 1};
  error if not (bl),
    "Hey, did base change and still don't have a degree 1 place?";
  return degree1place, FtoFpl;
end function;



////////////////////////////////////////////////////////////////////
//                                                                //
//                           Completion                           //
//                                                                //
////////////////////////////////////////////////////////////////////


function OrderTermInDerivation(g,gen,valdergen)
  // Given a series ring element g, whose ring generator is gen, 
  // return the order term in the derivation of g.
  precision:=AbsolutePrecision(g);  
  if ISA(Type(precision),RngIntElt) then
    return O(gen^(valdergen+precision-1));
  else
    assert precision eq Infinity();
    return 0;
  end if;
end function; 


// Partly written by Nils Bruin.
intrinsic Completion(F::RngDiff, pl::PlcFunElt:Precision:=Infinity()) -> RngDiff, Map
  {The completion of the differential field F w.r.t. the place pl.
   The map returned is the embedding of F into the completion.}
    // The underlying ring of the new differential ring is a Laurent Series 
    // Ring. 
  require IsAlgebraicDifferentialField(F):
    "The given differential operator ring is not defined over",
    "an algebraic differential field."; 
  require pl in Places(F):
    "The place is not a place of the first argument.";
  bl, Prec:=IsCoercible(Integers(),Precision);
  require bl or Precision cmpeq Infinity(): 
    "The set precision must be an integer greater than 1, or infinite.";
  if bl then
    Precision := Prec;
  end if;
  require Precision gt 1:
    "The set precision must be a positive integer greater than 1, or infinite.";
    // The series ring always only has one generator.
    // For a degree 1 place completing at the place is invertible.
    // For higher degree places there is no inverse (Feb 2005).
  UF:=UnderlyingRing(F);
  if Degree(pl) eq 1 then 
    UL,mpUFtoUL:=completion(pl,Precision);
    genUL:=UL.1;
    valdergenUL:=Valuation(Derivative(F!(genUL@@mpUFtoUL)), pl); 
    derivUF:=Derivation(F);
    derivUL:=Inverse(mpUFtoUL)*derivUF*mpUFtoUL;    
    derivationUL:=map<UL->UL| 
                  g:-> derivUL(g)+ OrderTermInDerivation(g,genUL,valdergenUL)>;
      // Here we need the corrective order (precision) term.
      // Used is that Valuation(x^j) = Valuation(der(x))+(j-1), where x=genUL.
    C := ExactConstantField(F);
    BUL:=CoefficientRing(UL);
    assert BUL eq C;
    L:=DifferentialRing(UL,derivationUL,C);
    if Type(BUL) eq RngDiff then
      L`BaseRing:=BUL;
    end if;
    L`BaseRingDiffLSRExtension:=C;
    if IsWeaklyZero(Derivation(L)(L.1)) then
      L`IsDifferentialLSR := false;
    else
      L`IsDifferentialLSR := true;
    end if;
    mpFtoL:= Coercion(F,UF)*mpUFtoUL*Coercion(UL,L);
    mpFtoL:=map<F->L|x:->mpFtoL(x), y:-> y@@mpFtoL>;
    return L, mpFtoL;
  else
      // There is no reverse map of mpFtoK in this case (Feb 9 2005).
    degree1place, mpFtoUK:=LiftPlace(pl);
    assert Degree(degree1place) eq 1;
    UK:=Codomain(mpFtoUK);
    assert ISA(Type(UK), FldFun);
    t:=SeparatingElement(F);
    K:=DifferentialField(UK,
         mpFtoUK(Differential(F)/Differential(t))*Differential(mpFtoUK(t)));
    mpFtoK:=mpFtoUK*Coercion(UK,K); 
    Cpl, mpKtoCpl := $$(K,degree1place:Precision:=Precision);
    mpFtoCpl := mpFtoK*mpKtoCpl;
    mpFtoCpl := map<F->Cpl|x:->mpFtoCpl(x), y:-> y@@mpFtoCpl>;
    return Cpl, mpFtoCpl;
  end if;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//    Operators over Differential Laurent Series by completion    //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Completion(R::RngDiffOp, pl::PlcFunElt:Precision:=Infinity()) -> 
                                                           RngDiffOp, Map
  {The operator ring, whose base ring is the completion of the base ring
   of R w.r.t. the place pl.}
  // The underlying ring of the new differential ring is a Laurent Series 
  // Ring. 
  F:=BaseRing(R);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator ring is not defined over",
    "an algebraic differential field.";
  require pl in Places(F):
    "The place is not a place of the first argument.";
  bl, Prec:=IsCoercible(Integers(),Precision);    
  require bl or Precision cmpeq Infinity(): "The precision must be an integer";  
  if bl then
    Precision := Prec;
  end if;
  require Precision gt 1:
    "The set precision must be a positive integer greater than 1.";
  if Precision cmpeq Infinity() then
    L,mpFtoL:=Completion(F,pl);
  else
    L,mpFtoL:=Completion(F,pl:Precision:=Precision);
  end if;
  mp := LiftMap(mpFtoL, R);
  return Codomain(mp), mp;
end intrinsic;




///////////////////////////////////////////////////////////////////


