freeze;


////////////////////////////////////////////////////////////////////
//                                                                //
//                                                                //
//                       Singularities, Places and                //
//                         Rational Solutions                     //
//                             Written by                         //
//                         Alexa van der Waall                    //
//                                and                             //
//                            Nils Bruin                          //
//                            Last update:                        //
//                             July 2009                          //
//                                                                //
//                                                                //
////////////////////////////////////////////////////////////////////


////////////////////////////////////////////////////////////////////
//                                                                //
//                     Functions on derivations                   //
//                                                                //
////////////////////////////////////////////////////////////////////


function HasProjectiveStandardDerivationOverSeries(R)
  // input: The differential operator ring R over a a Laurent series
  //        ring F=k((t)).
  // output: true iff R has derivation (c*t+O(*))*d/dt, where c is a constant.
  if Type(R) eq RngDiffOp then
    F:=BaseRing(R);
  else
    assert Type(R) eq RngDiff;
    F:=R;
  end if;
  assert IsDifferentialLaurentSeriesRing(F);
  derivtF:=(Derivation(R))(F.1);
  scalefunction:=F!((1/F.1)*(derivtF));
  if (Degree(scalefunction) eq 0) and (Valuation(scalefunction) eq 0) then
    return true;
  else
    return false;
  end if;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//               Functions on places and differentials            //
//                                                                //
////////////////////////////////////////////////////////////////////


// The following intrinsic was written by Nils Bruin.
function completion(P, Precision)
  //{Completion of the Function Field of P at the ideal induced by P.}
  K:=FunctionField(P);
  if Degree(K) ne Infinity() then
    Krer:=K;
  else
    Krer:=RationalExtensionRepresentation(K);
  end if;
  if Precision eq Infinity() then
    Cpl,mp:=Completion(Krer,Places(Krer)!P);
  else
    Cpl,mp:=Completion(Krer,Places(Krer)!P:Precision:=Precision);
  end if;
  if K eq Krer then
    mpKtoCpl  := map<K->Cpl|x:->mp(x), y:-> y@@mp>;
    return Cpl,mp;
  else
    mpKtoCpl := Coercion(K,Krer)*mp;
    mpKtoCpl := map<K->Cpl|x:->mpKtoCpl(x), y:-> y@@mpKtoCpl>;
  end if;
  return Cpl, mpKtoCpl;
end function;

// The following intrinsic was written by Nils Bruin.
function MovePlace(plc,iso)
  //{Moves a place along a field isomorphism K to L. In this implementation,
   //iso has to respect the concept of "infinity"}
  // Assumes that place on infty on K correspond to place on infty on L.
  K:=FunctionField(plc);
  assert IsIdentical(Domain(iso),K);
    //"The Domain of the map must be the function field of the place.";
  if Degree(K) eq Infinity() then
    Krer:=RationalExtensionRepresentation(K);
  else
    Krer:=K;
  end if;
  L:=Codomain(iso);
  if Degree(L) eq Infinity() then
    Lrer:=RationalExtensionRepresentation(L);
  else
    Lrer:=L;
  end if;
  IK:=Ideal(Places(Krer)!plc);
  OK:=Order(IK);
  if IsFiniteOrder(OK) then
    OL:=MaximalOrderFinite(Lrer);
  else
    OL:=MaximalOrderInfinite(Lrer);
  end if;
  IL:=ideal<OL|[Lrer!iso(K!f): f in Generators(IK)]>;
  return Places(L)!Place(IL);
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//              Functions relating to singular points             //
//                      and Fuchsian Equations.                   //
//                                                                //
////////////////////////////////////////////////////////////////////


// Instead of using the "scalefunction" and changing the operator
// L in to Lprime in the intrinsics in this section one could do the 
// following alternative construction.
//   tK:=UniformizingElement(pl);
//   Rprime:=DifferentialOperatorRing(Differential(tK));
//   Lprime:=Rprime!L;
// It uses that the parent of L is constructed with respect to
// a differential.


function MakeRngDiffOpOverFldDiffWithValAtPlace(R,pl,val)
  // Input: R, differential Operator Ring
  //        pl, a place of the algebraic differential field F over
  //             which R is defined.
  //        val, the valuation the new differential must have at
  //             the isomorphic copy of pl.
  // Output: 1.Differential Operator Ring Rprime over differential field
  //         Fprime naturally isomorphic to F, but whose differential
  //         has valuation at the copy val at pl.
  //         2. the copy of pl.
  //         3. The map induced map from R to Rprime.
  F:=BaseRing(R);
  valdatplace:=Valuation(Differential(R),pl);  
  if valdatplace eq val then 
      // "The operator ring already has the wanted valuation at the place.",
      // "The original ring is returned.";  
    return R,pl,map<R->R| L:->L, L:->L>;
  end if;
  scalefunction:=UniformizingElement(pl);
  scalefunction:=scalefunction^(valdatplace-val);
  Rprime,changemap:=ChangeDerivation(R,F!scalefunction);  
  K:=UnderlyingRing(F); 
  Fprime:=BaseRing(Rprime);
  assert K eq UnderlyingRing(Fprime);
  if Parent(pl) eq Places(K) then
    plprime:=MovePlace(pl,Coercion(K,Fprime));
  else 
    isoFtoFprime:=Inverse(Coercion(K,F))*Coercion(K,Fprime);
    plprime:=MovePlace(pl,isoFtoFprime);
  end if; 
  return Rprime,plprime,changemap;
end function;

intrinsic IsRegularPlace(L::RngDiffOpElt, pl::PlcFunElt) -> BoolElt
  {Returns `true' if pl is a regular place of L, otherwise `false'.}
  R:=Parent(L);
  F:=BaseRing(R); 
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";  
  require pl in Places(F):
    "The place is a place over the BaseField of the operator.";
  if Degree(L) in {-1,0} then
    return true;
  end if;  
  valdatplace:=Valuation(Differential(R),pl);
  if valdatplace ne 0 then  
    Rprime,plprime,changemap:=MakeRngDiffOpOverFldDiffWithValAtPlace(R,pl,0);
    Lprime:=changemap(L);
    return $$(Lprime,plprime);
  end if;
  Lmonic:=MonicDifferentialOperator(L);
  for coeff in Coefficients(Lmonic) do 
    if Valuation(coeff,pl) lt 0 then
        // Note: coeff is an element of the differential field F, but pl 
        // can be a place over the underlyingfield K. 
      return false;
    end if;
  end for;
  return true;
end intrinsic;

intrinsic IsRegularSingularPlace(L::RngDiffOpElt, pl::PlcFunElt) -> BoolElt
  {Returns `true' if pl is a regular singular place of L, otherwise `false'.}
  R:=Parent(L);
  F:=BaseRing(R); 
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";    
  require pl in Places(F):
    "The place is a place over the BaseField of the operator."; 
  degL:=Degree(L);
  if degL in {-1,0} then
    return false;
  end if;     
  valdatplace:=Valuation(Differential(R),pl);
  if valdatplace ne 0 then  
    Rprime,plprime,changemap:=MakeRngDiffOpOverFldDiffWithValAtPlace(R,pl,0);
    Lprime:=changemap(L);
    return $$(Lprime,plprime);
  end if;
  Lmonic:=MonicDifferentialOperator(L);
  coeffseqL:=Eltseq(Lmonic); 
  bl := false;
  for i := 0 to degL-1 do  
    valatplace := Valuation(coeffseqL[i+1],pl); 
      // Note: coeff... is an element of the differential field F, but pl 
      // can be a place over the underlyingfield K. 
    if valatplace lt i-degL then
      return false;
    end if;
    if bl eq false then 
      if (valatplace le -1) and (valatplace ge i-degL) then 
        bl := true;
      end if;
    end if;
  end for;
  return bl;
end intrinsic;

intrinsic IsIrregularSingularPlace(L::RngDiffOpElt, pl::PlcFunElt) -> BoolElt
  {Returns `true' if pl is an irregular singular place of L, otherwise `false'.}
  R:=Parent(L);
  F:=BaseRing(R); 
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";     
  require pl in Places(F):
    "The place is a place over the BaseField of the operator.";
  degL:=Degree(L);
  if degL in {-1,0} then
    return false;
  end if;      
  valdatplace:=Valuation(Differential(R),pl);
  if valdatplace ne 0 then  
    Rprime,plprime,changemap:=MakeRngDiffOpOverFldDiffWithValAtPlace(R,pl,0);
    Lprime:=changemap(L);
    return $$(Lprime,plprime);
  end if;
  Lmonic:=MonicDifferentialOperator(L);
  coeffseqL:=Eltseq(Lmonic);
  for i := 0 to degL-1 do
    if Valuation(coeffseqL[i+1],pl) lt i-degL then
        // Note: coeff... is an element of the differential field F, but pl 
        // can be a place over the underlyingfield K.
      return true;
    end if;
  end for;
  return false;  
end intrinsic;

intrinsic SetsOfSingularPlaces(L::RngDiffOpElt) -> SetEnum, SetEnum
  {Two exhaustive sets of divisors. The first set consists
  of the regular singular paces of L, the second the irregular singular places.}
  R:=Parent(L);
  F:=BaseRing(R);  
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";   
    // First find the support of the differential and put these places in a set. 
  diffL:=Differential(R);
  supportdiffL:=Support(Divisor(diffL)); 
  setsupportdiffL:=Seqset(supportdiffL);  
    // Find the poles of the coefficients of the monic operator.
    // these are singular points for sure if they do not appear in the
    // support of the differential.
  Lmonic:=MonicDifferentialOperator(L);
  coeffpolesset:={Places(F)|};
  for ci in Seqset(Coefficients(Lmonic)) do       
    if ci ne (BaseRing(R))!0 then  
      seqplacesci:=Poles(ci);      
      setplacesci:=Seqset(seqplacesci);    
      setplacesci:=SetToIndexedSet(setplacesci);
      coeffpolesset:=coeffpolesset join setplacesci;
    end if;
  end for;
  coeffpolesset:=coeffpolesset diff setsupportdiffL;
    // now we have to consider the two disjunct sets.
    // For each the places of the differential we have to rewrite the equation
    // with valuation zero in the new differential. Only then we can determine
    // what kind of point we are dealing with (i.e. regular, regular singular
    // or irregular singular).  
    // The places in the second set are singular but we don't know what type 
    // they are. We do not have to alter the equation.
  setsingularities:={};
  setirregularities:={};    
  for localplace in coeffpolesset do
    if IsIrregularSingularPlace(L,localplace) then
      Include(~setirregularities,localplace);        
    else 
      Include(~setsingularities,localplace);        
    end if;
  end for;
  for localplace in setsupportdiffL do
    Rprime,plprime,changemap
      :=MakeRngDiffOpOverFldDiffWithValAtPlace(R,localplace,0); 
    Lprime:=changemap(L); 
    if IsIrregularSingularPlace(Lprime,plprime) then
      Include(~setirregularities,localplace);    
    elif IsRegularPlace(Lprime,plprime) eq false then
      Include(~setsingularities,localplace);        
    end if;
  end for; 
  return setsingularities,setirregularities;        
end intrinsic;

intrinsic IsFuchsianOperator(L::RngDiffOpElt) -> BoolElt, SetEnum
  {Returns `true, Set of regular singular places' if L is a Fuchsian operator, 
   otherwise `false, _'.}
     // A Fuchsian Equation is an equation with no irregular singular points.
     // This routine is similar to SetsOfSingularPlaces, but is ended
     // immediately once an irregular singular point has been found.
  R:=Parent(L);
  F:=BaseRing(R);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";    
  diffL:=Differential(R);
  supportdiffL:=Support(Divisor(diffL));
  setsupportdiffL:=Seqset(supportdiffL);
  Lmonic:=MonicDifferentialOperator(L);
  coefficientsset:={};
  for ci in Seqset(Coefficients(Lmonic)) do       
    if ci ne F!0 then  
      seqplacesci:=Poles(ci);       
      setplacesci:=Seqset(seqplacesci);    
      setplacesci:=SetToIndexedSet(setplacesci);
      coefficientsset:=coefficientsset join setplacesci;
    end if;
  end for;
  coefficientsset:=coefficientsset diff setsupportdiffL;
  setsingularities:={};
  for localplace in coefficientsset do
    if IsIrregularSingularPlace(L,localplace) then
      return false, _;        
    else 
      Include(~setsingularities,localplace);        
    end if;
  end for;
  for localplace in setsupportdiffL do
    Rprime,plprime,changemap
      :=MakeRngDiffOpOverFldDiffWithValAtPlace(R,localplace,0);
    Lprime:=changemap(L); 
    if IsIrregularSingularPlace(Lprime,plprime) then
      return false, _;    
    elif IsRegularPlace(Lprime,plprime) eq false then
      Include(~setsingularities,localplace);        
    end if;
  end for; 
  return true, setsingularities;
end intrinsic;


intrinsic IsRegularSingularOperator(L::RngDiffOpElt) -> BoolElt, SetEnum
  {Returns true iff L is a regular singular operator, otherwise false.}
     // A Fuchsian Equation is an equation with no irregular singular points.
     // This routine is similar to SetsOfSingularPlaces, but is ended
     // immediately once an irregular singular point has been found.
  R:=Parent(L);
  F:=BaseRing(R);
  require IsAlgebraicDifferentialField(F) or
          IsDifferentialLaurentSeriesRing(F):
    "The given differential operator is not defined over an algebraic",
    "differential field or a differential Laurent series ring.";   
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0."; 
  if IsAlgebraicDifferentialField(F) then
    return IsFuchsianOperator(L);
  else 
    assert IsDifferentialLaurentSeriesRing(F);
    require HasProjectiveStandardDerivationOverSeries(R):
      "The derivation of the operator ring must be of the form c*t*d/dt";
    require IsWeaklyMonic(L):
      "The highest coefficient should be weakly equal to 1.";
    require WeakOrder(L) ge 1:
      "The degree of the operator should be at least 1."; 
    require not IsWeaklyZero(LeadingCoefficient(L)):
      "The leading coefficient is weakly monic to 0."; 
    minval := Minimum([Valuation(Coefficient(L,i)): i in [0..Degree(L)]]);
    if minval ge 0 then
      return true, _;
    else
      return false, _;
    end if;
  end if;
end intrinsic;



// The following intrinsic is written with the help of Nils Bruin.
intrinsic IndicialPolynomial(L::RngDiffOpElt, pl::PlcFunElt) -> RngElt
  {The monic indicial polynomial of L at the place pl.}
  // Based on Chapter 4.1 of Van der Put and Singer.
  // We also use that we calculate the polynomial w.r.t. a derivation
  // having no zeros or poles at the place. 
  // This is achieved by changing the derivation to (a scalar times)
  // d/dz, for F=C(z) and the place <> (1/z).
  // In the case that F=C(z) and pl = (1/z) one traditionally considers
  // the transformation by z|->zz:=1/z, 
  // We multiply the differential by a sufficient hight power of c*(1/z).
  // The difference with going to the local parameter zz (classical) is that
  // we keep looking at the point z=infinity, and not at zz=0.
  // For degree 1 places the indicial polynomial is a polynomial over C.
  // For higher degree places it is over C[z]/q(z), where (q)=pl.    
  R:=Parent(L);
  F:=BaseRing(R);
  require NumberOfGenerators(F) eq 1:
    "The base ring of the operator should have one generator."; 
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";  
  require pl in Places(F):
    "The place is a place over the BaseField of the operator.";
  C:=ExactConstantField(F);
    // So C is the Differential Constant Field of F.
  polring:=PolynomialRing(C);
  degL:=Degree(L);   
    // Trivial cases.
  if degL eq -1 then
    return polring!0;
  elif degL eq 0 then
    return polring!1;
  end if;  
    // Rewrite the operator w.r.t. a differential that has no poles
    // or zeros at the place pl.
  valdatplace:=Valuation(Differential(R),pl);   
  if valdatplace ne 0 then 
    Rprime,plprime,changemap:=MakeRngDiffOpOverFldDiffWithValAtPlace(R,pl,0);
    Lprime:=changemap(L); 
    return $$(Lprime,plprime);  
      // Notice that here we use the fact that the BaseRing(Rprime)
      // is isomorphic to the BaseRing(R).
  end if;   
  t:=UniformizingElement(pl);   
  if Degree(pl) gt 1 then 
      // We need to create the field C[z]/q(z).
      // The leading term-coeff. in the q-adic representation of the
      // coefficients in L should be considered in C[z]/q(z).
      // To make one field Cpl, in which we consider all, 
      // we make a field extension w.r.t.pl.
      // Then the indicial polynomial of L at q(z) is exactly the indicial
      // polynomial of L at a degree 1 place above pl. 
      // This is not in the book of Singer and V.d. Put.
    zeroinextension := Evaluate(t,pl); 
    Cpl:=Parent(zeroinextension); 
    Fpl, FtoFpl :=ConstantFieldExtension(F,Cpl); 
    Rpl:=DifferentialOperatorRing(Fpl);  
    RtoRpl:=map<R->Rpl| op:-> &+([Rpl|FtoFpl(a[i])*(Rpl.1)^(i-1):
                      i in [1..#a]]where a:=Eltseq(op))>;
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
    bl:=exists(degree1place){P: P in Support(Liftedplace)| Degree(P) eq 1};
    error if not (bl),
      "Hey, did base change and still don't have a degree 1 place?";
    return $$(RtoRpl(L),degree1place);
  end if;
    // Locate the terms a_iy^(i) in the operator whose series expansion
    // has lowest order.
  Lmonic:=MonicDifferentialOperator(L); 
  coeffseqL:=Eltseq(Lmonic);    
  setofindices:={};
  lowestdegree:=-degL;   
  for i := 0 to degL do
    val := Valuation(coeffseqL[i+1],pl); 
    if val-i eq lowestdegree then 
      Include(~setofindices,i);
    elif val-i lt lowestdegree then
      lowestdegree:=val-i;
      setofindices:={i};
    end if; 
  end for;
    // Construct the indicial polynomial.
    // First make sure the derivation of the local parameter is 1.
  t:=(1/Evaluate(Derivation(R)(t),pl))*t; 
  indicialpol:=polring!0; 
  for i in setofindices do
    coef:= Evaluate(coeffseqL[i+1]/(t^(lowestdegree+i)),pl); 
      // Returns an element in e.g. FldNum, must be in C.
    coef:=C!coef; 
    indicialpol:=indicialpol+coef*(&*[polring|(polring.1-j) : j in [0..i-1]]);
  end for; 
  return (1/LeadingCoefficient(indicialpol))*indicialpol;    
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//              Rational solutions of an operator.                //
//                                                                //
////////////////////////////////////////////////////////////////////


// Written by Nils Bruin:
intrinsic RationalSolutions(L::RngDiffOpElt) -> SeqEnum
  {Returns a basis of the nullspace of rational solutions of L(y)=0 
   in the base ring of L, given in a sequence.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";  
  require NumberOfGenerators(F) eq 1:
    "The base ring of the operator should have one generator.";
    // This is needed for the IndicialPolynomial to work.
  C:=ExactConstantField(F);
    // This the differential constant field of F.
  assert IsField(C);
  require Characteristic(C) eq 0:
    "The characteristic of the constant ring of the operator must be 0.";
  set1, set2 := SetsOfSingularPlaces(L);
  poles:= set1 join set2;  
  V:=[<p,[Integers()!v[1]: v in Roots(IndicialPolynomial(L,p))|
	     IsCoercible(Integers(),v[1])]>: p in poles]; 
  if exists{v: v in V | #v[2] eq 0} then
    SolutionsBasis:=[F|];
  else
    V:=[<v[1],Minimum(v[2])>:v in V];
      // Element is <place, minimum integer root of indicial pol.>.
    Dv:=&+[DivisorGroup(F)|-v[2]*v[1]: v in V]; 
      // = Divisor.
    RRS,RRmp:=RiemannRochSpace(Dv); 
    BasisOfCandidates:=[RRmp(b):b in Basis(RRS)]; 
    ImagesOfCDs:=[Apply(L,f):f in BasisOfCandidates];
    ImagesOfCDs:=ChangeUniverse(ImagesOfCDs,UnderlyingRing(F));
    SolutionSpace:=sub<RRS|Relations(ImagesOfCDs,C)>;
    SolutionsBasis:=[RRmp(f): f in Basis(SolutionSpace)];
    SolutionsBasis:=ChangeUniverse(SolutionsBasis,F);
  end if;  
  return SolutionsBasis;
end intrinsic;

intrinsic HasRationalSolutions(L::RngDiffOpElt, g::RngElt) ->
                                 BoolElt, RngElt, SeqEnum
  {Returns true if there exists a rational solution y in the base ring of
   L of L(y)=0.If such a solution exists, a particular solution of L(y)=g 
   and the nullspace of rational solutions of L in the base ring of L
   is also returned. However, if there is no solution 
   "false" is returned.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";
  require NumberOfGenerators(F) eq 1:
    "The base ring of the operator should have one generator.";
    // This is needed for the IndicialPolynomial to work.
  C:=ExactConstantField(F);
    // This is the differential constant field of F.
  assert IsField(C);
  require Characteristic(C) eq 0:
    "The characteristic of the constantfield of the operator must be 0.";
  require Parent(g) eq F:
    "The second argument should be in the BaseRing of the operator.";
  if g eq (Parent(g))!0 then
    return true, F!0, RationalSolutions(L);
  end if;
  Lh:=g*(Derivation(R)((1/g))*L) + (R.1)*L;
    // A (rational) functiony with  L(y)=g satisfies Lh(y)=0.
    // Conversely, if Lh(y)=0, then there exists a constant c,
    // such that L(y)=c*g. Thus L((1/c)*y)=g, for c not 0. 
  SolutionsBasis:= RationalSolutions(Lh);
    // Create the a bsis NullBasis for the Null space of L
    // and one specific solution.
  NewBasis:=[<f,(Apply(L,f))/g> : f in SolutionsBasis]; 
  SolBasis:=[ v[1]/v[2] : v in NewBasis |  not (v[2] eq F!0)];
  if #SolBasis eq 0 then 
    return false,_,_;
  else
    solution:=SolBasis[1];
    NullBasis:=[solution-f: f in Remove(SolBasis,1)] cat 
	           [ v[1] : v in NewBasis | v[2] eq F!0];
  end if;
  return true, solution, NullBasis;
end intrinsic;






