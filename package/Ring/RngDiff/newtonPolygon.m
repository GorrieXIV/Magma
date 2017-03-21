freeze;

// For references see the intrinsics NewtonPolygon and
// NewtonPolynomial.

// The definition we give is not the usual definition of a 
// Newton polynomial but is the reduced characteristic polynomial
// as defined in M.A. Barkatou - rational Newton Algorithm for computing
// formal solutions of linear differential equations, 1988.
// Also the definition used here is sligtly different than in the case of two
// variables in a commutative ring. For instance we have no negative slopes.
// Basically, our vertices are the `lowervertices' in the existing routine
// `NewtonPolynomial', except that our most lower left point might
// be different.
//
// The routines make use of the Newton Polygon over a polynomial ring.
// However, if we use it directly on the associated polynomial of the 
// differential operator we might not get the correct answer.
// That is why we sometimes add a term to the operator. So: 
// Important: The operator on which the Newton Polynomial is
// based might not be L! Be aware of this. We should fix this later.
//
// When the type RngDiffOpElt is put in C it is preferable to
// also construct a new and proper NewtonPolygon solely for these types 
// in C, rather than altering the operator to fit in an older definition.
// The ParentRing(NewtonPolygon) should then return the diff. operator ring.
// Polynomial(NewtonPolygon) must then return L. 
//
// So, until we have a type for our own, 
// we have to work with the Newton Polygons for Polynomial rings for
// now. To have a consistent answer resturned that we can retain
// the original constant term of L from, we add the coefficient at the 
// end point of the slope 0 to L.




////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////


declare attributes NwtnPgon:
   HasAddedTerm;


////////////////////////////////////////////////////////////////////
//                                                                //
//                         Newton Polygon                         //
//                                                                //
////////////////////////////////////////////////////////////////////


function OperatorAsPolynomialForNewtonPolygon(L, valsL);
  // Input: A localized operator over an algebraic differential field or
  //        over a differential Laurent series ring.
  // Output: The operator transformed as a polynomial over the underlying
  //         field in such a way that it is of the proper form for the 
  //         Newton polygon to work.
  //         The secons argument returned is a boolean that is true iff
  //         there was a correction term added.
  R:=Parent(L);
  F:=BaseRing(R);
  K:=UnderlyingRing(F); 
  T:=PolynomialRing(K); 
  if Degree(L) eq -1 then
    seqnewL:=Eltseq(L);
    bladdedterm := false;
  else
      // We consider the differential operator
      // as a univariate polynomial of its underlying field.     
    minimumval:=Minimum([v[1] : v in valsL]);
    lastindex:=
      Maximum([index: index in [1..#valsL] | valsL[index][1] eq minimumval]);
    if valsL[1][1] eq minimumval then
        // So there are no negative slopes
      seqnewL:=Eltseq(L);
      bladdedterm := false;
    else
        // Here we add a constant term to obtain a proper NewtonPolygon
        // from the already existing routine for elements of polyrings!!!
      seqnewL:= Eltseq(valsL[lastindex][2]+L); 
      bladdedterm := true;
    end if;
  end if;  
  assert Universe(seqnewL) eq F;
  seqnewL:= ChangeUniverse(seqnewL,K);
  pol := T!seqnewL;  
  return pol, bladdedterm;
end function;


 intrinsic NewtonPolygon(L::RngDiffOpElt,pl::PlcFunElt) -> NwtnPgon,
     RngDiffOpElt
  {The Newton Polygon of the differential operator L with respect to 
  the returned differential operator with derivation t*d/dt, 
  for a local uniformizing element t at pl.}
  // Based on V.d. Put & Singer - Ch3.3 def. 3.44.
  // With the help of Nicole Sutherland.
  // We determine the Newton polynomial with operator t*d/dt,
  // where t is a uniformizing element at pl.
  R:=Parent(L);
  F:=BaseRing(R);
  UF := UnderlyingRing(F);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require Ngens(F) eq 1:
    "The basefield of the operator should have 1 generator.";
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";
  require pl in Places(F):
    "The place is not a place of the BaseRing of the operator.";   
    // We need to make sure that the derivation is the correct one,
    // So locally of the form t*d/dt, for a local parameter t.
    // The coefficients of the returned operator do not depend on the chosen t.    
  tF:=UniformizingElement(pl);
  require not F!((Derivation(R))(tF)) eq F!0:
    "The derivation is trivial on the uniformizing element of the place.";
  L := Localization(L,pl);  
    // Alternative if Differential is assigned (so surely for FldDiffAlg's): 
    // Rprime:=DifferentialOperatorRing((1/tF)*Differential(tF));
    // L:=Rprime!L;
  assert UnderlyingRing(BaseRing(Parent(L))) eq UF;
  valsL :=  [<Valuation(v,pl),v> : v in Eltseq(L)];
  pol, bladdedterm := OperatorAsPolynomialForNewtonPolygon(L, valsL);
  assert BaseRing(pol) eq UF;
  np := NewtonPolygon(pol, pl : Faces:="Lower");  
  np`HasAddedTerm:=bladdedterm; 
  return np, L;
end intrinsic;


intrinsic NewtonPolygon(L::RngDiffOpElt) -> NwtnPgon, RngDiffOpElt
  {The Newton Polygon of the differential operator L over a 
   differential Laurent series ring, with respect to 
   the returned differential operator with derivation t*d/dt, 
   for a local uniformizing element t.}
  // Same remarks as in the other Newton Polygon. 
  R:=Parent(L); 
  F:=BaseRing(R);
  UF := UnderlyingRing(F);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsDifferentialLaurentSeriesRing(F):
    "The operator must be defined over a differential Laurent series ring.";     
  require not IsWeaklyEqual(Derivation(R)(F.1), F!0):
    "The derivation must be non trivial on the generator of the series ring.";
  require not IsOrderTerm(LeadingCoefficient(L)):
    "The operator must not have an order term as leading coefficient."; 
  L := Localization(L);
  assert UnderlyingRing(BaseRing(Parent(L))) eq UF;
  valsL:=[<Valuation(v),v> : v in Eltseq(L)];
  pol, bladdedterm := OperatorAsPolynomialForNewtonPolygon(L, valsL);
  assert BaseRing(pol) eq UF;
  np := NewtonPolygon(pol : Faces:="Lower");
  np`HasAddedTerm:=bladdedterm;
  return np, L;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                        Newton Polynomial                       //
//                                                                //
////////////////////////////////////////////////////////////////////


function slope(F)
  //{The slope of the face F, returning `Infinity' if the slope is
  //infinite.}
  Q:=Rationals();
  gradF:=GradientVector(F);
  if Q!(gradF[2]) ne Q!0 then
    return Q!(-gradF[1]/gradF[2]);
  else 
    return Infinity();
  end if;
end function;

intrinsic NewtonPolynomial(F::NwtnPgonFace) -> RngUPolElt
  {The Newton Polynomial of the face F, whose Newton Polygon
   should be defined with respect to a differential operator.
   The Newton Polynomial depends on the uniformizing element used,
   such that its variable is well-defined up to scalar multiplication by
   a fixed non-zero element.}
  // Based on M.van Hoeij. - Formal solutions and factorization
  // of differential operators with power series coefficients, 1997
  // Section 3.4.
  // With the help of Nicole Sutherland.
  // This routine uses the NewtonPolygon of F, which might be based
  // on a different operator then the given L, the operator L
  // with a constant term added. This only occurs when the Newton polygon
  // has a slope 0. In this case we have to do some corrective
  // trick.
  // The roots of the Newton Polynomial are determined of mutual 
  // multiplication by a fixed non-zero element, depending on the uniformizing 
  // element.  
  np:=Parent(F);
  require HasPolynomial(np):
    "The involved Newton Polygon has not been created w.r.t. a polynomial.";
  L:=Polynomial(np);
  R:=Parent(L);
  S:=BaseRing(R);
    // The creation of np might have been done over the underlying ring
    // of a differential operator.    
  if ISA(Type(S),RngDiff) then  
    if IsAlgebraicDifferentialField(S) then
      isalgebraic := true;
    elif IsDifferentialLaurentSeriesRing(S) then
      isalgebraic := false;
    else 
      require false:
      "The Newton Polygon must be defined over rational differential field or",
      "a differential Laurent series ring.";
    end if;
  else
    if ISA(Type(S), FldFun) then
      isalgebraic := true;
    elif ISA(Type(S),RngSerLaur) then
      isalgebraic := false;
    else
      require false:
      "The Newton Polygon must be defined over rational differential field or",
      "a differential Laurent series ring.";
    end if;
  end if;
  if isalgebraic then
    pl:=Prime(np);
    require ISA(Type(pl),PlcFunElt):
     "The Newton polygon of the face is not defined with respect to a place.";
    t:=UniformizingElement(pl);
  end if;
  Slope:=slope(F);
  facefunction:=FaceFunction(F);
  B:=BaseRing(Parent(facefunction)); 
  assert B eq S;
  if (Slope eq Rationals()!0) and np`HasAddedTerm then
    endvertex:=EndVertices(F)[2];
      // Corrective trick (based on the addition of an extra term in the
      // intrinsic NewtonPolygon):
    facefunction:=facefunction
                    -Coefficient(facefunction,Integers()!endvertex[1]);
      // So this is the correct facefunction!!!
    npol:=Eltseq(facefunction);
  else 
    seqnpol:=Eltseq(facefunction);
      // Unlike s <> 0, one first have to divide out by the lowest power
      // of the indeterminate of the polynomial ring.      
    seqnpol:=[B|seqnpol[i] : 
                 i in [Valuation(facefunction)+1..Degree(facefunction)+1]];
    deg:=#seqnpol-1;
      // Then the power of the indeterminate should be reduced
      // and the correct sequence of coefficients is made ("npol").
    den:=Integers()!(Denominator(Rationals()!Slope));
    npol:=[B|];  
    for i:=0 to Integers()!(deg/den) do 
      Append(~npol, seqnpol[i*den+1]);   
    end for;
  end if;
    // The coefficients should be evaluated in their lowest order
    // terms.  
  C:=BaseRing(B);
  newtonpol:=[C|];
  for v in npol do 
    if v eq B!0 then
      Append(~newtonpol,C!v);
    elif isalgebraic then
      Append(~newtonpol,Evaluate(v*t^(-Valuation(v,pl)),pl));
    else
      Append(~newtonpol,Truncate(v*(B.1)^(-Valuation(v))));
    end if;
  end for;
  return PolynomialRing(C)!newtonpol;
end intrinsic;  

intrinsic NewtonPolynomials(L::RngDiffOpElt) -> SeqEnum, SeqEnum
  {Returns all Newton polynomials of L with respect to the slopes of
   its Newton polygon. The second argument returned are the corresponding 
   slopes.}
  R := Parent(L);
  F := BaseRing(R);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsDifferentialLaurentSeriesRing(F):
    "The operator must be defined over a differential Laurent series ring.";
  require not IsWeaklyZero(L):
    "The operator is weakly equal to 0.";
  require Degree(L) ge 0:
    "The operator cannot be 0.";
  precF:=RelativePrecision(F);
  require (precF ge 1):
    "The precision of the differential series ring can not be 0.";
  np := NewtonPolygon(L);  
  slopes := Slopes(np);
  if #slopes eq 0 then
    return [ConstantRing(F)|], [Rationals()|];
  end if;
  faces := Faces(np);
  newtonpols := [NewtonPolynomial(faces[Index(slopes,slope)]): slope in slopes];
  return newtonpols, slopes;   
end intrinsic;  

