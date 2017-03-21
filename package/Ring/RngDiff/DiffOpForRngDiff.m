freeze;
 
import "ForOtherTypes.m" : ReplaceColumn;
import "singularities.m" : MovePlace;


function MySum(L)
  R:=Universe(L)!0;
  for a in L do
    R:=R+a;
  end for;
  return R;
end function;


////////////////////////////////////////////////////////////////////
//                                                                //
//             Differential Operators for RngDiff's               //
//                               by                               //
//                      Alexa van der Waall                       // 
//                                                                //
////////////////////////////////////////////////////////////////////




////////////////////////////////////////////////////////////////////
//                                                                //
//                     Attribute declarations                     //
//                                                                // 
////////////////////////////////////////////////////////////////////


declare attributes RngDiffOp:
   BaseRing,
   ConstantRing,
   PolyRing;
  
declare attributes RngDiffOpElt:
   Parent,
   Element;



////////////////////////////////////////////////////////////////////
//                                                                // 
//                       Creation functions                       // 
//                                                                //
////////////////////////////////////////////////////////////////////


function RDO_elt_create(R, S)
  x := HackobjCreateRaw(RngDiffOpElt);
  x`Parent := R;
  x`Element := S; 
  return x;  
end function;


// This function is the most geneneral one of creating a differential
// operator ring sofar.
// We can probably delete the restriction of K and C being fields
// for a more general setting in which K and C are rings.
function DiffOpRingGeneral(K,deriv,C) 
  // {Defines the ring of differential operators over the field K with 
  //  derivation deriv and constant field C.}
  assert IsField(K);
  assert IsField(C);
  if IsDifferentialField(K) then
    assert (Domain(deriv) eq Domain(Derivation(K))) and 
            (Codomain(deriv) eq  Codomain(Derivation(K)));
    // The derivation may be defined on the underlying field instead
    // of on the differential field.
  else
    assert Domain(deriv) eq K and Codomain(deriv) eq K;
  end if;
  R := HackobjCreateRaw(RngDiffOp);
  R`BaseRing := K;
  R`ConstantRing := C;  
  R`PolyRing := PolynomialRing(K:Global:= false);
  return R;
end function;

function DiffOpRing(K,dz)
  // {Returns the Ring of Differential Operators over the field K with 
  //  derivation d/(dz).}
  assert IsAlgebraicDifferentialField(K) or ISA(Type(K),FldFun);
  if IsAlgebraicDifferentialField(K) then
    assert FunctionField(dz) eq FunctionField(Differential(K!0));
    // The differential of a RngDiff may be defined on its underlying field.
  else
    assert FunctionField(dz) eq K;
  end if;
  assert not(dz eq Differential(K!0));
  R := HackobjCreateRaw(RngDiffOp);
  R`BaseRing := K;
  R`ConstantRing := ConstantField(K);
  R`PolyRing := PolynomialRing(K:Global:= false);
  return R;
end function;

// This one is basically the former routine.
function DiffOpRingDifferential(dz)
  // {Returns the Ring of Differential Operators over then function field
  // of dz, with derivation d/(dz).}  
  K:=FunctionField(dz);
  assert not(dz eq Differential(K!0));
  R:=DifferentialOperatorRing(K,dz);
  return R;
end function;

// FIRST ROUTINE FOR EXPORT AND THE MOST RESTRICTIVE ONE.
// As we only support DiffOpRings over RngDiffs for now.
// When we expand then the intrinsics above must be adjusted a bit.
// For instance the DiffOpRing could have a derivation assigned to it.
intrinsic DifferentialOperatorRing(F::RngDiff) -> RngDiffOp
  {Defines the ring of differential operators over the differential
   field F with induced derivation from F.}
  require IsDifferentialField(F):
    "The given argument is not a differential field.";
  if IsAlgebraicDifferentialField(F) then  
    R:=DiffOpRing(F,Differential(F)); 
  else
    R:=DiffOpRingGeneral(F,Derivation(F),ConstantRing(F));
  end if;
  return R;
end intrinsic;

// Keep as a function until really thought over what to support for an 
// operator ring over an RngMPol.
function DiffOpRingOverRngMPol(K,deriv,C) 
  // {Defines the ring of differential operators over the ring K with 
  //  derivation deriv and constant ring C.}
  assert IsDifferentialRing(K);
  assert Type(UnderlyingRing(K)) eq RngMPol;
  assert Domain(deriv) eq K and Codomain(deriv) eq K;
  R := HackobjCreateRaw(RngDiffOp);
  R`BaseRing := K;
  R`ConstantRing := C;  
  R`PolyRing := PolynomialRing(K:Global:= false);
  return R;
end function;

intrinsic AssignNames(~R::RngDiffOp, S::[MonStgElt])
{}
  AssignNames(~R`PolyRing, S);
end intrinsic;  

intrinsic Name(R::RngDiffOp, i::RngIntElt) -> .
{}
  return R.i;
end intrinsic;





////////////////////////////////////////////////////////////////////
//                                                                //
//                         Coercions                              //
//                                                                // 
////////////////////////////////////////////////////////////////////


intrinsic HackobjCoerceRngDiffOp(W::RngDiffOp,S::.) -> BoolElt, RngDiffOpElt
   {}
   if Type(S) eq RngDiffOpElt then  
     parentS:=Parent(S);
     BFW:=W`BaseRing;
     BFS:=parentS`BaseRing;
     if parentS eq W then 
         // S is an element of W.
       return true, S;
     elif IsAlgebraicDifferentialField(BFW) and 
          IsAlgebraicDifferentialField(BFS) and
          (BFW`UnderlyingRing eq BFS`UnderlyingRing) then  
          // The underlying function Fields are the same, only the 
          // differential is different. As the Space of differentials
          // is one-dimensional we can express the derivation of W as
          // a function times the derivation belonging to S.
       DofW:=Differential(BFW);   
       K:=UnderlyingRing(BFW);
       DofS:=Differential(BFS); 
       isoBFStoBFW:=Coercion(BFS,K)*Coercion(K,BFW);
       return true, MySum([W| isoBFStoBFW(a[i])*((DofW/DofS)*(W.1))^(i-1) 
                     : i in [1..#a]])
                     where a:=Eltseq(S);
     elif BFS eq BaseRing(BFW) then
       return IsCoercible(W,Eltseq(S));
         // So here we use that on BFS the Derivation(BFW) is Derivation(BFS) 
         // and that the differential operator inherits this derivation.
     else
       require false: "Can not coerce the operator in the differential ring.";     
     end if;
   elif Type(S) eq SeqEnum then
     bl,SW:=CanChangeUniverse(S,W`BaseRing);
     if bl then
       x := HackobjCreateRaw(RngDiffOpElt);
       x`Parent := W;
       x`Element := (W`PolyRing)!SW; 
       return true, x;
     else
       require false:"Cannot coerce elements of sequence into base field";
     end if;
   else
     bl,elt:=IsCoercible(W`BaseRing,S);
     if bl then
       x := HackobjCreateRaw(RngDiffOpElt);
       x`Parent := W;
       x`Element := (W`PolyRing)!S; 
       return true, x;   
     end if;
   end if;
   return false, "Illegal coercion.";
end intrinsic;

intrinsic '.'(W::RngDiffOp,i::RngIntElt) -> RngDiffOpElt
   {}
   require i eq 1: "Generator number must be in range [1..1]";
   return  RDO_elt_create(W, W`PolyRing.1);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                           Printing                             //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic HackobjPrintRngDiffOp(R::RngDiffOp, level::MonStgElt)
   {}
 printf "Differential operator ring over %o", Sprint(R`BaseRing,"Minimal");
end intrinsic;

intrinsic HackobjPrintRngDiffOpElt(x::RngDiffOpElt, level::MonStgElt)
   {}
   printf "%o", x`Element;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Membership and Equality                     //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic HackobjInRngDiffOp(x::., R::RngDiffOp) -> BoolElt
   {Returns true if x is in R.}
   if Type(x) eq RngDiffOpElt then
      return x`Parent eq R;
   end if;
   return false;
end intrinsic;

intrinsic HackobjParentRngDiffOpElt(x::RngDiffOpElt) -> RngDiffOp
   {}
   return x`Parent;
end intrinsic;

intrinsic 'eq' (R::RngDiffOp,S::RngDiffOp) -> BoolElt
   {}
   return IsIdentical(R,S);  
end intrinsic;

intrinsic 'eq' (x::RngDiffOpElt,y::RngDiffOpElt) -> BoolElt
   {}
   return Parent(x) eq Parent(y) and x`Element eq y`Element;
end intrinsic;

intrinsic IsWeaklyEqual(x::RngDiffOpElt, y::RngDiffOpElt) -> BoolElt
   {True iff differential operator x is weakly equal to y}
   R:=Parent(x);
   require R eq Parent(y):
     "The elements are not in the same ring.";
   F:=BaseRing(R);
   K:=UnderlyingRing(F);
   P:=PolynomialRing(K);
   xP:=P!ChangeUniverse(Eltseq(x),K);
   yP:=P!ChangeUniverse(Eltseq(y),K);
   return IsWeaklyEqual(xP,yP);
end intrinsic;

intrinsic IsWeaklyZero(x::RngDiffOpElt) -> BoolElt
   {True iff differential operator x is weakly equal to 0.}
   F:=BaseRing(Parent(x));
   K:=UnderlyingRing(F);
   P:=PolynomialRing(K);
   xP:=P!ChangeUniverse(Eltseq(x),K);
   return IsWeaklyZero(xP);
end intrinsic;

// ok
// Used in SlopeValuation and other factorisation codes.
// Can be done better for an algebraic differential ring using differentials.
intrinsic HasProjectiveDerivation(R::RngDiffOp) -> BoolElt
  {True iff R is defined over a ring with derivation weakly 
   of the form t*d/dt.}
  // input: The differential opearator ring R.
  // output: true iff R (weakly) has derivation t*d/dt.
  F := BaseRing(R);
  isADF := IsAlgebraicDifferentialField(F);
  isDLSR :=  IsDifferentialLaurentSeriesRing(F);
  require isADF or isDLSR:
     "The operator ring must be defined over an algebraic differential field",
     "a differential Laurent series ring.";
  require Characteristic(F) eq 0:
    "Routine only implemented for rings over a characteristic 0 field.";
  derivtF:=(Derivation(R))(F.1);  
  bl, scalefunction := IsCoercible(F, (1/F.1)*derivtF);
  assert bl;
  return IsWeaklyEqual(scalefunction-(F!1), F!0);
end intrinsic;

// ok
// Used in InitialLeftfactor and other FactorisationX codes.
intrinsic HasZeroDerivation(R::RngDiffOp) -> BoolElt
  {True iff the derivation of R (weakly) acts as zero on the
   generator of the base ring.}
  F := BaseRing(R); 
  require IsAlgebraicDifferentialField(F) or IsDifferentialLaurentSeriesRing(F):
    "The input must be defined over an algebraic differential field or",
    "a differential Laurent Series ring.";
  return IsWeaklyZero(F!((Derivation(R))(F.1)));
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Attribute Access Functions                  //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic BaseRing(R::RngDiffOp) -> Rng
   {The base ring of R.}
   return R`BaseRing;
end intrinsic;

// CoefficientRing need not be defined. It is synonym for BaseRing.

intrinsic ConstantRing(R::RngDiffOp) -> Rng
   {The constant ring of R.}
   return R`ConstantRing;
end intrinsic;

intrinsic Derivation(R::RngDiffOp) -> Map
   {The derivation of the base ring of R.}
   // assert not assigned(R`Derivation);
   return Derivation(BaseRing(R));
end intrinsic;

intrinsic Differential(R::RngDiffOp) -> DiffFunElt
   {The differential of the base ring to R.}
   // assert not assigned R`Differential;
   F:=BaseRing(R);
   require IsAlgebraicDifferentialField(F):
     "The given differential operator is not defined over",
     "an algebraic differential field."; 
   return Differential(F);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                    Arithmetic and Functionality                //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic One(R::RngDiffOp) -> RngDiffOpElt 
   {The identity element of R.}
   return R!1;
end intrinsic;

intrinsic Zero(R::RngDiffOp) -> RngDiffOpElt
   {The zero element of R.}
   return R!0;
end intrinsic;

intrinsic '-' (x::RngDiffOpElt) -> RngDiffOpElt
   {}
   return (-1)*x;
end intrinsic;

intrinsic '-' (x::RngDiffOpElt,y::RngElt) -> RngDiffOpElt
   {} 
   bl,yR:=IsCoercible(Parent(x),y);
   if bl then
     a := x`Element;
     b := yR`Element;
     return RDO_elt_create(Parent(x),a-b); 
   else
     require false:"Bad argument types\nArgument types given:",
        Type(x),",",Type(y);
   end if;  
end intrinsic;

intrinsic '-' (x::RngElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   bl,xR:=IsCoercible(Parent(y),x);
   if bl then
     a := xR`Element;
     b := y`Element;
     return RDO_elt_create(Parent(y),a-b); 
   else
     require false:"Bad argument types\nArgument types given:",
        Type(x),",",Type(y);
   end if;  
end intrinsic;

intrinsic '-' (x::RngDiffOpElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   W := Parent(x);
   require W cmpeq Parent(y): "Arguments have distinct parents.";
   a := x`Element; 
   b := y`Element;
   return RDO_elt_create(W,a-b); 
end intrinsic;

intrinsic '+' (x::RngDiffOpElt,y::RngElt) -> RngDiffOpElt
   {}
   bl,yR:=IsCoercible(Parent(x),y);
   if bl then
     a := x`Element;
     b := yR`Element;
     return RDO_elt_create(Parent(x),a+b); 
   else
     require false:"Bad argument types\nArgument types given:",
        Type(x),",",Type(y);
   end if;  
end intrinsic;

intrinsic '+' (x::RngElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   bl,xR:=IsCoercible(Parent(y),x);
   if bl then
     a := xR`Element; 
     b := y`Element;
     return RDO_elt_create(Parent(y),a+b); 
   else
     require false:"Bad argument types\nArgument types given:",
        Type(x),",",Type(y);
   end if;  
end intrinsic;

intrinsic '+' (x::RngDiffOpElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   R := Parent(x);
   require R cmpeq Parent(y): "Arguments have distinct parents.";
   a := x`Element;
   b := y`Element;
   return RDO_elt_create(R,a+b); 
end intrinsic;

intrinsic '*' (x::RngElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   bl,xR:=IsCoercible(Parent(y),x);
   if bl then
     a := xR`Element;
     b := y`Element;;
     return RDO_elt_create(Parent(y),a*b); 
   else
     require false:"Bad argument types\nArgument types given:",
        Type(x),",",Type(y);
   end if;  
end intrinsic;

intrinsic '*' (x::RngDiffOpElt,y::RngElt) -> RngDiffOpElt
   {}
   R := Parent(x);
   bl, yR := IsCoercible(R,y); 
   if bl eq false then
     require false :
     "Bad argument types\nArgument types given:", Type(x),",",Type(y);
   end if;     
   if Degree(x) eq -1 then
     return R!0;
   elif Degree(yR) eq -1 then
     return R!0;  
   else
     L:=Eltseq(x); 
     coeffy:=Coefficients(yR); 
     derivcoeffy:=[(Derivation(R))(q) : q in Eltseq(yR)]; 
       // q is an element of the base ring of R.
     derivy:= R!([0] cat coeffy) + R!derivcoeffy;
     return L[1]*y+$$(R!(L[2..#L]),derivy);                     
   end if;
end intrinsic;

intrinsic '*' (x::RngDiffOpElt,y::RngDiffOpElt) -> RngDiffOpElt
   {}
   R := Parent(x);
   require R cmpeq Parent(y): "Arguments have distinct parents.";
   if Degree(x) eq -1 then
     return R!0;
   elif Degree(y) eq -1 then
     return R!0;  
   else
     L:=Eltseq(x); 
     coeffy:=Coefficients(y); 
     derivcoeffy:=[(Derivation(R))(q) : q in Eltseq(y)];
       // q is an element of the base ring of R. 
     derivy:= R!([0] cat coeffy) + R!derivcoeffy;
     return L[1]*y+$$(R!(L[2..#L]),derivy);                 
   end if;
end intrinsic;


intrinsic '^' (x::RngDiffOpElt,n::RngIntElt) -> RngDiffOpElt
   {}
   require n ge 0: "Exponent must be non-negative.";
   if n eq 0 then 
      return Parent(x)!1;
   elif n eq 1 then 
      return x;
   elif n eq 2 then
      return x*x;
   end if;
   b := IntegerToSequence(n,2);
   y := x^b[1]; 
   for i in [2..#b] do 
      x := x^2;  
      if b[i] eq 1 then
         y := x*y;
      end if;
   end for;
   return y;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                      Predicates and Booleans                   //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic IsZero(L::RngDiffOpElt) -> BoolElt
  {True iff L is the zero operator.}
  if L eq (Parent(L))!0 then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic IsOne(L::RngDiffOpElt) -> BoolElt
  {True iff L is the identity operator.}
  if L eq (Parent(L))!1 then
    return true;
  else
    return false;
  end if;
end intrinsic;

intrinsic IsMonic(L::RngDiffOpElt) -> BoolElt
  {True iff L is monic.}
  return IsMonic(L`Element);
end intrinsic;

intrinsic IsDifferentialOperatorRing(R::.)->BoolElt
  {Tests if the given object is a Ring of Differential Operators}
  return ISA(Type(R),RngDiffOp);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                               Maps                             //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic TranslationMap(R::RngDiffOp, e ::RngElt) -> Map
  {Returns a map on R that replaces R.1 by (R.1+e).}
  F:=BaseRing(R);
  bl, e :=IsCoercible(F,e);
  require bl:
    "The second argument is not coercible in the base ring of the operator ring.";
  mp := map< R-> R| L :->  (deg cmpeq -1 select R!0 else
                            &+([Coefficient(L,i)*(R.1+e)^i : i in [0..deg]])
                            where deg := Degree(L)),
                    L :->  (deg cmpeq -1 select R!0 else
                            &+([Coefficient(L,i)*(R.1-e)^i : i in [0..deg]])
                            where deg := Degree(L))>;
  return mp;
end intrinsic;

// There is no check that mp is a differential map.
intrinsic LiftMap(mp::Map, R::RngDiffOp) ->  Map
  {Given the differential map mp : F -> FF on differential fields and 
   a differential operator ring R over F, lift mp to a map on 
   differential operator rings R -> RR. The basefield of RR is FF.}
  F:=Domain(mp);
  FF:= Codomain(mp);
  require IsDifferentialField(F) and IsDifferentialField(FF):
    "The domain and codomain of the map should be differential fields.";
  require BaseRing(R) eq F:
    "The basering of argument 2 should be the domain of argument 1.";
  RR := DifferentialOperatorRing(FF); 
  m:=map<R->RR| op:-> RR![FF|mp(a): a in Eltseq(op)],
                po:-> R![F|a@@mp: a in Eltseq(po)]>;
  return m;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                       Structure Operations                     //
//                                                                //
////////////////////////////////////////////////////////////////////

  
// do we want that the second element is coercible?
// Or maybe coercible in the underlyingfield?  
intrinsic ChangeDerivation(R::RngDiffOp,f::RngElt) 
    -> RngDiffOp,Map
  {Returns a ring R' of differential operators with isomorphic base ring to
   the one of R, but whose derivation is f*Derivation(R), with f not (weakly
   equal to) 0. The map is the morphism R<D> -> R'<D'>, induced by 
   D=(1/f)*D'.}
  F:=BaseRing(R);
  require IsDifferentialField(F):
    "The Differential Operator Ring must be defined over a FldDiff.";  
  bl, f :=IsCoercible(F,f);
  require bl eq true:
    "The second argument is not coercible in the BaseRing of the operator ring.";
    // More strict: 
    // IsIdentical(F,Parent(f)): 
    //   "The second argument must be an element in the BaseRing",
    //   " of the operator.";
  // require f ne F!0: 
  require not IsWeaklyZero(f):
    "The second argument must not be (weakly equal to) 0.";
  Fprime,iso:=ChangeDerivation(F,f);
  Rprime:=DifferentialOperatorRing(Fprime);
  phi:=map<R->Rprime|
     op:-> MySum([Rprime|iso(a[i])*((1/iso(f))*(Rprime.1))^(i-1):
                      i in [1..#a]]where a:=Eltseq(op)),
     po:-> MySum([R|((b[i])@@iso)*(f*(R.1))^(i-1):
                      i in [1..#b]]where b:=Eltseq(po))>;
  return Rprime,phi;
end intrinsic; 

intrinsic ChangeDifferential(R::RngDiffOp, df::DiffFunElt) -> RngDiffOp, Map
  {Returns the differential operator ring with differential df, and 
   whose underlying ring of its basefield coincides with the one of R. 
   The map returned is the bijective map of R into the new operator ring.}
  F := BaseRing(R);
  require IsAlgebraicDifferentialField(F):
    "The operator ring must be defined over an algebraic differential field.";
  require df in DifferentialSpace(F):
    "The differential does not belong the the basering of the first argument."; 
  require not df cmpeq Differential(F!0):
    "The differential must be non-zero.";  
  assert Differential(R) eq Differential(F);  
  f := Differential(F)/df;
    // differentials of F may be differentials of its underlying ring.
  assert (f in F) or (f in UnderlyingRing(F));
  return ChangeDerivation(R,F!f);  
end intrinsic;

intrinsic ConstantFieldExtension(R::RngDiffOp, Cext::Fld) -> RngDiffOp, Map
  {Returns the ring of differential operators with base ring isomorphic 
   to the one of R, but whose constant field is Cext.
   The derivation is extended over the new constant field.}
     // Maybe do more if Cext eq C or Cmpeq C. 
     // Need to implement Finite Fields.
  F:=BaseRing(R);
  require Characteristic(F) eq 0:
    "Routine only implemented for operators of characteristic 0.";
  require IsAlgebraicDifferentialField(F) or
          IsDifferentialLaurentSeriesRing(F):
    "The given differential operator ring is not defined over",
    "an algebraic differential field or a differential Laurent series ring."; 
  C:=ConstantField(F); 
  require ExistsCoveringStructure(C, Cext) : 
		"Argument 2 must extend the constant field of argument 1";
  require CoveringStructure(C, Cext) eq Cext : 
		"Argument 2 must extend the constant field of argument 1";
  Fprime, phi :=ConstantFieldExtension(F,Cext);
  opmap := LiftMap(phi, R);  
  return Codomain(opmap),opmap;
end intrinsic;

// change the name, as localization is usually related to a local field,
// i.e. what we call completion. 
intrinsic Localization(R::RngDiffOp, pl::PlcFunElt) -> RngDiffOp, Map, 
  PlcFunElt
  {Returns the operator ring whose differential has valuation -1 at pl,
   with derivation t *d/dt, where t is the uniformizing element at the
   place. Also the map between the operator rings, and the induced image of pl
   is returned.}
  F:=BaseRing(R);    
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";  
  require pl in Places(F):
    "The place is a place over the BaseField of the operator ring.";    
  tF := UniformizingElement(pl);
  derivtF:=F!(Derivation(R)(tF));
  require not derivtF eq F!0:
    "The derivation is trivial on the uniformizing element of the place.";
  scalefunction:=(1/tF)*derivtF;
                   // = Coefficient((1/tF)*R.1*tF,0);
  scalefunction:=F!scalefunction; 
  if scalefunction eq F!1 then   
    return R, Coercion(R,R), pl;
  else  
    Rprime,changemap:=ChangeDerivation(R,1/scalefunction);
      // This is a differential operator ring with derivation tF*d/dtF.
      // This is independent of the chosen uniformizing element.
    K:=UnderlyingRing(F); 
    Fprime:=BaseRing(Rprime);
    if Parent(pl) eq Places(K) then
      plprime:=MovePlace(pl,Coercion(K,Fprime));
    else 
      isoFtoFprime:=Inverse(Coercion(K,F))*Coercion(K,Fprime);
      plprime:=MovePlace(pl,isoFtoFprime);
    end if;      
    return Rprime, changemap, plprime;
  end if;
end intrinsic;

// change the name, as localization is usually related to a local field,
// i.e. what we call completion. 
intrinsic Localization(R::RngDiffOp) -> RngDiffOp, Map
  {Given a differential operator ring over a the differential Laurent series
   ring C((t)), returns the operator ring whose derivation 
   is of the form t*d/dt, 
   and the and map between the operator rings.}
  F:=BaseRing(R);    
  require IsDifferentialLaurentSeriesRing(F):
    "The given differential operator is not defined over",
    "a differential Laurent series ring.";    
  derivtF:=F!(Derivation(R)(F.1));
  require not IsWeaklyZero(derivtF) :
    "The derivation is not allowed to be weakly zero.";
  scalefunction:=(1/F.1)*derivtF;
  scalefunction:=F!scalefunction;
  // relprecscale := RelativePrecision(scalefunction); 
  if IsWeaklyEqual(scalefunction-(F!1), F!0) then   
    return R, Coercion(R,R);
  else  
    return ChangeDerivation(R,1/scalefunction);
      // This is a diff. operator ring with derivation (F.1+O(*))*d/d(F.1).
      // But the precision of the scalefunction is the minimum of
      // the precision of F and derivtF.
      // If Derivation(R) is f(z)*d/dz, and f has an order term,
      // then the derivation of Rprime has the same order term.
      // So the only case that might be different is when f(z), does not have 
      // an order term.
  end if; 
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                          Element Operations                    //
//                                  --                            //
//                              extractions                       //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic Coefficients(L::RngDiffOpElt) -> SeqEnum
   {The coefficients of L, put in a sequence.}
   return Coefficients(L`Element);
end intrinsic;

intrinsic Eltseq(L::RngDiffOpElt) -> SeqEnum
   {The coefficients of L, put in a sequence.}
   return Coefficients(L);
end intrinsic;

intrinsic Terms(L::RngDiffOpElt) -> SeqEnum
  {The sequence of non-zero terms of L.}
  R:=Parent(L);
  zero:=BaseRing(R)!0;
  seqL:=Eltseq(L);
  return [seqL[i]*(R.1)^(i-1): i in [1..#seqL] | not (seqL[i] eq zero)];
end intrinsic;

intrinsic Degree(L::RngDiffOpElt) -> RngIntElt
   {The order of the differential operator L.}
   return Degree(L`Element);
end intrinsic;

intrinsic Order(L::RngDiffOpElt) -> RngIntElt
   {The order of the differential operator L.}
   return Degree(L);
end intrinsic;

intrinsic Coefficient(L::RngDiffOpElt,i::RngIntElt) -> RngElt
   {The coefficient of D^i in L, where D is the derivation associated with L.}
   requirerange i ,0 , Degree(L);     
   return Coefficient(L`Element,i);
end intrinsic;

intrinsic LeadingCoefficient(L::RngDiffOpElt) -> RngElt
   {The coefficient of the highest power of the derivation in L.}
   if Degree(L) eq -1 then
     return (BaseRing(Parent(L)))!0;
   else
     return LeadingCoefficient(L`Element);
   end if;
end intrinsic;

intrinsic LeadingTerm(L::RngDiffOpElt) -> RngDiffOpElt 
  {The leading term of L.}
  R:=Parent(L);
  ordL:=Order(L);
  if ordL eq -1 then
    return L;
  else
    return LeadingCoefficient(L)*(R.1)^ordL;
  end if;
end intrinsic;

intrinsic IsWeaklyMonic(L::RngDiffOpElt) -> BoolElt 
  {If L is defined over a differential series ring, then returned 
   is true iff the leading coefficient of the operator is weakly equal to 1.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsDifferentialSeriesRing(F):
    "The element must be a differential series."; 
  require Degree(L) ge 0:
    "The operator must be non-zero.";
  return IsWeaklyEqual(LeadingCoefficient(L), F!1);
end intrinsic;

intrinsic WeakOrder(L::RngDiffOpElt) -> RngIntElt 
  {If L is defined over a differential series ring, then returned 
   is the highest exponent in L, whose coefficient is not weakly
   equal to 0.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsDifferentialSeriesRing(F):
    "The element must be a differential series."; 
  if IsWeaklyEqual(L,R!0) then
    return -1;
  end if;
  iszero := true;
  seqL:=Eltseq(L);
  index :=#seqL;
  while iszero do
    if IsWeaklyEqual(seqL[index],F!0) then
      index := index-1;
    else
      iszero := false;
    end if;
  end while;
  return index-1;
end intrinsic;

intrinsic WeakDegree(L::RngDiffOpElt) -> RngIntElt 
  {If L is defined over a differential series ring, then returned
   is the highest exponent in L, whose coefficient is not weakly
   equal to 0.}
  return WeakOrder(L);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                          Element Operations                    //
//                                  --                            //
//                              conversions                       //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic TruncateCoefficients(L::RngDiffOpElt) -> RngDiffOpElt 
  {If L is defined over a differential series ring, then returned 
   is the operator whose coefficients are the truncations of the 
   coefficients of L.}
  R:=Parent(L);
  F:=BaseRing(R);
  require IsDifferentialSeriesRing(F):
    "The coefficients of the operator must be differential series.";
  return R![Truncate(v):v in Eltseq(L)];
end intrinsic;

intrinsic MonicDifferentialOperator(L::RngDiffOpElt)->RngDiffOpElt
  {Returns the monic operator (1/LeadingCoefficient(L))*L for non-zero L.
   If L is 0, then it returns L.}
  if Degree(L) eq -1 then
    return L;
  else
    bl, invLCL:= IsInvertible(LeadingCoefficient(L)); 
    require bl:
      "The leading coefficient of the operator is not invertible.";
    return invLCL*L;
  end if;
end intrinsic;

intrinsic Adjoint(L::RngDiffOpElt)->RngDiffOpElt
  {The formal adjoint differential operator of L.}
  n:=Degree(L);
  R:=Parent(L);  
  if n eq -1 then
    return R!0;    
  elif n eq 0 then
    return L;
  end if;  
  D:=R.1;
  adjointL:=R!0;
  for i:=0 to n do
    adjointL := adjointL + ((-1)^i*D^i)*(R!Coefficient(L,i));		  
  end for;
    // adjointL := (-1)^n*adjointL;
  return adjointL;
end intrinsic;

intrinsic Apply(L::RngDiffOpElt,f::RngElt)->RngElt
  {Apply the differential operator L to the function f.}
  R := Parent(L);
  bl,f:=IsCoercible(BaseRing(R),f);
  require bl:
    "The function must be coercible into the BaseRing of the operator.";
  if Degree(L) eq -1 then
    return Parent(f)!0;
  else
    eltseqL:=Eltseq(L); 
    return eltseqL[1]*f
       + $$(R!(eltseqL[2..#eltseqL]),(Derivation(R))(f));
  end if;
end intrinsic;

intrinsic '@'(f::RngElt,L::RngDiffOpElt)->RngElt
  {Apply the differential operator L to the function f.}
  require IsCoercible(BaseRing(Parent(L)),f):
    "The function must be coercible into the BaseRing of the operator.";
  return Apply(L,f);
end intrinsic;

intrinsic Translation(L::RngDiffOpElt, e ::RngElt) -> RngDiffOpElt, Map
  {Replaces R.1 by (R.1+e) if L is an operator in R.
   The translation map on R is returned as a second argument.}
  R:=Parent(L);
  bl, e :=IsCoercible(BaseRing(R),e);
  require bl:
    "The second argument is not coercible in the base ring of the operator.";
  mp:=TranslationMap(R,e);
  return mp(L), mp;
end intrinsic;

intrinsic Localization(L::RngDiffOpElt, pl::PlcFunElt) -> RngDiffOpElt, Map, 
  PlcFunElt
  {Returns the localized operator of L, and the embeddings map between 
   the parents as well as the induced image of the place.}
  R := Parent(L);
  F:=BaseRing(R);    
  require IsAlgebraicDifferentialField(F):
    "The given differential operator is not defined over",
    "an algebraic differential field.";  
  require pl in Places(F): 
    "The place is a place over the BaseField of the operator.";
   _, mp, P := Localization(R, pl);
   return mp(L), mp, P;
end intrinsic;

intrinsic Localization(L::RngDiffOpElt) -> RngDiffOpElt, Map
  {Returns the localized operator of L, and the embeddings map between 
   the parents.}
   R := Parent(L);
   F := BaseRing(R);    
   require IsDifferentialLaurentSeriesRing(F):
    "The given differential operator is not defined over",
    "a differential Laurent series ring.";    
   _, mp := Localization(R);
   return mp(L), mp;
end intrinsic;



////////////////////////////////////////////////////////////////////
//                                                                //
//                    Matrices related to Diff. Operators         //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic CompanionMatrix(L::RngDiffOpElt) -> AlgMatElt
  {The companion matrix of the monic differential operator L.}
  R:=Parent(L);
  require IsMonic(L):
    "Operator must be monic.";
  return CompanionMatrix(L`Element);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                 Differential Ring Extensions                   //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic DifferentialRingExtension(L::RngDiffOpElt) -> RngDiff
  {Constructs a differential ring extension of the differential ring
   F=BaseRing(L), by adding a formal solution of L and its derivatives.}
  F:=BaseRing(Parent(L));
  require IsDifferentialField(F):
    "The given field must be a differential field.";
  r:=Degree(L);
  P:=PolynomialRing(F,r);
  cfs:=Eltseq(L);
  lst:=[P|P.i : i in [2..r]] cat [-&+([cfs[i]*P.i:i in [1..r]])/cfs[r+1]];
  return DifferentialRingExtension(lst);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                 Differential Field Extensions                  //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic DifferentialFieldExtension(L::RngDiffOpElt) -> RngDiff
  {Constructs a differential field extension of the differential field
   F=BaseRing(L), by adding a formal solution of L and its derivatives.}
  F:=BaseRing(Parent(L));
  require IsDifferentialField(F):
    "The given field must be a differential field.";
  r:=Degree(L);
  P:=PolynomialRing(F,r);
  cfs:=Eltseq(L);
  lst:=[P|P.i : i in [2..r]] cat [-&+([cfs[i]*P.i:i in [1..r]])/cfs[r+1]];
  return DifferentialFieldExtension(lst);
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//                       Symmetric Powers                         //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic SymmetricPower(L::RngDiffOpElt, m::RngIntElt) -> RngDiffOpElt
  {The m-th symmetric power of L.}
  // The returned m-th symmetric poer is monic, if the leading coefficient 
  // is invertible.
  // For degree(L)=2 this intrinsic is based on Mark van Hoeij's Maple-code,
  // who uses an iteration theorem from Bronstein/Mulders/Weil - On
  // symmetric powers of differential equations, 1997.
  // This paper also describes a method for differential operatorrs
  // of higher degree, which we use to a certain extend as well.
  // At the indicated spaces, there is room for improvement by
  // algorithms described in the paper.
  require m gt 0:
    "The second argument must be positive.";
  d:=Degree(L);
  if d eq -1 then
    return L;
  end if; 
  bl, invlc:= IsInvertible(LeadingCoefficient(L));
  require bl:
      "The leading coefficient of the operator is not invertible.";
  R:=Parent(L);
  if d eq 0 then
    return invlc*L;
  elif d eq 1 then
    return R!(R.1 + m*invlc*Coefficient(L,0));
  elif d eq 2 then
    L:=invlc*L;
    L0:=R!1;
    L1:=R.1;
    A1:=Coefficient(L,0);
    A2:=Coefficient(L,1);
    for i:=1 to m do
      L2:=L1;   
      L1:=(i*A2)*L1+(R.1)*L1 + i*(m-(i-1))*A1*L0; 
      L0:=L2;
    end for;
    return L1;
  else
    L:=invlc*L;
      // Delete this for more efficient implementation for the factor-free
      // implementation and using the preprocessing of the matrix.
    F:=BaseRing(R);
    E:=DifferentialRingExtension(L);
    V:=MonomialsOfDegree(E,m);    
    N:=Binomial(d+m-1,d-1);
    lc:=LeadingCoefficient(L);
    derivlc:=Derivation(E)(lc);
    omega:=(E.1)^m;
    row:=[F| MonomialCoefficient(omega,v): v in V];
    mat:=Matrix(F,1,N,row);
    independent:= true;
    i:=0;
    while independent and (i lt N+1) do
      omega:=lc*Derivative(omega)-i*derivlc*omega;
      row:=[F| MonomialCoefficient(omega,v): v in V];
      mat:=VerticalJoin(mat,Matrix(F,1,N,row));
        // put in optimalization preprocessing of matrix.
      kernel:=Kernel(mat);
      if Dimension(kernel) gt 0 then
        assert Dimension(kernel) eq 1;
        independent:=false;
      else
        i:=i+1;
      end if;
    end while;  
    basisvector:=(Basis(kernel))[1];
    sympower:=R!(Eltseq(basisvector));
    bl, invlc:= IsInvertible(LeadingCoefficient(sympower));
    if bl then 
      return invlc*(sympower);
    else
      return sympower;
    end if;
  end if;
end intrinsic;


////////////////////////////////////////////////////////////////////
//                                                                //
//          Differential Operator of an Algebraic Function        //
//                                                                //
////////////////////////////////////////////////////////////////////


intrinsic DifferentialOperator(f::RngUPolElt) -> RngDiffOpElt
  {The minimal differential operator to which roots of the irreducible
   polynomial f are solutions.}
  require IsIrreducible(f):
    "The polynomial is not irreducible.";
  P:=Parent(f);
  F:=BaseRing(P);
  require IsDifferentialField(F):
    "The coefficient ring of the polynomial must be a differential field.";
  require Characteristic(F) eq 0:
    "Routine only implemented for rings of characteristic 0.";
  R:=DifferentialOperatorRing(F);
  if Degree(f) eq -1 then
    return R!0;
  elif Degree(f) eq 0 then
    return R!1;
  end if;
  M:=ext<F|f>;
  X:=M.1;
  degf:=Degree(f);
  mat:=Matrix(M,1,degf,[M|v : v in Eltseq(X)]);
  ithderivative:=0; 
  while ithderivative lt degf do 
    X:=Derivative(X);
    mat:=VerticalJoin(mat,Matrix(M,1,degf,[M|v : v in Eltseq(X)]));
    kernel:=Kernel(mat);
    if Dimension(kernel) gt 0 then
      assert Dimension(kernel) eq 1;
      v:=Eltseq(Basis(Kernel(mat))[1]); 
      L:= [F!term: term in v];
      ithderivative:=degf;
    else
      ithderivative:=ithderivative+1;
    end if;
  end while;
  return MonicDifferentialOperator(R!L);
end intrinsic;
