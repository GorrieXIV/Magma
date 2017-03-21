freeze;

/////////////////////////////////////////////////////////////////////////
// multivalued_sections.m
/////////////////////////////////////////////////////////////////////////
// $Revision: 41262 $
// $Date: 2012-12-02 01:25:19 +1100 (Sun, 02 Dec 2012) $
// $LastChangedBy: kasprzyk $
/////////////////////////////////////////////////////////////////////////
// Authors: Gavin Brown, Jaroslaw Buczynski, Alexander Kasprzyk
/////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
// Type for Multivalued Sections 
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////

import "../utilities/functions.m": variables_of_ring, remove_repetitions;

declare type RngMRad[RngMRadElt];
declare type RngMRadElt;

declare attributes RngMRad:
//essential attributes:
   polynomial_ring;

declare attributes RngMPol:
 //optional attributes:
   family_of_multivalued_sections;



///////////////////////////////////////////////////////////////////////
// printing
// l is the level: it's a string that can take values like
// "Default", "Maximal", "Minimal", "Magma".



intrinsic Print(Xi::RngMRad, s::MonStgElt)
  {}
   R:=Ring(Xi);
  printf "Family of Multivalued Sections over \n%o", R;
end intrinsic;








///////////////////////////////////////////////////////////////////////
// Coercion and membership
///////////////////////////////////////////////////////////////////////




intrinsic IsCoercible(Xi::RngMRad,S::.) -> BoolElt, RngMRadElt
   {}
   if ISA(Type(S), RngElt)  then
      bool, x:=IsCoercible(FieldOfFractions(Ring(Xi)),S);
      if bool then
         return true, MultivaluedSection(x); 
      end if;
      
   elif ISA(Type(S), RngMRadElt)  then 
      if S in  Xi then
         return true, S; 
      end if; 
   end if;
   return false, "Illegal coercion.";
end intrinsic;


intrinsic 'in'(x::., Xi::RngMRad) -> BoolElt
{}
   require Type(x) eq RngMRadElt or Type(x) eq RngMPolElt: "Wrong type.";

   if Type(x) eq RngMRadElt then 
      return Parent(x) eq Xi;
   else
      return x in Ring(Xi);
   end if;
end intrinsic;



///////////////////////////////////////////////////////////////////////
// creation
///////////////////////////////////////////////////////////////////////

intrinsic FamilyOfMultivaluedSections(X::RngMPol) -> RngMRad
{}
  if assigned X`family_of_multivalued_sections then 
     return X`family_of_multivalued_sections;
  end if;
  Xi:=New(RngMRad); 
  Xi`polynomial_ring:=X;
  X`family_of_multivalued_sections := Xi;
  return Xi;
end intrinsic;

intrinsic FamilyOfMultivaluedSections(X::TorVar) -> RngMRad
{Returns the Family Of Multivalued Sections over X.}
  return FamilyOfMultivaluedSections(CoordinateRing(X));
end intrinsic;




///////////////////////////////////////////////////////////////////////
// recovering the attributes
///////////////////////////////////////////////////////////////////////



intrinsic Ring(Xi::RngMRad) -> RngMPol
{Returns the polynomial ring over which Xi was defined.}
  return Xi`polynomial_ring;
end intrinsic;

intrinsic BaseRing(Xi::RngMRad) -> Rng
{Returns the field over which the polynomial ring of Xi was defined.}
  return BaseRing(Ring(Xi));
end intrinsic;




 
 

///////////////////////////////////////////////////////////////////////
// comparison
///////////////////////////////////////////////////////////////////////

intrinsic 'eq'(Xi1::RngMRad, Xi2::RngMRad) -> BoolElt
{Equality test for Xi1 and Xi2}
  return Ring(Xi1) cmpeq Ring(Xi2);
end intrinsic;









///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
// Type for Multivalued Section 
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////



declare attributes RngMRadElt:
//essential attributes:
   poly_factors,
   coefficient,
//   is_standard,
//   is_factorised,
//optional attributes:
   rational_part,
   rational_function,
   irrational_part;

   


///////////////////////////////////////////////////////////////////////
// functions and procedures 
///////////////////////////////////////////////////////////////////////


  /////////////////////////////////////////////////////////////////////////
  // Here we mainly deal with factors (or their sequences), 
  // which will be represented as elements of a Cartesian product.
  // First coordinate is the polynomial ring or base field/ring, the second is Rationals().
  // The pair p:=(f,k) represents f^k (k may be fractional and/or negative). 
  // A sequence of such pairs (usually called factors) represents the product of those f^k.
  // Empty sequence represents 1;
  // 


forward mult;

function exponent(p)
   return p[2];
end function;

function base(p)
   return p[1];
end function;



function is_zero(p)
   // true iff p represents zero.
   // error will occur if illegal operations are observed.
   if IsZero(base(p)) then
     if IsZero(exponent(p)) then
         error "Illegal operation 0^0.";
     elif exponent(p) lt 0 then 
            error "Illegal operation 1/0.";
     end if;
     return true;
   end if;  
  return false;
end function;


function is_one(p)
   // true iff p represents 1.
   return base(p) eq 1 or IsZero(exponent(p));
end function;


function is_scalar(p);
   // true iff p represents a scalar.
   return  TotalDegree(base(p)) eq 0;
end function;




procedure simplify(~factors)
   // given a sequence of pairs, we want to get rid of redundancies:
   // if a base repeats in two factors, then we may add the exponents.
   // if an exponent is zero, then we may remove this factor.

   i:=1;
   while i le #factors do
      j:=i+1;
      bool, inv:=IsInvertible(base(factors[i]));
      
      while j le #factors do
         if base(factors[i]) eq base(factors[j]) then
            factors[i][2]+:=exponent(factors[j]); 
            Remove(~factors,j);
         elif bool and inv eq base(factors[j]) then
            factors[i][2]-:=exponent(factors[j]); 
            Remove(~factors,j);
         else
            j+:=1;
         end if;
      end while;
      if IsZero(base(factors[i])) then
         if IsZero(exponent(factors[i])) then
            error "Illegal operation 0^0.";
         elif exponent(factors[i]) lt 0 then 
            error "Illegal operation 1/0.";
         end if;
         factors[i][2]:=1;
         factors:=[factors[i]];
         i:=1;
      end if;  
      if is_one(factors[i]) then
         Remove(~factors,i);
      else
         i +:=1;
      end if;
   end while;
end procedure;




procedure resolve(~coefficient)
   // tries to reduce the root exponent: (a^2)^(1/4) = a^(1/2). 
   k:=exponent(coefficient);
   c:=base(coefficient);
   ff:=Factorisation(Denominator(k));
   for f in ff do
      i:=1;
      repeat
         bool, res:=IsPower(c,f[1]);
         if bool then 
            c:=res;
            k div:= f;
         end if;         
         i +:=1;
      until not bool or i gt f[2];
   end for;
   coefficient[1]:=c;
   coefficient[2]:=k;
end procedure;

   



function LiftToCartesianProduct(f,k)
   // 
   // f is assumed to be from a polynomial ring and k a rational number.
   // this function generates a sequence 
   // (either empty or consisting of a single element) representing f^k. 
   //
   R:=Parent(f);
   RRat:=car<R,Rationals()>;
   p:=elt<RRat|f,k>;
   if is_zero(p) then
      return [p];
   elif is_one(p) then
      return [RRat|];
   else
      return [p];  
   end if; 
end function;    


procedure simplify_coefficient(~coefficient)
   simplify(~coefficient);
   i:=1;
   r:=Universe(coefficient)[1]!1;
   while i le #coefficient do

      while i le #coefficient and IsIntegral(exponent(coefficient[i])) do 
         r*:=base(coefficient[i])^(Integers()!exponent(coefficient[i]));
         Remove(~coefficient,i);
      end while;
     
      if i le #coefficient then

        den:=Denominator(exponent(coefficient[i]));
        bool, res :=IsPower(base(coefficient[i]), den);
        if bool then
           num:=Numerator(exponent(coefficient[i]));
           r*:=res^num;
           Remove(~coefficient,i);
        else
           resolve(~coefficient[i]); 
           i+:=1;
        end if;
      end if;
   end while;
   if not IsOne(r) then
      Insert(~coefficient, 1, LiftToCartesianProduct(r,1)[1]);
   end if;
end procedure;




function NumeratorAndDenominator(f,k)
   //
   // as LiftToCartesianProduct, but now f may be in a RationalFunctionField 
   // and the returned sequence will have length at most 2.
   //
   if Type(f) eq RngMPolElt then
      return LiftToCartesianProduct(f,k);
   else 
      n:=Numerator(f);
      d:=Denominator(f);
      return  LiftToCartesianProduct(n,k) cat
              LiftToCartesianProduct(d,-k);
   end if;
end function;

function DefaultFactors(f,g,k)
   //
   // as  LiftToCartesianProduct, but now we represent as a sequence of factors f*g^k.
   // each of f and g may be either in PolynomialRing or RationalFunctionField.
   // 
   return NumeratorAndDenominator(f,1) cat NumeratorAndDenominator(g,k);
end function;





///////////////////////////////////////////////////////////////////////
// printing
// l is the level: it's a string that can take values like
// "Default", "Maximal", "Minimal", "Magma".


procedure FactorPrinting(p ,single)
  bool:= false; //(TotalDegree(base(p)) le 1 or exponent(p) eq 1) and #Terms(base(p)) le 1 
     //     and (coeff eq 1)) 
      //   or (exponent(p) eq 1 and single);
  if not bool then
     printf "(";
  end if;
  
  printf "%o", base(p);

  if not bool then
     printf ")";
  end if;

  if exponent(p) ne 1 then
     printf "^";
     bool:= (exponent(p) ge 0 and  IsIntegral(exponent(p) ));
     if not bool then
        printf "(";
     end if;
     printf "%o", exponent(p);
     if not bool then
       printf ")";
     end if;
  end if;
end procedure;



intrinsic Print(xi::RngMRadElt, s::MonStgElt)
  {}
  KFs, CP:=KnownFactorsAndCoefficient(xi);
  if IsEmpty(KFs) and IsEmpty(CP) then 
     printf "1"; 
     return;
  end if;
  
  if not IsEmpty(CP) then
      FactorPrinting(CP[1], #CP  + #KFs eq 1);
      for i in [2..#CP] do
         printf "*";
         FactorPrinting(CP[i], false);
      end for;
      if not IsEmpty(KFs) then
        printf "*";
      end if;
   end if;
   if not IsEmpty(KFs) then    
       FactorPrinting(KFs[1], #KFs eq 1);
       for i in [2..#KnownFactors(xi)] do
           printf "*";
           FactorPrinting(KFs[i], false);
       end for;
   end if;
end intrinsic;




///////////////////////////////////////////////////////////////////////
// Coercion and membership
///////////////////////////////////////////////////////////////////////

intrinsic Parent(xi::RngMRadElt) -> RngMPol
{Recovers the Family of Multivalued Sections of xi.}
   return FamilyOfMultivaluedSections(Ring(xi));
end intrinsic;



intrinsic IsCoercible(xi::RngMRadElt, S::.) ->   BoolElt, RngMRad
{Cannot coerce anything to RngMRadElt.}
   return false, "Illegal coercion";
end intrinsic;





///////////////////////////////////////////////////////////////////////
// creation
///////////////////////////////////////////////////////////////////////


intrinsic Zero(Xi::RngMRad) -> RngMRad
{Zero of Xi.}
         xi:=New(RngMRadElt);
         RQ:=CartesianProduct(Ring(Xi),Rationals());
         FQ:=CartesianProduct(BaseRing(Xi),Rationals());
         factors:=[RQ|];
         coefficient:=[FQ|<0,1>];
         xi`poly_factors:=factors;
         xi`coefficient:=coefficient;
         return xi;
end intrinsic;

 






function CreateMultivaluedSectionWithFactorsAndCoefficient(S,c)
 
   RQ:=Universe(S);
   R:=RQ[1];  
   if &or[is_zero(cc) : cc in c] then 
       return Zero(FamilyOfMultivaluedSections(R));
   end if;

   coefficient:=c;

   factors:=[RQ|];

   for factor in S do
      f:=base(factor);
      k:=exponent(factor);
      if IsZero(f) then 
         return Zero(FamilyOfMultivaluedSections(R));
      end if;
      ff, const:=Factorisation(f);
      ff:=[elt<RQ|base(fff), exponent(fff)*k> : fff in ff];
      factors cat:=ff;
      Append(~coefficient, elt<RQ|const, k>);
   end for;
   simplify(~factors);
   simplify_coefficient(~coefficient);

   xi:=New(RngMRadElt);
   xi`poly_factors:=factors;
   xi`coefficient:=coefficient;
   return xi; 
end function;



function CreateMultivaluedSectionWithFactors(S)
   RQ:=Universe(S);
   R:=RQ[1];  
   c:=[CartesianProduct(BaseRing(R), Rationals()) |];
   return CreateMultivaluedSectionWithFactorsAndCoefficient(S,c); 
end function;



function CreateMultivaluedSectionWithPolynomials(f,g,k) 
   xi:=CreateMultivaluedSectionWithFactors(DefaultFactors(f,g,k));
   return xi;
end function;





intrinsic MultivaluedSection(f::RngMPolElt,g::RngMPolElt,k::FldRatElt) -> RngMRadElt
   {}
   R:= Parent(f);
   require g in R:"Argument 1 and 2 must be in the same ring.";   
   return CreateMultivaluedSectionWithPolynomials(f,g,k);
end intrinsic;

intrinsic MultivaluedSection(f::FldFunRatElt,g::RngMPolElt,k::FldRatElt) -> RngMRadElt
   {}
   R:= Parent(g);
   K:=FieldOfFractions(R);
   require f in K:"Argument 1 and 2 must be in the same ring.";   
   return CreateMultivaluedSectionWithPolynomials(f,g,k);
end intrinsic;

intrinsic MultivaluedSection(f::RngMPolElt,g::FldFunRatElt,k::FldRatElt) -> RngMRadElt
   {}
   R:= Parent(f);
   K:=FieldOfFractions(R);
   require g in K:"Argument 1 and 2 must be in the same ring.";   
   return CreateMultivaluedSectionWithPolynomials(f,g,k);
end intrinsic;

intrinsic MultivaluedSection(f::FldFunRatElt,g::FldFunRatElt,k::FldRatElt) -> RngMRadElt
   {}
   K:= Parent(f);
   require g in K:"Argument 1 and 2 must be in the same ring.";   
   return CreateMultivaluedSectionWithPolynomials(f,g,k);
end intrinsic;

intrinsic MultivaluedSection(f::FldFunRatElt) -> RngMRadElt
   {}
   K:=Parent(f);   
   return CreateMultivaluedSectionWithPolynomials(f,K!1, 1);
end intrinsic;

intrinsic MultivaluedSection(f::RngMPolElt) -> RngMRadElt
   {}
   K:=Parent(f);   
   return CreateMultivaluedSectionWithPolynomials(f,K!1, 1);
end intrinsic;

intrinsic MultivaluedSection(g::RngMPolElt, k::FldRatElt) -> RngMRadElt
   {}
   K:=Parent(g);   
   return CreateMultivaluedSectionWithPolynomials(K!1,g,k);
end intrinsic;

intrinsic MultivaluedSection(g::FldFunRatElt, k::FldRatElt) -> RngMRadElt
{Multivalued section, which is equal to f*(g^k) or g^k or just f.}
   K:=Parent(g);   
   return CreateMultivaluedSectionWithPolynomials(K!1,g,k);
end intrinsic;








///////////////////////////////////////////////////////////////////////
// recovering attributes
///////////////////////////////////////////////////////////////////////



function NaiveIrrationalPartOfFactor(p)
   r:=p;
   if IsZero(base(p)) then
      r[1]:=1;
      r[2]:=1;
   else
      r[2]:=FractionalPart(exponent(p));
   end if;

   return r;
end function;


function NaiveRationalPartOfFactor(p)
   r:=p;
   r[2]:=Floor(exponent(p));
   return r;
end function;

function NaiveRationalRoundUpOfFactor(p)
   r:=p;
   r[2]:=Ceiling(exponent(p));
   return r;
end function;


function NaiveIrrationalPart(xi)
  // returns the product of factors of xi, 
  // each with multiplicity = 
  // fractional part of original multiplicity. 

  KFs,CP:= KnownFactorsAndCoefficient(xi);
  factors:=[Universe(KFs)|  NaiveIrrationalPartOfFactor(factor) : factor in KFs];
  coefficient:=[Universe(CP)|NaiveIrrationalPartOfFactor(coeff) : coeff in CP];
  return CreateMultivaluedSectionWithFactorsAndCoefficient(factors, coefficient);
end function;


function NaiveRationalPart(xi)
  // returns the product of factors of xi, 
  // each with multiplicity = 
  // Floor of original multiplicity.
  KFs,CP:= KnownFactorsAndCoefficient(xi);
  factors:=[Universe(KFs)|  NaiveRationalPartOfFactor(factor) : factor in KFs];
  coefficient:=[Universe(CP) |NaiveRationalPartOfFactor(coeff) : coeff in CP];
  return CreateMultivaluedSectionWithFactorsAndCoefficient(factors, coefficient);  
end function;

function NaiveRationalRoundUp(xi)
  // returns the product of factors of xi, 
  // each with multiplicity = 
  // Ceiling of original multiplicity.
  KFs,CP:= KnownFactorsAndCoefficient(xi);
  factors:=[Universe(KFs)|  NaiveRationalRoundUpOfFactor(factor) : factor in KFs];
  coefficient:=[Universe(CP) |NaiveRationalRoundUpOfFactor(coeff) : coeff in CP];
  return CreateMultivaluedSectionWithFactorsAndCoefficient(factors, coefficient);  
end function;



intrinsic RationalPart(xi::RngMRadElt) -> RngMPolElt
{Recovers the rational part of the multi-valued function.}
//   _:=StandardPresentation(xi);
   return NaiveRationalPart(xi);
end intrinsic;

intrinsic RationalRoundUp(xi::RngMRadElt) -> RngMPolElt
{Recovers the rational round up of the multi-valued function, i.e. rounds up all exponents in factors of xi.}
//   _:=StandardPresentation(xi);
   return NaiveRationalRoundUp(xi);
end intrinsic;


intrinsic IrrationalPart(xi::RngMRadElt) -> RngMPolElt
{Recovers the irrational part of the multi-valued function.}
//   _:=StandardPresentation(xi);
   return NaiveIrrationalPart(xi);
end intrinsic;



intrinsic KnownFactors(xi::RngMRadElt) -> SeqEnum
{Recovers factors of the multivalued section, that are already known.}
   return xi`poly_factors;
end intrinsic;

intrinsic KnownCoefficient(xi::RngMRadElt) -> SeqEnum
{Recovers coefficient of the multivalued section, that are already known.}
   return xi`coefficient;
end intrinsic;


intrinsic KnownFactorsAndCoefficient(xi::RngMRadElt) -> SeqEnum, SeqEnum
{Recovers factors and coefficient of the multivalued section, that are already known.}
    return KnownFactors(xi), KnownCoefficient(xi);
end intrinsic;


intrinsic Coefficient(xi:: RngMRadElt ) -> SeqEnum
{Calculates the coefficient of xi. It returns a sequence of up to 2 pairs p1,p2 with p1[2]=1. The actual coefficient is equal to p1[1]*p2[1]^p2[2]. If p1[1] =1, then p1 will not show up. Analogously for p2.}
    _:=Factorisation(xi);

    CP:=KnownCoefficient(xi);

    FQ:=Universe(CP);
    coeffrat:=FQ[1]!1;
    coeffirr:=elt<FQ|1,1>;
    for i in CP do
       if is_zero(i) then 
           xi`coefficient:=[elt<FQ| 0, 1>];
           return xi`coefficient;
       end if;
       rat:=NaiveRationalPartOfFactor(i);
       irr:=NaiveIrrationalPartOfFactor(i);
       resolve(~irr);
       coeffrat *:=base(rat)^(Integers()!exponent(rat));
       mult(~coeffirr, irr);
       resolve(~coeffirr);
    end for;

    xi`coefficient:=[elt<FQ| coeffrat, 1>, coeffirr ];
    simplify(~xi`coefficient);
    
    return xi`coefficient;
end intrinsic;




/*
intrinsic StandardPresentation(xi::RngMRadElt) -> RngMRadElt
{Calculates the standard presentation of xi, i.e. factorises the factors, which have irrational exponent.}
   if not IsStandardPresented(xi) then
      KFs,CP:=KnownFactorsAndCoefficient(xi);
      RQ:=Universe(KFs);
      FQ:=Universe(CP);
      factorsIrr:=[RQ|factor : factor in KFs| not IsIntegral(exponent(factor)) ];
      coeffIrr:=[FQ|coeff : coeff in CP| not IsIntegral(exponent(coeff)) ];
      xiIrr:= CreateMultivaluedSectionWithFactorsAndCoefficient(factorsIrr,coeffIrr); 
      factorsRat:=[RQ|factor : factor in KFs| IsIntegral(exponent(factor)) ];
      coeffRat:=[FQ|coeff : coeff in CP|  IsIntegral(exponent(coeff)) ];
      xiRat:= CreateMultivaluedSectionWithFactorsAndCoefficient(factorsRat,coeffRat);
      _:=Factorisation(xiIrr);
      newxi:=xiRat*xiIrr;
      xi`poly_factors:=KnownFactors(newxi);
      xi`coefficient:=KnownCoefficient(newxi);
      xi`is_standard:=true;
   end if;
   return xi;
end intrinsic;
*/

intrinsic Ring(xi::RngMRadElt) -> RngMPol
{Recovers the polynomial ring, for which xi is a section.}
   return Universe(KnownFactors(xi))[1];
end intrinsic;

intrinsic IsRational(xi::RngMRadElt) -> BoolElt
{True iff the xi has trivial irrational part.}
   return IsOne(IrrationalPart(xi));
end intrinsic;




///////////////////////////////////////////////////////////////////////
// improving attributes
///////////////////////////////////////////////////////////////////////





procedure mult(~p1,p2)
   if is_zero(p1) then
     return;
   end if;

   if is_zero(p2) then
     p1:=p2;
     return;
   end if;
   
   if is_one(p2) then
     return;
   end if;

   if is_one(p1) then
     p1:=p2;
     return;
   end if;
   
   B:=Parent(base(p1));
   
   f1:=base(p1);
   f2:=B!base(p2);
   k1:=exponent(p1);
   k2:=exponent(p2);
   num1:=Numerator(k1);
   den1:=Denominator(k1);
   num2:=Numerator(k2);
   den2:=Denominator(k2);
   gcdden:=GCD(den1,den2);
   newnum1:=num1*den2 div gcdden;
   newnum2:=num2*den1 div gcdden;
   gcdnum:=GCD(num1, num2);
   newexpnum1:=(num1*den2 div (gcdden*gcdnum));
   newexpnum2:=(num2*den1 div (gcdden*gcdnum));
   if newexpnum1 lt 0 then 
       f1:=1/f1;
       newexpnum1 *:=-1;
   end if;
   f1,newexpnum1;
   f1 ^:=newexpnum1;
   if newexpnum2 lt 0 then 
       f1 *:=f2^(-newexpnum2);
       newexpnum2 *:=-1;
   else 
       f1 *:=f2^newexpnum2;
   end if;
   k1 := gcdnum/LCM(den1,den2);
   if k1 lt 0 then
      p1[2]:= -k1;
      p1[1]:=1/f1;
   else
      p1[2]:=k1;
      p1[1]:=f1;
   end if;
end procedure;

function multi(p1,p2)
   p3:=p1;
   mult(~p3,p2);
   return p3;
end function;



intrinsic Factorisation(xi:: RngMRadElt) -> SeqEnum
{Factorization of xi into irreducible factors.}
   return KnownFactors(xi);

/*
   KFs, CP:=KnownFactorsAndCoefficient(xi);
   if IsFactorised(xi) then 
      return KFs;
   end if;
   RQ:=Universe(KFs);
   FQ:=Universe(CP);

   factors:=[RQ|];
   coefficient:=CP;
   for factor in KFs do
      f:=base(factor);
      k:=exponent(factor);
      if IsZero(f) then 
         factors:=[RQ|];
         coefficient:=[FQ|<0,1>];
         xi`poly_factors:=factors;
         xi`coefficient:=coefficient;
         xi`is_factorised:=true;
         xi`is_standard:=true;
         return [RQ|<0,1>];
      else 
         ff, const:=Factorisation(f);
         ff:=[elt<RQ|base(fff), exponent(fff)*k> : fff in ff];
         factors cat:=ff;
      end if;
      Append(~coefficient, elt<RQ|const, k>);
   end for;

   simplify(~factors);
   simplify_coefficient(~coefficient);
   xi`poly_factors:=factors;
   xi`coefficient:=coefficient;
   xi`is_factorised:=true;
   xi`is_standard:=true;

   return factors;
*/
end intrinsic;


intrinsic RationalFunction(xi::RngMRadElt) -> FldFunRatElt
{If xi is rational, then returns the rational function corresponding to xi.}
   if assigned xi`rational_function then 
        return xi`rational_function;
   end if;
   require IsRational(xi): "Argument must be rational.";
   q:=FieldOfFractions(Ring(xi))!1;
   for p in KnownFactors(xi) do
      e:=Integers()!exponent(p);
      if e lt 0 then
         q *:=1/(base(p)^(-e));
      else
         q *:=base(p)^e;       
      end if;    
   end for;
   for p in KnownCoefficient(xi) do
      e:=Integers()!exponent(p);
      if e lt 0 then
         q *:=1/(base(p)^(-e));
      else
         q *:=base(p)^e;       
      end if;    
   end for;
   xi`rational_function:=q;
   return xi`rational_function;
end intrinsic;



///////////////////////////////////////////////////////////////////////
// arithmetics
///////////////////////////////////////////////////////////////////////

intrinsic IsZero(xi::RngMRadElt) -> BoolElt
{True iff x is the zero element}
  coeff:=Coefficient(xi);
  return not IsEmpty(coeff) and is_zero(coeff[1]);
end intrinsic;

intrinsic IsOne(xi::RngMRadElt) -> BoolElt
{True iff x is equal to 1.}
  KFs:=Factorisation(xi);
  if IsEmpty(KFs) then
     return #Coefficient(xi) eq 0;
  end if;
  return false;
end intrinsic;



intrinsic IsScalar(xi::RngMRadElt) -> BoolElt
{True iff x is a scalar.}
  KFs:=Factorisation(xi);
  if IsEmpty(KFs) then
     return true;
  end if;
  return false; 
end intrinsic;


intrinsic IsRegular(xi::RngMRadElt) -> BoolElt
{True iff xi has no poles}
  if &and[exponent(p) ge 0 or is_scalar(p):  p in KnownFactors(xi)] then 
     return true;
  end if;
  if &and[exponent(p) ge 0 or is_scalar(p):  p in Factorisation(xi)] then 
     return true;
  end if;
  return false;
end intrinsic;


intrinsic IsMonomial(xi::RngMRadElt) -> BoolElt
{True iff xi is a product of variables to some powers (no constants)}
  if &and[IsMonomial(base(p)) :  p in Factorisation(xi)] 
      and #coeff eq 1 and is_one(coeff[1]) 
        where coeff is Coefficient(xi) 
      then 
     return true;
  end if;
  return false;
end intrinsic;






intrinsic '*'(xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{}
  require Ring(xi1) cmpeq Ring(xi2) : "Arguments must be sections of the same ring.";
  factors:=KnownFactors(xi1) cat KnownFactors(xi2);
  coefficient:=KnownCoefficient(xi1) cat KnownCoefficient(xi2);
  xi:=CreateMultivaluedSectionWithFactorsAndCoefficient(factors, coefficient);
  return xi;
end intrinsic;


intrinsic '*'(g::RngElt, xi::RngMRadElt) -> RngMRadElt
{}
  bool, gg:= IsCoercible(FieldOfFractions(Ring(xi)), g);
  require bool: "Arguments must be sections of the same ring.";
  gg:=MultivaluedSection(gg);
  return xi*gg;
end intrinsic;

intrinsic '*'( xi::RngMRadElt,g::RngElt) -> RngMRadElt
{Multiplication of multi-valued sections.}
  bool, gg:= IsCoercible(FieldOfFractions(Ring(xi)), g);
  require bool: "Arguments must be sections of the same ring.";
  return gg*xi;
end intrinsic;


intrinsic '/'(xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{}
  require Ring(xi1) cmpeq Ring(xi2) : "Arguments must be sections of the same ring.";
  require not IsZero(xi2): "Illegal operation (dividing by 0).";
  return xi1 * Power(xi2,-1);
end intrinsic;


intrinsic '/'(g::RngElt, xi::RngMRadElt) -> RngMRadElt
{}
  bool, gg:= IsCoercible(FieldOfFractions(Ring(xi)), g);
  require bool: "Arguments must be sections of the same ring.";
  require not IsZero(xi): "Illegal operation (dividing by 0).";
  return g*Power(xi,-1);
end intrinsic;

intrinsic '/'(xi::RngMRadElt, g::RngElt) -> RngMRadElt
{Division of multi-valued sections.}
  bool, gg:= IsCoercible(FieldOfFractions(Ring(xi)), g);
  require bool: "Arguments must be sections of the same ring.";
  require not IsZero(g): "Illegal operation (dividing by 0).";
  return xi*(1/g);
end intrinsic;


intrinsic '+'(xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{Addition of multi-valued sections. Since we assume the result is again simple multivalued section, the irrational parts must be the same. Use Sum([...]), rather than &+[...] for more complicated expressions, where terms may cancel.}
  require Ring(xi1) cmpeq Ring(xi2) : "Arguments must be sections of the same ring.";

  irr1:=IrrationalPart(xi1);
  rat2:=xi2/irr1;
  require IsRational(rat2) :"Arguments must have the same irrational part.";
  rat1:=RationalPart(xi1);
  q:=RationalFunction(rat1) + RationalFunction(rat2);
  xi:=q*irr1;
  return xi;
end intrinsic;

intrinsic Sum(S::[RngMRadElt]) -> RngMRadElt
{Addition of multi-valued sections.}  
  Xi:=Universe(S);
  SS:=[Xi| xi : xi in S |not IsZero(xi)];
  if IsEmpty(SS) then 
     return Zero(Xi);
  end if;
  Irr:=[IrrationalPart(xi) : xi in SS];
  Irr2:=Irr;
  remove_repetitions(~Irr2);
  indices:=[Index(Irr2, irr) : irr in Irr];
  sums:=[&+[SS[i] : i in [1..#indices]| indices[i] eq  j] : j in [1..#Irr2]];
  sums2:=[sum: sum in  sums | not IsZero(sum)];
  require #sums2 le 1 : "The sum of the argument is not simple multivalued section." ;
  if IsEmpty(sums2) then
    return Representative(sums);
  end if;
  return Representative(sums2);
end intrinsic;


intrinsic '-'(xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{Substraction of multi-valued sections. Since we assume the result is again simple multivalued section, the irrational parts must be the same.}
  require Ring(xi1) cmpeq Ring(xi2) : "Arguments must be sections of the same ring.";
  irr1:=IrrationalPart(xi1);
  rat2:=xi2/irr1;
  require IsRational(rat2) :"Arguments must have the same irrational part.";
  rat1:=RationalPart(xi1);
  q:=RationalFunction(rat1) - RationalFunction(rat2);
  xi:=q*irr1;
  return xi;
end intrinsic;


intrinsic 'eq' (xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{Equality of multivalued sections.}
  if IsZero(xi1) then 
    return IsZero(xi2);
  end if;
  return not IsZero(xi2) and IsOne(xi1/xi2);
end intrinsic;
   

intrinsic Power(xi::RngMRadElt, k::FldRatElt) -> RngMRadElt
{}
  require k gt 0 or not IsZero(xi): "Illegal operation (dividing by 0).";  
  factors:=KnownFactors(xi);
  coefficient :=KnownCoefficient(xi);
  for i in [1..#factors] do
     factors[i][2] *:=k;
  end for;
  for i in [1..#coefficient] do
     coefficient[i][2] *:=k;
  end for;
  return CreateMultivaluedSectionWithFactorsAndCoefficient(factors, coefficient);
end intrinsic;

intrinsic Power(xi::RngMRadElt, k::RngIntElt) -> RngMRadElt
{}
  require k gt 0 or not IsZero(xi): "Illegal operation (dividing by 0).";  
  return Power(xi,Rationals()!k);  
end intrinsic;

intrinsic Power(g::RngMPolElt, k::FldRatElt) -> RngMRadElt
{}
  require k gt 0 or not IsZero(g): "Illegal operation (dividing by 0).";  
  return MultivaluedSection(g,k);
end intrinsic;

intrinsic Power(g::FldFunRatElt, k::FldRatElt) -> RngMRadElt
{Multivalued section, which is k-th power of xi or g.}
  require k gt 0 or not IsZero(g): "Illegal operation (dividing by 0).";  
  return MultivaluedSection(g,k);
end intrinsic;


intrinsic '^'(xi::RngMRadElt, k::FldRatElt) -> RngMRadElt
{}
  return Power(xi,k);
end intrinsic;

intrinsic '^'(xi::RngMRadElt, k::RngIntElt) -> RngMRadElt
{}
  require k gt 0 or not IsZero(xi): "Illegal operation (dividing by 0).";
  return Power(xi, Rationals()!k);
end intrinsic;

/*
intrinsic '^'(g::RngMPolElt, k::FldRatElt) -> RngMRadElt
{}
  require k gt 0 or not IsZero(g): "Illegal operation (dividing by 0).";
  return MultivaluedSection(g,k);
end intrinsic;



intrinsic '^'(g::FldFunRatElt, k::FldRatElt) -> RngMRadElt
{Multivalued section, which is k-th power of xi or g.}
  require k gt 0 or not IsZero(g): "Illegal operation (dividing by 0).";  
  return MultivaluedSection(g,k);
end intrinsic;
*/

intrinsic Evaluate(f::RngMPolElt, S::[RngMRadElt] ) -> RngMRadElt
{}
   if &and [IsRational(xi) :xi in S] then 
       return Universe(S)!Evaluate(f, [Ring(Universe(S))|RationalFunction(xi) :  xi in S]);
   end if;
   monomials:=Monomials(f);
   coeffs:=Coefficients(f);
   evals:=[Universe(S)|];
   Vars:=variables_of_ring(Parent(f));
   for i in [1..#coeffs] do
      factors:=Factorisation(monomials[i]);
      evalu:=[Universe(S)!1];
      for p in factors do  
          j:=Index(Vars,base(p));
          Append(~evalu, S[j]^exponent(p));         
      end for;
      Append(~evals, coeffs[i]*(&*evalu));
   end for;
   return Sum(evals);  
end intrinsic;


intrinsic Evaluate(f::FldFunRatMElt, S::[RngMRadElt] ) -> RngMRadElt
{}
   if &and [IsRational(xi) :xi in S] then 
       return Universe(S)!Evaluate(f, [Ring(Universe(S))|RationalFunction(xi) :  xi in S]);
   end if;
   return Evaluate(Numerator(f),S)/Evaluate(Denominator(f),S);  
end intrinsic;


intrinsic Evaluate(f::RngMRadElt, S::[RngMRadElt] ) -> RngMRadElt
{}
   if IsRational(f) and &and [IsRational(xi) :xi in S] then 
       return Universe(S)!Evaluate(RationalFunction(f), [Ring(Universe(S))|RationalFunction(xi) :  xi in S]);
   end if;
   if IsZero(f) then 
      return Zero(Universe(S));
   end if;
   factors:=Factorisation(f);
   ring:=Ring(Representative(S));
   evalu:=MultivaluedSection(ring!1);
   for p in factors do
      evalu *:= Power(Evaluate(base(p), S),exponent(p));
   end for;
   return evalu;
end intrinsic;

intrinsic Evaluate(f::RngMRadElt, S::[RngMPolElt] ) -> RngMRadElt
{Evaluates f at S, i.e. calculates the expression f(S).}
   Xi:=FamilyOfMultivaluedSections(Universe(S));
   if IsRational(f) then 
       return Xi! Evaluate(RationalFunction(f), S);
   end if;
   return Evaluate(f, ChangeUniverse(S, Xi));
end intrinsic;


intrinsic Denominator(xi::RngMRadElt) -> RngMRadElt
{Simplifies the expression of xi and returns the inverse of the product of factors with negative powers.}
  KFs:=Factorisation(xi);
  factors:=[Universe(KFs)|p: p in KFs| exponent(p) lt 0 and not is_scalar(p)];
  xiden:=CreateMultivaluedSectionWithFactors(factors);
  return xiden;
end intrinsic;


intrinsic Numerator(xi::RngMRadElt) -> RngMRadElt
{Simplifies the expression of xi and returns the product of factors with positive powers.}
  KFs:=Factorisation(xi);
  factors:=[Universe(KFs)|p: p in KFs| exponent(p) gt 0 or is_scalar(p)];
  xinum:=CreateMultivaluedSectionWithFactorsAndCoefficient(factors,KnownCoefficient(xi));
  return xinum;
end intrinsic;


intrinsic Multiplicity(xi::RngMRadElt, f::RngMPolElt) -> FldRatElt
{Given irreducible polynomial f and section xi, reduces the multiplicity of xi along the locus f=0.}
    R:=Ring(xi);
    require Parent(f) cmpeq R:"Arguments must be sections of the same ring."; 
    require IsIrreducible(f) : "Argument 2 must be irreducible.";
    KFs:=Factorisation(xi);
    i:=Index([base(p) :  p in KFs], f/LeadingCoefficient(f));
    if IsZero(i) then
      return Zero(Rationals());
    end if;
    return exponent(KFs[i]);
end intrinsic;


intrinsic Exponents(S::[RngMRadElt]) -> SeqEnum, SeqEnum
{}
  KFs:=[Factorisation(xi) : xi in S];
  allfactors:=[base(p) : p in &cat KFs | not is_scalar(p)];
  remove_repetitions(~allfactors);
  mults:=[[Multiplicity(xi,f) : f in allfactors] : xi in S];
  return allfactors, mults;
end intrinsic;

intrinsic Exponents(S::[RngMPolElt]) -> SeqEnum, SeqEnum
{}
  return Exponents(ChangeUniverse(S, FamilyOfMultivaluedSections(Universe(S))));
end intrinsic;

intrinsic Exponents(S::[FldFunRatMElt]) -> SeqEnum, SeqEnum
{Factrorises all multivalued sections in S and returns a sequence of all factors (each factor once) together with sequence of exponents for each xi in S.}
  Xi:=FamilyOfMultivaluedSections(IntegerRing(Universe(S)));
  return Exponents(ChangeUniverse(S, Xi));
end intrinsic;





intrinsic GCD(S::[RngMRadElt]) -> RngMRadElt
{The greatest common divisor of S.}  
  R:=Ring(Universe(S));
  if IsEmpty(S) then
      return Universe(S)!1;
  end if;
  RQ:=Universe(KnownFactors(Representative(S)));
  allfactors,mults:= Exponents(S);
  xi:=CreateMultivaluedSectionWithFactors([elt<RQ|allfactors[i], 
                                           Min([p[i] : p in mults])> : i in [1..#allfactors]]);
  return xi;
end intrinsic;


intrinsic GCD(x::RngMRadElt, y::RngMRadElt) -> RngMRadElt
{The greatest common divisor of x and y.}  
  R:=Ring(x);
  require Ring(y) cmpeq R:"Arguments must be sections of the same ring.";
  return GCD([Parent(x) | x,y]);
end intrinsic;


intrinsic LCM(S::[RngMRadElt]) -> RngMRadElt
{The greatest common divisor of S.}  
  R:=Ring(Universe(S));
  if IsEmpty(S) then
      return Universe(S)!1;
  end if;
  RQ:=Universe(KnownFactors(Representative(S)));
  allfactors,mults:= Exponents(S);
  xi:=CreateMultivaluedSectionWithFactors([elt<RQ|allfactors[i], 
                                           Min([p[i] : p in mults])> : i in [1..#mults]]);
  return xi;
end intrinsic;

/*intrinsic LCM(x::RngMRadElt, y::RngMRadElt) -> RngMRadElt
{The least common multiple of x and y.}  
  R:=Ring(x);
  require Ring(y) cmpeq R:"Arguments must be sections of the same ring.";
  RQ:=Universe(KnownFactors(x));
  allfactors,mult1, mult2:= multiplicities_for_gcd(x,y);
  xi:=CreateMultivaluedSectionWithFactors([elt<RQ|allfactors[i], 
                                           Max(mult1[i], mult2[i])> : i in [1..#mult1]]);
  return xi;
end intrinsic;
*/

intrinsic CommonDenominator(xi1::RngMRadElt, xi2::RngMRadElt) -> RngMRadElt
{Returns the common denominator of xi1 and xi2.}
  require Ring(xi1) cmpeq Ring(xi2):"Arguments must be sections of the same ring.";
  return LCM(Denominator(xi1), Denominator(xi2));
end intrinsic;



