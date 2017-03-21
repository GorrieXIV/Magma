freeze;

CheckFunctionField := function(F)
   if Degree(F) ne Infinity() then
     return false, "Function field must be over its constant field";
   end if;

   if Genus(F) ne 0 then
     return false, "Genus of function field is not zero";
   end if;

   return true, "Argument is ok";
end function;
 
intrinsic Parametrization(F::FldFun, D::DivFunElt) -> FldFunElt, SeqEnum
{Parametrization for the algebraic function field F defined
by the divisor D of degree one};
 
   ok, mess := CheckFunctionField(F);
   require ok : mess;
 
   require Degree(D) eq 1 :
     "Divisor does not have degree one";

   require FunctionField(D) eq F : "Argument 2 must be a divisor of argument 1";

   assert Rank(Parent(DefiningPolynomial(F))) eq 2;
 
   ka := FunctionField(ConstantField(F)); a := ka.1;

   if IsRationalFunctionField(F) and TotalDegree(DefiningPolynomial(F)) eq 1 then
       return F.1, [ a ];
   end if;
 
   if Degree(DefiningPolynomial(F), 1) eq 0 then
       _, b := IsConstant(F.2);
       return F.1, [ a, b ];
   end if;
 
   if Degree(DefiningPolynomial(F), 2) eq 0 then
       _, b := IsConstant(F.1);
       return F.2, [ b, a ];
   end if;
 
   /*
   For rational function field with polynomial degree 2, this is the same as
    - rewrite the polynomial to be recursive over $.2
    - solve for $.1 (ie. $.1 = (some function in $.2) =: f($.2)
    - return F.1, [f(a), a]
   but maybe slower??
   */
   kaxy<x, y> := PolynomialRing(ka, 2);
 
   aa := Representative( [ b : b in Basis(D) | not IsConstant(b) ] );
 
   f := kaxy!DefiningPolynomial(F);
   h := (kaxy!Denominator(r)) * a - (kaxy!Numerator(r))
        where r is RationalFunction(aa);

   xa := Resultant(f, h, 2);
   ya := Resultant(f, h, 1);
 
   // Add the extra 0s to coeffs since in case z==<x,1> the constant
   // term 0 will not be listed among the coeffs and c[2] will be undef'd.
   xa := [ - c[2] / c[1] where c is Coefficients(z[1]) cat [0]
           : z in Factorization(xa) | Degree(z[1], 1) eq 1 ];
   xa := [ z : z in xa | not IsConstant(z) ];
   ya := [ - c[2] / c[1] where c is Coefficients(z[1]) cat [0]
           : z in Factorization(ya) | Degree(z[1], 2) eq 1 ];
   ya := [ z : z in ya | not IsConstant(z) ];
 
   for xxa in xa do
     for yya in ya do
       if Evaluate(f, [xxa, yya]) eq 0 then
           return aa, [xxa, yya];
       end if;
     end for;
   end for;
 
   // should never happen
   require false : "Algorithm failed";
 
end intrinsic;

