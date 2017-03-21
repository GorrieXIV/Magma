freeze;

/* presentation on standard generators for J3 */

PresentationJ3 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   return Fct (a) eq 2 and Fct (b) eq 3 and Fct (a * b) eq 19
   and Fct ((a,b)) eq 9 and Fct ((a*b)^6*(a*b^-1)^5) eq 2
   and Fct ((a*b*a*b*a*b^-1)^2*a*b*a*b^-1*a*b^-1*a*b*a*b^-1) eq 2
   and Fct (a*b*a*b*(a*b*a*b^-1)^3*a*b*a*b*(a*b*a*b^-1)^4*a*b^-1*(a*b*a*b^-1)^3) eq 1
   and Fct (a*b*a*b*a*b*a*b*a*b^-1*a*b*a*b^-1) eq 4;
end function;
