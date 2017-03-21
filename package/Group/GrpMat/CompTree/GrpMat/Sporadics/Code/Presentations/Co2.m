freeze;

/* presentation on standard generators for Co2 */

PresentationCo2 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   return Fct (a) eq 2 and Fct (b) eq 5 and Fct (a * b^2) eq 9 and Fct ((a,b)) eq 4 
   and Fct ((a,b^2)) eq 4 and Fct ((a,b*a*b)) eq 3
   and Fct ((a,b*a*b^2*a*b)) eq 2 and Fct ((a,b*a*b^-2)) eq 3
   and Fct ((a,b^-2*a*b*a*b^-2)) eq 2 and Fct (a*b*a*b^2*a*b^-1*a*b^-2) eq 7;
end function;