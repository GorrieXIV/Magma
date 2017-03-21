freeze;

/* presentation on standard generators for HS */

PresentationHS := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   return Fct (a) eq 2 and Fct (b) eq 5 and Fct (a*b) eq 11 and Fct (a*b^2) eq 10
   and Fct ((a,b)) eq 5 and Fct ((a,b^2)) eq 6 and Fct ((a,b*a*b)) eq 3
   and Fct (a*b*a*b*a*b^2*a*b^-1*a*b^-2*a*b^-1*a*b^2*a*b*a*b*(a*b^-2)^4) eq 1
   and Fct (a*b*(a*b^2*(a*b^-2)^2)^2*a*b^2*a*b*a*b^2*(a*b^-1*a*b^2)^2) eq 1
   and Fct (a*b*a*b*(a*b^2)^2*a*b*(a*b^-1)^2*a*b*(a*b^2)^2*a*b*a*b*a*b^-2*a*b^-1*a*b^-2) eq 1;
end function;