freeze;

/* presentation on standard generators for He */

PresentationHe := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   return Fct (a) eq 2 and Fct (b) eq 7 and Fct (a * b) eq 17
   and Fct ((a,b*a*b*a*b^-1*a*b*a*b)) eq 1
   and Fct ((a,b^3)) eq 5 and Fct ((a,b)) eq 6
   and Fct ((a*b)^4*a*b^2*a*b^-3*a*b*a*b*a*b^-1*a*b^3*a*b^-2*a*b^2) eq 1;
end function;