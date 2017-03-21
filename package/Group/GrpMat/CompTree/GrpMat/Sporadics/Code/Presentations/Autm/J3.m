freeze;



/* presentation on standard generators for J3:2 */

PresentationJ3Autm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   return Fct (c) eq 2 and Fct (d) eq 3 and Fct (c*d) eq 24 and Fct ((c,d)) eq 9
   and Fct (c*d*(c*d*c*d^-1)^2) eq 4 and Fct (c*d*c*d*c*d^-1*(c*d*c*d*c*d^-1*c*d^-1)^2) eq 2
   and Fct ((c,(d*c)^4*(d^-1*c)^2*d)) eq 2 and Fct ((c,d*(c*d^-1)^2*(c*d)^4)) eq 2;
end function;