freeze;



/* presentation on standard generators for M22.2 */

PresentationM22Autm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   return Fct (c) eq 2 and Fct (d) eq 4 and Fct (c * d) eq 11
   and Fct (c*d) eq 11 and Fct (c*d^2) eq 6 and Fct ((c,d)) eq 4
   and Fct (c*d*c*d*c*d^2*c*d^2) eq 3;
end function;