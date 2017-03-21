freeze;



/* presentation on standard generators for McL:2 */

PresentationMcLAutm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   return Fct (c) eq 2 and Fct (d) eq 3 and Fct (c*d) eq 22 and Fct (c*d*c*d*c*d^-1) eq 6
   and Fct ((c,(d*c*d*c*d^-1*c)^2*d*c*d^-1*c*d^-1)) eq 1 and Fct ((c,d^-1*c*d*c*d)) eq 4
   and Fct ((c*d)^6*c*d^-1*c*d*(c*d*c*d*c*d^-1)^2*(c*d*c*d^-1)^2*c*d*c*d*c*d^-1*(c*d)^4*(c*d^-1)^6*c*d*c*d*c*d^-1) eq 1
   and Fct ((c*d)^5*c*d^-1*(c*d)^3*(c*d^-1*c*d^-1*c*d)^2*c*d*(c*d*c*d^-1*c*d^-1)^2*(c*d*c*d^-1)^3*c*d^-1*c*d*(c*d*c*d*c*d^-1)^2) eq 1;
end function;