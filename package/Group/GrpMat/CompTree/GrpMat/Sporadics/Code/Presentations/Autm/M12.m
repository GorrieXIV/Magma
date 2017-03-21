freeze;



/* presentation on standard generators for M12:2 */

PresentationM12Autm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   return Fct (c) eq 2 and Fct (d) eq 3 and Fct (c * d) eq 12
   and Fct ((c*d)^5*(c,d)*(c*d^-1)^3*c*d*(c,d^-1)^2*c*d*c*d*(c*d^-1)^3*(c,d^-1)) eq 1;
end function;