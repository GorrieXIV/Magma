freeze;



/* presentation on standard generators for Fi22:2 */

PresentationFi22Autm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   return Fct (c) eq 2 and Fct (d) eq 18 and Fct ((c,d)) eq 3 and Fct ((c,d^2)) eq 3
   and Fct ((c,d^3)) eq 3 and Fct ((c,d^4)) eq 3 and Fct ((c,d^5)) eq 3
   and Fct ((c,d^6)) eq 2 and Fct ((c,d^7)) eq 2 and Fct ((c,d^8)) eq 3
   and Fct (c*d^9) eq 4 and Fct ((c,d*c*d*c*d^-2*c*d)) eq 1
   and Fct ((c,d^2*c*d^2*c*d^-4*c*d^2)) eq 1 and Fct ((c*d^3)^4*c*d^-4) eq 2
   and Fct (c*d^4*c*d^5*c*d^5) eq 5 and Fct (c*d*c*d^-3) eq 8;
end function;