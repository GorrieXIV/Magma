freeze;



/* presentation on standard generators for He.2 */

PresentationHeAutm := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   c := UserGenerators[1]; d := UserGenerators[2];
   "Warning: presentation not available";
   return Fct (c) eq 2 and Fct (d) eq 6; //not complete
end function;