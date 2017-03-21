freeze;

/* presentation on standard generators for J4 */

PresentationJ4 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 3 then "Require 3 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2]; t := UserGenerators[3];
   // "Warning: presentation not available";
   return true;
end function;
