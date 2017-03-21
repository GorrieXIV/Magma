freeze;

/* presentation on standard generators for 2.U63 */

Presentation2U63 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2];
   // "Warning: presentation not available";
   return true;
end function;
