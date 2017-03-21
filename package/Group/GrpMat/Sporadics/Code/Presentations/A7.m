freeze;

/* presentation on standard generators for A7 */

PresentationA7 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2];
   relators := {x^3,y^5,(x*y)^7,(x*x^y)^2,(x*y^(-2)*x*y^2)^2};
   return relators eq {Identity(G)};
end function;
