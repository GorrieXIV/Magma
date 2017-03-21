freeze;

/* presentation on standard generators for U37 */

PresentationU37 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2];
   relators := {x^2,y^3,(x*y)^43,(x,y)^4,(x,y*x*y*x*y*x*y)^3,
		x*y*(x*y*x*y*x*y^-1)^2*((x*y)^3*(x*y^-1)^3)^3};
   return relators eq {Identity(G)};
end function;
