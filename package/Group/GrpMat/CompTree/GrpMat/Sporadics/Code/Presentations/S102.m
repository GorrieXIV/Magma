freeze;

/* presentation on standard generators for S102 */

PresentationS102 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2];
   relators := {x^2, y^11, (x*y)^15, (x*y^5)^18, (x,y)^3, (x,y^2)^2,(x,y^3)^2,
		(x,y^4)^2, (x,y^5)^3, (x,(x*y)^5)^2};
   return relators eq {Identity(G)};
end function;
