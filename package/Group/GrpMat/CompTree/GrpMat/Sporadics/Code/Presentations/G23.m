freeze;

/* presentation on standard generators for G23 */

PresentationG23 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   relators := {a^2, b^3, (a*b)^13, (a,b)^13, 
		a*b*a*b*(a,b)^4*(a*b)^3*(a,b*a*b)^3,
		(((a*b)^3*a*b^(-1))^2*(a*b)^2*(a*b^(-1))^2)^2};
   return relators eq {Identity(G)};
end function;