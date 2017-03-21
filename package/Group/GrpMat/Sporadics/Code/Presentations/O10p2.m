freeze;

/* presentation on standard generators for O10p2 */

PresentationO10p2 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   x := UserGenerators[1]; y := UserGenerators[2];
   // this is presentation for O10:2 not O10 
   // relators := {x^2, y^16,(x,y^2)^2,(x,y^3)^3,(x,y^4)^2,(x,y^5)^2,(x,y^6)^2,
   //		(x,y^7)^2,(x*y^8)^4,(x*y^2*x*y^2*x*y^-1)^9};
   // return relators eq {Identity(G)};
   return true;
end function;
