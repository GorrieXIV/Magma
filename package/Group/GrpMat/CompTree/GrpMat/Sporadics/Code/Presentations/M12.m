freeze;

/* presentation on standard generators for M12 */

// intrinsic PresentationM12 (G :: GrpMat : UserGenerators := [], 
// Projective := false) -> BoolElt 
// {Do the generators of G satisfy (projectively) the standard presentation for M12?}

PresentationM12 := function (G : UserGenerators := [], Projective := false)
   Fct := Projective select CentralOrder else Order;
   if #UserGenerators eq 0 then 
      UserGenerators := [G.i : i in [1..Ngens (G)]];
   end if;
   if #UserGenerators ne 2 then "Require 2 user generators"; 
                           return false; end if;
   a := UserGenerators[1]; b := UserGenerators[2];
   return Fct (a) eq 2 and Fct (b) eq 3 and Fct (a * b) eq 11 and Fct ((a,b)) eq 6 
   and Fct (a*b*a*b*a*b^-1) eq 6;
//end intrinsic;
 end function;
