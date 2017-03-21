freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/J2.m":StandardGeneratorsJ2Autm;

/* generators for maximal subgroups of J2:2 */

GeneratorsJ2AutmMax1 := function (a,b)
   w1 := a; w2 := b;
   return [w1,w2];
end function;

/* list of subgroups of J2:2 */

DataJ2Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J2:2", generators := [a, b], order := 1209600>,
   
   rec <SporadicRF | name := "J2", parent := "J2:2", generators := 
   GeneratorsJ2AutmMax1(a,b), order := 604800, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of J2:2 and 
   produce listing of maximal subgroups */

MaximalsJ2Autm := function (G)

   x, y := StandardGeneratorsJ2Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J2:2", DataJ2Autm());

end function;
