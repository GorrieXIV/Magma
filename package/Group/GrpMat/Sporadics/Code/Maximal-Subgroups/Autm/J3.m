freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/J3.m":StandardGeneratorsJ3Autm;

/* generators for maximal subgroups of J3:2 */

GeneratorsJ3AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w1:=w3^12;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;

   return [w1,w2];

end function;

/* list of subgroups of J3:2 */

DataJ3Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J3:2", generators := [a, b], order := 100465920>,
   
   rec <SporadicRF | name := "J3", parent := "J3:2", generators := 
   GeneratorsJ3AutmMax1(a,b), order := 50232960, index := 2>

   ];
   
   return L;

  
end function;

/* code to find standard generators of J3:2 and produce listing of maximal subgroups */

MaximalsJ3Autm := function (G)

   x, y := StandardGeneratorsJ3Autm(G);
x;
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J3:2", DataJ3Autm());

end function;
