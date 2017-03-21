freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/M22.m":StandardGeneratorsM22Autm;

/* generators for maximal subgroups of M22.2 */

GeneratorsM22AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w1:=w2*w2;
w2:=w7*w7;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

/* list of subgroups of M22:2 */

DataM22Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M22:2", generators := [a, b], order := 887040>,
   
   rec <SporadicRF | name := "M22", parent := "M22:2", generators := 
   GeneratorsM22AutmMax1(a,b), order := 443520, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of M22:2 and produce listing of maximal subgroups */

MaximalsM22Autm := function (G)

   x, y := StandardGeneratorsM22Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M22:2", DataM22Autm());

end function;
