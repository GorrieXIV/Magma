freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/M12.m":StandardGeneratorsM12Autm;

/* generators for maximal subgroups of M12:2 */

GeneratorsM12AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w6:=w7*w7;
w1:=w7*w6;
w5:=w3*w3;
w2:=w5*w5;
w3:=w4*w4;
w5:=w4*w3;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;

   return [w1,w2];

end function;

/* list of subgroups of M12:2 */

DataM12Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M12:2", generators := [a, b], order := 190080>,
   
   rec <SporadicRF | name := "M12", parent := "M12:2", generators := 
   GeneratorsM12AutmMax1(a,b), order := 95040, index := 2>
   
   ];
   
   return L;
   
end function;

/* code to find standard generators of M12:2 and produce listing of maximal subgroups */

MaximalsM12Autm := function (G)

   x, y := StandardGeneratorsM12Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M12:2", DataM12Autm());

end function;
