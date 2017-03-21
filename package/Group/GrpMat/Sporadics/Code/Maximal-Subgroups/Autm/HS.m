freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/HS.m":StandardGeneratorsHSAutm;

/* generators for maximal subgroups of HS.2 */

GeneratorsHSAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4^10;
w1:=w3^-1*w6*w3;
w6:=w4^4;
w7:=w5^4;
w2:=w7^-1*w6*w7;

   return [w1,w2];

end function;

/* list of subgroups of HS:2 */

DataHSAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "HS:2", generators := [a, b], order := 88704000>,
   
   rec <SporadicRF | name := "HS", parent := "HS:2", generators := 
   GeneratorsHSAutmMax1(a,b), order := 44352000, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of HS:2 and 
   produce listing of maximal subgroups */

MaximalsHSAutm := function (G)

   x, y := StandardGeneratorsHSAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "HS:2", DataHSAutm());

end function;
