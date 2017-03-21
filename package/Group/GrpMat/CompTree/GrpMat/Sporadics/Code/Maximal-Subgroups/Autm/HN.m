freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/HN.m":StandardGeneratorsHNAutm;

/* generators for maximal subgroups of HN:2 */

GeneratorsHNAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w7:=w5*w6;
w2:=w6*w7;
w6:=w4*w4;
w7:=w6*w6;
w8:=w7*w7;
w9:=w6*w8;
w10:=w8*w2;
w2:=w10*w9;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w9:=w10*w10;
w8:=w10*w9;
w7:=w9*w8;
w1:=w7*w7;
w4:=w3*w3;
w5:=w3*w4;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;

   return [w1,w2];

end function;

/* list of subgroups of HN:2 */

DataHNAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "HN:2", generators := [a, b], order := 546061824000000>,
   
   rec <SporadicRF | name := "HN", parent := "HN:2", generators := 
   GeneratorsHNAutmMax1(a,b), order := 273030912000000, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of HN:2 and 
   produce listing of maximal subgroups */

MaximalsHNAutm := function (G)

   x, y := StandardGeneratorsHNAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "HN:2", DataHNAutm());

end function;
