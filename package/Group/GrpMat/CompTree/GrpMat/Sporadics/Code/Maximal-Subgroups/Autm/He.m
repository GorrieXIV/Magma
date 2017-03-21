freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/He.m":StandardGeneratorsHeAutm;

/* generators for maximal subgroups of He:2 */

GeneratorsHeAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w2:=w6*w7;
w7:=w4*w4;
w8:=w7^-1;
w9:=w8*w2;
w2:=w9*w7;
w7:=w6*w5;
w8:=w7*w3;
w1:=w8^14;

   return [w1,w2];

end function;

/* list of subgroups of He.2 */

DataHeAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "He:2", generators := [a, b], order := 8060774400>,
   
   rec <SporadicRF | name := "He", parent := "He:2", generators := 
   GeneratorsHeAutmMax1(a,b), order := 4030387200, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of He.2 and produce listing of maximal subgroups */

MaximalsHeAutm := function (G)

   x, y := StandardGeneratorsHeAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "He:2", DataHeAutm());

end function;
