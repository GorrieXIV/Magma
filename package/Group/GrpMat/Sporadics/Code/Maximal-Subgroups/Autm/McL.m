freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/McL.m":StandardGeneratorsMcLAutm;

/* generators for maximal subgroups of McL:2 */

GeneratorsMcLAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w7;
w1:=w8^12;
w6:=w3^-1;
w7:=w6*w1;
w1:=w7*w3;
w6:=w5*w5;
w2:=w5*w6;
w5:=w4*w4;
w6:=w4*w5;
w7:=w6^-1;
w5:=w7*w2;
w2:=w5*w6;

   return [w1,w2];

end function;

/* list of subgroups of McL:2 */

DataMcLAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "McL:2", generators := [a, b], order := 1796256000>,
   
   rec <SporadicRF | name := "McL", parent := "McL:2", generators := 
   GeneratorsMcLAutmMax1(a,b), order := 898128000, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of McL:2 and produce listing of maximal subgroups */

MaximalsMcLAutm := function (G)

   x, y := StandardGeneratorsMcLAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "McL:2", DataMcLAutm());

end function;
