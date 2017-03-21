freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/Suz.m":StandardGeneratorsSuzAutm;

/* generators for maximal subgroups of Suz:2 */

GeneratorsSuzAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w1:=w3^14;
w5:=w4*w4;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;

   return [w1,w2];

end function;

/* list of subgroups of Suz.2 */

DataSuzAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Suz:2", generators := [a, b], order := 896690995200>,
   
   rec <SporadicRF | name := "Suz", parent := "Suz:2", generators := 
   GeneratorsSuzAutmMax1(a,b), order := 448345497600, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Suz:2 and produce listing of maximal subgroups */

MaximalSuzAutm := function (G)

   x, y := StandardGeneratorsSuzAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Suz:2", DataSuzAutm());

end function;
