freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/Fi24.m":StandardGeneratorsFi24Autm;

/* generators for maximal subgroups of Fi24':2 */

GeneratorsFi24AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w1:=w4^10;
w2:=w7^8;
w6:=w5^10;
w7:=w6^-1;
w3:=w7*w2;
w2:=w3*w6;

   return [];

end function;

/* list of subgroups of Fi24'.2 */

DataFi24Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Fi24':2", generators := [a, b], order := 2510411418381323442585600>,

   rec <SporadicRF | name := "Fi24'", parent := "Fi24':2", generators := 
   GeneratorsFi24AutmMax1(a,b), order := 1255205709190661721292800, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Fi24':2 and 
   produce listing of maximal subgroups */

MaximalsFi24Autm := function (G)

   x, y := StandardGeneratorsFi24Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Fi24':2", DataFi24Autm());

end function;
