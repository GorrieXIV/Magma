freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/Fi22.m":StandardGeneratorsFi22Autm;

/* generators for maximal subgroups of Fi22:2 */

GeneratorsFi22AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w4*w5;
w4:=w3*w3;
w5:=w3*w4;
w3:=w4*w5;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of Fi22:2 */

DataFi22Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Fi22:2", generators := [a, b], order := 129123503308800>,
   
   rec <SporadicRF | name := "Fi22", parent := "Fi22:2", generators := 
   GeneratorsFi22AutmMax1(a,b), order := 64561751654400, index := 2>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Fi22:2 and produce listing of maximal subgroups */

MaximalsFi22Autm := function (G)

   x, y := StandardGeneratorsFi22Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Fi22:2", DataFi22Autm());

end function;
