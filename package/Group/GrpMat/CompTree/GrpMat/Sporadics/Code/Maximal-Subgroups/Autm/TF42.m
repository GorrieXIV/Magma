freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/TF42.m":StandardGeneratorsTF42Autm;

/* generators for maximal subgroups of TF42.2 */

GeneratorsTF42AutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w3;
w5:=w4*w4;
w3:=w4*w2;
w4:=w3*w3;
w3:=w4*w2;
w4:=w1*w3;
w3:=w5*w4;
w5:=w4^-1;
w2:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of TF42.2 */

DataTF42Autm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "TF42:2", generators := [a, b], order := 35942400>,
   
   rec <SporadicRF | name := "TF42", parent := "TF42:2", generators := 
   GeneratorsTF42AutmMax1(a,b), order := 17971200, index := 2>
 
   ];
   
   return L;
   
end function;

/* code to find standard generators of TF42:2 
   and produce listing of maximal subgroups */

MaximalTF42Autm := function (G)

   x, y := StandardGeneratorsTF42Autm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "TF42:2", DataTF42Autm());

end function;
