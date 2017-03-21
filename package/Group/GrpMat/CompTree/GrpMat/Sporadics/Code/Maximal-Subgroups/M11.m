freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of M11 */

GeneratorsM11Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w5:=w4*w4;
w6:=w5^-1;
w4:=w6*w7;
w2:=w4*w5;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsM11Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w2:=w4*w4;

   return [w1,w2];

end function;

GeneratorsM11Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3*w3;
w5:=w4^-1;
w3:=w5*w1;
w1:=w3*w4;

   return [w1,w2];

end function;

GeneratorsM11Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w3*w4;
w3:=w5*w4;
w2:=w3*w3;

   return [w1,w2];

end function;

GeneratorsM11Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w3;
w2:=w5*w5;

   return [w1,w2];

end function;

/* list of subgroups of M11 */

DataM11 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M11", generators := [a, b], order := 7920>,
   
   rec <SporadicRF | name := "M10", parent := "M11", generators := 
   GeneratorsM11Max1(a,b), order := 720, index := 11>,
   
   rec <SporadicRF | name := "L2(11)", parent := "M11", generators := 
   GeneratorsM11Max2(a,b), order := 660, index := 12>,

   rec <SporadicRF | name := "M9:2", parent := "M11", generators := 
   GeneratorsM11Max3(a,b), order := 144, index := 55>,

   rec <SporadicRF | name := "S5", parent := "M11", generators := 
   GeneratorsM11Max4(a,b), order := 120, index := 66>,

   rec <SporadicRF | name := "2S4", parent := "M11", generators := 
   GeneratorsM11Max5(a,b), order := 48, index := 165>
  
   ];
   
   return L;
   
end function;

/* code to find standard generators of M11 and produce listing of maximal subgroups */

/* 
MaximalsM11 := function (G)

   x, y := StandardGeneratorsM11(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M11", DataM11());

end function;
*/
