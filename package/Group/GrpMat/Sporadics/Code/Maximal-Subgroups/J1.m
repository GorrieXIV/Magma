freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of J1 */

GeneratorsJ1Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w4:=w3*w3;
w3:=w4^-1;
w6:=w3*w1;
w1:=w6*w4;
w4:=w5*w5;
w3:=w4*w4;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsJ1Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6*w3;
w6:=w5*w5;
w7:=w5*w6;
w5:=w6*w7;
w6:=w3*w5;
w7:=w6^-1;
w3:=w7*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsJ1Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w7:=w3*w6;
w3:=w7*w7;
w2:=w3*w7;
w3:=w7*w6;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsJ1Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w3;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w5:=w4*w4;
w3:=w4*w5;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsJ1Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w8:=w7*w7;
w2:=w7*w8;
w5:=w4*w4;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsJ1Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w4:=w3*w3;
w6:=w5*w5;
w7:=w5*w6;
w8:=w4*w7;
w9:=w8^-1;
w3:=w9*w2;
w2:=w3*w8;
w3:=w1*w2;
w7:=w6^-1;
w8:=w4*w7;
w9:=w8^-1;
w4:=w9*w3;
w2:=w4*w8;

   return [w1,w2];

end function;

GeneratorsJ1Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3*w3;
w5:=w3*w4;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;

   return [w1,w2];

end function;

/* list of subgroups of J1 */

DataJ1 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J1", generators := [a, b], order := 175560>,
   
   rec <SporadicRF | name := "L2(11)", parent := "J1", generators := 
   GeneratorsJ1Max1(a,b), order := 660, index := 266>,

   rec <SporadicRF | name := "2^3:7:3", parent := "J1", generators := 
   GeneratorsJ1Max2(a,b), order := 168, index := 1045>,

   rec <SporadicRF | name := "2xA5", parent := "J1", generators := 
   GeneratorsJ1Max3(a,b), order := 120, index := 1463>,

   rec <SporadicRF | name := "19:6", parent := "J1", generators := 
   GeneratorsJ1Max4(a,b), order := 114, index := 1540>,

   rec <SporadicRF | name := "11:10", parent := "J1", generators := 
   GeneratorsJ1Max5(a,b), order := 110, index := 1596>,

   rec <SporadicRF | name := "D6xD10", parent := "J1", generators := 
   GeneratorsJ1Max6(a,b), order := 60, index := 2926>,

   rec <SporadicRF | name := "7:6", parent := "J1", generators := 
   GeneratorsJ1Max7(a,b), order := 42, index := 4180>

   ];
   
   return L;
   
end function;

/* code to find standard generators of J1 and produce listing of maximal subgroups */

/* 
MaximalsJ1 := function (G)

   x, y := StandardGenerators(G, "J1");
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J1", DataJ1());

end function;
*/
