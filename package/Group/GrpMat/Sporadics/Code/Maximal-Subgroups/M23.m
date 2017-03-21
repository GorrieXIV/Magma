freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of M23 */

GeneratorsM23Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w2*w4;
w6:=w3*w5;
w2:=w4*w6;

   return [w1,w2];

end function;

GeneratorsM23Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w2:=w6*w7;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w4:=w5*w2;
w2:=w4*w6;
w4:=w3*w3;
w5:=w3*w4;
w4:=w5*w5;
w3:=w4*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsM23Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w2:=w6*w7;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w4:=w5*w2;
w2:=w4*w6;
w4:=w3*w3;
w5:=w4*w4;
w4:=w5*w5;
w5:=w3*w4;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;

   return [w1,w2];

end function;

GeneratorsM23Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w3;
w5:=w2*w4;
w3:=w4*w4;
w6:=w3*w1;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;
w4:=w6^-1;
w3:=w4*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsM23Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w1:=w2*w3;
w4:=w1*w1;
w1:=w2*w4;
w4:=w1*w3;
w1:=w4*w4;

   return [w1,w2];

end function;

GeneratorsM23Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w3;
w5:=w3*w4;
w7:=w5*w1;
w3:=w4*w5;
w6:=w2*w3;
w4:=w6^-1;
w3:=w4*w1;
w1:=w3*w6;
w4:=w7^-1;
w3:=w4*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsM23Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w2:=w6*w10;
w4:=w7*w8;
w5:=w4*w4;
w4:=w5^-1;
w6:=w5*w2;
w2:=w6*w4;
w9:=w1*w8;
w4:=w3*w3;
w5:=w3*w4;
w3:=w5*w5;
w4:=w3^-1;
w5:=w4*w9;
w1:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of M23 */

DataM23 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M23", generators := [a, b], order := 10200960>,
   
   rec <SporadicRF | name := "M22", parent := "M23", generators := 
   GeneratorsM23Max1(a,b), order := 443520, index := 23>,

   rec <SporadicRF | name := "L3(4):2b", parent := "M23", generators := 
   GeneratorsM23Max2(a,b), order := 40320, index := 253>,

   rec <SporadicRF | name := "2^4:A7", parent := "M23", generators := 
   GeneratorsM23Max3(a,b), order := 40320, index := 253>,

   rec <SporadicRF | name := "A8", parent := "M23", generators := 
   GeneratorsM23Max4(a,b), order := 20160, index := 506>,

   rec <SporadicRF | name := "M11", parent := "M23", generators := 
   GeneratorsM23Max5(a,b), order := 7920, index := 1288>,

   rec <SporadicRF | name := "2^4:(3xA5):2", parent := "M23", generators := 
   GeneratorsM23Max6(a,b), order := 5760, index := 1771>,

   rec <SporadicRF | name := "23:11", parent := "M23", generators := 
   GeneratorsM23Max7(a,b), order := 253, index := 40320>

   ];
   
   return L;
   
end function;

/* code to find standard generators of M23 and produce listing of maximal subgroups */

/* 
MaximalsM23 := function (G)

   x, y := StandardGeneratorsM23(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M23", DataM23());

end function;
*/
