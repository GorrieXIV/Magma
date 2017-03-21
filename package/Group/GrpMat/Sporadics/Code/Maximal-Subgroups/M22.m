freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of M22 */

GeneratorsM22Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w7:=w3^3;
w8:=w7*w6;
w9:=w8^-1;
w10:=w9*w2;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsM22Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5^6;
w7:=w3^4;
w8:=w7*w6;
w9:=w8^-1;
w10:=w9*w4;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsM22Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w3;
w7:=w5^7;
w8:=w6*w7;
w9:=w8^-1;
w10:=w9*w4;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsM22Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3^3;
w8:=w6*w5;
w9:=w8^-1;
w10:=w9*w4;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsM22Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w8:=w5*w10;
w2:=w8*w3;

   return [w1,w2];

end function;

GeneratorsM22Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w3;
w7:=w5^3;
w8:=w6*w7;
w9:=w8^-1;
w10:=w9*w2;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsM22Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w4;
w3:=w7*w2;
w5:=w4^-1;
w6:=w5*w3;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsM22Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w3;
w7:=w5^3;
w8:=w6*w7;
w9:=w8^-1;
w10:=w9*w4;
w2:=w10*w8;

   return [w1,w2];

end function;

/* list of subgroups of M22 */

DataM22 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M22", generators := [a, b], order := 443520>,
   
   rec <SporadicRF | name := "L3(4)", parent := "M22", generators := 
   GeneratorsM22Max1(a,b), order := 20160, index := 22>,

   rec <SporadicRF | name := "2^4:A6", parent := "M22", generators := 
   GeneratorsM22Max2(a,b), order := 5760, index := 77>,

   rec <SporadicRF | name := "A7", parent := "M22", generators := 
   GeneratorsM22Max3(a,b), order := 2520, index := 176>,

   rec <SporadicRF | name := "A7b", parent := "M22", generators := 
   GeneratorsM22Max4(a,b), order := 2520, index := 176>,

   rec <SporadicRF | name := "2^4:S5", parent := "M22", generators := 
   GeneratorsM22Max5(a,b), order := 1920, index := 231>,

   rec <SporadicRF | name := "2^3:L3(2)", parent := "M22", generators := 
   GeneratorsM22Max6(a,b), order := 1344, index := 330>,

   rec <SporadicRF | name := "M10", parent := "M22", generators := 
   GeneratorsM22Max7(a,b), order := 720, index := 616>,

   rec <SporadicRF | name := "L2(11)", parent := "M22", generators := 
   GeneratorsM22Max8(a,b), order := 660, index := 672>

   ];
   
   return L;
   
end function;

/* code to find standard generators of M22 and produce listing of maximal subgroups */

/* 
MaximalsM22 := function (G)

   x, y := StandardGeneratorsM22(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M22", DataM22());

end function;
*/
