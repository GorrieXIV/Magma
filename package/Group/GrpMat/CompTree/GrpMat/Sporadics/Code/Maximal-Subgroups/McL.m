freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of McL */

GeneratorsMcLMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w2*w9;
w5:=w4*w4;
w6:=w5*w5;
w7:=w4*w6;
w8:=w7^-1;
w9:=w8*w10;
w2:=w9*w7;

   return [w1,w2];

end function;

GeneratorsMcLMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w2:=w6*w7;
w5:=w4*w4;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w5:=w3*w3;
w6:=w5*w5;
w5:=w6^-1;
w7:=w6*w2;
w2:=w7*w5;

   return [w1,w2];

end function;

GeneratorsMcLMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w2:=w6*w7;
w5:=w3*w3;
w6:=w5^-1;
w7:=w5*w1;
w1:=w7*w6;
w5:=w4*w4;
w6:=w5*w5;
w5:=w6^-1;
w7:=w6*w2;
w2:=w7*w5;

   return [w1,w2];

end function;

GeneratorsMcLMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w4;
w12:=w3*w11;
w13:=w12*w3;
w14:=w13*w4;
w13:=w11*w14;
w1:=w13*w13;
w8:=w9*w9;
w7:=w9*w8;
w6:=w7^-1;
w5:=w6*w1;
w1:=w5*w7;
w9:=w4*w10;
w8:=w9^15;
w7:=w8^-1;
w6:=w7*w2;
w2:=w6*w8;

   return [w1,w2];

end function;

GeneratorsMcLMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w1:=w4*w4;
w5:=w3*w4;
w6:=w5*w2;
w2:=w6*w4;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsMcLMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w2*w8;
w6:=w5*w5;
w7:=w5*w6;
w6:=w7^-1;
w8:=w6*w9;
w2:=w8*w7;
w5:=w4*w4;
w6:=w4*w5;
w7:=w5*w6;
w8:=w7^-1;
w9:=w8*w1;
w1:=w9*w7;

   return [w1,w2];

end function;

GeneratorsMcLMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w8:=w2*w9;
w6:=w4*w4;
w4:=w6^-1;
w7:=w6*w1;
w1:=w7*w4;
w4:=w5*w5;
w3:=w5*w4;
w5:=w3*w4;
w6:=w5^-1;
w9:=w6*w8;
w2:=w9*w5;

   return [w1,w2];

end function;

GeneratorsMcLMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w1:=w3*w4;
w2:=w4*w3;
w3:=w1^7;
w4:=w2^7;
w5:=w3*w4;
w3:=w5*w5;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsMcLMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w2*w4;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsMcLMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3*w3;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;
w3:=w1*w2;
w4:=w3*w2;
w5:=w2*w4;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsMcLMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2^-1;
w5:=w4*w1;
w1:=w5*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w2:=w6*w7;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4*w4;
w3:=w5*w2;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsMcLMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w2;
w2:=w6*w4;
w7:=w4*w4;
w1:=w7*w7;
w6:=w5*w5;
w5:=w6*w6;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w5:=w4*w3;
w4:=w5*w5;
w5:=w4*w4;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;

   return [w1,w2];

end function;

/* list of subgroups of McL */

DataMcL := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "McL", generators := [a, b], order := 898128000>,
   
   rec <SporadicRF | name := "U4(3)", parent := "McL", generators := 
   GeneratorsMcLMax1(a,b), order := 3265920, index := 275>,

   rec <SporadicRF | name := "M22", parent := "McL", generators := 
   GeneratorsMcLMax2(a,b), order := 443520, index := 2025>,

   rec <SporadicRF | name := "M22b", parent := "McL", generators := 
   GeneratorsMcLMax3(a,b), order := 443520, index := 2025>,

   rec <SporadicRF | name := "U3(5)", parent := "McL", generators := 
   GeneratorsMcLMax4(a,b), order := 126000, index := 7128>,

   rec <SporadicRF | name := "3^(1+4):2.S5", parent := "McL", generators := 
   GeneratorsMcLMax5(a,b), order := 58320, index := 15400>,

   rec <SporadicRF | name := "3^4:M10", parent := "McL", generators := 
   GeneratorsMcLMax6(a,b), order := 58320, index := 15400>,

   rec <SporadicRF | name := "L3(4):2", parent := "McL", generators := 
   GeneratorsMcLMax7(a,b), order := 40320, index := 22275>,

   rec <SporadicRF | name := "2.A8", parent := "McL", generators := 
   GeneratorsMcLMax8(a,b), order := 40320, index := 22275>,

   rec <SporadicRF | name := "2^4:A7", parent := "McL", generators := 
   GeneratorsMcLMax9(a,b), order := 40320, index := 22275>,

   rec <SporadicRF | name := "2^4:A7b", parent := "McL", generators := 
   GeneratorsMcLMax10(a,b), order := 40320, index := 22275>,

   rec <SporadicRF | name := "M11", parent := "McL", generators := 
   GeneratorsMcLMax11(a,b), order := 7920, index := 113400>,

   rec <SporadicRF | name := "5^(1+2):3:8", parent := "McL", generators := 
   GeneratorsMcLMax12(a,b), order := 3000, index := 299376>

   ];
   
   return L;
   
end function;

/* code to find standard generators of McL and produce listing of maximal subgroups */

/* 
MaximalsMcL := function (G)

   x, y := StandardGeneratorsMcL(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "McL", DataMcL());

end function;
*/
