freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Th; 
   Note: Generators for Max6 - Max11, Max 14, Max 15 are unknown */

GeneratorsThMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w8:=w7*w9;
w2:=w8^5;
w4:=w3^8;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsThMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w3;
w6:=w5*w5;
w5:=w3^15;
w7:=w4^9;
w8:=w5*w7;
w5:=w3^12;
w7:=w8*w5;
w5:=w4^16;
w8:=w7*w5;
w5:=w3^17;
w7:=w8*w5;
w8:=w7^-1;
w3:=w8*w6;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsThMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w1*w6;
w8:=w6*w1;
w9:=w8^-1;
w8:=w9*w7;
w9:=w8^9;
w2:=w7*w9;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w7:=w1*w10;
w8:=w10*w1;
w9:=w8^-1;
w8:=w9*w7;
w1:=w8^14;

   return [w1,w2];

end function;

GeneratorsThMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4^-1;
w3:=w5*w2;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsThMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w8:=w3*w7;
w2:=w8^5;
w5:=w3*w10;
w6:=w5*w4;
w7:=w9*w6;
w8:=w6*w9;
w6:=w7^27;
w7:=w8^7;
w8:=w6*w7;
w7:=w8^-1;
w5:=w7*w1;
w1:=w5*w8;
w5:=w4*w9;
w6:=w5*w3;
w7:=w10*w6;
w8:=w7^10;
w7:=w8^-1;
w5:=w7*w2;
w2:=w5*w8;

   return [w1,w2];

end function;

GeneratorsThMax6 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax7 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax9 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax10 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax11 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^6;
w5:=w4^6;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;
w4:=w3*w3;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsThMax13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^6;
w5:=w4^8;
w4:=w5^-1;
w6:=w4*w1;
w1:=w6*w5;
w4:=w3^8;
w3:=w4^-1;
w6:=w3*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsThMax14 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax15 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsThMax16 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w3*w7;
w2:=w8^5;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w4*w9;
w12:=w11*w3;
w11:=w12*w10;
w13:=w10*w12;
w8:=w13^29;
w6:=w11^23;
w7:=w8*w6;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;
w5:=w9*w3;
w6:=w10*w4;
w4:=w5*w6;
w3:=w4^27;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of Th */

DataTh := function ()
   "Note: Generators for Max6 - Max11, Max 14, Max 15 are unknown";

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Th", generators := [a, b], order := 90745943887872000>,
   
   rec <SporadicRF | name := "^3D4(2):3", parent := "Th", generators := 
   GeneratorsThMax1(a,b), order := 634023936, index := 143127000>,

   rec <SporadicRF | name := "2^5.L5(2)", parent := "Th", generators := 
   GeneratorsThMax2(a,b), order := 319979520, index := 283599225>,

   rec <SporadicRF | name := "2^(1+8).A9", parent := "Th", generators := 
   GeneratorsThMax3(a,b), order := 92897280, index := 976841775>,

   rec <SporadicRF | name := "U3(8):6", parent := "Th", generators := 
   GeneratorsThMax4(a,b), order := 33094656, index := 2742012000>,

   rec <SporadicRF | name := "(3xG2(3)):2", parent := "Th", generators := 
   GeneratorsThMax5(a,b), order := 25474176, index := 3562272000>,

   rec <SporadicRF | name := "3.[3^8].2S4", parent := "Th", generators := 
   GeneratorsThMax6(a,b), order := 944784, index := 96049408000>,

   rec <SporadicRF | name := "3^2.[3^7].2S4", parent := "Th", generators := 
   GeneratorsThMax7(a,b), order := 944784, index := 96049408000>,

   rec <SporadicRF | name := "3^5:2.S6", parent := "Th", generators := 
   GeneratorsThMax8(a,b), order := 349920, index := 259333401600>,

   rec <SporadicRF | name := "5^(1+2):4S4", parent := "Th", generators := 
   GeneratorsThMax9(a,b), order := 12000, index := 7562161990656>,

   rec <SporadicRF | name := "5^2:GL2(5)", parent := "Th", generators := 
   GeneratorsThMax10(a,b), order := 12000, index := 7562161990656>,

   rec <SporadicRF | name := "7^2:(3x2S4)", parent := "Th", generators := 
   GeneratorsThMax11(a,b), order := 7056, index := 12860819712000>,

   rec <SporadicRF | name := "L2(19):2", parent := "Th", generators := 
   GeneratorsThMax12(a,b), order := 6840, index := 13266950860800>,

   rec <SporadicRF | name := "L3(3)", parent := "Th", generators := 
   GeneratorsThMax13(a,b), order := 5616, index := 16158465792000>,

   rec <SporadicRF | name := "M10", parent := "Th", generators := 
   GeneratorsThMax14(a,b), order := 720, index := 22442313600>,

   rec <SporadicRF | name := "31:15", parent := "Th", generators := 
   GeneratorsThMax15(a,b), order := 465, index := 195152567500800>,

   rec <SporadicRF | name := "S5", parent := "Th", generators := 
   GeneratorsThMax16(a,b), order := 120, index := 756216199065600>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Th and produce listing of maximal subgroups */

/* 
MaximalsTh := function (G)

   x, y := StandardGeneratorsTh(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Th", DataTh());

end function;
*/
