freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Ly */

GeneratorsLyMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w9:=w5*w2;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w7;
w2:=w7*w8;
w3:=w9^7;
w4:=w3^-1;
w5:=w3*w1;
w1:=w5*w4;
w8:=w6^25;
w7:=w8^-1;
w3:=w7*w2;
w2:=w3*w8;

   return [w1,w2];

end function;

GeneratorsLyMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w9:=w2*w5;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w7;
w2:=w7*w8;
w3:=w6^15;
w4:=w3^-1;
w5:=w3*w1;
w1:=w5*w4;
w8:=w9^12;
w7:=w8^-1;
w3:=w7*w2;
w2:=w3*w8;

   return [w1,w2];

end function;

GeneratorsLyMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w5:=w3^-1;
w9:=w5*w1;
w1:=w9*w3;
w2:=w7^3;
w6:=w4^12;
w5:=w6^-1;
w3:=w5*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsLyMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w4:=w3^7;
w5:=w4*w10;
w6:=w10*w4;
w7:=w6^-1;
w6:=w7*w5;
w7:=w6^10;
w2:=w10*w7;
w4:=w1*w1;
w1:=w4*w3;

   return [w1,w2];

end function;

GeneratorsLyMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w4:=w3^7;
w5:=w4*w10;
w6:=w10*w4;
w7:=w6^-1;
w6:=w7*w5;
w7:=w6^10;
w12:=w10*w7;
w4:=w1*w1;
w11:=w4*w3;
w3:=w11*w12;
w4:=w3*w12;
w5:=w3^5;
w6:=w5*w5;
w3:=w4^-1;
w7:=w4*w6;
w6:=w7*w3;
w7:=w6^-1;
w8:=w7*w5;
w5:=w8*w6;
w3:=w2^-1;
w6:=w5^4;
w7:=w3*w6;
w6:=w7*w2;
w7:=w4*w5;
w8:=w7*w5;
w9:=w7*w8;
w10:=w7*w9;
w8:=w10*w9;
w7:=w8*w8;
w8:=w6*w7;
w10:=w8^11;
w9:=w2*w10;
w8:=w9^-1;
w10:=w8*w11;
w11:=w10*w9;
w10:=w8*w12;
w12:=w10*w9;
w3:=w11*w12;
w6:=w3^8;
w7:=w3*w12;
w8:=w3*w7;
w7:=w3*w8;
w8:=w7^5;
w7:=w8*w6;
w8:=w7^-1;
w9:=w8*w6;
w10:=w9*w7;
w1:=w4*w10;
w6:=w7*w5;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsLyMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w2:=w8^3;
w3:=w5*w7;
w5:=w3^31;
w3:=w5^-1;
w8:=w3*w1;
w1:=w8*w5;
w3:=w4*w6;
w4:=w3^13;
w3:=w4^-1;
w8:=w4*w2;
w2:=w8*w3;

   return [w1,w2];

end function;

GeneratorsLyMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w2;
w7:=w6*w5;
w6:=w7*w3;
w5:=w4^4;
w7:=w5*w6;
w6:=w3*w7;
w7:=w6^12;
w3:=w2^-1;
w4:=w7*w3;
w3:=w7*w2;
w5:=w4*w3;
w4:=w5^3;
w2:=w1*w4;
w1:=w7*w6;
w7:=w6*w4;
w5:=w6*w7;
w3:=w2*w5;
w7:=w6*w5;
w2:=w3*w7;
w3:=w2*w4;
w5:=w7*w7;
w2:=w3*w5;
w7:=w6^5;
w3:=w2*w7;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsLyMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w3:=w4*w2;
w2:=w5*w3;
w5:=w2*w3;
w2:=w6^17;
w3:=w4^21;
w7:=w2*w3;
w2:=w7^-1;
w3:=w2*w1;
w1:=w3*w7;
w2:=w4^16;
w3:=w6^30;
w7:=w2*w3;
w6:=w7^-1;
w3:=w6*w5;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsLyMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7^3;
w7:=w6^7;
w6:=w7^-1;
w4:=w7*w1;
w7:=w4*w6;
w4:=w5*w3;
w5:=w4^15;
w4:=w5^-1;
w9:=w5*w8;
w8:=w9*w4;
w2:=w7*w8;
w3:=w2^3;
w4:=w1*w3;
w1:=w4^20;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w1:=w9^3;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w9:=w3^3;
w10:=w4^5;
w8:=w9*w10;
w9:=w8^-1;
w10:=w9*w2;
w1:=w10*w8;
w2:=w6^8;
w4:=w3^-1;
w5:=w3*w2;
w2:=w5*w4;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w9:=w6*w3;
w4:=w3*w3;
w3:=w4^-1;
w10:=w3*w9;
w2:=w10*w4;
w3:=w7*w2;
w1:=w3^9;

   return [w1,w2];

end function;

/* list of subgroups of Ly */

DataLy := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Ly", generators := [a, b], order := 51765179004000000>,
   
   rec <SporadicRF | name := "G2(5)", parent := "Ly", generators := 
   GeneratorsLyMax1(a,b), order := 5859000000, index := 8835156>,

   rec <SporadicRF | name := "3.McL:2", parent := "Ly", generators := 
   GeneratorsLyMax2(a,b), order := 5388768000, index := 9606125>,

   rec <SporadicRF | name := "5^3.L3(5)", parent := "Ly", generators := 
   GeneratorsLyMax3(a,b), order := 46500000, index := 1113229656>,

   rec <SporadicRF | name := "2.A11", parent := "Ly", generators := 
   GeneratorsLyMax4(a,b), order := 39916800, index := 1296826875>,

   rec <SporadicRF | name := "5^(1+4):4.S6", parent := "Ly", generators := 
   GeneratorsLyMax5(a,b), order := 9000000, index := 5751686556>,

   rec <SporadicRF | name := "3^5:(2xM11)", parent := "Ly", generators := 
   GeneratorsLyMax6(a,b), order := 3849120, index := 13448575000>,

   rec <SporadicRF | name := "3^(2+4):2.A5.D8", parent := "Ly", generators := 
   GeneratorsLyMax7(a,b), order := 699840, index := 73967162500>,

   rec <SporadicRF | name := "67:22", parent := "Ly", generators := 
   GeneratorsLyMax8(a,b), order := 1474, index := 35118846000000>,

   rec <SporadicRF | name := "37:18", parent := "Ly", generators := 
   GeneratorsLyMax9(a,b), order := 666, index := 77725494000000>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Ly and produce listing of maximal subgroups */

/* 
MaximalsLy := function (G)

   x, y := StandardGeneratorsLy(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Ly", DataLy());

end function;

*/
