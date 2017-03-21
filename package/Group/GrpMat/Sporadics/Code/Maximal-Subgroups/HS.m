freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of HS */

GeneratorsHSMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w2*w5;
w2:=w6*w6;
w5:=w4*w4;
w6:=w4*w5;
w4:=w5*w6;
w3:=w4*w2;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsHSMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w10;
w1:=w10*w11;
w2:=w7*w9;
w6:=w3*w3;
w7:=w6*w6;
w8:=w7^-1;
w6:=w7*w2;
w2:=w6*w8;
w6:=w5^5;
w7:=w6^-1;
w8:=w6*w1;
w1:=w8*w7;

   return [w1,w2];

end function;

GeneratorsHSMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w10;
w1:=w10*w11;
w2:=w7*w9;
w3:=w4*w4;
w4:=w3^-1;
w6:=w4*w2;
w2:=w6*w3;
w6:=w5^5;
w7:=w6^-1;
w8:=w6*w1;
w1:=w8*w7;

   return [w1,w2];

end function;

GeneratorsHSMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w10;
w1:=w10*w11;
w5:=w3*w3;
w6:=w5^-1;
w10:=w6*w1;
w1:=w10*w5;
w2:=w7*w9;
w5:=w4*w4;
w7:=w5*w5;
w8:=w7^-1;
w3:=w8*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsHSMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w10;
w1:=w10*w11;
w5:=w3*w3;
w7:=w3*w5;
w5:=w7*w7;
w7:=w5^-1;
w10:=w7*w1;
w1:=w10*w5;
w5:=w4*w4;
w7:=w4*w5;
w8:=w7^-1;
w3:=w7*w6;
w2:=w3*w8;

   return [w1,w2];

end function;

GeneratorsHSMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w2:=w1*w9;
w4:=w3*w3;
w5:=w3*w4;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;
w6:=w7*w7;
w5:=w7*w6;
w4:=w6*w5;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsHSMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w2*w5;
w1:=w6*w6;
w2:=w5^5;
w5:=w4*w4;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;
w4:=w3*w3;
w5:=w4^-1;
w3:=w5*w1;
w1:=w3*w4;

   return [w1,w2];

end function;

GeneratorsHSMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w2:=w7*w9;
w5:=w3^-1;
w6:=w5*w1;
w1:=w6*w3;
w5:=w4*w4;
w6:=w4*w5;
w7:=w5*w6;
w8:=w7^-1;
w3:=w8*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsHSMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w2;
w2:=w3*w3;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w2:=w7*w9;
w5:=w3^-1;
w6:=w5*w1;
w1:=w6*w3;
w5:=w4*w4;
w6:=w4*w5;
w7:=w5*w6;
w8:=w7^-1;
w3:=w8*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsHSMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w3:=w7*w7;
w4:=w7*w3;
w5:=w3*w4;
w6:=w1*w5;
w5:=w6*w6;
w1:=w6*w5;
w2:=w1*w7;

   return [w1,w2];

end function;

GeneratorsHSMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w9;
w9:=w10*w10;
w6:=w5*w5;
w7:=w9*w6;
w1:=w4^5;
w8:=w7^-1;
w11:=w8*w1;
w2:=w11*w7;
w6:=w5^-1;
w7:=w6*w9;
w8:=w7^-1;
w11:=w8*w1;
w3:=w11*w7;

   return [w2,w3,w4];

end function;

GeneratorsHSMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w5*w2;
w2:=w5*w8;
w6:=w7*w7;
w7:=w6^-1;
w8:=w4*w4;
w9:=w4*w8;
w1:=w8*w9;
w8:=w1*w7;
w1:=w6*w8;

   return [w1,w2];

end function;

/* list of subgroups of HS */

DataHS := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "HS", generators := [a, b], order := 44352000>,
   
   rec <SporadicRF | name := "M22", parent := "HS", generators := 
   GeneratorsHSMax1(a,b), order := 443520, index := 100>,

   rec <SporadicRF | name := "U3(5):2", parent := "HS", generators := 
   GeneratorsHSMax2(a,b), order := 252000, index := 176>,

   rec <SporadicRF | name := "U3(5):2b", parent := "HS", generators := 
   GeneratorsHSMax3(a,b), order := 252000, index := 176>,

   rec <SporadicRF | name := "L3(4):2", parent := "HS", generators := 
   GeneratorsHSMax4(a,b), order := 40320, index := 1100>,

   rec <SporadicRF | name := "S8", parent := "HS", generators := 
   GeneratorsHSMax5(a,b), order := 40320, index := 1100>,

   rec <SporadicRF | name := "2^4.S6", parent := "HS", generators := 
   GeneratorsHSMax6(a,b), order := 11520, index := 3850>,

   rec <SporadicRF | name := "4^3.L3(2)", parent := "HS", generators := 
   GeneratorsHSMax7(a,b), order := 10752, index := 4125>,

   rec <SporadicRF | name := "M11", parent := "HS", generators := 
   GeneratorsHSMax8(a,b), order := 7920, index := 5600>,

   rec <SporadicRF | name := "M11b", parent := "HS", generators := 
   GeneratorsHSMax9(a,b), order := 7920, index := 5600>,

   rec <SporadicRF | name := "4.2^4.S5", parent := "HS", generators := 
   GeneratorsHSMax10(a,b), order := 7680, index := 5775>,

   rec <SporadicRF | name := "2x(A6.2.2)", parent := "HS", generators := 
   GeneratorsHSMax11(a,b), order := 2880, index := 15400>,

   rec <SporadicRF | name := "(5:4)xA5", parent := "HS", generators := 
   GeneratorsHSMax12(a,b), order := 1200, index := 36960>

   ];
   
   return L;
   
end function;

/* code to find standard generators of HS and produce listing of maximal subgroups */

/* 
MaximalsHS := function (G)

   x, y := StandardGeneratorsHS(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "HS", DataHS());

end function;
*/
