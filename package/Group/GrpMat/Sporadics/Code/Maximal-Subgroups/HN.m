freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of HN; 
   Note: Generators for Max8, Max9, Max13 are unknown */

GeneratorsHNMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w9:=w10*w10;
w8:=w10*w9;
w2:=w9*w8;

   return [w1,w2];

end function;

GeneratorsHNMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w2:=w3*w4;
w6:=w3*w2;
w7:=w6*w3;
w5:=w6^-1;
w3:=w6*w1;
w1:=w3*w5;
w6:=w7*w7;
w5:=w6^-1;
w3:=w5*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsHNMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6^10;
w5:=w4^2;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;
w4:=w3^5;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsHNMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^5;
w5:=w4^9;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;
w4:=w3^2;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsHNMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w2:=w3*w4;
w6:=w3*w2;
w7:=w3^9;
w8:=w6^4;
w9:=w8^-1;
w10:=w7*w9;
w11:=w10^-1;
w12:=w11*w1;
w13:=w12*w10;
w7:=w6*w3;
w5:=w6^-1;
w3:=w6*w1;
w1:=w3*w5;
w6:=w7*w7;
w5:=w6^-1;
w3:=w5*w2;
w2:=w3*w6;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w5:=w10^15;
w6:=w8^3;
w11:=w5*w6;
w5:=w3*w4;
w6:=w4^10;
w1:=w3^-1*w6*w3;
w6:=w4^4;
w7:=w5^4;
w2:=w7^-1*w6*w7;
w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w1:=w5^5;
w5:=w4*w3;
w6:=w3*w3;
w7:=w5*w6;
w8:=w6*w5;
w9:=w8*w7;
w8:=w6*w9;
w7:=w4*w8;
w4:=w3^-1;
w5:=w4*w7;
w12:=w11^-1;
w10:=w11*w13;
w9:=w10*w12;
w2:=w5*w9;

   return [w1,w2];

end function;

GeneratorsHNMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w22:=w6^5;
w5:=w4^9;
w6:=w5^-1;
w4:=w6*w22;
w22:=w4*w5;
w4:=w3^2;
w5:=w4^-1;
w6:=w5*w1;
w21:=w6*w4;
w3:=w21*w22;
w4:=w3*w22;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w22;
w31:=w6*w5;
w4:=w3*w3;
w32:=w3*w4;
w3:=w31*w32;
w33:=w31*w32;
w4:=w3*w32;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w4;
w12:=w3*w11;
w13:=w12*w3;
w14:=w13*w4;
w15:=w14*w4;
w24:=w7*w15;
w25:=w3^4;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w25*w7;
w9:=w7*w25;
w10:=w9^-1;
w9:=w10*w8;
w10:=w9*w9;
w2:=w7*w10;
w3:=w33*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7^3;
w9:=w5^13;
w10:=w8*w9;
w11:=w10^-1;
w3:=w24^10;
w4:=w11*w3;
w3:=w4*w10;
w2:=w32*w3;
w4:=w31*w3;
w1:=w4*w3;

   return [w1,w2];

end function;

GeneratorsHNMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w2:=w3*w4;
w5:=w3^-1;
w6:=w5*w1;
w1:=w6*w3;
w3:=w4^5;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsHNMax8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsHNMax9 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsHNMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w3:=w1*w6;
w4:=w3*w8;
w3:=w4^19;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;
w1:=w6^10;

   return [w1,w2];

end function;

GeneratorsHNMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w4;
w12:=w3*w11;
w14:=w12*w5;
w15:=w14*w4;
w16:=w5*w15;
w17:=w16*w5;
w1:=w6^10;
w3:=w8*w17;
w4:=w3^4;
w3:=w4^-1;
w5:=w4*w1;
w1:=w5*w3;
w3:=w17*w8;
w4:=w3^14;
w3:=w4^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsHNMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w5;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w4;
w12:=w3*w11;
w14:=w12*w5;
w15:=w14*w4;
w16:=w5*w15;
w17:=w16*w5;
w1:=w6^10;
w3:=w7*w17;
w4:=w3^8;
w3:=w4^-1;
w5:=w4*w1;
w1:=w5*w3;
w3:=w17*w7;
w4:=w3^9;
w3:=w4^-1;
w5:=w3*w2;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsHNMax13 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsHNMax14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6^10;
w5:=w4^8;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;
w4:=w3^9;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

/* list of subgroups of HN */

DataHN := function ()

   "Note: Generators for Max8, Max9, Max13 are unknown";

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "HN", generators := [a, b], order := 273030912000000>,
   
   rec <SporadicRF | name := "A12", parent := "HN", generators := 
   GeneratorsHNMax1(a,b), order := 239500800, index := 1140000>,

   rec <SporadicRF | name := "2.HS.2", parent := "HN", generators := 
   GeneratorsHNMax2(a,b), order := 177408000, index := 1539000>,

   rec <SporadicRF | name := "U3(8):3", parent := "HN", generators := 
   GeneratorsHNMax3(a,b), order := 16547328, index := 16500000>,

   rec <SporadicRF | name := "2^(1+8).(A5xA5).2", parent := "HN", generators := 
   GeneratorsHNMax4(a,b), order := 3686400, index := 74064375>,

   rec <SporadicRF | name := "(D10xU3(5)).2", parent := "HN", generators := 
   GeneratorsHNMax5(a,b), order := 2520000, index := 108345600>,

   rec <SporadicRF | name := "5^(1+4).2^(1+4).5.4", parent := "HN", generators := 
   GeneratorsHNMax6(a,b), order := 2000000, index := 136515456>,

   rec <SporadicRF | name := "2^6.U4(2)", parent := "HN", generators := 
   GeneratorsHNMax7(a,b), order := 1658880, index := 164587500>,

   rec <SporadicRF | name := "(A6xA6).D8", parent := "HN", generators := 
   GeneratorsHNMax8(a,b), order := 1036800, index := 263340000>,

   rec <SporadicRF | name := "2^(3+2+6).(3xL3(2))", parent := "HN", generators := 
   GeneratorsHNMax9(a,b), order := 1032192, index := 264515625>,

   rec <SporadicRF | name := "5^(2+1+2).4.A5", parent := "HN", generators := 
   GeneratorsHNMax10(a,b), order := 750000, index := 364041216>,

   rec <SporadicRF | name := "M12:2", parent := "HN", generators := 
   GeneratorsHNMax11(a,b), order := 190080, index := 1436400000>,

   rec <SporadicRF | name := "M12:2b", parent := "HN", generators := 
   GeneratorsHNMax12(a,b), order := 190080, index := 1436400000>,

   rec <SporadicRF | name := "3^4:2.(A4xA4).4", parent := "HN", generators := 
   GeneratorsHNMax13(a,b), order := 93312, index := 2926000000>,

   rec <SporadicRF | name := "3^(1+4):4.A5", parent := "HN", generators := 
   GeneratorsHNMax14(a,b), order := 58320, index := 4681600000>

   ];
   
   return L;
   
end function;

/* code to find standard generators of HN and produce listing of maximal subgroups */

/* 
MaximalsHN := function (G)

   x, y := StandardGeneratorsHN(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "HN", DataHN());

end function;
*/
