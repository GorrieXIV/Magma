freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Co2 */

GeneratorsCo2Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w2:=w3*w3;

   return [w1,w2];

end function;

GeneratorsCo2Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w10:=w5*w5;
w1:=w10*w10;
w10:=w3*w3;
w9:=w10*w10;
w11:=w10*w3;
w3:=w9*w11;
w9:=w7*w7;
w4:=w9*w9;
w9:=w8*w8;
w10:=w9*w9;
w6:=w9*w10;
w7:=w4*w6;
w6:=w7^-1;
w8:=w6*w3;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsCo2Max3 := function (a,b)

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
w9:=w11*w11;
w8:=w10*w11;
w1:=w9*w8;
w10:=w3*w3;
w11:=w5*w5;
w8:=w11*w11;
w9:=w10*w8;
w10:=w6*w6;
w11:=w10*w10;
w6:=w10*w11;
w8:=w9^-1;
w10:=w8*w6;
w2:=w10*w9;

   return [w1,w2];

end function;

GeneratorsCo2Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w10:=w5*w5;
w1:=w10*w10;
w10:=w3*w3;
w9:=w10*w10;
w11:=w10*w3;
w3:=w9*w11;
w9:=w7*w7;
w11:=w8*w8;
w10:=w11*w8;
w6:=w9*w10;
w7:=w6^-1;
w8:=w7*w3;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsCo2Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w8:=w7*w7;
w6:=w7*w8;
w7:=w3*w3;
w3:=w7*w7;
w9:=w4*w4;
w10:=w3*w9;
w8:=w10^-1;
w7:=w8*w6;
w2:=w7*w10;

   return [w1,w2];

end function;

GeneratorsCo2Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w7*w7;
w11:=w8*w8;
w10:=w9*w11;
w9:=w10^-1;
w11:=w9*w2;
w2:=w11*w10;

   return [w1,w2];

end function;

GeneratorsCo2Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w5*w8;
w10:=w9*w9;
w11:=w10*w10;
w10:=w9*w11;
w9:=w4^-1;
w11:=w9*w10;
w1:=w11*w4;
w9:=w5*w7;
w10:=w5*w8;
w11:=w9*w10;
w9:=w11*w11;
w2:=w9*w11;

   return [w1,w2];

end function;

GeneratorsCo2Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w3;
w7:=w6*w5;
w5:=w3*w3;
w6:=w4*w4;
w4:=w5*w6;
w2:=w4*w3;
w6:=w7^-1;
w3:=w1*w6;
w4:=w1*w7;
w1:=w3*w4;

   return [w1,w2];

end function;

GeneratorsCo2Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w6:=w7*w10;
w8:=w4*w5;
w11:=w6*w8;
w6:=w11*w11;
w1:=w6*w6;
w5:=w3*w3;
w7:=w4*w4;
w8:=w5*w7;
w9:=w8^-1;
w10:=w9*w6;
w2:=w10*w8;
w3:=w1*w2;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;
w4:=w3*w2;
w5:=w4*w4;
w4:=w5*w5;
w3:=w5*w2;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsCo2Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w4:=w5*w8;
w1:=w4^5;
w4:=w5^3;
w5:=w6^17;
w6:=w9^24;
w7:=w5*w6;
w8:=w7^-1;
w6:=w8*w4;
w2:=w6*w7;

   return [w1,w2];

end function;

GeneratorsCo2Max11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w2;
w1:=w4^3;
w4:=w5*w5;
w5:=w3*w3;
w2:=w5*w4;
w4:=w2^5;
w5:=w6^20;
w6:=w3^6;
w3:=w5*w6;
w5:=w3^-1;
w6:=w5*w4;
w2:=w6*w3;

   return [w1,w2];

end function;

/* list of subgroups of Co2 */

DataCo2 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Co2", generators := [a, b], order := 42305421312000>,
   
   rec <SporadicRF | name := "U6(2):2", parent := "Co2", generators := 
   GeneratorsCo2Max1(a,b), order := 18393661440, index := 2300>,

   rec <SporadicRF | name := "2^10:M22:2", parent := "Co2", generators := 
   GeneratorsCo2Max2(a,b), order := 908328960, index := 46575>,

   rec <SporadicRF | name := "McL", parent := "Co2", generators := 
   GeneratorsCo2Max3(a,b), order := 898128000, index := 47104>,

   rec <SporadicRF | name := "2^(1+8).S6(2)", parent := "Co2", generators := 
   GeneratorsCo2Max4(a,b), order := 743178240, index := 56925>,

   rec <SporadicRF | name := "HS:2", parent := "Co2", generators := 
   GeneratorsCo2Max5(a,b), order := 88704000, index := 476928>,

   rec <SporadicRF | name := "(2^4x2^(1+6)).A8", parent := "Co2", generators := 
   GeneratorsCo2Max6(a,b), order := 41287680, index := 1024650>,

   rec <SporadicRF | name := "U4(3):D8", parent := "Co2", generators := 
   GeneratorsCo2Max7(a,b), order := 26127360, index := 1619200>,

   rec <SporadicRF | name := "2^(4+10).(S5xS3)", parent := "Co2", generators := 
   GeneratorsCo2Max8(a,b), order := 11796480, index := 3586275>,

   rec <SporadicRF | name := "M23", parent := "Co2", generators := 
   GeneratorsCo2Max9(a,b), order := 10200960, index := 4147200>,

   rec <SporadicRF | name := "3^(1+4).2^(1+4).S5", parent := "Co2", generators := 
   GeneratorsCo2Max10(a,b), order := 933120, index := 45337600>,

   rec <SporadicRF | name := "5^(1+2):4S4", parent := "Co2", generators := 
   GeneratorsCo2Max11(a,b), order := 12000, index := 3525451776>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Co2 and produce listing of maximal subgroups */

/* 
MaximalsCo2 := function (G)

   x, y := StandardGeneratorsCo2(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Co2", DataCo2());

end function;
*/
