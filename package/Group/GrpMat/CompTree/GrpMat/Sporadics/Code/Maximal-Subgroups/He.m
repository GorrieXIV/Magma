freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of He */

GeneratorsHeMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w2*w9;
w2:=w10^7;
w7:=w4^7;
w8:=w7^-1;
w9:=w8*w2;
w2:=w9*w7;

   return [w1,w2];

end function;

GeneratorsHeMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsHeMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w2;
w7:=w6*w2;
w8:=w7*w2;
w3:=w7*w5;
w4:=w6*w8;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsHeMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w2;
w7:=w6*w2;
w8:=w7*w2;
w3:=w7*w4;
w4:=w6*w8;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsHeMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w2^-1;
w4:=w1*w2;
w5:=w4*w2;
w1:=w5*w2;
w5:=w1^4;
w4:=w5*w3;
w3:=w5*w2;
w5:=w3*w4;
w6:=w5*w5;
w5:=w4*w3;
w4:=w5*w5;
w2:=w4*w6;

   return [w1,w2];

end function;

GeneratorsHeMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^5;
w5:=w2*w2;
w3:=w5*w1;
w1:=w4*w3;

   return [w1,w2];

end function;

GeneratorsHeMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w2^3;
w7:=w5*w6;
w8:=w6*w4;
w9:=w8*w7;
w2:=w9*w5;

   return [w1,w2];

end function;

GeneratorsHeMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w2:=w4*w4;
w6:=w2*w2;
w1:=w2*w6;
w4:=w3^7;
w6:=w4^-1;
w7:=w6*w1;
w1:=w7*w4;
w6:=w5^5;
w5:=w6^-1;
w7:=w5*w2;
w2:=w7*w6;

   return [w1,w2];

end function;

GeneratorsHeMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w5*w5;
w1:=w5*w2;
w5:=w3*w4;
w6:=w5*w5;
w5:=w6^-1;
w4:=w5*w1;
w1:=w4*w6;
w4:=w3^6;
w3:=w4^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsHeMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w5*w5;
w1:=w5*w5;
w5:=w3*w4;
w6:=w5^11;
w5:=w6^-1;
w4:=w5*w1;
w1:=w4*w6;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsHeMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w2;
w7:=w6*w2;
w6:=w5*w7;
w2:=w6*w3;

   return [w1,w2];

end function;

/* list of subgroups of He */

DataHe := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "He", generators := [a, b], order := 4030387200>,
   
   rec <SporadicRF | name := "S4(4):2", parent := "He", generators := 
   GeneratorsHeMax1(a,b), order := 1958400, index := 2058>,

   rec <SporadicRF | name := "2^2.L3(4).S3", parent := "He", generators := 
   GeneratorsHeMax2(a,b), order := 483840, index := 8330>,

   rec <SporadicRF | name := "2^6:3.S6", parent := "He", generators := 
   GeneratorsHeMax3(a,b), order := 138240, index := 29155>,

   rec <SporadicRF | name := "2^6:3.S6b", parent := "He", generators := 
   GeneratorsHeMax4(a,b), order := 138240, index := 29155>,

   rec <SporadicRF | name := "2^(1+6)L3(2)", parent := "He", generators := 
   GeneratorsHeMax5(a,b), order := 21504, index := 187425>,

   rec <SporadicRF | name := "7^2:2.L2(7)", parent := "He", generators := 
   GeneratorsHeMax6(a,b), order := 16464, index := 244800>,

   rec <SporadicRF | name := "3.S7", parent := "He", generators := 
   GeneratorsHeMax7(a,b), order := 15120, index := 266560>,

   rec <SporadicRF | name := "7^(1+2):(3xS3)", parent := "He", generators := 
   GeneratorsHeMax8(a,b), order := 6174, index := 652800>,

   rec <SporadicRF | name := "S4xL3(2)", parent := "He", generators := 
   GeneratorsHeMax9(a,b), order := 4032, index := 999600>,

   rec <SporadicRF | name := "(7:3)xL3(2)", parent := "He", generators := 
   GeneratorsHeMax10(a,b), order := 3528, index := 1142400>,

   rec <SporadicRF | name := "5^2:4A4", parent := "He", generators := 
   GeneratorsHeMax11(a,b), order := 1200, index := 3358656>

   ];
   
   return L;
   
end function;

/* code to find standard generators of He and produce listing of maximal subgroups */

/* 
MaximalsHe := function (G)

   x, y := StandardGeneratorsHe(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "He", DataHe());

end function;
*/
