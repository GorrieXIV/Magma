freeze;

import "../recformat.m":SporadicRF;
 
/* generators for maximal subgroups of ON */

GeneratorsONMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsONMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w6:=w5^-1;
w3:=w2^-1;
w4:=w2*w1;
w1:=w4*w3;
w4:=w6*w3;
w2:=w4*w5;

   return [w1,w2];

end function;

GeneratorsONMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w8:=w9*w9;
w2:=w8*w8;
w6:=w5^6;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;
w5:=w4^7;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;

   return [w1,w2];

end function;

GeneratorsONMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5^10;
w7:=w6*w2;
w8:=w2*w6;
w9:=w8^-1;
w6:=w9*w7;
w1:=w6^14;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsONMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w7*w8;
w2:=w9*w9;
w1:=w9*w9;
w7:=w6*w4;
w8:=w7^19;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w4*w6;
w8:=w7^17;
w6:=w5*w4;
w7:=w6*w3;
w9:=w7^8;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsONMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w7*w8;
w2:=w9*w9;
w1:=w9*w9;
w7:=w6*w4;
w8:=w7^19;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w8:=w4*w6;
w6:=w5*w4;
w7:=w6*w3;
w9:=w7^12;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsONMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w4:=w5*w2;
w5:=w4*w4;
w2:=w5*w5;
w4:=w3*w3;
w5:=w3*w4;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;

   return [w1,w2];

end function;

GeneratorsONMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w4:=w5*w3;
w3:=w4*w4;
w2:=w3*w3;
w4:=w5*w5;
w3:=w5*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsONMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w8:=w9*w9;
w2:=w8*w8;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsONMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w7*w8;
w2:=w9*w9;
w7:=w6*w4;
w8:=w7^4;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w4*w6;
w8:=w7^19;
w6:=w5*w4;
w7:=w6*w3;
w9:=w7^2;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsONMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w7*w8;
w2:=w9*w9;
w7:=w6*w4;
w8:=w7^14;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w4*w6;
w8:=w7^2;
w6:=w5*w4;
w9:=w6*w3;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsONMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w9:=w2*w5;
w2:=w9*w9;
w8:=w6*w4;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w4*w6;
w8:=w7^10;
w6:=w5*w4;
w7:=w6*w3;
w9:=w7^3;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

GeneratorsONMax13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w9:=w2*w5;
w2:=w9*w9;
w7:=w6*w4;
w8:=w7^13;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w4*w6;
w8:=w7^27;
w6:=w5*w4;
w7:=w6*w3;
w9:=w7^3;
w7:=w8*w9;
w6:=w7^-1;
w8:=w6*w2;
w2:=w8*w7;

   return [w1,w2];

end function;

/* list of subgroups of ON */

DataON := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "ON", generators := [a, b], order := 460815505920>,
   
   rec <SporadicRF | name := "L3(7):2", parent := "ON", generators := 
   GeneratorsONMax1(a,b), order := 3753792, index := 122760>,

   rec <SporadicRF | name := "L3(7):2b", parent := "ON", generators := 
   GeneratorsONMax2(a,b), order := 3753792, index := 122760>,

   rec <SporadicRF | name := "J1", parent := "ON", generators := 
   GeneratorsONMax3(a,b), order := 175560, index := 2624832>,

   rec <SporadicRF | name := "4.L3(4):2", parent := "ON", generators := 
   GeneratorsONMax4(a,b), order := 161280, index := 2857239>,

   rec <SporadicRF | name := "((3^2:4)xA6).2", parent := "ON", generators := 
   GeneratorsONMax5(a,b), order := 25920, index := 17778376>,

   rec <SporadicRF | name := "3^4:2^(1+4).D10", parent := "ON", generators := 
   GeneratorsONMax6(a,b), order := 25920, index := 17778376>,

   rec <SporadicRF | name := "L2(31)", parent := "ON", generators := 
   GeneratorsONMax7(a,b), order := 14880, index := 30968784>,

   rec <SporadicRF | name := "L2(31)b", parent := "ON", generators := 
   GeneratorsONMax8(a,b), order := 14880, index := 30968784>,

   rec <SporadicRF | name := "4^3.L3(2)", parent := "ON", generators := 
   GeneratorsONMax9(a,b), order := 10752, index := 42858585>,

   rec <SporadicRF | name := "M11", parent := "ON", generators := 
   GeneratorsONMax10(a,b), order := 7920, index := 58183776>,

   rec <SporadicRF | name := "M11b", parent := "ON", generators := 
   GeneratorsONMax11(a,b), order := 7920, index := 58183776>,

   rec <SporadicRF | name := "A7", parent := "ON", generators := 
   GeneratorsONMax12(a,b), order := 2520, index := 182863296>,

   rec <SporadicRF | name := "A7b", parent := "ON", generators := 
   GeneratorsONMax13(a,b), order := 2520, index := 182863296>

   ];
   
   return L;
   
end function;

/* code to find standard generators of O'N and produce listing of maximal subgroups */

/* 
MaximalsON := function (G)

   x, y := StandardGeneratorsON(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "ON", DataON());

end function;
*/
