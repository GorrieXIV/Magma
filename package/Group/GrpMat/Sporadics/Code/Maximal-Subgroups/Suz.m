freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Suz */

GeneratorsSuzMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6^6;
w2:=w5^3;
w5:=w4^4;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3^5;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w5:=w3*w10;
w2:=w5*w5;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsSuzMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w3:=w8*w8;
w1:=w3*w3;
w3:=w7*w9;
w4:=w3*w3;
w5:=w3*w4;
w2:=w5*w5;
w5:=w7^9;
w6:=w5^-1;
w7:=w5*w2;
w2:=w7*w6;

   return [w1,w2];

end function;

GeneratorsSuzMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w2:=w5*w6;
w5:=w4*w4;
w6:=w5*w5;
w4:=w5*w6;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsSuzMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w7:=w3*w6;
w8:=w7*w7;
w1:=w8*w8;
w2:=w8*w1;
w6:=w4^5;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;
w4:=w3^6;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w2:=w5*w6;
w5:=w4*w4;
w6:=w5*w5;
w4:=w5*w6;
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

GeneratorsSuzMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w2:=w8*w8;
w5:=w4^6;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3^5;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^6;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w9:=w5*w10;
w2:=w9^3;
w6:=w7^4;
w7:=w5^4;
w4:=w7*w6;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;
w4:=w3*w2;
w5:=w3*w4;
w2:=w5^5;
w6:=w3*w5;
w3:=w6^9;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsSuzMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4^6;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w9:=w5*w10;
w8:=w9^3;
w4:=w3^12;
w3:=w4^-1;
w9:=w3*w8;
w1:=w9*w4;
w6:=w5^12;
w5:=w7^3;
w7:=w6*w5;
w6:=w7^-1;
w9:=w6*w8;
w2:=w9*w7;

   return [w1,w2];

end function;

GeneratorsSuzMax12 := function (a,b)

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
w9:=w5*w10;
w8:=w9^3;
w5:=w3*w6;
w6:=w5^7;
w9:=w7^12;
w7:=w6*w9;
w6:=w7^-1;
w9:=w6*w8;
w1:=w9*w7;
w13:=w12^6;
w10:=w11*w3;
w9:=w13*w10;
w13:=w9^-1;
w7:=w13*w8;
w2:=w7*w9;

   return [w1,w2];

end function;

GeneratorsSuzMax13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w7:=w6*w8;
w2:=w7*w7;
w5:=w4*w4;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3*w3;
w3:=w4^-1;
w5:=w3*w2;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w7:=w6*w8;
w2:=w7*w7;
w6:=w4*w4;
w5:=w4*w6;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3*w3;
w3:=w4^-1;
w5:=w3*w2;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsSuzMax15 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w3*w6;
w8:=w7^-1;
w2:=w5^5;
w3:=w8*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsSuzMax16 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w8:=w3*w10;
w2:=w8*w8;
w8:=w7*w7;
w9:=w8^-1;
w10:=w9*w1;
w1:=w10*w8;
w7:=w3*w6;
w8:=w7*w7;
w9:=w7*w8;
w3:=w8*w9;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of Suz */

DataSuz := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Suz", generators := [a, b], order := 448345497600>,
   
   rec <SporadicRF | name := "G2(4)", parent := "Suz", generators := 
   GeneratorsSuzMax1(a,b), order := 251596800, index := 1782>,

   rec <SporadicRF | name := "3.U4(3):2", parent := "Suz", generators := 
   GeneratorsSuzMax2(a,b), order := 19595520, index := 22880>,

   rec <SporadicRF | name := "U5(2)", parent := "Suz", generators := 
   GeneratorsSuzMax3(a,b), order := 13685760, index := 32760>,

   rec <SporadicRF | name := "2^(1+6).U4(2)", parent := "Suz", generators := 
   GeneratorsSuzMax4(a,b), order := 3317760, index := 135135>,

   rec <SporadicRF | name := "3^5:M11", parent := "Suz", generators := 
   GeneratorsSuzMax5(a,b), order := 1924560, index := 232960>,

   rec <SporadicRF | name := "J2:2", parent := "Suz", generators := 
   GeneratorsSuzMax6(a,b), order := 1209600, index := 370656>,

   rec <SporadicRF | name := "2^(4+6):3.A6", parent := "Suz", generators := 
   GeneratorsSuzMax7(a,b), order := 1105920, index := 405405>,

   rec <SporadicRF | name := "(A4xL3(4)):2", parent := "Suz", generators := 
   GeneratorsSuzMax8(a,b), order := 483840, index := 926640>,

   rec <SporadicRF | name := "2^(2+8):(A5xS3)", parent := "Suz", generators := 
   GeneratorsSuzMax9(a,b), order := 368640, index := 1216215>,

   rec <SporadicRF | name := "M12:2", parent := "Suz", generators := 
   GeneratorsSuzMax10(a,b), order := 190080, index := 2358720>,

   rec <SporadicRF | name := "(A6xA5).2", parent := "Suz", generators := 
   GeneratorsSuzMax11(a,b), order := 43200, index := 10378368>,

   rec <SporadicRF | name := "(A6x(3^2:4)).2", parent := "Suz", generators := 
   GeneratorsSuzMax12(a,b), order := 25920, index := 17297280>,

   rec <SporadicRF | name := "L3(3):2", parent := "Suz", generators := 
   GeneratorsSuzMax13(a,b), order := 11232, index := 39916800>,

   rec <SporadicRF | name := "L3(3):2b", parent := "Suz", generators := 
   GeneratorsSuzMax14(a,b), order := 11232, index := 39916800>,

   rec <SporadicRF | name := "L2(25)", parent := "Suz", generators := 
   GeneratorsSuzMax15(a,b), order := 7800, index := 57480192>,

   rec <SporadicRF | name := "A7", parent := "Suz", generators := 
   GeneratorsSuzMax16(a,b), order := 2520, index := 177914880>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Suz and produce listing of maximal subgroups */

/* 
MaximalsSuz := function (G)

   x, y := StandardGeneratorsSuz(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Suz", DataSuz());

end function;
*/
