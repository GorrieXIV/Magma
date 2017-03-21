freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of B;
   Note: Generators for Max7 - Max10, Max12, Max14, Max15, 
   Max17 - Max20, Max22 - Max30 are unknown */

GeneratorsBMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^14;
w2:=w5*w4;
w6:=w2^19;
w7:=w1*w6;
w1:=w7^3;

   return [w1,w2];

end function;

GeneratorsBMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w3;
w3:=w5*w5;
w2:=w3*w4;
w3:=w2*w2;
w4:=w2*w3;
w5:=w4*w4;
w3:=w5*w5;
w4:=w3*w3;
w3:=w1*w4;
w1:=w3*w3;

   return [w1,w2];

end function;

GeneratorsBMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w6:=w7*w7;
w2:=w6*w6;
w6:=w5*w5;
w7:=w5*w6;
w5:=w6*w7;
w6:=w5*w5;
w1:=w6*w6;
w5:=w4*w4;
w6:=w5*w5;
w5:=w6*w6;
w6:=w4*w5;
w7:=w6^-1;
w5:=w7*w2;
w2:=w5*w6;
w4:=w3*w3;
w5:=w3*w4;
w6:=w4*w5;
w5:=w6*w6;
w6:=w5^-1;
w4:=w6*w1;
w1:=w4*w5;

   return [w1,w2];

end function;

GeneratorsBMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^10;
w8:=w3*w7;
w9:=w8^-1;
w8:=w7*w3;
w10:=w9*w8;
w11:=w10^17;
w2:=w3*w11;
w8:=w4*w7;
w9:=w8^-1;
w8:=w7*w4;
w10:=w9*w8;
w11:=w10^16;
w12:=w4*w11;
w10:=w2*w12;
w9:=w10^20;
w8:=w7*w9;
w9:=w3*w8;
w10:=w9^-1;
w9:=w8*w3;
w8:=w10*w9;
w1:=w8^12;

   return [w1,w2];

end function;

GeneratorsBMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6*w6;
w6:=w5*w5;
w7:=w5*w6;
w1:=w6*w7;
w5:=w4*w4;
w6:=w5*w5;
w5:=w6*w6;
w6:=w5*w5;
w5:=w4*w6;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3*w3;
w5:=w3*w4;
w4:=w5*w5;
w5:=w4*w4;
w4:=w3*w5;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsBMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w7:=w8^9;
w6:=w1*w7;
w1:=w6^13;
w4:=w3^-1;
w5:=w7*w4;
w6:=w7*w3;
w4:=w5*w6;
w5:=w4^5;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsBMax7 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax9 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax10 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w1;
w4:=w3*w3;
w5:=w3*w4;
w4:=w1*w5;
w3:=w5^-1;
w1:=w3*w4;
w3:=w4*w2;
w4:=w2*w3;
w5:=w3^-1;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsBMax12 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w3;
w3:=w5*w5;
w12:=w3*w4;
w3:=w12*w12;
w4:=w12*w3;
w5:=w4*w4;
w3:=w5*w5;
w4:=w3*w3;
w3:=w1*w4;
w11:=w3*w3;
w3:=w11*w12;
w4:=w3*w12;
w5:=w3*w3;
w6:=w4*w3;
w7:=w5*w6;
w8:=w7*w7;
w9:=w7*w8;
w13:=w8*w9;
w5:=w3*w4;
w6:=w5*w5;
w7:=w12*w6;
w8:=w7*w7;
w9:=w8*w8;
w7:=w4*w6;
w3:=w7*w5;
w4:=w3^-1;
w5:=w4*w9;
w14:=w5*w3;
w3:=w13*w14;
w4:=w3*w14;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w4:=w5*w8;
w15:=w4^5;
w4:=w5^3;
w5:=w6^17;
w6:=w9^24;
w7:=w5*w6;
w8:=w7^-1;
w6:=w8*w4;
w16:=w6*w7;
w3:=w15*w16;
w4:=w3^10;
w5:=w15^-1;
w6:=w15*w4;
w7:=w4^-1;
w8:=w7*w15;
w9:=w6*w5;
w17:=w9*w8;
w5:=w16^-1;
w6:=w16*w4;
w8:=w7*w16;
w9:=w6*w5;
w2:=w9*w8;
w3:=w17*w2;
w4:=w3^15;
w5:=w12^24;
w6:=w4*w5;
w7:=w1*w6;
w1:=w7^26;
w5:=w3^5;
w3:=w5*w5;
w4:=w1*w3;
w5:=w4*w4;
w6:=w5^-1;
w7:=w5*w3;
w8:=w6*w3;
w9:=w7*w8;
w4:=w9*w5;
w6:=w4^-1;
w7:=w4*w3;
w8:=w6*w3;
w9:=w7*w8;
w5:=w9*w4;
w1:=w17*w5;

   return [w1,w2];

end function;

GeneratorsBMax14 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax15 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax16 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w7:=w8^9;
w6:=w1*w7;
w9:=w6^13;
w6:=w3^-1;
w5:=w7*w6;
w6:=w7*w3;
w7:=w5*w6;
w5:=w7^5;
w10:=w3*w5;
w11:=w9*w10;
w12:=w11*w10;
w13:=w11*w12;
w14:=w11*w13;
w15:=w14*w11;
w16:=w15*w12;
w17:=w11*w16;
w18:=w14*w16;
w23:=w18^15;
w20:=w17^17;
w12:=w10*w9;
w13:=w12^-1;
w12:=w13*w11;
w13:=w12^6;
w11:=w10*w13;
w12:=w9*w14;
w13:=w14*w9;
w15:=w13^-1;
w13:=w15*w12;
w15:=w13^6;
w12:=w14*w15;
w16:=w4^4;
w17:=w16^-1;
w18:=w17*w9;
w19:=w16*w20;
w20:=w18*w19;
w19:=w20^7;
w21:=w19*w17;
w22:=w21^-1;
w24:=w22*w23;
w23:=w24*w21;
w1:=w12*w11;
w13:=w11*w12;
w2:=w13*w23;

   return [w1,w2];

end function;

GeneratorsBMax17 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax18 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax19 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax20 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax21 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w3;
w3:=w5*w5;
w12:=w3*w4;
w3:=w12*w12;
w4:=w12*w3;
w5:=w4*w4;
w3:=w5*w5;
w10:=w3*w3;
w3:=w1*w10;
w11:=w3*w3;
w3:=w11*w12;
w4:=w3*w12;
w5:=w3*w3;
w6:=w4*w3;
w7:=w5*w6;
w8:=w7*w7;
w9:=w7*w8;
w13:=w8*w9;
w5:=w3*w4;
w6:=w5*w5;
w7:=w12*w6;
w8:=w7*w7;
w9:=w8*w8;
w7:=w4*w6;
w3:=w7*w5;
w4:=w3^-1;
w5:=w4*w9;
w14:=w5*w3;
w3:=w13*w14;
w4:=w3*w14;
w5:=w4*w14;
w6:=w5*w14;
w15:=w4^3;
w4:=w5*w5;
w5:=w3*w3;
w7:=w5*w4;
w4:=w7^5;
w5:=w6^20;
w6:=w3^6;
w3:=w5*w6;
w5:=w3^-1;
w6:=w5*w4;
w16:=w6*w3;
w3:=w15*w16;
w4:=w3*w16;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^6;
w8:=w15^-1;
w9:=w7*w8;
w6:=w7*w15;
w5:=w9*w6;
w6:=w5*w5;
w17:=w15*w6;
w8:=w16^-1;
w9:=w7*w8;
w5:=w7^3;
w6:=w5*w16;
w5:=w9*w6;
w6:=w5*w5;
w18:=w16*w6;
w3:=w17*w18;
w4:=w3*w18;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^15;
w19:=w7*w10;
w3:=w1*w19;
w20:=w3^17;
w21:=w6^6;
w3:=w20*w21;
w4:=w3^4;
w5:=w4^-1;
w6:=w21*w5;
w7:=w21*w4;
w8:=w6*w7;
w7:=w8*w8;
w5:=w4*w7;
w4:=w5^-1;
w6:=w21*w4;
w7:=w21*w5;
w8:=w6*w7;
w7:=w8*w8;
w1:=w5*w7;
w2:=w17*w18;

   return [w1,w2];

end function;

GeneratorsBMax22 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax23 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax24 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax25 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax26 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax27 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax28 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax29 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsBMax30 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

/* list of subgroups of B */

DataB := function ()
 
   "Note: Generators for Max7 - Max10, Max12, Max14, Max15, Max17 - Max20, Max22 - Max30 are unknown";

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "B", generators := [a, b], order := 4154781481226426191177580544000000>,
   
   rec <SporadicRF | name := "2.^2E6(2):2", parent := "B", generators := 
   GeneratorsBMax1(a,b), order := 306129918735099415756800, index := 13571955000>,

   rec <SporadicRF | name := "2^(1+22)Co2", parent := "B", generators := 
   GeneratorsBMax2(a,b), order := 354883595661213696000, index := 11707448673375>,

   rec <SporadicRF | name := "Fi23", parent := "B", generators := 
   GeneratorsBMax3(a,b), order := 4089470473293004800, index := 1015970529280000>,

   rec <SporadicRF | name := "2^(9+16).S8(2)", parent := "B", generators := 
   GeneratorsBMax4(a,b), order := 1589728887019929600, index := 2613515747968125>,

   rec <SporadicRF | name := "Th", parent := "B", generators := 
   GeneratorsBMax5(a,b), order := 90745943887872000, index := 45784762417152000>,

   rec <SporadicRF | name := "(2^2xF4(2)):2", parent := "B", generators := 
   GeneratorsBMax6(a,b), order := 26489012826931200, index := 156849238149120000>,

   rec <SporadicRF | name := "2^(2+10+20)((M22:2)xS3)", parent := "B", generators := 
   GeneratorsBMax7(a,b), order := 22858846741463040, index := 181758140654146875>,

   rec <SporadicRF | name := "[2^30].L5(2)", parent := "B", generators := 
   GeneratorsBMax8(a,b), order := 10736731045232640, index := 386968944618506250>,

   rec <SporadicRF | name := "S3x(F22:2)", parent := "B", generators := 
   GeneratorsBMax9(a,b), order := 774741019852800, index := 5998018641586846875>,

   rec <SporadicRF | name := "[2^35].(S5xL3(2))", parent := "B", generators := 
   GeneratorsBMax10(a,b), order := 692692325498880, index := 5998018641586846875>,

   rec <SporadicRF | name := "HN:2", parent := "B", generators := 
   GeneratorsBMax11(a,b), order := 546061824000000, index := 7608628361513926656>,

   rec <SporadicRF | name := "O8+(3):S4", parent := "B", generators := 
   GeneratorsBMax12(a,b), order := 118852315545600, index := 34957513971466240000>,

   rec <SporadicRF | name := "3^(1+8).2^(1+6).U4(2).2", parent := "B", generators := 
   GeneratorsBMax13(a,b), order := 130606940160, index := 31811337714034278400000>,

   rec <SporadicRF | name := "((3^2D8)x(U4(3).2.2)).2", parent := "B", generators := 
   GeneratorsBMax14(a,b), order := 1881169920, index := 2208615732717237043200000>,

   rec <SporadicRF | name := "(5:4)x(HS:2)", parent := "B", generators := 
   GeneratorsBMax15(a,b), order := 1774080000, index := 2341935809673986624716800>,

   rec <SporadicRF | name := "S4x^2F4(2)", parent := "B", generators := 
   GeneratorsBMax16(a,b), order := 862617600, index := 4816481232502590013440000>,

   rec <SporadicRF | name := "[3^11](S4x2S4)", parent := "B", generators := 
   GeneratorsBMax17(a,b), order := 204073344, index := 20359256136981938176000000>,

   rec <SporadicRF | name := "S5x(M22:2)", parent := "B", generators := 
   GeneratorsBMax18(a,b), order := 106444800, index := 39032263494566443745280000>,

   rec <SporadicRF | name := "(S6x(L3(4):2)).2", parent := "B", generators := 
   GeneratorsBMax19(a,b), order := 58060800, index := 71559149740038480199680000>,

   rec <SporadicRF | name := "5^3.L3(5)", parent := "B", generators := 
   GeneratorsBMax20(a,b), order := 46500000, index := 89350139381213466476937216>,

   rec <SporadicRF | name := "5^(1+4).2^(1+4).A5.4", parent := "B", generators := 
   GeneratorsBMax21(a,b), order := 24000000, index := 173115895051101091299065856>,

   rec <SporadicRF | name := "(S6xS6).4", parent := "B", generators := 
   GeneratorsBMax22(a,b), order := 2073600, index := 2003656192721077445591040000>,

   rec <SporadicRF | name := "(5^2:4S4)xS5", parent := "B", generators := 
   GeneratorsBMax23(a,b), order := 288000, index := 14426324587591757608255488000>,

   rec <SporadicRF | name := "L2(49).2", parent := "B", generators := 
   GeneratorsBMax24(a,b), order := 117600, index := 35329774500224712510013440000>,

   rec <SporadicRF | name := "L2(31)", parent := "B", generators := 
   GeneratorsBMax25(a,b), order := 14880, index := 279219185566292082740428800000>,

   rec <SporadicRF | name := "M11", parent := "B", generators := 
   GeneratorsBMax26(a,b), order := 7920, index := 524593621366973003936563200000>,

   rec <SporadicRF | name := "L3(3)", parent := "B", generators := 
   GeneratorsBMax27(a,b), order := 5616, index := 739811517312397826064384000000>,

   rec <SporadicRF | name := "L2(17):2", parent := "B", generators := 
   GeneratorsBMax28(a,b), order := 4896, index := 848607328681868094603264000000>,

   rec <SporadicRF | name := "L2(11):2", parent := "B", generators := 
   GeneratorsBMax29(a,b), order := 1320, index := 3147561728201838023619379200000>,

   rec <SporadicRF | name := "43:23", parent := "B", generators := 
   GeneratorsBMax30(a,b), order := 1081, index := 3843461129719173164826624000000>

   ];
   
   return L;
   
end function;

/* code to find standard generators of B and produce listing of maximal subgroups */

/* 
MaximalsB := function (G)

   x, y := StandardGeneratorsB(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "B", DataB());

end function;
*/
