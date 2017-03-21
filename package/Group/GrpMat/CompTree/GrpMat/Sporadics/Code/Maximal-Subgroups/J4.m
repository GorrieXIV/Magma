freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of J4 */

GeneratorsJ4Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6*w6;
w6:=w5*w5;
w5:=w6*w6;
w6:=w4*w2;
w7:=w6^-1;
w8:=w7*w5;
w2:=w8*w6;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsJ4Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w5^5;
w5:=w4*w2;
w2:=w6^8;
w7:=w3^9;
w8:=w7^-1;
w9:=w8*w1;
w1:=w9*w7;
w6:=w5^21;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsJ4Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w4:=w3^8;
w6:=w4^-1;
w7:=w2*w4;
w2:=w6*w7;
w3:=w5^4;
w4:=w3^-1;
w5:=w1*w3;
w1:=w4*w5;

   return [w1,w2];

end function;

GeneratorsJ4Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^3;
w5:=w4*w2;
w4:=w2*w1;
w1:=w5*w2;
w2:=w1^3;
w1:=w4^22;
w5:=w3^13;
w3:=w1*w5;
w5:=w4*w4;
w1:=w3^-1;
w4:=w1*w2;
w1:=w2*w2;
w2:=w4*w3;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;

   return [w1,w2];

end function;

GeneratorsJ4Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w5^5;
w5:=w4*w2;
w2:=w6^8;
w7:=w3^5;
w8:=w7^-1;
w9:=w8*w1;
w1:=w9*w7;
w6:=w5^4;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsJ4Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6*w4;
w2:=w6^6;
w4:=w3^-1;
w6:=w1*w3;
w1:=w4*w6;
w4:=w3^3;
w6:=w5^24;
w5:=w6^-1;
w6:=w4*w5;
w3:=w6^-1;
w4:=w3*w2;
w2:=w4*w6;

   return [w1,w2];

end function;

GeneratorsJ4Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6*w4;
w3:=w4^4;
w4:=w5^8;
w5:=w4^-1;
w6:=w5*w3;
w3:=w6*w4;
w4:=w1*w3;
w5:=w4*w3;
w6:=w5^3;
w5:=w4*w4;
w3:=w6*w5;
w5:=w4^6;
w4:=w5*w3;
w3:=w4^20;
w5:=w3*w2;
w6:=w2*w3;
w3:=w6^-1;
w6:=w3*w5;
w2:=w6^3;
w3:=w4*w2;
w5:=w4*w3;
w3:=w5^7;
w5:=w4^-1;
w6:=w5*w2;
w5:=w2*w6;
w2:=w4^8;
w6:=w2*w5;
w5:=w6^-1;
w2:=w1*w4;
w4:=w5*w3;
w1:=w4*w6;

   return [w1,w2];

end function;

GeneratorsJ4Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w2*w4;
w8:=w6*w2;
w1:=w8^6;
w9:=w5*w5;
w2:=w5*w9;
w8:=w7^9;
w9:=w8^-1;
w7:=w9*w1;
w1:=w7*w8;
w7:=w4*w6;
w8:=w7^27;
w3:=w6*w4;
w4:=w3^49;
w5:=w8*w4;
w6:=w5^-1;
w7:=w6*w2;
w3:=w7*w5;
w2:=w3*w3;

   return [w1,w2];

end function;

GeneratorsJ4Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w5^5;
w5:=w4*w2;
w2:=w6^8;
w7:=w3^5;
w8:=w7^-1;
w9:=w8*w1;
w1:=w9*w7;
w6:=w5^20;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsJ4Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^3;
w5:=w4*w2;
w4:=w2*w1;
w2:=w5^4;
w5:=w3^16;
w6:=w5^-1;
w5:=w4^24;
w7:=w6*w5;
w6:=w7^-1;
w5:=w6*w2;
w2:=w5*w7;
w5:=w4^8;
w6:=w3*w5;
w7:=w3^18;
w5:=w6*w7;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;

   return [w1,w2];

end function;

GeneratorsJ4Max11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^3;
w5:=w4*w2;
w4:=w5*w2;
w1:=w4^6;
w5:=w3^8;
w3:=w4*w5;
w4:=w5^-1;
w5:=w4*w3;
w4:=w5^6;
w3:=w4*w2;
w6:=w2*w4;
w4:=w6^-1;
w6:=w4*w3;
w4:=w6^7;
w3:=w2*w4;
w2:=w3^-1;
w4:=w5*w2;
w6:=w4*w4;
w2:=w3^5;
w4:=w2*w6;
w6:=w4^-1;
w2:=w6*w5;
w5:=w2*w4;
w2:=w3*w5;
w4:=w2*w2;
w6:=w3*w3;
w3:=w5^3;
w2:=w3*w4;
w7:=w4*w3;
w4:=w7^-1;
w7:=w4*w2;
w4:=w7*w7;
w2:=w4*w6;
w7:=w3*w6;
w4:=w6*w3;
w3:=w4^-1;
w6:=w3*w7;
w4:=w2*w6;
w3:=w4*w4;
w2:=w5*w4;
w6:=w2*w5;
w7:=w6*w2;
w2:=w7*w3;
w5:=w2^5;
w6:=w3*w5;
w7:=w3*w2;
w4:=w6*w6;
w6:=w4*w7;
w7:=w6^-1;
w5:=w2*w6;
w2:=w7*w5;

   return [w1,w2];

end function;

GeneratorsJ4Max12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w1:=w4*w2;
w2:=w5*w5;
w5:=w2*w1;
w2:=w5^3;
w5:=w3*w3;
w3:=w5*w1;
w1:=w3^6;
w3:=w4*w4;
w4:=w5*w3;
w3:=w4^26;
w6:=w5*w3;
w3:=w6^-1;
w7:=w1*w6;
w1:=w3*w7;
w3:=w4^33;
w6:=w5^11;
w7:=w3*w6;
w6:=w7^-1;
w4:=w2*w7;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsJ4Max13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^8;
w6:=w5^5;
w8:=w3^8;
w9:=w8^-1;
w10:=w9*w6;
w6:=w10*w8;
w8:=w2*w1;
w9:=w8^19;
w8:=w9^-1;
w10:=w8*w7;
w7:=w10*w9;
w8:=w6*w7;
w9:=w8^3;
w10:=w1*w9;
w11:=w10^8;
w3:=w2*w9;
w4:=w9*w2;
w5:=w3^-1;
w3:=w5*w4;
w4:=w3^18;
w12:=w2*w4;
w1:=w11*w12;
w3:=w1*w8;
w4:=w3*w8;
w5:=w3*w4;
w16:=w3*w5;
w18:=w16*w5;
w9:=w3*w18;
w10:=w11*w9;
w20:=w10^7;
w13:=w5^5;
w14:=w8*w13;
w23:=w14^3;
w4:=w3^-1;
w13:=w1^4;
w14:=w13*w4;
w13:=w14^-1;
w15:=w13*w20;
w21:=w15*w14;
w13:=w1^8;
w14:=w4^7;
w15:=w13*w14;
w14:=w15^-1;
w13:=w14*w20;
w22:=w13*w15;
w13:=w1^10;
w14:=w4^6;
w15:=w13*w14;
w14:=w15^-1;
w13:=w14*w20;
w24:=w13*w15;
w20:=w21^-1;
w19:=w20*w8;
w18:=w19*w21;
w19:=w18*w8;
w21:=w19*w20;
w20:=w22^-1;
w19:=w20*w8;
w18:=w19*w22;
w19:=w18*w8;
w22:=w19*w20;
w20:=w24^-1;
w19:=w20*w8;
w18:=w19*w24;
w19:=w18*w8;
w24:=w19*w20;
w1:=w21*w23;
w2:=w22*w24;
w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w1^-1;
w3:=w5*w2;
w4:=w3^-1;
w5:=w4*w21;
w2:=w5*w3;
w9:=w8*w7;
w1:=w9*w7;

   return [w1,w2];

end function;

/* list of subgroups of J4 */

DataJ4 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J4", generators := [a, b], order := 86775571046077562880>,
   
   rec <SporadicRF | name := "2^11:M24", parent := "J4", generators := 
   GeneratorsJ4Max1(a,b), order := 501397585920, index := 173067389>,

   rec <SporadicRF | name := "2^(1+12).3.M22:2", parent := "J4", generators := 
   GeneratorsJ4Max2(a,b), order := 21799895040, index := 3980549947>,

   rec <SporadicRF | name := "2^10:L5(2)", parent := "J4", generators := 
   GeneratorsJ4Max3(a,b), order := 10239344640, index := 8474719242>,

   rec <SporadicRF | name := "2^(3+12).(S5xL3(2))", parent := "J4", generators := 
   GeneratorsJ4Max4(a,b), order := 660602880, index := 131358148251>,

   rec <SporadicRF | name := "U3(11):2", parent := "J4", generators := 
   GeneratorsJ4Max5(a,b), order := 141831360, index := 611822174208>,

   rec <SporadicRF | name := "M22:2", parent := "J4", generators := 
   GeneratorsJ4Max6(a,b), order := 887040, index := 97825995497472>,

   rec <SporadicRF | name := "11^(1+2):(5x2S4)", parent := "J4", generators := 
   GeneratorsJ4Max7(a,b), order := 319440, index := 271649045348352>,

   rec <SporadicRF | name := "L2(32):5", parent := "J4", generators := 
   GeneratorsJ4Max8(a,b), order := 163680, index := 530153782050816>,

   rec <SporadicRF | name := "L2(23):2", parent := "J4", generators := 
   GeneratorsJ4Max9(a,b), order := 12144, index := 7145550975467520>,

   rec <SporadicRF | name := "U3(3)", parent := "J4", generators := 
   GeneratorsJ4Max10(a,b), order := 6048, index := 14347812672962560>,

   rec <SporadicRF | name := "29:28", parent := "J4", generators := 
   GeneratorsJ4Max11(a,b), order := 812, index := 106866466805514240>,

   rec <SporadicRF | name := "43:14", parent := "J4", generators := 
   GeneratorsJ4Max12(a,b), order := 602, index := 144145466853949440>,

   rec <SporadicRF | name := "37:12", parent := "J4", generators := 
   GeneratorsJ4Max13(a,b), order := 444, index := 195440475329003520>

   ];
   
   return L;
   
end function;

/* code to find standard generators of J4 and produce listing of maximal subgroups */

/* 
MaximalsJ4 := function (G)

   x, y := StandardGeneratorsJ4(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J4", DataJ4());

end function;
*/
