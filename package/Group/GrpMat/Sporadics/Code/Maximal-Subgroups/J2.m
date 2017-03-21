freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of J2 */

GeneratorsJ2Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w5^6;
w7:=w6*w6;
w4:=w7*w3;
w8:=w4*w3;
w9:=w5*w5;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w5*w5;
w8:=w7*w3;
w9:=w6^3;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w3;
w9:=w5*w5;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w1:=w5^6;
w6:=w5*w5;
w8:=w6*w3;
w6:=w3*w10;
w7:=w4*w5;
w9:=w6*w7;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w9:=w7^6;
w6:=w5*w5;
w8:=w6*w9;
w7:=w8^-1;
w10:=w7*w2;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w9:=w6^4;
w10:=w7^4;
w8:=w9*w10;
w9:=w5*w5;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^3;
w5:=w3^-1;
w6:=w5*w7;
w2:=w6*w3;

   return [w1,w2];

end function;

GeneratorsJ2Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w1:=w5^6;
w6:=w5*w5;
w7:=w6*w3;
w8:=w7*w3;
w6:=w3*w10;
w7:=w4*w5;
w9:=w6*w7;
w7:=w8^-1;
w10:=w7*w9;
w2:=w10*w8;

   return [w1,w2];

end function;

GeneratorsJ2Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5^9;
w8:=w3*w6;
w7:=w8^-1;
w10:=w7*w2;
w2:=w10*w8;

   return [w1,w2];

end function;

/* list of subgroups of J2 */

DataJ2 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J2", generators := [a, b], order := 604800>,
   
   rec <SporadicRF | name := "U3(3)", parent := "J2", generators := 
   GeneratorsJ2Max1(a,b), order := 6048, index := 100>,

   rec <SporadicRF | name := "3.A6.2", parent := "J2", generators := 
   GeneratorsJ2Max2(a,b), order := 2160, index := 280>,

   rec <SporadicRF | name := "2^(1+4).A5", parent := "J2", generators := 
   GeneratorsJ2Max3(a,b), order := 1920, index := 315>,

   rec <SporadicRF | name := "2^(2+4):(3xS3)", parent := "J2", generators := 
   GeneratorsJ2Max4(a,b), order := 1152, index := 525>,

   rec <SporadicRF | name := "A4xA5", parent := "J2", generators := 
   GeneratorsJ2Max5(a,b), order := 720, index := 840>,

   rec <SporadicRF | name := "A5xD10", parent := "J2", generators := 
   GeneratorsJ2Max6(a,b), order := 600, index := 1008>,

   rec <SporadicRF | name := "L3(2):2", parent := "J2", generators := 
   GeneratorsJ2Max7(a,b), order := 336, index := 1800>,

   rec <SporadicRF | name := "5^2:D12", parent := "J2", generators := 
   GeneratorsJ2Max8(a,b), order := 300, index := 2016>,

   rec <SporadicRF | name := "A5", parent := "J2", generators := 
   GeneratorsJ2Max9(a,b), order := 60, index := 10080>

   ];
   
   return L;
   
end function;

/* code to find standard generators of J2 and produce listing of maximal subgroups */

/* 
MaximalsJ2 := function (G)

   x, y := StandardGeneratorsJ2(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J2", DataJ2());

end function;
*/
