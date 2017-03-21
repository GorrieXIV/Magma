freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Co3 */

GeneratorsCo3Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6^-1;
w8:=w7*w2;
w2:=w8*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w1:=w2*w2;
w7:=w5^6;
w8:=w3^5;
w9:=w5^3;
w6:=w8*w9;
w8:=w6^-1;
w9:=w8*w7;
w2:=w9*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w1*w6;
w1:=w7^11;
w7:=w5^7;
w8:=w3*w7;
w7:=w8^-1;
w9:=w7*w2;
w2:=w9*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w1:=w2*w2;
w7:=w5^6;
w6:=w3*w5;
w8:=w6^-1;
w9:=w8*w7;
w2:=w9*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6^5;
w6:=w3^4;
w7:=w5^4;
w8:=w6*w7;
w9:=w8^-1;
w7:=w9*w2;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w3;
w7:=w5^3;
w8:=w6*w7;
w9:=w8^-1;
w6:=w9*w2;
w2:=w6*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w7:=w3^3;
w8:=w5^9;
w6:=w7*w8;
w9:=w6^-1;
w7:=w9*w2;
w2:=w7*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w1*w6;
w1:=w7^11;
w7:=w4^4;
w8:=w3^5;
w9:=w5^11;
w6:=w8*w9;
w8:=w6^-1;
w9:=w8*w7;
w2:=w9*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w1:=w2*w2;
w7:=w5^6;
w8:=w3^7;
w9:=w5^7;
w6:=w8*w9;
w8:=w6^-1;
w9:=w8*w7;
w2:=w9*w6;

   return [w1,w2];

end function;

GeneratorsCo3Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w1*w3;
w7:=w3*w1;
w1:=w2*w2;
w9:=w6^3;
w8:=w9*w3;
w6:=w8*w9;
w8:=w7*w7;
w9:=w3*w3;
w7:=w8*w9;
w10:=w6*w7;
w6:=w5^9;
w8:=w9*w6;
w9:=w8^-1;
w7:=w9*w10;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w6^5;
w6:=w3^4;
w7:=w5*w5;
w8:=w6*w7;
w9:=w8^-1;
w7:=w9*w2;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w10:=w1*w9;
w2:=w10*w4;
w7:=w1*w4;
w8:=w3*w7;
w9:=w3*w8;
w8:=w7^9;
w7:=w1*w6;
w1:=w9^11;
w9:=w7^4;
w7:=w8*w9;
w8:=w7^-1;
w3:=w8*w1;
w1:=w3*w7;

   return [w1,w2];

end function;

GeneratorsCo3Max13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w1*w6;
w6:=w1*w3;
w7:=w3*w1;
w1:=w8^11;
w9:=w6^3;
w8:=w9*w3;
w6:=w8*w9;
w8:=w7*w7;
w9:=w3*w3;
w7:=w8*w9;
w9:=w6*w7;
w10:=w9*w9;
w6:=w3^6;
w7:=w5^5;
w8:=w6*w7;
w9:=w8^-1;
w7:=w9*w10;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsCo3Max14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w11:=w4*w8;
w9:=w3*w8;
w10:=w1*w9;
w2:=w10*w4;
w7:=w1*w4;
w8:=w3*w7;
w9:=w3*w8;
w8:=w7^7;
w7:=w1*w6;
w1:=w9^11;
w9:=w7^20;
w7:=w8*w9;
w8:=w7^-1;
w3:=w8*w1;
w1:=w3*w7;
w3:=w11^15;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of Co3 */

DataCo3 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Co3", generators := [a, b], order := 495766656000>,
   
   rec <SporadicRF | name := "McL:2", parent := "Co3", generators := 
   GeneratorsCo3Max1(a,b), order := 1796256000, index := 276>,

   rec <SporadicRF | name := "HS", parent := "Co3", generators := 
   GeneratorsCo3Max2(a,b), order := 44352000, index := 11178>,

   rec <SporadicRF | name := "U4(3).2.2", parent := "Co3", generators := 
   GeneratorsCo3Max3(a,b), order := 13063680, index := 37950>,

   rec <SporadicRF | name := "M23", parent := "Co3", generators := 
   GeneratorsCo3Max4(a,b), order := 10200960, index := 48600>,

   rec <SporadicRF | name := "3^5:(2xM11)", parent := "Co3", generators := 
   GeneratorsCo3Max5(a,b), order := 3849120, index := 128800>,

   rec <SporadicRF | name := "2.S6(2)", parent := "Co3", generators := 
   GeneratorsCo3Max6(a,b), order := 2903040, index := 170775>,

   rec <SporadicRF | name := "U3(5):S3", parent := "Co3", generators := 
   GeneratorsCo3Max7(a,b), order := 756000, index := 655776>,

   rec <SporadicRF | name := "3^(1+4):4S6", parent := "Co3", generators := 
   GeneratorsCo3Max8(a,b), order := 699840, index := 708400>,

   rec <SporadicRF | name := "2^4.A8", parent := "Co3", generators := 
   GeneratorsCo3Max9(a,b), order := 322560, index := 1536975>,

   rec <SporadicRF | name := "L3(4).D12", parent := "Co3", generators := 
   GeneratorsCo3Max10(a,b), order := 241920, index := 2049300>,

   rec <SporadicRF | name := "2xM12", parent := "Co3", generators := 
   GeneratorsCo3Max11(a,b), order := 190080, index := 2608200>,

   rec <SporadicRF | name := "[2^10.3^3]", parent := "Co3", generators := 
   GeneratorsCo3Max12(a,b), order := 27648, index := 17931375>,

   rec <SporadicRF | name := "S3x(L2(8):3)", parent := "Co3", generators := 
   GeneratorsCo3Max13(a,b), order := 9072, index := 54648000>,

   rec <SporadicRF | name := "A4xS5", parent := "Co3", generators := 
   GeneratorsCo3Max14(a,b), order := 1440, index := 344282400>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Co3 and produce listing of maximal subgroups */

/* 
MaximalsCo3 := function (G)

   x, y := StandardGeneratorsCo3(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Co3", DataCo3());

end function;
*/
