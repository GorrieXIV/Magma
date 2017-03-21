freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Fi23;
   Note: Generators for Max7, Max8, Max11, Max12 are unknown; */

GeneratorsFi23Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w7;
w1:=w8^13;
w2:=w8^24;
w5:=w3^13;
w6:=w5^-1;
w7:=w5*w1;
w8:=w7*w6;
w5:=w4^11;
w6:=w5^-1;
w7:=w5*w2;
w2:=w7*w6;
w3:=w8*w2;
w4:=w3^11;
w1:=w4*w8;

   return [w1,w2];

end function;

GeneratorsFi23Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^3;
w6:=w4^3;
w4:=w6*w5;
w1:=w4*w4;
w5:=w3^8;
w3:=w5*w4;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsFi23Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^12;
w3:=w2*w4;
w2:=w3*w3;

   return [w1,w2];

end function;

GeneratorsFi23Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w5*w4;
w4:=w2*w3;
w5:=w3*w3;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsFi23Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^3;
w2:=w4^3;
w6:=w2*w5;
w1:=w6*w6;
w5:=w3*w4;
w6:=w3*w5;
w3:=w5*w4;
w5:=w6*w3;
w4:=w3*w6;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsFi23Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w1;
w5:=w3^7;
w3:=w5*w4;
w2:=w3*w4;

   return [w1,w2];

end function;

GeneratorsFi23Max7 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi23Max8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi23Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^9;
w3:=w4^12;
w4:=w5*w3;
w2:=w4*w5;

   return [w1,w2];

end function;

GeneratorsFi23Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^3;
w6:=w4^3;
w2:=w6*w5;
w1:=w2*w2;
w5:=w3^11;
w6:=w4^13;
w4:=w3*w6;
w3:=w5*w6;
w2:=w4*w3;

   return [w1,w2];

end function;

GeneratorsFi23Max11 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi23Max12 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsFi23Max13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w1;
w5:=w4^12;
w2:=w3^16;
w6:=w3*w5;
w3:=w6*w2;
w6:=w3*w5;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsFi23Max14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3^3;
w1:=w4^10;
w6:=w5*w1;
w1:=w6*w3;
w3:=w4^3;
w4:=w3*w5;
w6:=w1^-1;
w3:=w2*w1;
w2:=w6*w3;
w1:=w4*w4;

   return [w1,w2];

end function;

/* list of subgroups of Fi23 */

DataFi23 := function ()
  
   "Note: Generators for Max7, Max8, Max11, Max12 are unknown";

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Fi23", generators := [a, b], order := 4089470473293004800>,
   
   rec <SporadicRF | name := "2.Fi22", parent := "Fi23", generators := 
   GeneratorsFi23Max1(a,b), order := 129123503308800, index := 31671>,

   rec <SporadicRF | name := "O8+(3):S3", parent := "Fi23", generators := 
   GeneratorsFi23Max2(a,b), order := 29713078886400, index := 137632>,

   rec <SporadicRF | name := "2^2.U6(2).2", parent := "Fi23", generators := 
   GeneratorsFi23Max3(a,b), order := 73574645760, index := 55582605>,

   rec <SporadicRF | name := "S8(2)", parent := "Fi23", generators := 
   GeneratorsFi23Max4(a,b), order := 47377612800, index := 86316516>,

   rec <SporadicRF | name := "O7(3)xS3", parent := "Fi23", generators := 
   GeneratorsFi23Max5(a,b), order := 27512110080, index := 148642560>,

   rec <SporadicRF | name := "2^11.M23", parent := "Fi23", generators := 
   GeneratorsFi23Max6(a,b), order := 20891566080, index := 195747435>,

   rec <SporadicRF | name := "3^(1+8).2^(1+6).3^(1+2).2S4", parent := "Fi23", generators := 
   GeneratorsFi23Max7(a,b), order := 3265173504, index := 1252451200>,

   rec <SporadicRF | name := "[3^10].(L3(3)x2)", parent := "Fi23", generators := 
   GeneratorsFi23Max8(a,b), order := 663238368, index := 6165913600>,

   rec <SporadicRF | name := "S12", parent := "Fi23", generators := 
   GeneratorsFi23Max9(a,b), order := 479001600, index := 8537488128>,

   rec <SporadicRF | name := "(2^2x2^(1+8).(3xU4(2)).2", parent := "Fi23", generators := 
   GeneratorsFi23Max10(a,b), order := 318504960, index := 12839581755>,

   rec <SporadicRF | name := "2^(6+8):(A7xS3)", parent := "Fi23", generators := 
   GeneratorsFi23Max11(a,b), order := 247726080, index := 16508033685>,

   rec <SporadicRF | name := "S6(2)xS4", parent := "Fi23", generators := 
   GeneratorsFi23Max12(a,b), order := 34836480, index := 117390461760>,

   rec <SporadicRF | name := "S4(4):4", parent := "Fi23", generators := 
   GeneratorsFi23Max13(a,b), order := 3916800, index := 1044084577536>,

   rec <SporadicRF | name := "L2(23)", parent := "Fi23", generators := 
   GeneratorsFi23Max14(a,b), order := 6072, index := 673496454758400>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Fi23 and produce listing of maximal subgroups */

/* 
MaximalsFi23 := function (G)

   x, y := StandardGeneratorsFi23(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Fi23", DataFi23());

end function;
*/
