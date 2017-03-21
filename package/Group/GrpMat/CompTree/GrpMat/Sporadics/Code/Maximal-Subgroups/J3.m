freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of J3 */

GeneratorsJ3Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w4:=w5*w5;
w5:=w3*w4;
w4:=w5*w5;
w3:=w5*w4;
w2:=w3*w3;

   return [w1,w2];

end function;

GeneratorsJ3Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w2:=w5*w6;
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

GeneratorsJ3Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w3;
w6:=w5*w5;
w2:=w5*w6;
w5:=w3*w3;
w6:=w5*w5;
w5:=w6^-1;
w3:=w5*w2;
w2:=w3*w6;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsJ3Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w1:=w5*w6;
w5:=w4*w4;
w4:=w5*w5;
w5:=w4*w4;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsJ3Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w2:=w5*w6;
w5:=w4*w4;
w6:=w5*w5;
w5:=w4*w6;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsJ3Max6 := function (a,b)

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

GeneratorsJ3Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w2:=w3*w6;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6*w6;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3*w3;
w5:=w4*w4;
w4:=w5*w5;
w5:=w3*w4;
w4:=w5^-1;
w3:=w4*w1;
w1:=w3*w5;

   return [w1,w2];

end function;

GeneratorsJ3Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w9:=w3^5;
w10:=w9^-1;
w11:=w10*w1;
w10:=w11*w9;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5*w5;
w7:=w3*w6;
w8:=w3*w7;
w1:=w8*w4;
w4:=w1^15;
w5:=w10*w4;
w6:=w5*w5;
w7:=w5*w6;
w2:=w7*w7;

   return [w1,w2];

end function;

GeneratorsJ3Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w4;
w8:=w7*w7;
w9:=w3*w3;
w3:=w9*w9;
w6:=w5*w3;
w9:=w6*w8;
w2:=w9*w9;
w5:=w4^10;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3^-1;
w6:=w4*w1;
w1:=w6*w3;

   return [w1,w2];

end function;

/* list of subgroups of J3 */

DataJ3 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "J3", generators := [a, b], order := 50232960>,
   
   rec <SporadicRF | name := "L2(16):2", parent := "J3", generators := 
   GeneratorsJ3Max1(a,b), order := 8160, index := 6156>,

   rec <SporadicRF | name := "L2(19)", parent := "J3", generators := 
   GeneratorsJ3Max2(a,b), order := 3420, index := 14688>,

   rec <SporadicRF | name := "L2(19)b", parent := "J3", generators := 
   GeneratorsJ3Max3(a,b), order := 3420, index := 14688>,

   rec <SporadicRF | name := "2^4:(3xA5)", parent := "J3", generators := 
   GeneratorsJ3Max4(a,b), order := 2880, index := 17442>,

   rec <SporadicRF | name := "L2(17)", parent := "J3", generators := 
   GeneratorsJ3Max5(a,b), order := 2448, index := 20520>,

   rec <SporadicRF | name := "(3xA6):2", parent := "J3", generators := 
   GeneratorsJ3Max6(a,b), order := 2160, index := 23256>,

   rec <SporadicRF | name := "3^(2+1+2):8", parent := "J3", generators := 
   GeneratorsJ3Max7(a,b), order := 1944, index := 25840>,

   rec <SporadicRF | name := "2^(1+4):A5", parent := "J3", generators := 
   GeneratorsJ3Max8(a,b), order := 1920, index := 26163>,

   rec <SporadicRF | name := "2^(2+4):(3xS3)", parent := "J3", generators := 
   GeneratorsJ3Max9(a,b), order := 1152, index := 43605>

   ];
   
   return L;
   
end function;

/* code to find standard generators of J3 and produce listing of maximal subgroups */

/*
MaximalsJ3 := function (G)

   x, y := StandardGeneratorsJ3(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "J3", DataJ3());

end function;
*/
