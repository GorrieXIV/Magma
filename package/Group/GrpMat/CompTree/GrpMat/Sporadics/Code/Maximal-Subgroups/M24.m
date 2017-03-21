freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of M24 */

GeneratorsM24Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w2:=w7*w7;
w1:=w2*w2;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w7:=w5*w2;
w2:=w7*w6;
w4:=w3*w3;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w1;
w1:=w6*w5;

   return [w1,w2];

end function;

GeneratorsM24Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3^3;
w5:=w4*w2;
w6:=w5^-1;
w4:=w6*w2;
w2:=w4*w5;

   return [w1,w2];

end function;

GeneratorsM24Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w5^9;
w7:=w3^11;
w8:=w7*w6;
w6:=w5*w5;
w7:=w3*w6;
w6:=w7*w7;
w7:=w8^-1;
w5:=w7*w6;
w2:=w5*w8;

   return [w1,w2];

end function;

GeneratorsM24Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3^12;
w7:=w5^5;
w8:=w6*w7;
w9:=w8^-1;
w6:=w9*w2;
w2:=w6*w8;

   return [w1,w2];

end function;

GeneratorsM24Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w5^3;
w9:=w3^8;
w8:=w9*w5;
w5:=w6^3;
w9:=w8^-1;
w7:=w9*w5;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsM24Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w1:=w6^6;
w9:=w5^10;
w8:=w3*w9;
w5:=w7*w7;
w9:=w8^-1;
w7:=w9*w5;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsM24Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w9:=w3^7;
w10:=w5^11;
w8:=w9*w10;
w5:=w6^3;
w9:=w8^-1;
w7:=w9*w5;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsM24Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3^7;
w7:=w5^11;
w8:=w6*w7;
w6:=w5^3;
w9:=w8^-1;
w7:=w9*w6;
w2:=w7*w8;

   return [w1,w2];

end function;

GeneratorsM24Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3^3;
w7:=w5^4;
w8:=w6*w7;
w6:=w5^3;
w9:=w8^-1;
w7:=w9*w6;
w2:=w7*w8;

   return [w1,w2];

end function;

/* list of subgroups of M24 */

DataM24 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M24", generators := [a, b], order := 244823040>,
   
   rec <SporadicRF | name := "M23", parent := "M24", generators := 
   GeneratorsM24Max1(a,b), order := 10200960, index := 24>,

   rec <SporadicRF | name := "M22.2", parent := "M24", generators := 
   GeneratorsM24Max2(a,b), order := 887040, index := 276>,

   rec <SporadicRF | name := "2^4.A8", parent := "M24", generators := 
   GeneratorsM24Max3(a,b), order := 322560, index := 759>,

   rec <SporadicRF | name := "M12.2", parent := "M24", generators := 
   GeneratorsM24Max4(a,b), order := 190080, index := 1288>,

   rec <SporadicRF | name := "2^6:3.S6", parent := "M24", generators := 
   GeneratorsM24Max5(a,b), order := 138240, index := 1771>,

   rec <SporadicRF | name := "L3(4):S3", parent := "M24", generators := 
   GeneratorsM24Max6(a,b), order := 120960, index := 2024>,

   rec <SporadicRF | name := "2^6:(L3(2)xS3)", parent := "M24", generators := 
   GeneratorsM24Max7(a,b), order := 64512, index := 3795>,

   rec <SporadicRF | name := "L2(23)", parent := "M24", generators := 
   GeneratorsM24Max8(a,b), order := 6072, index := 40320>,

   rec <SporadicRF | name := "L2(7)", parent := "M24", generators := 
   GeneratorsM24Max9(a,b), order := 168, index := 1457280>

   ];
   
   return L;
   
end function;

/* code to find standard generators of M24 and produce listing of maximal subgroups */

/* 
MaximalsM24 := function (G)

   x, y := StandardGeneratorsM24(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M24", DataM24());

end function;
*/
