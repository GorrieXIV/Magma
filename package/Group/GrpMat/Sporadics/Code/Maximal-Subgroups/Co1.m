freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Co1; 
   Generators for Max7 - Max22 are unknown */

GeneratorsCo1Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w5:=w4^22;
w6:=w3^20;
w10:=w5*w6;
w11:=w4^18;
w1:=w10*w11;
w3:=w8^14;
w4:=w3*w3;
w5:=w7*w9;
w7:=w5^6;
w8:=w4*w7;
w2:=w8*w3;

   return [w1,w2];

end function;

GeneratorsCo1Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w7;
w7:=w8*w8;
w6:=w7*w7;
w2:=w6*w6;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3*w3;
w3:=w4^-1;
w6:=w3*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsCo1Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w6*w7;
w7:=w8*w8;
w2:=w7*w7;
w6:=w5*w5;
w1:=w5*w6;
w5:=w4*w4;
w6:=w4*w5;
w7:=w5*w6;
w8:=w7^-1;
w6:=w8*w2;
w2:=w6*w7;
w4:=w3*w3;
w5:=w3*w4;
w6:=w5*w5;
w7:=w6^-1;
w8:=w7*w1;
w1:=w8*w6;

   return [w1,w2];

end function;

GeneratorsCo1Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w1:=w3^20;
w5:=w6*w4;
w2:=w5^5;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w3:=w5*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsCo1Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w2:=w5*w5;
w1:=w2*w5;
w6:=w4*w5;
w2:=w4*w6;
w4:=w2*w6;
w6:=w3*w3;
w2:=w4*w6;
w4:=w2*w5;
w2:=w4*w3;

   return [w1,w2];

end function;

GeneratorsCo1Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w3;
w6:=w5*w5;
w1:=w5*w6;

   return [w1,w2];

end function;

GeneratorsCo1Max7 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max8 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max9 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max10 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max11 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max12 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max13 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max14 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max15 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max16 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max17 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max18 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max19 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max20 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max21 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

GeneratorsCo1Max22 := function (a,b)

   w1 := a; w2 := b;

//generators unknown

   return [];

end function;

/* list of subgroups of Co1 */

DataCo1 := function ()

   "Note: Generators for Max7 - Max22 are unknown";

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Co1", generators := [a, b], order := 4157776806543360000>,
   
   rec <SporadicRF | name := "Co2", parent := "Co1", generators := 
   GeneratorsCo1Max1(a,b), order := 42305421312000, index := 98280>,

   rec <SporadicRF | name := "3.Suz:2", parent := "Co1", generators := 
   GeneratorsCo1Max2(a,b), order := 2690072985600, index := 1545600>,

   rec <SporadicRF | name := "2^11:M24", parent := "Co1", generators := 
   GeneratorsCo1Max3(a,b), order := 501397585920, index := 8292375>,

   rec <SporadicRF | name := "Co3", parent := "Co1", generators := 
   GeneratorsCo1Max4(a,b), order := 495766656000, index := 8386560>,

   rec <SporadicRF | name := "2^(1+8).O8+(2)", parent := "Co1", generators := 
   GeneratorsCo1Max5(a,b), order := 89181388800, index := 46621575>,

   rec <SporadicRF | name := "U6(2):S3", parent := "Co1", generators := 
   GeneratorsCo1Max6(a,b), order := 55180984320, index := 75348000>,

   rec <SporadicRF | name := "(A4xG2(4)):2", parent := "Co1", generators := 
   GeneratorsCo1Max7(a,b), order := 6038323200, index := 688564800>,

   rec <SporadicRF | name := "2^(2+12):(A8xS3)", parent := "Co1", generators := 
   GeneratorsCo1Max8(a,b), order := 1981808640, index := 2097970875>,

   rec <SporadicRF | name := "2^(4+12).(S3x(3.S6))", parent := "Co1", generators := 
   GeneratorsCo1Max9(a,b), order := 849346560, index := 4895265375>,

   rec <SporadicRF | name := "3^2.U4(3).D8", parent := "Co1", generators := 
   GeneratorsCo1Max10(a,b), order := 235146240, index := 17681664000>,

   rec <SporadicRF | name := "3^6:2.M12", parent := "Co1", generators := 
   GeneratorsCo1Max11(a,b), order := 138568320, index := 30005248000>,

   rec <SporadicRF | name := "(A5xJ2):2", parent := "Co1", generators := 
   GeneratorsCo1Max12(a,b), order := 72576000, index := 57288591360>,

   rec <SporadicRF | name := "3^(1+4):2.S4(3).2", parent := "Co1", generators := 
   GeneratorsCo1Max13(a,b), order := 25194240, index := 165028864000>,

   rec <SporadicRF | name := "(A6xU3(3)).2", parent := "Co1", generators := 
   GeneratorsCo1Max14(a,b), order := 4354560, index := 954809856000>,

   rec <SporadicRF | name := "3^(3+4):2.(S4xS4)", parent := "Co1", generators := 
   GeneratorsCo1Max15(a,b), order := 2519424, index := 1650288640000>,

   rec <SporadicRF | name := "A9xS3", parent := "Co1", generators := 
   GeneratorsCo1Max16(a,b), order := 1088640, index := 3819239424000>,

   rec <SporadicRF | name := "(A7xL2(7)):2", parent := "Co1", generators := 
   GeneratorsCo1Max17(a,b), order := 846720, index := 4910450688000>,

   rec <SporadicRF | name := "(D10x((A5xA5).2)).2", parent := "Co1", generators := 
   GeneratorsCo1Max18(a,b), order := 144000, index := 28873450045440>,

   rec <SporadicRF | name := "5^(1+2):GL2(5)", parent := "Co1", generators := 
   GeneratorsCo1Max19(a,b), order := 60000, index := 69296280109056>,

   rec <SporadicRF | name := "5^3:(4xA5).2", parent := "Co1", generators := 
   GeneratorsCo1Max20(a,b), order := 60000, index := 69296280109056>,

   rec <SporadicRF | name := "7^2:(3x(2.S4))", parent := "Co1", generators := 
   GeneratorsCo1Max21(a,b), order := 7056, index := 589254082560000>,

   rec <SporadicRF | name := "5^2:2A5", parent := "Co1", generators := 
   GeneratorsCo1Max22(a,b), order := 3000, index := 1385925602181120>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Co1 and produce listing of maximal subgroups */

/* 
MaximalsCo1 := function (G)

   x, y := StandardGeneratorsCo1(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Co1", DataCo1());

end function;
*/
