freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of M12 */

GeneratorsM12Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w3*w6;
w8:=w7*w4;
w9:=w8*w5;
w2:=w9*w9;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;
w4:=w3*w3;
w3:=w4^-1;
w5:=w3*w1;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsM12Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w2:=w10*w10;
w5:=w4*w4;
w3:=w4*w5;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsM12Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w3*w6;
w6:=w4*w5;
w2:=w7*w6;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3*w3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsM12Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w2:=w4*w8;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w8:=w5*w2;
w2:=w8*w6;
w4:=w3*w3;
w5:=w3*w4;
w6:=w5^-1;
w8:=w6*w1;
w1:=w8*w5;

   return [w1,w2];

end function;

GeneratorsM12Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w3;
w6:=w5*w3;
w5:=w6*w6;
w1:=w6*w5;
w5:=w4*w4;
w4:=w5^-1;
w6:=w4*w2;
w2:=w6*w5;

   return [w1,w2];

end function;

GeneratorsM12Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w3:=w2^-1;
w4:=w3*w1;
w1:=w4*w2;
w4:=w5*w2;
w2:=w4*w6;

   return [w1,w2];

end function;

GeneratorsM12Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w3;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;
w5:=w4*w4;
w6:=w4*w5;
w5:=w6^-1;
w7:=w5*w2;
w2:=w7*w6;

   return [w1,w2];

end function;

GeneratorsM12Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w1:=w6*w7;
w7:=w6*w5;
w2:=w4*w7;
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

GeneratorsM12Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w4*w6;
w8:=w6*w4;
w4:=w3*w3;
w5:=w3*w4;
w2:=w5*w7;
w3:=w5*w8;
w5:=w4^-1;
w8:=w2*w2;
w9:=w8*w8;
w6:=w9*w5;
w8:=w3*w3;
w9:=w8*w8;
w7:=w9*w4;
w8:=w6*w7;
w7:=w8*w8;
w5:=w4*w7;
w6:=w5^-1;
w7:=w6*w3;
w1:=w7*w5;

   return [w1,w2];

end function;

GeneratorsM12Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w2:=w3*w5;
w5:=w2*w2;
w1:=w2*w5;
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

GeneratorsM12Max11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6*w6;
w1:=w6*w5;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of M12 */

DataM12 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "M12", generators := [a, b], order := 95040>,
   
   rec <SporadicRF | name := "M11", parent := "M12", generators := 
   GeneratorsM12Max1(a,b), order := 7920, index := 12>,

   rec <SporadicRF | name := "M11b", parent := "M12", generators := 
   GeneratorsM12Max2(a,b), order := 7920, index := 12>,

   rec <SporadicRF | name := "A6.2.2", parent := "M12", generators := 
   GeneratorsM12Max3(a,b), order := 1440, index := 66>,

   rec <SporadicRF | name := "A6.2.2b", parent := "M12", generators := 
   GeneratorsM12Max4(a,b), order := 1440, index := 66>,

   rec <SporadicRF | name := "L2(11)", parent := "M12", generators := 
   GeneratorsM12Max5(a,b), order := 660, index := 144>,

   rec <SporadicRF | name := "3^2:2S4", parent := "M12", generators := 
   GeneratorsM12Max6(a,b), order := 432, index := 220>,

   rec <SporadicRF | name := "3^2:2S4b", parent := "M12", generators := 
   GeneratorsM12Max7(a,b), order := 432, index := 220>,

   rec <SporadicRF | name := "2xS5", parent := "M12", generators := 
   GeneratorsM12Max8(a,b), order := 240, index := 396>,

   rec <SporadicRF | name := "2^(1+4):S3", parent := "M12", generators := 
   GeneratorsM12Max9(a,b), order := 192, index := 495>,

   rec <SporadicRF | name := "4^2:D12", parent := "M12", generators := 
   GeneratorsM12Max10(a,b), order := 192, index := 495>,

   rec <SporadicRF | name := "A4xS3", parent := "M12", generators := 
   GeneratorsM12Max11(a,b), order := 72, index := 1320>
   
   ];
   
   return L;
   
end function;

/* code to find standard generators of M12 and produce listing of maximal subgroups */

/* 
MaximalsM12 := function (G)

   x, y := StandardGeneratorsM12(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "M12", DataM12());

end function;
*/
