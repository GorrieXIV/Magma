freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of ^2F4(2)' */

GeneratorsTF42Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w6*w5;
w1:=w4*w4;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^3;
w5:=w4^6;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3^4;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsTF42Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w6*w5;
w1:=w4*w4;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^3;
w5:=w4^6;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3^2;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsTF42Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w6*w5;
w1:=w4*w4;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^3;
w5:=w4^9;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;
w4:=w3^3;
w5:=w4^-1;
w6:=w5*w1;
w1:=w6*w4;

   return [w1,w2];

end function;

GeneratorsTF42Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w6*w5;
w1:=w4*w4;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w2:=w6^3;

   return [w1,w2];

end function;

GeneratorsTF42Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w6*w5;
w1:=w4*w4;
w5:=w3^4;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;

   return [w1,w2];

end function;

GeneratorsTF42Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w3*w2;
w2:=w6*w5;
w1:=w2*w2;
w5:=w3*w4;
w6:=w3*w5;
w5:=w6^5;
w6:=w5^-1;
w7:=w6*w2;
w2:=w7*w5;

   return [w1,w2];

end function;

GeneratorsTF42Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4*w1;
w6:=w5^-1;
w5:=w1*w4;
w4:=w3*w2;
w2:=w6*w5;
w1:=w2*w2;
w5:=w3*w4;
w6:=w3*w5;
w4:=w6^2;
w6:=w4^-1;
w7:=w6*w1;
w1:=w7*w4;
w6:=w5*w3;
w5:=w6^-1;
w7:=w5*w2;
w2:=w7*w6;

   return [w1,w2];

end function;

GeneratorsTF42Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w4:=w5*w5;
w3:=w5*w4;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

/* list of subgroups of TF42 */

DataTF42 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "TF42", generators := [a, b], order := 17971200>,
   
   rec <SporadicRF | name := "L3(3):2", parent := "TF42", generators := 
   GeneratorsTF42Max1(a,b), order := 11232, index := 1600>,

   rec <SporadicRF | name := "L3(3):2b", parent := "TF42", generators := 
   GeneratorsTF42Max2(a,b), order := 11232, index := 1600>,

   rec <SporadicRF | name := "2.[2^8].5.4", parent := "TF42", generators := 
   GeneratorsTF42Max3(a,b), order := 10240, index := 1755>,

   rec <SporadicRF | name := "L2(25)", parent := "TF42", generators := 
   GeneratorsTF42Max4(a,b), order := 7800, index := 2304>,

   rec <SporadicRF | name := "2^2.[2^8].S3", parent := "TF42", generators := 
   GeneratorsTF42Max5(a,b), order := 6144, index := 2925>,

   rec <SporadicRF | name := "A6.2^2", parent := "TF42", generators := 
   GeneratorsTF42Max6(a,b), order := 1440, index := 12480>,

   rec <SporadicRF | name := "A6.2^2b", parent := "TF42", generators := 
   GeneratorsTF42Max7(a,b), order := 1440, index := 12480>,

   rec <SporadicRF | name := "5^2:4A4", parent := "TF42", generators := 
   GeneratorsTF42Max8(a,b), order := 1200, index := 14976>
 
   ];
   
   return L;
   
end function;

/* code to find standard generators of TF42 and produce listing of maximal subgroups */

/* 
MaximalsTF42 := function (G)

   x, y := StandardGeneratorsTF42(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "TF42", DataTF42());

end function;
*/
