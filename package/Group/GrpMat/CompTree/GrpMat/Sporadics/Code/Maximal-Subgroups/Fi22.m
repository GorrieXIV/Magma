freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Fi22 */

GeneratorsFi22Max1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w4;
w2:=w4*w5;
w4:=w3*w3;
w5:=w3*w4;
w3:=w4*w5;
w4:=w3^-1;
w5:=w4*w1;
w1:=w5*w3;

   return [w1,w2];

end function;

GeneratorsFi22Max2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w3:=w4*w4;
w2:=w4*w3;
w4:=w5*w5;
w3:=w5*w4;
w5:=w4*w3;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsFi22Max3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w3;
w3:=w4*w4;
w4:=w3^-1;
w5:=w2*w2;
w6:=w3*w5;
w2:=w6*w4;
w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w3:=w4*w4;
w2:=w4*w3;
w4:=w5*w5;
w3:=w5*w4;
w5:=w4*w3;
w4:=w5^-1;
w3:=w4*w2;
w2:=w3*w5;

   return [w1,w2];

end function;

GeneratorsFi22Max4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w3;
w5:=w4^3;
w3:=w2^5;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsFi22Max5 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w2;
w4:=w3*w3;
w8:=w2*w1;
w9:=w2*w8;
w10:=w8*w9;
w11:=w3*w4;
w12:=w2*w11;
w5:=w1*w4;
w6:=w4*w1;
w7:=w6^-1;
w2:=w7*w5;
w1:=w10*w12;

   return [w1,w2];

end function;

GeneratorsFi22Max6 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w2;
w4:=w3*w3;
w8:=w2*w1;
w9:=w2^11;
w10:=w9*w1;
w9:=w2^6;
w11:=w8*w10;
w5:=w1*w4;
w6:=w4*w1;
w7:=w6^-1;
w2:=w7*w5;
w1:=w11*w9;

   return [w1,w2];

end function;

GeneratorsFi22Max7 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w2;
w4:=w3*w3;
w8:=w2*w1;
w9:=w3*w8;
w10:=w8*w9;
w11:=w2*w4;
w5:=w1*w4;
w6:=w4*w1;
w7:=w6^-1;
w2:=w7*w5;
w1:=w10*w11;

   return [w1,w2];

end function;

GeneratorsFi22Max8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w2*w1;
w5:=w2^-1;
w6:=w4*w5;
w7:=w6*w3;
w8:=w7*w7;
w7:=w8*w8;
w9:=w1*w8;
w1:=w9*w7;
w3:=w2^5;
w5:=w4*w3;
w6:=w4*w5;
w2:=w5*w6;

   return [w1,w2];

end function;

GeneratorsFi22Max9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w6;
w6:=w7*w7;
w1:=w6*w6;
w6:=w4*w4;
w7:=w4*w6;
w8:=w7^-1;
w9:=w8*w2;
w2:=w9*w7;
w6:=w2*w4;
w7:=w6*w6;
w2:=w6*w7;
w6:=w5^-1;
w7:=w6*w1;
w1:=w7*w5;

   return [w1,w2];

end function;

GeneratorsFi22Max10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w9:=w3*w8;
w1:=w9^6;
w2:=w6^4;
w5:=w3^-1;
w6:=w3*w1;
w1:=w6*w5;
w3:=w4^10;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsFi22Max11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w14:=w1*w3;
w4:=w2*w1;
w5:=w2^-1;
w6:=w4*w5;
w7:=w6*w3;
w8:=w7*w7;
w7:=w8*w8;
w9:=w1*w8;
w1:=w9*w7;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w2;
w7:=w6*w2;
w8:=w7*w2;
w9:=w8*w2;
w10:=w9*w2;
w11:=w7*w10;
w12:=w11^-1;
w13:=w12*w1;
w2:=w13*w11;
w15:=w14^7;
w16:=w8*w3;
w17:=w4*w10;
w4:=w15*w16;
w3:=w4*w17;

   return [w1,w2,w3];

end function;

GeneratorsFi22Max12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w2*w4;
w6:=w4*w4;
w7:=w4*w6;
w8:=w6*w7;
w9:=w8^-1;
w6:=w9*w5;
w2:=w6*w8;
w4:=w3*w3;
w5:=w4*w4;
w6:=w4*w5;
w7:=w3*w6;
w8:=w7^-1;
w9:=w8*w1;
w1:=w9*w7;

   return [w1,w2];

end function;

GeneratorsFi22Max13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w2*w4;
w7:=w3^-1;
w6:=w7*w5;
w2:=w6*w3;
w5:=w4^13;
w6:=w5^-1;
w4:=w6*w1;
w1:=w4*w5;

   return [w1,w2];

end function;

GeneratorsFi22Max14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w8:=w9*w9;
w7:=w9*w8;
w1:=w7*w7;
w9:=w2*w10;
w8:=w9*w9;
w2:=w8*w8;
w3:=w4*w4;
w4:=w3*w3;
w3:=w4^-1;
w6:=w3*w1;
w1:=w6*w4;
w4:=w5*w5;
w5:=w4*w4;
w4:=w5*w5;
w3:=w4^-1;
w6:=w3*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

/* list of subgroups of Fi22 */

DataFi22 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Fi22", generators := [a, b], order := 64561751654400>,
   
   rec <SporadicRF | name := "2.U6(2)", parent := "Fi22", generators := 
   GeneratorsFi22Max1(a,b), order := 18393661440, index := 3510>,

   rec <SporadicRF | name := "O7(3)", parent := "Fi22", generators := 
   GeneratorsFi22Max2(a,b), order := 4585351680, index := 14080>,

   rec <SporadicRF | name := "O7(3)b", parent := "Fi22", generators := 
   GeneratorsFi22Max3(a,b), order := 4585351680, index := 14080>,

   rec <SporadicRF | name := "O8+(2):S3", parent := "Fi22", generators := 
   GeneratorsFi22Max4(a,b), order := 1045094400, index := 61776>,

   rec <SporadicRF | name := "2^10:M22", parent := "Fi22", generators := 
   GeneratorsFi22Max5(a,b), order := 454164480, index := 142155>,

   rec <SporadicRF | name := "2^6:S6(2)", parent := "Fi22", generators := 
   GeneratorsFi22Max6(a,b), order := 92897280, index := 694980>,

   rec <SporadicRF | name := "(2x2^(1+8)):(U4(2):2)", parent := "Fi22", generators := 
   GeneratorsFi22Max7(a,b), order := 53084160, index := 1216215>,

   rec <SporadicRF | name := "(U4(3):2)xS3", parent := "Fi22", generators := 
   GeneratorsFi22Max8(a,b), order := 39191040, index := 1647360>,

   rec <SporadicRF | name := "^2F4(2)'", parent := "Fi22", generators := 
   GeneratorsFi22Max9(a,b), order := 17971200, index := 3592512>,

   rec <SporadicRF | name := "2^(5+8):(S3xA6)", parent := "Fi22", generators := 
   GeneratorsFi22Max10(a,b), order := 17694720, index := 3648645>,

   rec <SporadicRF | name := "3^(1+6):2^(3+4):3^2:2", parent := "Fi22", generators := 
   GeneratorsFi22Max11(a,b), order := 5038848, index := 12812800>,

   rec <SporadicRF | name := "S10", parent := "Fi22", generators := 
   GeneratorsFi22Max12(a,b), order := 3628800, index := 17791488>,

   rec <SporadicRF | name := "S10b", parent := "Fi22", generators := 
   GeneratorsFi22Max13(a,b), order := 3628800, index := 17791488>,

   rec <SporadicRF | name := "M12", parent := "Fi22", generators := 
   GeneratorsFi22Max14(a,b), order := 95040, index := 679311360>

   ];
   
   return L;
   
end function;

/* code to find standard generators of Fi22 and produce listing of maximal subgroups */

/* 
MaximalsFi22 := function (G)

   x, y := StandardGeneratorsFi22(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Fi22", DataFi22());

end function;
*/
