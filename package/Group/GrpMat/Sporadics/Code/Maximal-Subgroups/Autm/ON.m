freeze;

import "../../recformat.m": SporadicRF;
import "../../List.m": ListMaximals;
import "../../BlackBoxes/Autm/ON.m":StandardGeneratorsONAutm;

/* generators for maximal subgroups of ON.2 */

GeneratorsONAutmMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w2*w2;
w4:=w1*w3;
w5:=w4*w4;
w6:=w5^-1;
w7:=w3*w5;
w1:=w6*w7;

   return [w1,w2];

end function;

GeneratorsONAutMax2 := function (a,b)

   w1 := a; w2:= b;

w3:=w2*w2;
w4:=w1*w2;
w5:=w3*w4;
w6:=w4*w4;
w7:=w5*w6;
w3:=w5^-1;
w4:=w1*w3;
w3:=w1*w5;
w6:=w4*w3;
w3:=w6^5;
w4:=w7^-1;
w6:=w1*w4;
w4:=w1*w7;
w1:=w5*w3;
w3:=w6*w4;
w4:=w3^9;
w2:=w7*w4;

    return [w1,w2];

end function;

GeneratorsONAutMax3 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4^18;
w6:=w2*w2;
w7:=w3*w4;
w8:=w4*w3;
w3:=w7*w8;
w4:=w3^-1;
w2:=w6*w4;
w4:=w6*w3;
w6:=w2*w4;
w4:=w6^9;
w2:=w5*w1;
w1:=w3*w4;

   return [w1,w2];

end function;

GeneratorsONAutMax4 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4^5;
w6:=w4*w4;
w4:=w3*w3;
w7:=w6*w4;
w4:=w7^4;
w6:=w3*w5;
w2:=w6^-1;
w3:=w2*w4;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsONAutMax5 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w3*w3;
w7:=w5*w6;
w6:=w7^7;
w8:=w7*w1;
w7:=w3*w5;
w3:=w7*w4;
w4:=w3*w5;
w3:=w4*w5;
w4:=w3*w8;
w3:=w4^-1;
w5:=w3*w6;
w1:=w5*w4;

   return [w1,w2];

end function;

GeneratorsONAutMax6 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w4;
w4:=w5*w5;
w5:=w3^3;
w7:=w4*w5;
w4:=w7^5;
w5:=w3*w6;
w7:=w5*w6;
w5:=w7*w3;
w3:=w5*w1;
w1:=w2*w2;
w2:=w3^-1;
w5:=w2*w4;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsONAutMax7 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w5;
w4:=w3^3;
w3:=w6*w4;
w1:=w3^5;
w4:=w2*w2;
w2:=w3*w6;
w3:=w2*w5;
w2:=w3^-1;
w5:=w2*w4;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsONAutMax8 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w3;
w7:=w6*w3;
w6:=w5*w7;
w5:=w6*w3;
w6:=w4*w3;
w4:=w6*w7;
w3:=w5^4;
w2:=w4^-1;
w5:=w2*w3;
w2:=w5*w4;

   return [w1,w2];

end function;

GeneratorsONAutMax9 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w4*w3;
w4:=w6*w6;
w6:=w5*w5;
w5:=w3^3;
w3:=w6*w5;
w5:=w3^10;
w3:=w4*w2;
w2:=w3^-1;
w4:=w2*w5;
w2:=w4*w3;

   return [w1,w2];

end function;

GeneratorsONAutMax10 := function (a,b)

   w1 := a; w2:= b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w4*w2;
w6:=w5*w3;
w7:=w5*w6;
w8:=w3*w3;
w3:=w7*w8;
w5:=w3^10;
w3:=w2*w2;
w2:=w3*w6;
w3:=w2*w4;
w4:=w3*w6;
w2:=w4^-1;
w3:=w2*w5;
w2:=w3*w4;

   return [w1,w2];

end function;

/* list of subgroups of ON:2 */

DataONAutm := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "ON:2", generators := [a, b], order := 921631011840>,
   
   rec <SporadicRF | name := "ON", parent := "ON:2", generators := GeneratorsONAutmMax1(a,b), order := 460815505920, index := 2>,

   rec <SporadicRF | name :="7^{1+2} : (3 x D_{16})", parent := "ON:2", generators := GeneratorsONAutMax2(a,b), order := 16464, index := 55978560>,

   rec <SporadicRF | name := "J_1 x 2", parent := "ON:2", generators := GeneratorsONAutMax3(a,b), order := 351120, index := 2624832>,

   rec <SporadicRF | name := "4.PSL(3,4).2.2", parent := "ON:2", generators := GeneratorsONAutMax4(a,b), order := 322560, index := 2857239>,

   rec <SporadicRF | name := "(3^2 : 4 x Alt(6)).2.2", parent := "ON:2", generators := GeneratorsONAutMax5(a,b), order := 51840, index := 17778376>,

   rec <SporadicRF | name := "3^4 : 2^{1+4}.D_{10}.2", parent := "ON:2", generators := GeneratorsONAutMax6(a,b), order := 51840, index := 17778376>,

   rec <SporadicRF | name := "31 : 30", parent := "ON:2", generators := GeneratorsONAutMax7(a,b), order := 930, index := 991001088>,

   rec <SporadicRF | name := "4^3.(PSL(3,2) x 2)", parent := "ON:2", generators := GeneratorsONAutMax8(a,b), order := 21504, index := 42858585>,

   rec <SporadicRF | name := "Alt(6) : 2", parent := "ON:2", generators := GeneratorsONAutMax10(a,b), order := 720, index := 1280043072>,

   rec <SporadicRF | name := "PSL(2,7) : 2", parent := "ON:2", generators := GeneratorsONAutMax9(a,b), order := 336, index := 5485898880>

   ];
   
   return L;
   
end function;

/* code to find standard generators of ON:2 and produce 
   listing of maximal subgroups */

MaximalsONAutm := function (G)

   x, y := StandardGeneratorsONAutm(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "ON:2", DataONAutm());

end function;
