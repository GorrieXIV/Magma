freeze;

import "../recformat.m":SporadicRF;

/* generators for maximal subgroups of Ru */

GeneratorsRuMax1 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w8:=w7*w7;
w5:=w6*w7;
w3:=w5*w8;
w1:=w2*w2;
w4:=w3^-1;
w5:=w4*w2;
w2:=w5*w3;

   return [w1,w2];

end function;

GeneratorsRuMax2 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w1:=w2*w2;
w2:=w7^5;
w7:=w6^-1;
w3:=w7*w2;
w2:=w3*w6;

   return [w1,w2];

end function;

GeneratorsRuMax3 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w5;
w2:=w7^5;
w6:=w5^11;
w7:=w3*w6;
w6:=w7^-1;
w3:=w6*w2;
w2:=w3*w7;

   return [w1,w2];

end function;

GeneratorsRuMax4 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w1:=w2*w2;
w2:=w8^5;
w7:=w6^-1;
w4:=w7*w2;
w2:=w4*w6;
w9:=w3*w8;
w8:=w9*w9;
w7:=w8^-1;
w3:=w7*w1;
w1:=w3*w8;

   return [w1,w2];

end function;

GeneratorsRuMax5 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w1:=w2*w2;
w2:=w8^5;
w7:=w6^-1;
w4:=w7*w2;
w2:=w4*w6;
w9:=w3*w8;
w8:=w9^3;
w7:=w8^-1;
w3:=w7*w1;
w1:=w3*w8;

   return [w1,w2];

end function;

GeneratorsRuMax6 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7*w4;
w6:=w5^-1;
w9:=w6*w1;
w10:=w9*w5;
w1:=w3*w8;
w9:=w1^10;
w8:=w9*w10;
w11:=w8^6;
w8:=w7*w7;
w7:=w8^-1;
w6:=w7*w10;
w10:=w6*w8;
w8:=w9*w10;
w12:=w8^4;
w2:=w11*w12;

   return [w1,w2];

end function;

GeneratorsRuMax7 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w8:=w6*w5;
w7:=w6^7;
w9:=w7*w8;
w10:=w9^-1;
w3:=w10*w2;
w2:=w3*w9;

   return [w1,w2];

end function;

GeneratorsRuMax8 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w1:=w2*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w8:=w6*w5;
w7:=w6^8;
w9:=w7*w8;
w10:=w9^-1;
w3:=w10*w2;
w2:=w3*w9;

   return [w1,w2];

end function;

GeneratorsRuMax9 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w2:=w8^5;
w6:=w5^16;
w7:=w6^-1;
w8:=w7*w1;
w1:=w8*w6;
w4:=w3^3;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsRuMax10 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w1:=w2*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w8:=w6*w5;
w7:=w6*w6;
w9:=w8*w8;
w8:=w9*w9;
w9:=w7*w8;
w10:=w9^-1;
w3:=w10*w2;
w2:=w3*w9;

   return [w1,w2];

end function;

GeneratorsRuMax11 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w8:=w6*w5;
w10:=w8^9;
w9:=w6*w10;
w10:=w9^-1;
w3:=w10*w2;
w2:=w3*w9;

   return [w1,w2];

end function;

GeneratorsRuMax12 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w7:=w6^6;
w8:=w6*w5;
w10:=w8^10;
w9:=w7*w10;
w10:=w9^-1;
w3:=w10*w2;
w2:=w3*w9;

   return [w1,w2];

end function;

GeneratorsRuMax13 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w8:=w6*w5;
w2:=w8^5;
w6:=w5*w5;
w7:=w6^-1;
w8:=w7*w1;
w1:=w8*w6;
w4:=w3^4;
w5:=w4^-1;
w6:=w5*w2;
w2:=w6*w4;

   return [w1,w2];

end function;

GeneratorsRuMax14 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w4*w5;
w7:=w6*w5;
w8:=w7*w7;
w9:=w6*w8;
w10:=w5*w9;
w7:=w6*w6;
w8:=w7*w7;
w9:=w8*w10;
w2:=w9*w9;
w6:=w3*w5;
w7:=w6*w3;
w8:=w5^3;
w9:=w7^22;
w10:=w8*w9;
w9:=w10^-1;
w3:=w9*w2;
w2:=w3*w10;

   return [w1,w2];

end function;

GeneratorsRuMax15 := function (a,b)

   w1 := a; w2 := b;

w3:=w1*w2;
w4:=w3*w2;
w5:=w3*w4;
w6:=w3*w5;
w7:=w6*w3;
w8:=w7^3;
w9:=w5^3;
w10:=w8*w9;
w9:=w10^-1;
w11:=w10*w1;
w1:=w11*w9;
w8:=w7*w4;
w9:=w3*w8;
w10:=w9*w4;
w11:=w10*w2;
w5:=w4*w3;
w7:=w3*w6;
w6:=w5^3;
w8:=w6*w7;
w9:=w8^-1;
w10:=w9*w11;
w2:=w10*w8;

   return [w1,w2];

end function;

/* list of subgroups of Ru */

DataRu := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Ru", generators := [a, b], order := 145926144000>,
   
   rec <SporadicRF | name := "^2F4(2)", parent := "Ru", generators := 
   GeneratorsRuMax1(a,b), order := 35942400, index := 4060>,

   rec <SporadicRF | name := "2^6.U3(3).2", parent := "Ru", generators := 
   GeneratorsRuMax2(a,b), order := 774144, index := 188500>,

   rec <SporadicRF | name := "(2^2xSz(8)):3", parent := "Ru", generators := 
   GeneratorsRuMax3(a,b), order := 349440, index := 417600>,

   rec <SporadicRF | name := "2^(3+8):L3(2)", parent := "Ru", generators := 
   GeneratorsRuMax4(a,b), order := 344064, index := 424125>,

   rec <SporadicRF | name := "U3(5):2", parent := "Ru", generators := 
   GeneratorsRuMax5(a,b), order := 252000, index := 579072>,

   rec <SporadicRF | name := "2^(1+4+6).S5", parent := "Ru", generators := 
   GeneratorsRuMax6(a,b), order := 245760, index := 593775>,

   rec <SporadicRF | name := "L2(25).2.2", parent := "Ru", generators := 
   GeneratorsRuMax7(a,b), order := 31200, index := 4677120>,

   rec <SporadicRF | name := "A8", parent := "Ru", generators := 
   GeneratorsRuMax8(a,b), order := 20160, index := 7238400>,

   rec <SporadicRF | name := "L2(29)", parent := "Ru", generators := 
   GeneratorsRuMax9(a,b), order := 12180, index := 11980800>,

   rec <SporadicRF | name := "5^2:4.S5", parent := "Ru", generators := 
   GeneratorsRuMax10(a,b), order := 12000, index := 12160512>,

   rec <SporadicRF | name := "3.A6.2.2", parent := "Ru", generators := 
   GeneratorsRuMax11(a,b), order := 4320, index := 33779200>,

   rec <SporadicRF | name := "5^(1+2):[2^5]", parent := "Ru", generators := 
   GeneratorsRuMax12(a,b), order := 4000, index := 36481536>,

   rec <SporadicRF | name := "L2(13):2", parent := "Ru", generators := 
   GeneratorsRuMax13(a,b), order := 2184, index := 66816000>,

   rec <SporadicRF | name := "A6.2.2", parent := "Ru", generators := 
   GeneratorsRuMax14(a,b), order := 1440, index := 101337600>,

   rec <SporadicRF | name := "(5:4)xA5", parent := "Ru", generators := 
   GeneratorsRuMax15(a,b), order := 1200, index := 121605120>
   ];
   
   return L;
   
end function;

/* code to find standard generators of Ru and produce listing of maximal subgroups */

/* 
MaximalsRu := function (G)

   x, y := StandardGeneratorsRu(G);
   if Type(x) eq BoolElt then "Unable to find Standard Generators"; return false; end if;

   G := sub<G|x[1],x[2]>;
   return ListMaximals(G, "Ru", DataRu());

end function;
*/
