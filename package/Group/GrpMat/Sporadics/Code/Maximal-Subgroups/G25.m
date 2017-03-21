freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of G25 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max1W1
GeneratorsG25Max1 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w8 * w3;
  w2 := w8^3;
  w4 := w8 * w3;
  w5 := w4^5;
  w6 := w5^-1;
  w7 := w6 * w2;
  w1 := w7 * w5;
  w8 := w9^23;
  w7 := w8^-1;
  w3 := w7 * w2;
  w2 := w3 * w8;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max2W1
GeneratorsG25Max2 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w8 * w3;
  w1 := w8^3;
  w7 := w6 * w4;
  w6 := w7 * w5;
  w7 := w6 * w8;
  w2 := w7^6;
  w4 := w8 * w3;
  w8 := w9^24;
  w7 := w8^-1;
  w3 := w7 * w2;
  w2 := w3 * w8;
  return [w1,w2];
end function;  
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max3W1
GeneratorsG25Max3 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w3;
  w7 := w6 * w6;
  w1 := w5 * w7;
  w6 := w4 * w4;
  w7 := w5 * w5;
  w8 := w3 * w7;
  w9 := w8 * w8;
  w7 := w8 * w9;
  w5 := w7 * w6;
  w8 := w6 * w6;
  w7 := w8 * w4;
  w2 := w7 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max4W1
GeneratorsG25Max4 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6^12;
  w8 := w7^-1;
  w3 := w8 * w2;
  w2 := w3 * w7;
  return [w1,w2];
end function;


// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max5W1
GeneratorsG25Max5 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w4 * w5;
  w11 := w10 * w8;
  w1 := w6 * w11;
  w12 := w9 * w11;
  w13 := w12 * w5;
  w2 := w13 * w8;
  w5 := w1^12;
  w6 := w2^15;
  w12 := w5 * w6;
  w13 := w12^10;
  w14 := w13^-1;
  w15 := w14 * w2;
  w2 := w15 * w13;
  return [w1,w2];
end function;
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max6W1
GeneratorsG25Max6 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w8 * w3;
  w2 := w8^3;
  w4 := w8 * w3;
  w5 := w4^-1;
  w6 := w4 * w1;
  w1 := w6 * w5;
  w8 := w9^20;
  w7 := w8^-1;
  w3 := w7 * w2;
  w2 := w3 * w8;
  return [w1,w2];
end function;
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G25/words/G25G1-max7W1
GeneratorsG25Max7 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w6;
  w8 := w7^-1;
  w6 := w8 * w1;
  w1 := w6 * w7;
  w4 := w5^5;
  w5 := w4^-1;
  w3 := w5 * w2;
  w2 := w3 * w4;
  return [w1,w2];
end function;
  
  
/* list of subgroups of G25 */

DataG25 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "G25", generators := [a, b], 
       order := 5859000000>,
  
   rec <SporadicRF | name := "5^(1+4):GL25", parent := "G25", generators := 
   GeneratorsG25Max1([a,b]), order := 1500000, index := 3906>,

   rec <SporadicRF | name := "5^(3+2):GL25", parent := "G25", generators := 
   GeneratorsG25Max2([a,b]), order := 1500000, index := 3906>,

   rec <SporadicRF | name := "3U35d2", parent := "G25", generators := 
   GeneratorsG25Max3([a,b]), order := 756000, index := 7750>,
       
   rec <SporadicRF | name := "L35d2", parent := "G25", generators := 
   GeneratorsG25Max4([a,b]), order := 744000, index := 7875>,

   rec <SporadicRF | name := "2.(A5xA5).2", parent := "G25", generators := 
   GeneratorsG25Max5([a,b]), order := 14400, index := 406875>,

   rec <SporadicRF | name := "U33d2", parent := "G25", generators := 
   GeneratorsG25Max6([a,b]), order := 12096, index := 484375>,

   rec <SporadicRF | name := "2^3.L32", parent := "G25", generators := 
   GeneratorsG25Max7([a,b]), order := 1344, index := 4359375>
       
   ];
   
   return L;
   
end function;
