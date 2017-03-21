freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of G24 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max1W1
GeneratorsG24Max1 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w9 * w4;
  w3 := w10 * w10;
  w1 := w10 * w3;
  w5 := w4 * w4;
  w4 := w5 * w5;
  w5 := w4^-1;
  w7 := w8 * w8;
  w6 := w8 * w7;
  w8 := w7 * w6;
  w9 := w5 * w8;
  w2 := w9 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max2W1
GeneratorsG24Max2 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w7 * w4;
  w9 := w3 * w8;
  w10 := w9 * w4;
  w3 := w10 * w10;
  w1 := w10 * w3;
  w5 := w4 * w4;
  w7 := w5 * w5;
  w6 := w7 * w5;
  w5 := w4 * w6;
  w7 := w8 * w8;
  w4 := w8 * w7;
  w8 := w7 * w4;
  w9 := w6 * w8;
  w2 := w9 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max3W1
GeneratorsG24Max3 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w1 * w6;
  w3 := w7 * w4;
  w7 := w3 * w5;
  w1 := w7^5;
  w7 := w4^-1;
  w3 := w4 * w1;
  w1 := w3 * w7;
  w7 := w6^9;
  w6 := w7^-1;
  w4 := w6 * w5;
  w2 := w4 * w7;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max4W1
GeneratorsG24Max4 := function(S)
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
  w10 := w9 * w4;
  w9 := w10 * w10;
  w1 := w10 * w9;
  w6 := w3 * w3;
  w3 := w6 * w6;
  w6 := w3^-1;
  w7 := w6 * w1;
  w1 := w7 * w3;
  w5 := w4 * w4;
  w4 := w5 * w5;
  w5 := w4^-1;
  w7 := w8 * w8;
  w6 := w8 * w7;
  w9 := w7 * w6;
  w8 := w9 * w9;
  w9 := w5 * w8;
  w2 := w9 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max5W1
GeneratorsG24Max5 := function(S)
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
  w10 := w9 * w4;
  w9 := w10 * w10;
  w1 := w10 * w9;
  w6 := w3 * w3;
  w7 := w3 * w6;
  w3 := w6 * w7;
  w6 := w3^-1;
  w7 := w6 * w1;
  w1 := w7 * w3;
  w5 := w4^-1;
  w7 := w8 * w8;
  w6 := w8 * w7;
  w8 := w7 * w6;
  w9 := w5 * w8;
  w2 := w9 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max6W1
GeneratorsG24Max6 := function(S)
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
  w10 := w9 * w4;
  w9 := w10 * w10;
  w1 := w10 * w9;
  w6 := w3 * w3;
  w3 := w6^-1;
  w7 := w6 * w1;
  w1 := w7 * w3;
  w5 := w4 * w4;
  w4 := w5 * w5;
  w5 := w4^-1;
  w7 := w8 * w8;
  w6 := w8 * w7;
  w9 := w7 * w6;
  w8 := w9 * w9;
  w9 := w4 * w8;
  w2 := w9 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max7W1
GeneratorsG24Max7 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w4;
  w6 := w7 * w5;
  w7 := w1 * w6;
  w1 := w7^5;
  w5 := w4^9;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  w4 := w3^3;
  w5 := w4^-1;
  w7 := w5 * w1;
  w1 := w7 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G24/words/G24G1-max8W1
GeneratorsG24Max8 := function(S)
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
  w10 := w9 * w4;
  w3 := w10 * w10;
  w1 := w10 * w3;
  w7 := w6 * w6;
  w4 := w6 * w7;
  w3 := w4^-1;
  w6 := w4 * w1;
  w1 := w6 * w3;
  w7 := w8 * w8;
  w6 := w8 * w7;
  w8 := w7 * w6;
  w6 := w5 * w5;
  w5 := w6^-1;
  w9 := w5 * w8;
  w2 := w9 * w6;
  return [w1,w2];
end function;

  
/* list of subgroups of G24 */

DataG24 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "G24", generators := [a, b], 
       order := 251596800>,
  
   rec <SporadicRF | name := "J2", parent := "G24", generators := 
   GeneratorsG24Max1(a,b), order := 604800, index := 416>,

   rec <SporadicRF | name := "2^(2+8):(A5x3)", parent := "G24", generators := 
   GeneratorsG24Max2(a,b), order := 184320, index := 1365>,

   rec <SporadicRF | name := "2^(4+6):(A5x3)", parent := "G24", generators := 
   GeneratorsG24Max3([a,b]), order := 184320, index := 1365>,

   rec <SporadicRF | name := "U34d2", parent := "G24", generators := 
   GeneratorsG24Max4([a,b]), order := 124800, index := 2016>,

   rec <SporadicRF | name := "3L34d2", parent := "G24", generators := 
   GeneratorsG24Max5([a,b]), order := 120960, index := 2080>,

   rec <SporadicRF | name := "U33d2", parent := "G24", generators := 
   GeneratorsG24Max6([a,b]), order := 12096, index := 20800>,

   rec <SporadicRF | name := "A5xA5", parent := "G24", generators := 
   GeneratorsG24Max7([a,b]), order := 3600, index := 69888>,

   rec <SporadicRF | name := "L213", parent := "G24", generators := 
   GeneratorsG24Max8([a,b]), order := 1092, index := 230400>
      
   ];
   
   return L;
   
end function;
