freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of G25 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max1W1
GeneratorsTD42Max1 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w2 := w7 * w7;
  w5 := w6 * w6;
  w1 := w6 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max2W1
GeneratorsTD42Max2 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w5 * w2;
  w7 := w6 * w2;
  w2 := w7 * w7;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max3W1
GeneratorsTD42Max3 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w2 := w6 * w6;
  w1 := w6 * w2;
  w4 := w5^7;
  w5 := w4^-1;
  w3 := w5 * w2;
  w2 := w3 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max4W1
GeneratorsTD42Max4 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w2 := w6 * w6;
  w1 := w6 * w2;
  w4 := w5^4;
  w5 := w4^-1;
  w6 := w5 * w1;
  w1 := w6 * w4;
  w4 := w3^12;
  w5 := w4^-1;
  w6 := w5 * w2;
  w2 := w6 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max5W1
GeneratorsTD42Max5 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w1 := w6^3;
  w6 := w4 * w2;
  w2 := w4 * w6;
  w4 := w5^9;
  w5 := w4^-1;
  w6 := w5 * w2;
  w2 := w6 * w4;
  w4 := w3^9;
  w5 := w4^-1;
  w6 := w5 * w1;
  w1 := w6 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max6W1
GeneratorsTD42Max6 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w5 := w6 * w6;
  w1 := w6 * w5;
  w4 := w2 * w2;
  w5 := w2 * w4;
  w2 := w5 * w5;
  w4 := w3^7;
  w3 := w4^-1;
  w5 := w3 * w1;
  w1 := w5 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max7W1
GeneratorsTD42Max7 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w1 := w6^2;
  w6 := w4 * w2;
  w7 := w4 * w6;
  w2 := w7 * w6;
  w6 := w3^3;
  w7 := w6^-1;
  w4 := w7 * w2;
  w2 := w4 * w6;
  w6 := w5^12;
  w5 := w6^-1;
  w4 := w5 * w1;
  w1 := w4 * w6;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max8W1
GeneratorsTD42Max8 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w8 := w6 * w5;
  w9 := w3 * w8;
  w1 := w6^2;
  w6 := w4 * w2;
  w7 := w4 * w6;
  w2 := w7 * w6;
  w6 := w8^25;
  w7 := w6^-1;
  w4 := w7 * w2;
  w2 := w4 * w6;
  w6 := w9^18;
  w5 := w6^-1;
  w4 := w5 * w1;
  w1 := w4 * w6;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/TD42/words/TD42G1-max9W1
GeneratorsTD42Max9 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w1 := w6^3;
  w6 := w4 * w2;
  w7 := w4 * w6;
  w2 := w7 * w6;
  w6 := w5^8;
  w5 := w6^-1;
  w4 := w5 * w2;
  w2 := w4 * w6;
  w6 := w3^4;
  w5 := w6^-1;
  w4 := w5 * w1;
  w1 := w4 * w6;
  return [w1,w2];
end function;


/* list of subgroups of TD42 */

DataTD42 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "TD42", generators := [a, b], 
       order := 211341312>,
  
   rec <SporadicRF | name := "2^(1+8):L28", parent := "TD42", generators := 
   GeneratorsTD42Max1([a,b]), order := 258048, index := 819>,

   rec <SporadicRF | name := "[2^11]:(7xS3)", parent := "TD42", generators := 
   GeneratorsTD42Max2([a,b]), order := 86016, index := 2457>,

   rec <SporadicRF | name := "U33d2", parent := "TD42", generators := 
   GeneratorsTD42Max3([a,b]), order := 12096, index := 17472>,

   rec <SporadicRF | name := "S3xL28", parent := "TD42", generators := 
   GeneratorsTD42Max4([a,b]), order := 3024, index := 69888>,

   rec <SporadicRF | name := "(7xL27):2", parent := "TD42", generators := 
   GeneratorsTD42Max5([a,b]), order := 2352, index := 89856>,

   rec <SporadicRF | name := "3^(1+2).2S4", parent := "TD42", generators := 
   GeneratorsTD42Max6([a,b]), order := 1296, index := 163072>,

   rec <SporadicRF | name := "7^2:2A4", parent := "TD42", generators := 
   GeneratorsTD42Max7([a,b]), order := 1176, index := 179712>,

   rec <SporadicRF | name := "3^2:2A4", parent := "TD42", generators := 
   GeneratorsTD42Max8([a,b]), order := 216, index := 978432>,

   rec <SporadicRF | name := "13:4", parent := "TD42", generators := 
   GeneratorsTD42Max9([a,b]), order := 52, index := 4064256>
   
   ];
   
   return L;
   
end function;
