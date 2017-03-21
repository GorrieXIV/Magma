freeze;

import "../recformat.m":SporadicRF;
  
/* list of subgroups of Sz8 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/Sz8/words/Sz8G1-max1W1
function maximal1(S)
  // WARNING! This is not an SLP!
  w1 := S.1;
  w2 := S.2;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w3 := w4 * w5;
  w5 := w3 * w3;
  w3 := w5^-1;
  w6 := w3 * w4;
  w1 := w6 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/Sz8/words/Sz8G1-max2W1
function maximal2(S)
  // WARNING! This is not an SLP!
  w1 := S.1;
  w2 := S.2;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w4^-1;
  w6 := w5 * w2;
  w2 := w6 * w4;
  w4 := w3 * w3;
  w5 := w3 * w4;
  w3 := w4 * w1;
  w1 := w3 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/Sz8/words/Sz8G1-max3W1
function maximal3(S)
  // WARNING! This is not an SLP!
  w1 := S.1;
  w2 := S.2;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w2 * w5;
  w5 := w4^-1;
  w3 := w5 * w2;
  w2 := w3 * w4;
  w5 := w6 * w6;
  w4 := w5 * w5;
  w3 := w4 * w4;
  w5 := w6 * w4;
  w4 := w3 * w1;
  w1 := w4 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/Sz8/words/Sz8G1-max4W1
function maximal4(S)
  // WARNING! This is not an SLP!
  w1 := S.1;
  w2 := S.2;
  w3 := w2 * w2;
  w4 := w3 * w3;
  w2 := w3 * w4;
  return [w1,w2];
end function;






DataSz8 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "Sz8", generators := [a, b], 
       order := 29120>,
   rec <SporadicRF | name := "2^(3+3):7", parent := "Sz8", generators := 
       maximal1(F), order := 448, index := 65>,
   rec <SporadicRF | name := "13:4", parent := "Sz8", generators := 
       maximal2(F), order := 52, index := 560>,
   rec <SporadicRF | name := "5:4", parent := "Sz8", generators := 
       maximal3(F), order := 20, index := 1456>,
   rec <SporadicRF | name := "D14", parent := "Sz8", generators := 
       maximal4(F), order := 14, index := 2080>       
   ];
   
   return L;
   
end function;
