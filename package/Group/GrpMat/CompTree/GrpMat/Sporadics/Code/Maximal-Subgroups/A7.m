freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of A7 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/alt/A7/words/A7G1-max1W1
GeneratorsA7Max1 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w2 * w1;
  w5 := w4 * w3;
  w2 := w3 * w5;
  w3 := w5 * w4;
  w1 := w3 * w3;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/alt/A7/words/A7G1-max2W1
GeneratorsA7Max2 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w2 * w1;
  w4 := w3 * w2;
  w5 := w4 * w2;
  w6 := w3 * w1;
  w2 := w3 * w6;
  w1 := w4 * w5;
  return [w1,w2];
end function;



  
/* list of subgroups of A7 */

DataA7 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "A7", generators := [a, b], 
       order := 2520>,
   
   rec <SporadicRF | name := "A6", parent := "A7", generators := 
   GeneratorsA7Max1([a,b]), order := 360, index := 7>,

   rec <SporadicRF | name := "L27", parent := "A7", generators := 
   GeneratorsA7Max2([a,b]), order := 168, index := 15>
       
   ];
   
   return L;
   
end function;
