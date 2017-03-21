freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of F42 */

  // BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/F42/words/F42G1-max3W1
GeneratorsF42Max1 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w3;
  w6 := w5 * w4;
  w2 := w6^6;
  w6 := w4 * w5;
  w1 := w6^15;
  w7 := w4^-1;
  w8 := w7 * w2;
  w2 := w8 * w4;
  w5 := w3^4;
  w6 := w5^-1;
  w7 := w6 * w1;
  w1 := w7 * w5;
  return [w1,w2];
end function;

/* list of subgroups of F42 */

DataF42 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "F42", generators := [a, b], 
       order := 3311126603366400>,
   
   rec <SporadicRF | name := "S82", parent := "F42", generators := 
   GeneratorsF42Max1(a,b), order := 47377612800, index := 69888>
   
   ];
   
   return L;
   
end function;
