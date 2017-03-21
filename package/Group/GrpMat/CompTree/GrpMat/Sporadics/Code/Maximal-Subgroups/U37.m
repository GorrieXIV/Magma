freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of U37 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/clas/U37/words/U37G1-max1W1
GeneratorsU37Max1 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w4 * w4;
  w4 := w3^6;
  w2 := w4 * w5;
  return [w1,w2];
end function;  

  // BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/clas/U37/words/U37G1-max2W1
GeneratorsU37Max2 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w2 := w4 * w4;
  w4 := w3^3;
  w3 := w4 * w2;
  w2 := w3 * w4;
  return [w1,w2];
end function;
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/clas/U37/words/U37G1-max3W1
GeneratorsU37Max3 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w4 * w4;
  w4 := w3 * w5;
  w5 := w3 * w4;
  w4 := w5 * w3;
  w3 := w4 * w2;
  w2 := w3 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/clas/U37/words/U37G1-max4W1
GeneratorsU37Max4 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w2 * w1;
  w4 := w3^4;
  w3 := w2 * w2;
  w2 := w4 * w3;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/clas/U37/words/U37G1-max5W1
GeneratorsU37Max5 := function(S)
  // WARNING! This is not an SLP!
  w1 := S[1];
  w2 := S[2];
  w3 := w1 * w2;
  w4 := w2 * w3;
  w1 := w3^4;
  w3 := w1 * w4;
  w1 := w3 * w3;
  return [w1,w2];
end function;
  
/* list of subgroups of U37 */

DataU37 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "U37", generators := [a, b], 
       order := 5663616>,
   
   rec <SporadicRF | name := "7^(1+2):48", parent := "U37", generators := 
   GeneratorsU37Max1([a,b]), order := 16464, index := 344>,

   rec <SporadicRF | name := "2.(L2(7) × 4).2", parent := "U37", generators := 
   GeneratorsU37Max2([a,b]), order := 2688, index := 2107>,
       
   rec <SporadicRF | name := "8^2:S3", parent := "U37", generators := 
   GeneratorsU37Max3([a,b]), order := 384, index := 14749>,

   rec <SporadicRF | name := "L2(7):2", parent := "U37", generators := 
   GeneratorsU37Max4([a,b]), order := 336, index := 16856>,

   rec <SporadicRF | name := "43:3", parent := "U37", generators := 
   GeneratorsU37Max5([a,b]), order := 129, index := 43904>
       
   ];
   
   return L;
   
end function;
