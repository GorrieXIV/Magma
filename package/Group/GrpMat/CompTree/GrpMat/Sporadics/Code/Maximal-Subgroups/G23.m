freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of G23 */

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max1W1
GeneratorsG23Max1 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w1 * w8;
  w2 := w7 * w7;
  w5 := w4^6;
  w4 := w5^-1;
  w3 := w4 * w2;
  w2 := w3 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max2W1
GeneratorsG23Max2 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w1 * w8;
  w2 := w7 * w7;
  w5 := w4^4;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  w4 := w3^-1;
  w5 := w4 * w1;
  w1 := w5 * w3;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max3W1
GeneratorsG23Max3 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w2 * w7;
  w5 := w4^3;
  w6 := w5^-1;
  w7 := w6 * w8;
  w2 := w7 * w5;
  w4 := w3^6;
  w5 := w4^-1;
  w6 := w5 * w1;
  w1 := w6 * w4;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max4W1
GeneratorsG23Max4 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w2 * w7;
  w5 := w4 * w4;
  w6 := w5^-1;
  w7 := w6 * w8;
  w2 := w7 * w5;
  return [w1,w2];
end function;
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max5W1
GeneratorsG23Max5 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w3 * w8;
  w2 := w7 * w7;
  w4 := w3^-1;
  w5 := w4 * w1;
  w1 := w5 * w3;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max6W1
GeneratorsG23Max6 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w3 * w8;
  w2 := w7 * w7;
  w5 := w4^10;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max7W1
GeneratorsG23Max7 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w1 * w8;
  w2 := w7 * w7;
  w5 := w4 * w4;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  w4 := w3 * w3;
  w3 := w4^-1;
  w5 := w3 * w1;
  w1 := w5 * w4;
  return [w1,w2];
end function;
  
// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max8W1
GeneratorsG23Max8 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w1 * w8;
  w2 := w7 * w7;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max9W1
GeneratorsG23Max9 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6 * w3;
  w8 := w6 * w7;
  w7 := w3 * w8;
  w2 := w7 * w7;
  w5 := w4 * w4;
  w6 := w5^-1;
  w7 := w6 * w2;
  w2 := w7 * w5;
  return [w1,w2];
end function;

// BBOX converted automatically from
// http://brauer.maths.qmul.ac.uk/Atlas/exc/G23/words/G23G1-max10W1
GeneratorsG23Max10 := function(a,b)
  // WARNING! This is not an SLP!
  w1 := a;
  w2 := b;
  w3 := w1 * w2;
  w4 := w3 * w2;
  w5 := w3 * w4;
  w6 := w3 * w5;
  w7 := w6^4;
  w8 := w1 * w7;
  w4 := w8^3;
  w8 := w2 * w7;
  w9 := w8^-1;
  w8 := w7 * w2;
  w5 := w9 * w8;
  w8 := w5^4;
  w5 := w2 * w8;
  w2 := w4 * w5;
  w8 := w3 * w7;
  w9 := w8^-1;
  w8 := w7 * w3;
  w5 := w9 * w8;
  w3 := w5^3;
  return [w6, w2, w3];
end function;
  
  
/* list of subgroups of G23 */

DataG23 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "G23", generators := [a, b], 
       order := 4245696>,
  
   rec <SporadicRF | name := "U33d2", parent := "G23", generators := 
   GeneratorsG23Max1(a,b), order := 12096, index := 351>,

   rec <SporadicRF | name := "U33d2", parent := "G23", generators := 
   GeneratorsG23Max2(a,b), order := 12096, index := 351>,

   rec <SporadicRF | name := "(3^2 x 3^(1+2)).2S4", parent := "G23", 
       generators := GeneratorsG23Max3(a,b), order := 11664, index := 364>,

   rec <SporadicRF | name := "(3^2 x 3^(1+2)).2S4", parent := "G23", 
       generators := GeneratorsG23Max4(a,b), order := 11664, index := 364>,

   rec <SporadicRF | name := "L33d2", parent := "G23", 
       generators := GeneratorsG23Max5(a,b), order := 11232, index := 378>,

   rec <SporadicRF | name := "L33d2", parent := "G23", 
       generators := GeneratorsG23Max6(a,b), order := 11232, index := 378>,

   rec <SporadicRF | name := "L28d3", parent := "G23", 
       generators := GeneratorsG23Max7(a,b), order := 1512, index := 2808>,

   rec <SporadicRF | name := "2^3.L32", parent := "G23", 
       generators := GeneratorsG23Max8(a,b), order := 1344, index := 3159>,

   rec <SporadicRF | name := "L213", parent := "G23", 
       generators := GeneratorsG23Max9(a,b), order := 1092, index := 3888>,

   rec <SporadicRF | name := "2^(1+4):3^2:2", parent := "G23", 
       generators := GeneratorsG23Max10(a,b), order := 576, index := 7371>
       
   ];
   
   return L;
   
end function;
