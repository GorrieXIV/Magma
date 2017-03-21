freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of S82 */

GeneratorsS82Max1 := function(S)
 
    T := SLPGroup (2);
    w21 := T.1^-1; w28 := T.2^2; w12 := w21 * w28; w29 := T.2^3; w9 := T.1 * 
    w29; w3 := w12 * w9; w23 := T.2 * w21; w41 := w21 * w23; w43 := T.2^-1; w6 
    := w43 * w21; w47 := w23 * w6; w20 := w41 * w47; w32 := w3 * w20; 

    w21 := T.1^-1; w26 := w21 * T.2; w36 := T.1 * T.2; w22 := w26 * w36; w43 := 
    T.2^-1; w27 := T.1 * w43; w18 := w27 * w26; w16 := w22 * w18; w13 := T.1^4; 
    w29 := T.2^3; w4 := w29 * w21; w33 := w13 * w4; w25 := w16 * w33; 

    words := [w32, w25];
    return Evaluate (words, S);
end function;

/* list of subgroups of S82 */

DataS82 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "S82", generators := [a, b], 
       order := 47377612800>,
   
   rec <SporadicRF | name := "2^7:S62", parent := "S82", generators := 
   GeneratorsS82Max1([a,b]), order := 185794560, index := 255>
       
   ];
   
   return L;
end function;
