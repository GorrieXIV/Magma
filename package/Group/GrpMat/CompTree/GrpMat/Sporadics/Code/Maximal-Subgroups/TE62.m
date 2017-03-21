freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of TE62 */

/* list of subgroups of TE62 */

DataTE62 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "TE62", generators := [a, b], 
       order := 76532479683774853939200>,
   
   rec <SporadicRF | name := "F42", parent := "TE62", generators := 
       [(a * b)^(-5) * b * (a * b)^4, (a * b * b)^(-4) * b * (a * b * b)^4],
   order := 3311126603366400, index := 23113728>
   
   ];
   
   return L;
   
end function;
