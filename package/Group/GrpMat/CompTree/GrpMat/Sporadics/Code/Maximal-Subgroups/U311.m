freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of U37 */
  
/* list of subgroups of U311 */

DataU311 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "U311", generators := [a, b], 
       order := 70915680>,
   
   rec <SporadicRF | name := "11^(1+2):40", parent := "U311", generators := 
   [a, (a * b)^6 * (a * b^2)^3 * (a * b)^2], order := 53240, index := 1332>
       
   ];
   
   return L;
   
end function;
