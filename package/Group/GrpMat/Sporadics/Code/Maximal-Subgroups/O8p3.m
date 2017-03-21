freeze;

import "../recformat.m":SporadicRF;
  
/* list of subgroups of O8p3 */

DataO8p3 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "O8p3", generators := [a, b], 
       order := 4952179814400>,
   rec <SporadicRF | name := "O73", parent := "O8p3", generators := 
	[a, b^2 * a * b^2], order := 4585351680, index := 1080>,
   rec <SporadicRF | name := "O73", parent := "O8p3", generators := 
	[a, b * a * b^2 * a * b^2 * a * b^4], order := 4585351680, index := 1080>,
   rec <SporadicRF | name := "3^6:L43", parent := "O8p3", generators := 
        [a, a * b * a * b^3], order := 4421589120, index := 1120>,
   rec <SporadicRF | name := "O8p2", parent := "O8p3", generators := 
        [a, a * b * a * b * a * b * a * b^2 * a * b], order := 174182400, index := 28431>,
   rec <SporadicRF | name := "O8p2", parent := "O8p3", generators := 
        [a, a * b * a * b^2 * a * b * a * b * a * b], order := 174182400, index := 28431>,
   rec <SporadicRF | name := "O8p2", parent := "O8p3", generators := 
        [a, a * b * a * b^3 * a * b * a * b^2 * a * b], order := 174182400, index := 28431>,
   rec <SporadicRF | name := "O8p2", parent := "O8p3", generators := 
        [a, a * b * a * b^2 * a * b * a * b^3 * a * b], order := 174182400, index := 28431>
       
   ];
   
   return L;
   
end function;
