freeze;

import "../recformat.m":SporadicRF;
  
/* list of subgroups of 2.O8p3 */

Data2O8p3 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "2O8p3", generators := [a, b], 
       order := 9904359628800>,
   rec <SporadicRF | name := "O73", parent := "2O8p3", generators := 
	[a, b^2 * a * b^2], order := 4585351680, index := 2160>,
   rec <SporadicRF | name := "O73", parent := "2O8p3", generators := 
	[a, b * a * b^2 * a * b^2 * a * b^4], order := 4585351680, index := 2160>,
   rec <SporadicRF | name := "3^6:L43", parent := "2O8p3", generators := 
        [a, a * b * a * b^3], order := 4421589120, index := 2240>,
   rec <SporadicRF | name := "O8p2", parent := "2O8p3", generators := 
        [a, a * b * a * b * a * b * a * b^2 * a * b], order := 174182400, index := 56862>,
   rec <SporadicRF | name := "O8p2", parent := "2O8p3", generators := 
        [a, a * b * a * b^2 * a * b * a * b * a * b], order := 174182400, index := 56862>,
   rec <SporadicRF | name := "O8p2", parent := "2O8p3", generators := 
        [a, a * b * a * b^3 * a * b * a * b^2 * a * b], order := 174182400, index := 56862>,
   rec <SporadicRF | name := "O8p2", parent := "2O8p3", generators := 
        [a, a * b * a * b^2 * a * b * a * b^3 * a * b], order := 174182400, index := 56862>
       
   ];
   
   return L;
   
end function;
