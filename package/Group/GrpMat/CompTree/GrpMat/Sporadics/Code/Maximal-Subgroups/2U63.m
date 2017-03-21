freeze;

import "../recformat.m":SporadicRF;
/* generators for maximal subgroups of 2.U63 */
  
/* list of subgroups of 2.U63 */

Data2U63 := function ()

   F<a, b> := SLPGroup (2);
   
   L := [
   rec <SporadicRF | name := "2U63", generators := [a, b], 
       order := 45674944864174080>,
   
   rec <SporadicRF | name := "3^{1+8}:4.U4(3):4", parent := "2U63", 
       generators := [a, b * a * b^5], order := 771397240320, index := 59210>,

   rec <SporadicRF | name := "U5(3)x2", parent := "2U63", 
       generators := [a, b^3], order := 516381143040, index := 88452>,

   rec <SporadicRF | name := "U5(3)x2", parent := "2U63", 
       generators := [a, a^b, a^(b^(-1)), b^2 * (a, b^2), b^4 * (a, b^4)], 
       order := 516381143040, index := 88452>
       
   ];
   
   return L;
   
end function;
