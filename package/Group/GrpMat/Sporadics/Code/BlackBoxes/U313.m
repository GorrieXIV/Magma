freeze;

/* black box recognition procedure for U3(13) */

import "../Presentations/U313.m":PresentationU313;
 
StandardGeneratorsU313 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, {2}, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {3}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;
      
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 42 and Fct ((a * b)^3 * b) eq 7 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
