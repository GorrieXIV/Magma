freeze;

/* black box recognition procedure for J1 */

import "../Presentations/J1.m":PresentationJ1;
 
StandardGeneratorsJ1 := function (G : Projective := false, Limit := 300)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, 3, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 7 and Fct (a * b * a * b^2) eq 19) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
