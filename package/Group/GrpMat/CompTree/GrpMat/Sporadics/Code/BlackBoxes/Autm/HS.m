freeze;

/* black box recognition procedure for HS.2 */

import "../../Presentations/Autm/HS.m":PresentationHSAutm;

StandardGeneratorsHSAutm := function (G : Projective := false, Limit := 150)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   y, yw := ElementOfOrder (P, 30, Limit: Fct := Fct);
   if Type (y) eq BoolElt then return false, _; end if;

   o := Fct (y);
   x := y^(o div 2); xw := yw^(o div 2);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * y) eq 5 and Fct (a * y^3) eq 20) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   b := a*y;
   bw := aw*yw;

   return [a, b], [aw, bw];

end function;
