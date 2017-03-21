freeze;

/* black box recognition procedure for M22.2 */

import "../../Presentations/Autm/M22.m":PresentationM22Autm;

StandardGeneratorsM22Autm := function (G : Projective := false, Limit := 40)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 12, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   h, v := ElementOfOrder (P, 14, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if;

   o1 := Fct (g); o2 := Fct(h);
   x := h^(o2 div 2); xw := v^(o2 div 2);
   b := g^(o1 div 4); bw := w^(o1 div 4);

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 11 and Fct (a * b * a * b^2) eq 10) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw;

   return [a, b], [aw, bw];

end function;
