freeze;

/* black box recognition procedure for O'N.2 */

import "../../Presentations/Autm/ON.m":PresentationONAutm;

StandardGeneratorsONAutm := function (G : Projective := false, Limit := 50)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {22,30,38}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   h, v := ElementOfOrder (P, {20,28,56}, Limit: Fct := Fct);
   if Type (h) eq BoolElt then return false, _; end if;

   o1 := Fct (g); o2 := Fct (h);
   x := g^(o1 div 2); xw := w^(o1 div 2);
   b := h^(o2 div 4); bw := v^(o2 div 4);

   nmr := Limit;
   repeat
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 22 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
