freeze;

/* black box recognition procedure for McL:2 */

import "../../Presentations/Autm/McL.m":PresentationMcLAutm;

StandardGeneratorsMcLAutm := function (G : Projective := false, Limit := 250)

   Fct := Projective select CentralOrder else Order;

   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, 22, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o1 := Fct (g);
   x := g^(o1 div 2); xw := w^(o1 div 2);

   nmr0 := 10;
   repeat
      nmr0 -:= 1;

      h, v := ElementOfOrder (P, 6, Limit: Fct := Fct);
      if Type (h) eq BoolElt then return false, _; end if;

      o2 := Fct (h);
      b := h^(o2 div 3); bw := v^(o2 div 3);
 
      nmr := Limit;
      repeat 
         nmr -:= 1;
         c, cw := Random (P);
         a := x^c;
      until (Fct (a * b) eq 22 and Fct ((a*b)^2*(a*b*a*b^2)^2*a*b^2) eq 24) or nmr eq 0;

      aw := xw^cw; 
   
   until nmr ne 0 or nmr0 eq 0;
   
   if nmr0 eq 0 then return false, _; end if;

   return [a, b], [aw, bw];

end function;
