freeze;

/* black box recognition procedure for U3(7) */

import "../Presentations/U37.m":PresentationU37;
 
StandardGeneratorsU37 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {6,12,24,48}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   
   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);

   b := g^(o div 3); 
   bw := w^(o div 3);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 43 and Fct ((a * b)^2 * b) eq 4 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
