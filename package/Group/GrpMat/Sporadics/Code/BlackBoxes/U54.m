freeze;

/* black box recognition procedure for U5(4) */

import "../Presentations/U54.m":PresentationU54;
 
StandardGeneratorsU54 := function (G : Projective := false, Limit := 500)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {8,12,20,26,30}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {12}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);
     
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 41 and Fct (a * b^2) eq 15 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
