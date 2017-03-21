freeze;

/* black box recognition procedure for TD4(2) */

import "../Presentations/TD42.m":PresentationTD42;
 
StandardGeneratorsTD42 := function (G : Projective := false, Limit := 400)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   g, w := ElementOfOrder (P, {12,14,18,28}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   b, bw := ElementOfOrder (P, {9}, Limit: Fct := Fct);
   if Type (b) eq BoolElt then return false, _; end if;

   o := Fct (g);
   x := g^(o div 2); xw := w^(o div 2);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 13 and Fct (a * b^2) eq 8 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
