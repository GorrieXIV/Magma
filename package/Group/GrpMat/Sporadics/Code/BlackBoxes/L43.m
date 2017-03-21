freeze;

/* black box recognition procedure for L_4(3) */

import "../Presentations/L43.m":PresentationL43;

StandardGeneratorsL43 := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;

   P := RandomProcessWithWords (G); 

   g, w := ElementOfOrder (P, {10,20}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   
   o := Fct(g);
   x := g^(o div 2);
   xw := w^(o div 2);

   g, w := ElementOfOrder (P, {8}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;
   o := Fct(g);
   b := g^(o div 4); 
   bw := w^(o div 4);
   
   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 13 and Fct (a * b * b) eq 8 or nmr eq 0;
   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 
   
   return [a, b], [aw, bw];

end function;
