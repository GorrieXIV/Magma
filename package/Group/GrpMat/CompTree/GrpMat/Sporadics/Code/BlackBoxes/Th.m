freeze;

/* black box recognition procedure for Th */

import "../Presentations/Th.m":PresentationTh;
 
StandardGeneratorsTh := function (G : Projective := false, Limit := 600)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   g, w := ElementOfOrder (P, {21,39}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   b := g^(o div 3); bw := w^(o div 3);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until Fct (a * b) eq 19 or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
