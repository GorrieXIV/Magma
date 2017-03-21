freeze;

/* black box recognition procedure for McL */

import "../Presentations/McL.m":PresentationMcL;
 
StandardGeneratorsMcL := function (G : Projective := false, Limit := 100)

   Fct := Projective select CentralOrder else Order;
   
   P := RandomProcessWithWords (G); 
   x, xw := ElementOfOrder (P, 2, Limit: Fct := Fct);
   if Type (x) eq BoolElt then return false, _; end if;
   g, w := ElementOfOrder (P, {10,15}, Limit: Fct := Fct);
   if Type (g) eq BoolElt then return false, _; end if;

   o := Fct (g);
   b := g^(o div 5); bw := w^(o div 5);

   nmr := Limit;
   repeat 
      nmr -:= 1;
      c, cw := Random (P);
      a := x^c;
   until (Fct (a * b) eq 11 and Fct ((a * b)^2 * (a * b * a * b^2)^2 * a * b^2) eq 7) or nmr eq 0;

   if nmr eq 0 then return false, _; end if;

   aw := xw^cw; 

   return [a, b], [aw, bw];

end function;
